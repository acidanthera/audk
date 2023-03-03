/** @file
  Copyright (c) 2021, Marvin Häuser. All rights reserved.
  Copyright (c) 2022, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause
**/

#include "ImageTool.h"

#define PE_COFF_SECT_NAME_RELOC  ".reloc\0"
#define PE_COFF_SECT_NAME_RESRC  ".rsrc\0\0"
#define PE_COFF_SECT_NAME_DEBUG  ".debug\0"

static
bool
OverflowGetDestinationSize (
  IN  PE_COFF_LOADER_IMAGE_CONTEXT *Context,
  OUT UINT32                       *Size
  )
{
  UINT32 AlignedSize;
  UINT32 SegmentAlignment;

  assert (Context != NULL);
  assert (Size    != NULL);

  AlignedSize      = PeCoffGetSizeOfImage (Context);
  SegmentAlignment = PeCoffGetSectionAlignment (Context);

  if (SegmentAlignment < EFI_PAGE_SIZE) {
    SegmentAlignment = EFI_PAGE_SIZE;
  }
  //
  // The Image needs to be at least EFI_PAGE_SIZE aligned inside the calloc() buffer.
  //
  return BaseOverflowAddU32 (
    AlignedSize,
    SegmentAlignment - 1,
    Size
    );
}

static
bool
ScanPeGetHeaderInfo (
  OUT image_tool_header_info_t     *HeaderInfo,
  IN  PE_COFF_LOADER_IMAGE_CONTEXT *Context,
  IN  const char                   *ModuleType OPTIONAL
  )
{
  assert (HeaderInfo != NULL);
  assert (Context    != NULL);

  HeaderInfo->PreferredAddress  = (uint64_t)PeCoffGetImageBase (Context);
  HeaderInfo->EntryPointAddress = PeCoffGetAddressOfEntryPoint (Context);
  // FIXME:
  HeaderInfo->Machine = PeCoffGetMachine (Context);
  HeaderInfo->IsXip   = true;

  if (ModuleType == NULL) {
    HeaderInfo->Subsystem = PeCoffGetSubsystem (Context);
    return true;
  }

  if ((strcmp (ModuleType, "BASE") == 0)
    || (strcmp (ModuleType, "SEC") == 0)
    || (strcmp (ModuleType, "SECURITY_CORE") == 0)
    || (strcmp (ModuleType, "PEI_CORE") == 0)
    || (strcmp (ModuleType, "PEIM") == 0)
    || (strcmp (ModuleType, "COMBINED_PEIM_DRIVER") == 0)
    || (strcmp (ModuleType, "PIC_PEIM") == 0)
    || (strcmp (ModuleType, "RELOCATABLE_PEIM") == 0)
    || (strcmp (ModuleType, "DXE_CORE") == 0)
    || (strcmp (ModuleType, "BS_DRIVER") == 0)
    || (strcmp (ModuleType, "DXE_DRIVER") == 0)
    || (strcmp (ModuleType, "DXE_SMM_DRIVER") == 0)
    || (strcmp (ModuleType, "UEFI_DRIVER") == 0)
    || (strcmp (ModuleType, "SMM_CORE") == 0)
    || (strcmp (ModuleType, "MM_STANDALONE") == 0)
    || (strcmp (ModuleType, "MM_CORE_STANDALONE") == 0)) {
      HeaderInfo->Subsystem = EFI_IMAGE_SUBSYSTEM_EFI_BOOT_SERVICE_DRIVER;
  } else if ((strcmp (ModuleType, "UEFI_APPLICATION") == 0)
    || (strcmp (ModuleType, "APPLICATION") == 0)) {
      HeaderInfo->Subsystem = EFI_IMAGE_SUBSYSTEM_EFI_APPLICATION;
  } else if ((strcmp (ModuleType, "DXE_RUNTIME_DRIVER") == 0)
    || (strcmp (ModuleType, "RT_DRIVER") == 0)) {
      HeaderInfo->Subsystem = EFI_IMAGE_SUBSYSTEM_EFI_RUNTIME_DRIVER;
  } else if ((strcmp (ModuleType, "DXE_SAL_DRIVER") == 0)
    || (strcmp (ModuleType, "SAL_RT_DRIVER") == 0)) {
      HeaderInfo->Subsystem = EFI_IMAGE_SUBSYSTEM_SAL_RUNTIME_DRIVER;
  } else {
    fprintf (stderr, "ImageTool: Unknown EFI_FILETYPE = %s\n", ModuleType);
    return false;
  }

  return true;
}

static
bool
ScanPeGetRelocInfo (
  OUT image_tool_reloc_info_t       *RelocInfo,
  IN  PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  )
{
  BOOLEAN                               Overflow;
  UINT32                                RelocBlockRvaMax;
  UINT32                                TopOfRelocDir;
  UINT32                                RelocBlockRva;
  const EFI_IMAGE_BASE_RELOCATION_BLOCK *RelocBlock;
  UINT32                                RelocBlockSize;
  UINT32                                SizeOfRelocs;
  UINT32                                NumRelocs;
  UINT32                                RelocIndex;
  uint32_t                              RelocDirSize;
  const char                            *ImageBuffer;
  UINT16                                RelocType;
  UINT16                                RelocOffset;

  assert (RelocInfo != NULL);
  assert (Context   != NULL);

  RelocInfo->RelocsStripped = false;

  // FIXME: PE/COFF context access
  RelocBlockRva = Context->RelocDirRva;
  RelocDirSize  = Context->RelocDirSize;
  //
  // Verify the Relocation Directory is not empty.
  //
  if (RelocDirSize == 0) {
    return true;
  }

  RelocInfo->Relocs = calloc (RelocDirSize / sizeof (UINT16), sizeof (*RelocInfo->Relocs));
  if (RelocInfo->Relocs == NULL) {
    fprintf (stderr, "ImageTool: Could not allocate memory for Relocs[]\n");
    return false;
  }

  TopOfRelocDir = RelocBlockRva + RelocDirSize;

  RelocBlockRvaMax = TopOfRelocDir - sizeof (EFI_IMAGE_BASE_RELOCATION_BLOCK);
  //
  // Align TopOfRelocDir because, if the policy does not demand Relocation Block
  // sizes to be aligned, the code below will manually align them. Thus, the
  // end offset of the last Relocation Block must be compared to a manually
  // aligned Relocation Directoriy end offset.
  //
  Overflow = BaseOverflowAlignUpU32 (
                TopOfRelocDir,
                ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK),
                &TopOfRelocDir
                );
  if (Overflow) {
    fprintf (stderr, "ImageTool: Overflow during TopOfRelocDir calculation\n");
    return false;
  }
  //
  // Apply all Base Relocations of the Image.
  //
  ImageBuffer = (char *)PeCoffLoaderGetImageAddress (Context);
  while (RelocBlockRva <= RelocBlockRvaMax) {
    RelocBlock = (const EFI_IMAGE_BASE_RELOCATION_BLOCK *)(const void *)(ImageBuffer + RelocBlockRva);
    //
    // Verify the Base Relocation Block size is well-formed.
    //
    Overflow = BaseOverflowSubU32 (
                 RelocBlock->SizeOfBlock,
                 sizeof (EFI_IMAGE_BASE_RELOCATION_BLOCK),
                 &SizeOfRelocs
                 );
    if (Overflow) {
      fprintf (stderr, "ImageTool: Overflow during SizeOfRelocs calculation\n");
      return false;
    }
    //
    // Verify the Base Relocation Block is in bounds of the Relocation
    // Directory.
    //
    if (SizeOfRelocs > RelocBlockRvaMax - RelocBlockRva) {
      fprintf (stderr, "ImageTool:  Base Relocation Block is out of bounds of the Relocation Directory\n");
      return false;
    }
    //
    // This arithmetic cannot overflow because we know
    //   1) RelocBlock->SizeOfBlock <= RelocMax <= TopOfRelocDir
    //   2) IS_ALIGNED (TopOfRelocDir, ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK)).
    //
    RelocBlockSize = ALIGN_VALUE (
                        RelocBlock->SizeOfBlock,
                        ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK)
                        );
    //
    // This division is safe due to the guarantee made above.
    //
    NumRelocs = SizeOfRelocs / sizeof (*RelocBlock->Relocations);
    //
    // Process all Base Relocations of the current Block.
    //
    for (RelocIndex = 0; RelocIndex < NumRelocs; ++RelocIndex) {
      RelocType   = IMAGE_RELOC_TYPE (RelocBlock->Relocations[RelocIndex]);
      RelocOffset = IMAGE_RELOC_OFFSET (RelocBlock->Relocations[RelocIndex]);

      // FIXME: Make separate functions for UE
      switch (RelocType) {
        case EFI_IMAGE_REL_BASED_ABSOLUTE:
          continue;
        case EFI_IMAGE_REL_BASED_HIGHLOW:
        case EFI_IMAGE_REL_BASED_DIR64:
          RelocInfo->Relocs[RelocInfo->NumRelocs].Type = (uint8_t)RelocType;
          break;
        default:
          fprintf (stderr, "ImageTool: Unknown RelocType = 0x%x\n", RelocType);
          return false;
      }

      RelocInfo->Relocs[RelocInfo->NumRelocs].Target = RelocBlock->VirtualAddress + RelocOffset;
      ++RelocInfo->NumRelocs;
    }
    //
    // This arithmetic cannot overflow because it has been checked that the
    // Image Base Relocation Block is in bounds of the Image buffer.
    //
    RelocBlockRva += RelocBlockSize;
  }
  //
  // Verify the Relocation Directory size matches the contained data.
  //
  if (RelocBlockRva != TopOfRelocDir) {
    fprintf (stderr, "ImageTool: Relocation Directory size does not match the contained data\n");
    return false;
  }

  return true;
}

static
bool
ScanPeGetSegmentInfo (
  OUT image_tool_segment_info_t    *SegmentInfo,
  OUT image_tool_hii_info_t        *HiiInfo,
  IN  PE_COFF_LOADER_IMAGE_CONTEXT *Context
  )
{
  const EFI_IMAGE_SECTION_HEADER *Section;
  uint32_t                       NumSections;
  image_tool_segment_t           *ImageSegment;
  const char                     *ImageBuffer;
  uint32_t                       Index;
  UINT32                         Size;

  assert (SegmentInfo != NULL);
  assert (HiiInfo     != NULL);
  assert (Context     != NULL);

  SegmentInfo->SegmentAlignment = PeCoffGetSectionAlignment (Context);

  NumSections = PeCoffGetSectionTable (Context, &Section);

  SegmentInfo->Segments = calloc (NumSections, sizeof (*SegmentInfo->Segments));
  if (SegmentInfo->Segments == NULL) {
    fprintf (stderr, "ImageTool: Could not allocate memory for Segments[]\n");
    return false;
  }

  ImageBuffer = (char *)PeCoffLoaderGetImageAddress (Context);

  ImageSegment = SegmentInfo->Segments;
  for (Index = 0; Index < NumSections; ++Index, ++Section) {
    STATIC_ASSERT (
      sizeof(PE_COFF_SECT_NAME_RELOC) == sizeof(Section->Name) &&
      sizeof(PE_COFF_SECT_NAME_RESRC) == sizeof(Section->Name) &&
      sizeof(PE_COFF_SECT_NAME_DEBUG) == sizeof(Section->Name),
      "Section names exceed section name bounds."
      );

    if ((Section->Characteristics & EFI_IMAGE_SCN_MEM_DISCARDABLE) == 0
      && memcmp (Section->Name, PE_COFF_SECT_NAME_RELOC, sizeof (Section->Name)) != 0
      && memcmp (Section->Name, PE_COFF_SECT_NAME_RESRC, sizeof (Section->Name)) != 0
      && memcmp (Section->Name, PE_COFF_SECT_NAME_DEBUG, sizeof (Section->Name)) != 0) {
      ImageSegment->Name = calloc (1, sizeof (Section->Name));
      if (ImageSegment->Name == NULL) {
        fprintf (stderr, "ImageTool: Could not allocate memory for Segment Name\n");
        return false;
      }

      memmove (ImageSegment->Name, Section->Name, sizeof (Section->Name));

      Size = ALIGN_VALUE (Section->VirtualSize, SegmentInfo->SegmentAlignment);

      ImageSegment->Data = calloc (1, Size);
      if (ImageSegment->Data == NULL) {
        fprintf (stderr, "ImageTool: Could not allocate memory for Segment Data\n");
        free (ImageSegment->Name);
        return false;
      }

      memmove (
        ImageSegment->Data,
        ImageBuffer + Section->VirtualAddress,
        MIN (Section->VirtualSize, Section->SizeOfRawData)
        );

      ImageSegment->DataSize     = Size;
      ImageSegment->ImageAddress = Section->VirtualAddress;
      ImageSegment->ImageSize    = Size;

      if ((Section->Characteristics & EFI_IMAGE_SCN_MEM_READ) != 0) {
        ImageSegment->Read = true;
      }

      if ((Section->Characteristics & EFI_IMAGE_SCN_MEM_WRITE) != 0) {
        ImageSegment->Write = true;
      }

      if ((Section->Characteristics & EFI_IMAGE_SCN_MEM_EXECUTE) != 0) {
        ImageSegment->Execute = true;
      }

      if (ImageSegment->Execute) {
        ImageSegment->Type = ToolImageSectionTypeCode;
      } else {
        ImageSegment->Type = ToolImageSectionTypeInitialisedData;
      }

      ++SegmentInfo->NumSegments;
      ++ImageSegment;
    } else if (memcmp (Section->Name, PE_COFF_SECT_NAME_RESRC, sizeof (Section->Name)) == 0) {
      Size = ALIGN_VALUE (Section->VirtualSize, SegmentInfo->SegmentAlignment);

      HiiInfo->Data = calloc (1, Size);
      if (HiiInfo->Data == NULL) {
        fprintf (stderr, "ImageTool: Could not allocate memory for Hii Data\n");
        return false;
      }

      memmove (
        HiiInfo->Data,
        ImageBuffer + Section->VirtualAddress,
        MIN (Section->VirtualSize, Section->SizeOfRawData)
        );

      HiiInfo->DataSize = Size;
    }
  }

  return true;
}

bool
ScanPeGetDebugInfo (
  OUT image_tool_debug_info_t      *DebugInfo,
  IN  PE_COFF_LOADER_IMAGE_CONTEXT *Context
  )
{
  const CHAR8   *PdbPath;
  UINT32        PdbPathSize;
  RETURN_STATUS Status;

  assert (DebugInfo != NULL);
  assert (Context   != NULL);

  Status = PeCoffGetPdbPath (Context, &PdbPath, &PdbPathSize);
  if (Status == RETURN_NOT_FOUND) {
    return true;
  }
  if (RETURN_ERROR (Status)) {
    fprintf (stderr, "ImageTool: Could not get PdbPath\n");
    return false;
  }

  DebugInfo->SymbolsPath = calloc (1, PdbPathSize);
  if (DebugInfo->SymbolsPath == NULL) {
    fprintf (stderr, "ImageTool: Could not allocate memory for SymbolsPath\n");
    return false;
  }

  memmove (DebugInfo->SymbolsPath, PdbPath, PdbPathSize);

  assert (PdbPathSize >= 1);
  assert (DebugInfo->SymbolsPath[PdbPathSize - 1] == '\0');

  DebugInfo->SymbolsPathLen = PdbPathSize - 1;

  return true;
}

bool
ScanPeGetHiiInfo (
  OUT image_tool_hii_info_t        *HiiInfo,
  IN  PE_COFF_LOADER_IMAGE_CONTEXT *Context
  )
{
  UINT32        HiiRva;
  UINT32        HiiSize;
  RETURN_STATUS Status;
  const char    *ImageBuffer;

  assert (HiiInfo != NULL);
  assert (Context != NULL);

  Status = PeCoffGetHiiDataRva (Context, &HiiRva, &HiiSize);
  if (Status == RETURN_NOT_FOUND) {
    return true;
  }
  if (RETURN_ERROR (Status)) {
    fprintf (stderr, "ImageTool: Could not get HiiRva\n");
    return false;
  }

  HiiInfo->Data = calloc (1, HiiSize);
  if (HiiInfo->Data == NULL) {
    fprintf (stderr, "ImageTool: Could not allocate memory for HiiInfo Data\n");
    return false;
  }

  ImageBuffer = (char *)PeCoffLoaderGetImageAddress (Context);

  memmove (HiiInfo->Data, ImageBuffer + HiiRva, HiiSize);
  HiiInfo->DataSize = HiiSize;

  return true;
}

bool
ToolContextConstructPe (
  OUT image_tool_image_info_t *Image,
  IN  const void              *File,
  IN  size_t                  FileSize,
  IN  const char              *ModuleType OPTIONAL
  )
{
  PE_COFF_LOADER_IMAGE_CONTEXT Context;
  RETURN_STATUS                Status;
  UINT32                       DestinationSize;
  bool                         Overflow;
  void                         *Destination;
  uintptr_t                    Addend;
  void                         *AlignedDest;
  bool                         Result;

  assert (Image != NULL);
  assert (File != NULL || FileSize == 0);

  if (FileSize > MAX_UINT32) {
    fprintf (stderr, "ImageTool: FileSize is too huge\n");
    return false;
  }

  Status = PeCoffInitializeContext (&Context, File, (UINT32)FileSize);
  if (RETURN_ERROR (Status)) {
    fprintf (stderr, "ImageTool: Could not initialise Context\n");
    return false;
  }

  Overflow = OverflowGetDestinationSize (&Context, &DestinationSize);
  if (Overflow) {
    fprintf (stderr, "ImageTool: DestinationSize is too huge\n");
    return false;
  }

  Destination = calloc (1, DestinationSize);
  if (Destination == NULL) {
    fprintf (stderr, "ImageTool: Could not allocate Destination buffer\n");
    return false;
  }

  Addend      = ALIGN_VALUE_ADDEND ((uintptr_t)Destination, EFI_PAGE_SIZE);
  AlignedDest = (char *)Destination + Addend;

  Status = PeCoffLoadImage (&Context, AlignedDest, DestinationSize - Addend);
  if (RETURN_ERROR (Status)) {
    fprintf (stderr, "ImageTool: Could not Load Image\n");
    free (Destination);
    return false;
  }

  memset (Image, 0, sizeof (*Image));

  Result  = ScanPeGetHeaderInfo (&Image->HeaderInfo, &Context, ModuleType);
  if (!Result) {
    fprintf (stderr, "ImageTool: Could not retrieve header info\n");
    free (Destination);
    return false;
  }

  Result = ScanPeGetDebugInfo (&Image->DebugInfo, &Context);
  if (!Result) {
    fprintf (stderr, "ImageTool: Could not retrieve debug info\n");
    free (Destination);
    return false;
  }

  Result = ScanPeGetSegmentInfo (&Image->SegmentInfo, &Image->HiiInfo, &Context);
  if (!Result) {
    fprintf (stderr, "ImageTool: Could not retrieve segment info\n");
    free (Destination);
    return false;
  }

  Result = ScanPeGetRelocInfo (&Image->RelocInfo, &Context);
  if (!Result) {
    fprintf (stderr, "ImageTool: Could not retrieve reloc info\n");
  }

  free (Destination);

  return Result;
}
