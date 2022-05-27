#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include <assert.h>
#include <string.h>
#include <stdio.h>

#include <Base.h>

#include <IndustryStandard/PeImage2.h>
#include <IndustryStandard/UeImage.h>

#include <Library/PeCoffLib2.h>

#include "../../MdePkg/Library/BasePeCoffLib2/BaseOverflow.h"

#include "ImageTool.h"

bool
OverflowGetDestinationSize (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT *Context,
  OUT    UINT32                       *Size
  )
{
  assert(Context != NULL);
  assert(Size != NULL);

  UINT32 AlignedSize      = PeCoffGetSizeOfImage(Context);
  UINT32 SegmentAlignment = PeCoffGetSectionAlignment(Context);
  //
  // The Image needs to be aligned inside the malloc() buffer.
  //
  assert(SegmentAlignment > 0);
  return BaseOverflowAddU32(
    AlignedSize,
    SegmentAlignment - 1,
    Size
    );
}

#define PE_COFF_SECT_NAME_RELOC  ".reloc\0"
#define PE_COFF_SECT_NAME_RESRC  ".rsrc\0\0"
#define PE_COFF_SECT_NAME_DEBUG  ".debug\0"

bool ScanPeGetHeaderInfo (
  image_tool_header_info_t     *HeaderInfo,
  PE_COFF_LOADER_IMAGE_CONTEXT *Context
  )
{
  assert(HeaderInfo != NULL);
  assert(Context != NULL);

  HeaderInfo->PreferredAddress  = (uint64_t) PeCoffGetImageBase(Context);
  HeaderInfo->EntryPointAddress = PeCoffGetAddressOfEntryPoint(Context);
  // FIXME:
  HeaderInfo->Machine   = PeCoffGetMachine(Context);
  HeaderInfo->Subsystem = PeCoffGetSubsystem(Context);

  return true;
}

bool ScanPeGetSegmentInfo (
  image_tool_segment_info_t    *SegmentInfo,
  PE_COFF_LOADER_IMAGE_CONTEXT *Context
  )
{
  assert(SegmentInfo != NULL);
  assert(Context != NULL);

  SegmentInfo->SegmentAlignment = PeCoffGetSectionAlignment(Context);

  const EFI_IMAGE_SECTION_HEADER *Section;
  uint32_t                       NumSections;
  image_tool_segment_t           *ImageSegment;

  NumSections = PeCoffGetSectionTable(Context, &Section);

  SegmentInfo->Segments = calloc(
    NumSections,
    sizeof(*SegmentInfo->Segments)
    );
  if (SegmentInfo->Segments == NULL) {
    return false;
  }

  const char *ImageBuffer = (char *) PeCoffLoaderGetImageAddress(Context);

  ImageSegment = SegmentInfo->Segments;
  for (uint32_t Index = 0; Index < NumSections; ++Index, ++Section, ++ImageSegment) {

    ImageSegment->Name = malloc(sizeof(Section->Name));
    if (ImageSegment->Name == NULL) {
      return false;
    }

    memmove(ImageSegment->Name, Section->Name, sizeof(Section->Name));

    ImageSegment->ImageAddress = Section->VirtualAddress;
    ImageSegment->ImageSize    = Section->VirtualSize;

    if ((Section->Characteristics & EFI_IMAGE_SCN_MEM_READ) != 0) {
      ImageSegment->Read = true;
    }

    if ((Section->Characteristics & EFI_IMAGE_SCN_MEM_WRITE) != 0) {
      ImageSegment->Write = true;
    }

    if ((Section->Characteristics & EFI_IMAGE_SCN_MEM_EXECUTE) != 0) {
      ImageSegment->Execute = true;
    }

    _Static_assert(
      sizeof(PE_COFF_SECT_NAME_RELOC) == sizeof(Section->Name) &&
      sizeof(PE_COFF_SECT_NAME_RESRC) == sizeof(Section->Name) &&
      sizeof(PE_COFF_SECT_NAME_DEBUG) == sizeof(Section->Name),
      "Section names exceed section name bounds."
      );

    if ((Section->Characteristics & EFI_IMAGE_SCN_MEM_DISCARDABLE) == 0
      && memcmp(Section->Name, PE_COFF_SECT_NAME_RELOC, sizeof(Section->Name)) != 0
      && memcmp(Section->Name, PE_COFF_SECT_NAME_RESRC, sizeof(Section->Name)) != 0
      && memcmp(Section->Name, PE_COFF_SECT_NAME_DEBUG, sizeof(Section->Name)) != 0) {
      ImageSegment->Data = malloc(Section->VirtualSize);
      if (ImageSegment->Data == NULL) {
        free(ImageSegment->Name);
        return false;
      }

      memmove(
        ImageSegment->Data,
        ImageBuffer + Section->VirtualAddress,
        Section->VirtualSize
        );

      ImageSegment->DataSize = Section->VirtualSize;
    } else {
      assert(ImageSegment->DataSize == 0);

      if ((Section->Characteristics & EFI_IMAGE_SCN_MEM_WRITE) != 0) {
        free(ImageSegment->Name);
        raise();
        return false;
      }

      if ((Section->Characteristics & EFI_IMAGE_SCN_MEM_EXECUTE) != 0) {
        free(ImageSegment->Name);
        raise();
        return false;
      }
    }
  }

  SegmentInfo->NumSegments = NumSections;

  return true;
}

bool ScanPeGetRelocInfo (
  image_tool_reloc_info_t      *RelocInfo,
  PE_COFF_LOADER_IMAGE_CONTEXT *Context
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

  assert(Context != NULL);

  // FIXME: PE/COFF context access
  RelocBlockRva = Context->RelocDirRva;
  uint32_t RelocDirSize = Context->RelocDirSize;
  //
  // Verify the Relocation Directory is not empty.
  //
  if (RelocDirSize == 0) {
    return true;
  }

  RelocInfo->Relocs = calloc(RelocDirSize / sizeof(UINT16), sizeof(*RelocInfo->Relocs));
  if (RelocInfo->Relocs == NULL) {
    raise();
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
    raise();
    return false;
  }
  //
  // Apply all Base Relocations of the Image.
  //
  const char *ImageBuffer = (char *) PeCoffLoaderGetImageAddress(Context);
  while (RelocBlockRva <= RelocBlockRvaMax) {
    RelocBlock = (const EFI_IMAGE_BASE_RELOCATION_BLOCK *) (const void *) (
                   ImageBuffer + RelocBlockRva
                   );
    //
    // Verify the Base Relocation Block size is well-formed.
    //
    Overflow = BaseOverflowSubU32 (
                 RelocBlock->SizeOfBlock,
                 sizeof (EFI_IMAGE_BASE_RELOCATION_BLOCK),
                 &SizeOfRelocs
                 );
    if (Overflow) {
      raise();
      return false;
    }
    //
    // Verify the Base Relocation Block is in bounds of the Relocation
    // Directory.
    //
    if (SizeOfRelocs > RelocBlockRvaMax - RelocBlockRva) {
      raise();
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
      UINT16 RelocType   = IMAGE_RELOC_TYPE (RelocBlock->Relocations[RelocIndex]);
      UINT16 RelocOffset = IMAGE_RELOC_OFFSET (RelocBlock->Relocations[RelocIndex]);

      switch (RelocType) {
        case EFI_IMAGE_REL_BASED_ABSOLUTE:
          continue;

        case EFI_IMAGE_REL_BASED_HIGHLOW:
          RelocInfo->Relocs[RelocInfo->NumRelocs].Type = UeRelocRel32;

          break;

        case EFI_IMAGE_REL_BASED_DIR64:
          RelocInfo->Relocs[RelocInfo->NumRelocs].Type = UeRelocRel64;

          break;

        case EFI_IMAGE_REL_BASED_ARM_MOV32T:
          RelocInfo->Relocs[RelocInfo->NumRelocs].Type = UeRelocArmMov32t;

          break;

        default:
          raise();
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
    raise();
    return false;
  }

  return true;
}

bool ScanPeGetDebugInfo (
  image_tool_debug_info_t      *DebugInfo,
  PE_COFF_LOADER_IMAGE_CONTEXT *Context
  )
{
  assert(DebugInfo != NULL);
  assert(Context != NULL);

  const CHAR8   *PdbPath;
  UINT32        PdbPathSize;
  RETURN_STATUS Status = PeCoffGetPdbPath(
    Context,
    &PdbPath,
    &PdbPathSize
    );
  if (Status == RETURN_NOT_FOUND) {
    return true;
  }
  if (RETURN_ERROR(Status)) {
    raise();
    return false;
  }

  DebugInfo->SymbolsPath = malloc(PdbPathSize);
  if (DebugInfo->SymbolsPath == NULL) {
    raise();
    return false;
  }

  memmove(DebugInfo->SymbolsPath, PdbPath, PdbPathSize);

  assert(PdbPathSize >= 1);
  assert(DebugInfo->SymbolsPath[PdbPathSize - 1] == '\0');

  DebugInfo->SymbolsPathLen = PdbPathSize - 1;

  return true;
}

bool ScanPeGetHiiInfo (
  image_tool_hii_info_t        *HiiInfo,
  PE_COFF_LOADER_IMAGE_CONTEXT *Context
  )
{
  assert(HiiInfo != NULL);
  assert(Context != NULL);

  UINT32        HiiRva;
  UINT32        HiiSize;
  RETURN_STATUS Status = PeCoffGetHiiDataRva(Context, &HiiRva, &HiiSize);
  if (Status == RETURN_NOT_FOUND) {
    return true;
  }
  if (RETURN_ERROR (Status)) {
    return false;
  }

  HiiInfo->Data = malloc(HiiSize);
  if (HiiInfo->Data == NULL) {
    raise();
    return false;
  }

  const char *ImageBuffer = (char *) PeCoffLoaderGetImageAddress(Context);

  memmove(HiiInfo->Data, ImageBuffer + HiiRva, HiiSize);
  HiiInfo->DataSize = HiiSize;

  return true;
}

bool ToolContextConstructPe(image_tool_image_info_t *Image, const void *File, size_t FileSize)
{
  assert(File != NULL || FileSize == 0);

  if (FileSize > MAX_UINT32) {
    return false;
  }

  PE_COFF_LOADER_IMAGE_CONTEXT Context;

  RETURN_STATUS Status = PeCoffInitializeContext(
    &Context,
    File,
    (UINT32) FileSize
    );
  if (RETURN_ERROR(Status)) {
    return false;
  }

  UINT32 DestinationSize;
  bool Overflow = OverflowGetDestinationSize(&Context, &DestinationSize);
  if (Overflow) {
    return false;
  }

  void *Destination = malloc(DestinationSize + EFI_PAGE_SIZE);
  if (Destination == NULL) {
    return false;
  }

  uintptr_t Addend = ALIGN_VALUE_ADDEND ((uintptr_t)Destination, EFI_PAGE_SIZE);
  void *AlignedDest = (char *)Destination + Addend;

  Status = PeCoffLoadImage(&Context, AlignedDest, DestinationSize + EFI_PAGE_SIZE - Addend);
  if (RETURN_ERROR(Status)) {
    free(Destination);
    return false;
  }

  memset(Image, 0, sizeof(*Image));

  bool Result = ScanPeGetHeaderInfo(&Image->HeaderInfo, &Context);
  Result     &= ScanPeGetSegmentInfo(&Image->SegmentInfo, &Context);
  Result     &= ScanPeGetRelocInfo(&Image->RelocInfo, &Context);
  Result     &= ScanPeGetHiiInfo(&Image->HiiInfo, &Context);
  Result     &= ScanPeGetDebugInfo(&Image->DebugInfo, &Context);

  free(Destination);

  return Result;
}
