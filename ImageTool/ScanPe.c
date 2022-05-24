#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include <assert.h>
#include <string.h>

#include <Base.h>

#include <IndustryStandard/PeImage2.h>
#include <IndustryStandard/UeImage.h>

#include <Library/PeCoffLib2.h>

#include "../MdePkg/Library/BasePeCoffLib2/BaseOverflow.h"

#include "ImageTool.h"

typedef struct {
  const unsigned char          *FileBuffer;
  PE_COFF_LOADER_IMAGE_CONTEXT Lib;
} image_tool_context_pe;

// FIXME: Remove
bool PeRvaToOffset(PE_COFF_LOADER_IMAGE_CONTEXT *Context, uint32_t *Rva, uint32_t *Size, bool AllowLess)
{
  const EFI_IMAGE_SECTION_HEADER *Sections;
  UINT32 NumSections = PeCoffGetSectionTable(Context, &Sections);

  UINT32 Index;
  for (Index = 0; Index < NumSections; ++Index) {
    if (Sections[Index].VirtualAddress <= *Rva
     && *Rva + *Size <= Sections[Index].VirtualAddress + Sections[Index].VirtualSize) {
      *Rva -= Sections[Index].VirtualAddress;
      if (*Rva + *Size > Sections[Index].SizeOfRawData) {
        if (!AllowLess) {
          raise();
          return false;
        }

        *Size = Sections[Index].SizeOfRawData - *Rva;
      }
      *Rva += Sections[Index].PointerToRawData;
      return true;
    }
  }

  raise();
  return false;
}

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
  image_tool_segment_info_t  *SegmentInfo,
  image_tool_context_pe      *Context
  )
{
  assert(SegmentInfo != NULL);
  assert(Context != NULL);

  SegmentInfo->SegmentAlignment = PeCoffGetSectionAlignment(&Context->Lib);

  const EFI_IMAGE_SECTION_HEADER *Sections;
  uint32_t                       NumSections;
  NumSections = PeCoffGetSectionTable(&Context->Lib, &Sections);

  SegmentInfo->Segments = calloc(
    NumSections,
    sizeof(*SegmentInfo->Segments)
    );
  if (SegmentInfo->Segments == NULL) {
    return false;
  }

  int64_t LastUndiscardable = -1;
  for (uint32_t Index = 0; Index < NumSections; ++Index) {
    const EFI_IMAGE_SECTION_HEADER *Section = Sections + Index;
    image_tool_segment_t *ImageSegment = SegmentInfo->Segments + Index;

    size_t NameSize = strnlen(
      (const char *) Section->Name,
      sizeof(Section->Name)
      );
    ImageSegment->Name = calloc(NameSize + 1, 1);
    if (ImageSegment->Name == NULL) {
      return false;
    }

    memcpy(ImageSegment->Name, Section->Name, NameSize);

    ImageSegment->Data = malloc(Section->SizeOfRawData);
    if (ImageSegment->Data == NULL) {
      return false;
    }

    memcpy(
      ImageSegment->Data,
      Context->FileBuffer + Section->PointerToRawData,
      Section->SizeOfRawData
      );

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

    if ((Section->Characteristics & EFI_IMAGE_SCN_MEM_DISCARDABLE) != 0
      || strncmp((const char *) Section->Name, ".reloc", sizeof(Section->Name)) == 0
      || strncmp((const char *) Section->Name, ".rsrc", sizeof(Section->Name)) == 0
      || strncmp((const char *) Section->Name, ".debug", sizeof(Section->Name)) == 0) {
      ImageSegment->DataSize = 0;
    } else {
      ImageSegment->DataSize = Section->SizeOfRawData;
      LastUndiscardable = (int64_t) Index;
    }
  }

  SegmentInfo->NumSegments = (uint32_t) (LastUndiscardable + 1);

  return true;
}

bool ScanPeGetRelocInfo (
  image_tool_reloc_info_t *RelocInfo,
  image_tool_context_pe   *Context
  )
{
  BOOLEAN                               Overflow;

  UINT32                                RelocBlockOffsetMax;
  UINT32                                TopOfRelocDir;

  UINT32                                RelocBlockOffset;
  const EFI_IMAGE_BASE_RELOCATION_BLOCK *RelocBlock;
  UINT32                                RelocBlockSize;
  UINT32                                SizeOfRelocs;
  UINT32                                NumRelocs;
  UINT32                                RelocIndex;

  assert(Context != NULL);
  //
  // Verify the Relocation Directory is not empty.
  //
  if (Context->Lib.RelocDirSize == 0) {
    return true;
  }

  RelocInfo->Relocs = calloc(Context->Lib.RelocDirSize / sizeof(UINT16), sizeof(*RelocInfo->Relocs));
  if (RelocInfo->Relocs == NULL) {
    raise();
    return false;
  }

  RelocBlockOffset = Context->Lib.RelocDirRva;
  uint32_t RelocDirSize = Context->Lib.RelocDirSize;
  bool Result = PeRvaToOffset(
    &Context->Lib,
    &RelocBlockOffset,
    &RelocDirSize,
    true
    );
  if (!Result) {
    return false;
  }

  TopOfRelocDir = RelocBlockOffset + RelocDirSize;

  RelocBlockOffsetMax = TopOfRelocDir - sizeof (EFI_IMAGE_BASE_RELOCATION_BLOCK);
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
  while (RelocBlockOffset <= RelocBlockOffsetMax) {
    RelocBlock = (const EFI_IMAGE_BASE_RELOCATION_BLOCK *) (const VOID *) (
                   (const CHAR8 *) Context->Lib.FileBuffer + RelocBlockOffset
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
    if (SizeOfRelocs > RelocBlockOffsetMax - RelocBlockOffset) {
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
    RelocBlockOffset += RelocBlockSize;
  }
  //
  // Verify the Relocation Directory size matches the contained data.
  //
  if (RelocBlockOffset != TopOfRelocDir) {
    raise();
    return false;
  }

  return true;
}

bool ScanPeGetDebugInfo (
  image_tool_debug_info_t  *DebugInfo,
  image_tool_context_pe    *Context
  )
{
  assert(DebugInfo != NULL);
  assert(Context != NULL);

  const CHAR8   *PdbPath;
  UINT32        PdbPathSize;
  RETURN_STATUS Status = PeCoffGetPdbPath(
    &Context->Lib,
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

  DebugInfo->SymbolsPath = calloc(PdbPathSize, 1);
  if (DebugInfo->SymbolsPath == NULL) {
    raise();
    return false;
  }

  memcpy(DebugInfo->SymbolsPath, PdbPath, PdbPathSize);

  return true;
}

// FIXME: Remove
RETURN_STATUS
PeCoffGetHiiDataRva2 (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  OUT    UINT32                        *HiiRva,
  OUT    UINT32                        *HiiSize
  )
{
  UINT16                                    Index;
  const EFI_IMAGE_NT_HEADERS32              *Pe32Hdr;
  const EFI_IMAGE_NT_HEADERS64              *Pe32PlusHdr;
  const EFI_IMAGE_DATA_DIRECTORY            *ResDirTable;
  const EFI_IMAGE_RESOURCE_DIRECTORY        *ResourceDir;
  const EFI_IMAGE_RESOURCE_DIRECTORY_ENTRY  *ResourceDirEntry;
  const EFI_IMAGE_RESOURCE_DIRECTORY_STRING *ResourceDirString;
  const EFI_IMAGE_RESOURCE_DATA_ENTRY       *ResourceDataEntry;
  BOOLEAN                                   Overflow;
  UINT32                                    Offset;
  UINT32                                    TopOffset;
  UINT8                                     ResourceLevel;
  UINT32                                    HiiRvaEnd;

  //
  // Retrieve the Image's Resource Directory Table.
  //
  switch (Context->ImageType) {
    case PeCoffLoaderTypeTe:
      return RETURN_UNSUPPORTED;

    case PeCoffLoaderTypePe32:
      Pe32Hdr = (const EFI_IMAGE_NT_HEADERS32 *) (const VOID *) (
                  (const CHAR8 *) Context->FileBuffer + Context->ExeHdrOffset
                  );
      if (Pe32Hdr->NumberOfRvaAndSizes <= EFI_IMAGE_DIRECTORY_ENTRY_RESOURCE) {
        return RETURN_NOT_FOUND;
      }

      ResDirTable = &Pe32Hdr->DataDirectory[EFI_IMAGE_DIRECTORY_ENTRY_RESOURCE];
      break;

    case PeCoffLoaderTypePe32Plus:
      Pe32PlusHdr = (const EFI_IMAGE_NT_HEADERS64 *) (const VOID *) (
                      (const CHAR8 *) Context->FileBuffer + Context->ExeHdrOffset
                      );
      if (Pe32PlusHdr->NumberOfRvaAndSizes <= EFI_IMAGE_DIRECTORY_ENTRY_RESOURCE) {
        return RETURN_NOT_FOUND;
      }

      ResDirTable = &Pe32PlusHdr->DataDirectory[EFI_IMAGE_DIRECTORY_ENTRY_RESOURCE];
      break;

    default:
      assert(false);
      return RETURN_UNSUPPORTED;
  }

  if (ResDirTable->Size == 0) {
    return RETURN_NOT_FOUND;
  }
  //
  // Verify the start of the Resource Directory Table is sufficiently aligned.
  //
  if (!IS_ALIGNED (ResDirTable->VirtualAddress, ALIGNOF (EFI_IMAGE_RESOURCE_DIRECTORY))) {
    raise();
    return RETURN_UNSUPPORTED;
  }
  // FIXME: Verify against first Image section / Headers due to XIP TE.
  //
  // Verify the Resource Directory Table is in bounds of the Image buffer.
  //
  Overflow = BaseOverflowAddU32 (
               ResDirTable->VirtualAddress,
               ResDirTable->Size,
               &TopOffset
               );
  if (Overflow || TopOffset > Context->SizeOfImage) {
    raise();
    return RETURN_UNSUPPORTED;
  }

  UINT32 ResOffset = ResDirTable->VirtualAddress;
  UINT32 ResSize   = ResDirTable->Size;
  bool Result = PeRvaToOffset(
    Context,
    &ResOffset,
    &ResSize,
    true
    );
  if (!Result) {
    return false;
  }
  //
  // Verify the Resource Directory Table contains at least one entry.
  //
  if (ResSize < sizeof (EFI_IMAGE_RESOURCE_DIRECTORY) + sizeof (*ResourceDir->Entries)) {
    return RETURN_NOT_FOUND;
  }

  ResourceDir = (const EFI_IMAGE_RESOURCE_DIRECTORY *) (const VOID *) (
                  (const CHAR8 *) Context->FileBuffer + ResOffset
                  );
  //
  // Verify the Resource Directory Table can hold all of its entries.
  //
  STATIC_ASSERT (
    sizeof (*ResourceDirEntry) * MAX_UINT16 <= ((UINT64) MAX_UINT32 + 1U) / 2 - sizeof (EFI_IMAGE_RESOURCE_DIRECTORY),
    "The following arithmetic may overflow."
    );
  TopOffset = sizeof (EFI_IMAGE_RESOURCE_DIRECTORY) + sizeof (*ResourceDirEntry) *
                ((UINT32) ResourceDir->NumberOfNamedEntries + ResourceDir->NumberOfIdEntries);
  if (TopOffset > ResSize) {
    raise();
    return RETURN_UNSUPPORTED;
  }
  //
  // Try to locate the "HII" Resource entry.
  //
  for (Index = 0; Index < ResourceDir->NumberOfNamedEntries; ++Index) {
    ResourceDirEntry = &ResourceDir->Entries[Index];
    //
    // Filter entries with a non-Unicode name entry.
    //
    if (ResourceDirEntry->u1.s.NameIsString == 0) {
      continue;
    }
    //
    // Verify the Resource Directory String header is in bounds of the Resource
    // Directory Table.
    //
    Overflow = BaseOverflowAddU32 (
                 ResourceDirEntry->u1.s.NameOffset,
                 sizeof (*ResourceDirString),
                 &TopOffset
                 );
    if (Overflow || TopOffset > ResSize) {
      raise();
      return RETURN_UNSUPPORTED;
    }
    //
    // Verify the Resource Directory String offset is sufficiently aligned.
    //
    Offset = ResDirTable->VirtualAddress + ResourceDirEntry->u1.s.NameOffset;
    if (!IS_ALIGNED (Offset, ALIGNOF (EFI_IMAGE_RESOURCE_DIRECTORY_STRING))) {
      raise();
      return RETURN_UNSUPPORTED;
    }

    UINT32 OffsetSize = sizeof (*ResourceDirString);
    bool Result = PeRvaToOffset(
      Context,
      &Offset,
      &OffsetSize,
      false
      );
    if (!Result) {
      return false;
    }

    ResourceDirString = (const EFI_IMAGE_RESOURCE_DIRECTORY_STRING *) (const VOID *) (
                          (const CHAR8 *) Context->FileBuffer + Offset
                          );
    //
    // Verify the Resource Directory String is in bounds of the Resource
    // Directory Table.
    //
    Overflow = BaseOverflowAddU32 (
                 TopOffset,
                 (UINT32) ResourceDirString->Length * sizeof (CHAR16),
                 &TopOffset
                 );
    if (Overflow || TopOffset > ResSize) {
      raise();
      return RETURN_UNSUPPORTED;
    }
    //
    // Verify the type name matches "HII".
    //
    if (ResourceDirString->Length == 3
     && ResourceDirString->String[0] == L'H'
     && ResourceDirString->String[1] == L'I'
     && ResourceDirString->String[2] == L'I') {
      break;
    }
  }
  //
  // Verify the "HII" Type Resource Directory Entry exists.
  //
  if (Index == ResourceDir->NumberOfNamedEntries) {
    return RETURN_NOT_FOUND;
  }
  //
  // Walk down the conventional "Name" and "Language" levels to reach the
  // data directory.
  //
  for (ResourceLevel = 0; ResourceLevel < 2; ++ResourceLevel) {
    //
    // Succeed early if one of the levels is omitted.
    //
    if (ResourceDirEntry->u2.s.DataIsDirectory == 0) {
      break;
    }
    //
    // Verify the Resource Directory Table fits at least the Resource Directory
    // with and one Relocation Directory Entry.
    //
    if (ResourceDirEntry->u2.s.OffsetToDirectory > ResSize - sizeof (EFI_IMAGE_RESOURCE_DIRECTORY) + sizeof (*ResourceDir->Entries)) {
      raise();
      return RETURN_UNSUPPORTED;
    }
    //
    // Verify the next Relocation Directory offset is sufficiently aligned.
    //
    Offset = ResDirTable->VirtualAddress + ResourceDirEntry->u2.s.OffsetToDirectory;
    if (!IS_ALIGNED (Offset, ALIGNOF (EFI_IMAGE_RESOURCE_DIRECTORY))) {
      raise();
      return RETURN_UNSUPPORTED;
    }

    UINT32 OffsetSize = sizeof (EFI_IMAGE_RESOURCE_DIRECTORY) + sizeof (*ResourceDir->Entries);
    bool Result = PeRvaToOffset(
      Context,
      &Offset,
      &OffsetSize,
      false
      );
    if (!Result) {
      return false;
    }
    //
    // Verify the Resource Directory has at least one entry.
    //
    ResourceDir = (const EFI_IMAGE_RESOURCE_DIRECTORY *) (const VOID *) (
                    (const CHAR8 *) Context->FileBuffer + Offset
                    );
    if ((UINT32) ResourceDir->NumberOfIdEntries + ResourceDir->NumberOfNamedEntries == 0) {
      raise();
      return RETURN_UNSUPPORTED;
    }
    //
    // Always take the first entry for simplicity.
    //
    ResourceDirEntry = &ResourceDir->Entries[0];
  }
  //
  // Verify the final Resource Directory Entry is of a data type.
  //
  if (ResourceDirEntry->u2.s.DataIsDirectory != 0) {
    raise();
    return RETURN_UNSUPPORTED;
  }
  //
  // Verify the Resource Directory Table fits at least the Resource Directory.
  //
  STATIC_ASSERT (
    sizeof (EFI_IMAGE_RESOURCE_DATA_ENTRY) <= sizeof (EFI_IMAGE_RESOURCE_DIRECTORY),
    "The following arithmetic may overflow."
    );
  if (ResourceDirEntry->u2.OffsetToData > ResSize - sizeof (EFI_IMAGE_RESOURCE_DATA_ENTRY)) {
    raise();
    return RETURN_UNSUPPORTED;
  }
  //
  // Verify the Relocation Directory Entry offset is sufficiently aligned.
  //
  Offset = ResDirTable->VirtualAddress + ResourceDirEntry->u2.OffsetToData;
  if (!IS_ALIGNED (Offset, ALIGNOF (EFI_IMAGE_RESOURCE_DATA_ENTRY))) {
    raise();
    return RETURN_UNSUPPORTED;
  }

  UINT32 OffsetSize = sizeof (EFI_IMAGE_RESOURCE_DATA_ENTRY);
  Result = PeRvaToOffset(
    Context,
    &Offset,
    &OffsetSize,
    false
    );
  if (!Result) {
    return false;
  }

  ResourceDataEntry = (const EFI_IMAGE_RESOURCE_DATA_ENTRY *) (const VOID *) (
                        (const CHAR8 *) Context->FileBuffer + Offset
                        );
  //
  // Verify the "HII" data is in bounds of the Image buffer.
  //
  Overflow = BaseOverflowAddU32 (
               ResourceDataEntry->OffsetToData,
               ResourceDataEntry->Size,
               &HiiRvaEnd
               );
  if (Overflow || HiiRvaEnd > Context->SizeOfImage) {
    raise();
    return RETURN_UNSUPPORTED;
  }

  *HiiRva  = ResourceDataEntry->OffsetToData;
  *HiiSize = ResourceDataEntry->Size;

  return RETURN_SUCCESS;
}

bool ScanPeGetHiiInfo (
  image_tool_hii_info_t  *HiiInfo,
  image_tool_context_pe  *Context
  )
{
  assert(HiiInfo != NULL);
  assert(Context != NULL);

  UINT32        HiiRva;
  UINT32        HiiSize;
  RETURN_STATUS Status = PeCoffGetHiiDataRva2(&Context->Lib, &HiiRva, &HiiSize);
  if (Status == RETURN_NOT_FOUND) {
    return true;
  }
  if (RETURN_ERROR (Status)) {
    return false;
  }

  UINT32 HiiOffset = HiiRva;
  bool Result = PeRvaToOffset(
    &Context->Lib,
    &HiiOffset,
    &HiiSize,
    true
    );
  if (!Result) {
    return false;
  }

  HiiInfo->Data = calloc(HiiSize, 1);
  if (HiiInfo->Data == NULL) {
    raise();
    return false;
  }

  memcpy(HiiInfo->Data, Context->FileBuffer + HiiOffset, HiiSize);
  HiiInfo->DataSize = HiiSize;

  printf("Emitted HII %u\n", HiiSize);

  return true;
}

image_tool_image_info_t *ToolContextConstructPe(void *File, size_t FileSize)
{
  assert(File != NULL || FileSize == 0);

  if (FileSize > MAX_UINT32) {
    return NULL;
  }

  image_tool_context_pe Context;
  Context.FileBuffer = File;

  RETURN_STATUS Status = PeCoffInitializeContext(
    &Context.Lib,
    File,
    (UINT32) FileSize
    );
  if (RETURN_ERROR(Status)) {
    return NULL;
  }

  image_tool_image_info_t *Image = calloc(1, sizeof(image_tool_image_info_t));
  if (Image == NULL) {
    return NULL;
  }

  bool Result = ScanPeGetHeaderInfo(&Image->HeaderInfo, &Context.Lib);
  if (!Result) {
    return NULL;
  }

  Result = ScanPeGetSegmentInfo(&Image->SegmentInfo, &Context);
  if (!Result) {
    return NULL;
  }

  Result = ScanPeGetRelocInfo(&Image->RelocInfo, &Context);
  if (!Result) {
    return NULL;
  }

  Result = ScanPeGetHiiInfo(&Image->HiiInfo, &Context);
  if (!Result) {
    return NULL;
  }

  Result = ScanPeGetDebugInfo(&Image->DebugInfo, &Context);
  if (!Result) {
    return NULL;
  }

  return Image;
}
