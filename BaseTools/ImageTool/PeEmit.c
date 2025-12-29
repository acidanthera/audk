/** @file
  Copyright (c) 2021, Marvin Häuser. All rights reserved.
  Copyright (c) 2022, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause
**/

#include "ImageTool.h"

#if PE_ARCH == 32

#define EFI_IMAGE_NT_HEADERS             EFI_IMAGE_NT_HEADERS32
#define EFI_IMAGE_NT_OPTIONAL_HDR_MAGIC  EFI_IMAGE_NT_OPTIONAL_HDR32_MAGIC

#elif PE_ARCH == 64

#define EFI_IMAGE_NT_HEADERS             EFI_IMAGE_NT_HEADERS64
#define EFI_IMAGE_NT_OPTIONAL_HDR_MAGIC  EFI_IMAGE_NT_OPTIONAL_HDR64_MAGIC

#endif

#define PE_SUFFIX__(Name, Arch)  Name##Arch
#define PE_SUFFIX_(Name, Arch)   PE_SUFFIX__ (Name, Arch)
#define PE_SUFFIX(Name)          PE_SUFFIX_ (Name, PE_ARCH)

typedef struct {
  uint8_t     NumExtraSections;
  uint32_t    SizeOfHeaders;
  uint8_t     NumberOfRvaAndSizes;
  uint16_t    SizeOfOptionalHeader;
  uint32_t    SectionHeadersSize;
  uint32_t    ExtraSectionHeadersSize;
} image_tool_emit_pe_hdr_info_t;

typedef struct {
  const image_tool_image_info_t    *Image;
  EFI_IMAGE_NT_HEADERS             *PeHdr;
  image_tool_emit_pe_hdr_info_t    HdrInfo;
  uint32_t                         SectionsSize;
  uint32_t                         HiiSectionAddress;
  uint32_t                         ExtraSectionsSize;
  uint32_t                         UnsignedFileSize;
  uint32_t                         RelocTableSize;
  uint32_t                         DebugTableSize;
  uint32_t                         FileAlignment;
} image_tool_pe_emit_context_t;

#define EmitPeGetHeaderSizes  PE_SUFFIX (EmitPeGetHeaderSizes)
static
bool
EmitPeGetHeaderSizes (
  const image_tool_image_info_t  *Image,
  image_tool_emit_pe_hdr_info_t  *HdrInfo
  )
{
  assert (Image   != NULL);
  assert (HdrInfo != NULL);

  if (Image->RelocInfo.NumRelocs > 0) {
    HdrInfo->ExtraSectionHeadersSize += sizeof (EFI_IMAGE_SECTION_HEADER);
  }

  if (Image->HiiInfo.DataSize > 0) {
    HdrInfo->ExtraSectionHeadersSize += sizeof (EFI_IMAGE_SECTION_HEADER);
  }

  if (Image->DebugInfo.SymbolsPath != NULL) {
    HdrInfo->ExtraSectionHeadersSize += sizeof (EFI_IMAGE_SECTION_HEADER);
  }

  HdrInfo->SectionHeadersSize   = (uint32_t)Image->SegmentInfo.NumSegments * sizeof (EFI_IMAGE_SECTION_HEADER);
  HdrInfo->NumberOfRvaAndSizes  = EFI_IMAGE_NUMBER_OF_DIRECTORY_ENTRIES;
  HdrInfo->SizeOfOptionalHeader = sizeof (EFI_IMAGE_NT_HEADERS) - sizeof (EFI_IMAGE_NT_HEADERS_COMMON_HDR)
                                  + HdrInfo->NumberOfRvaAndSizes * sizeof (EFI_IMAGE_DATA_DIRECTORY);
  HdrInfo->SizeOfHeaders = sizeof (EFI_IMAGE_DOS_HEADER) + sizeof (EFI_IMAGE_NT_HEADERS)
                           + HdrInfo->NumberOfRvaAndSizes * sizeof (EFI_IMAGE_DATA_DIRECTORY)
                           + HdrInfo->SectionHeadersSize + HdrInfo->ExtraSectionHeadersSize;

  return true;
}

#define EmitPeGetSectionsSize  PE_SUFFIX (EmitPeGetSectionsSize)
static
bool
EmitPeGetSectionsSize (
  const image_tool_pe_emit_context_t  *Context,
  uint32_t                            *SectionsSize
  )
{
  const image_tool_image_info_t  *Image;
  uint8_t                        Index;
  uint32_t                       DataSize;
  bool                           Overflow;

  assert (Context      != NULL);
  assert (SectionsSize != NULL);

  Image         = Context->Image;
  *SectionsSize = 0;

  for (Index = 0; Index < Image->SegmentInfo.NumSegments; ++Index) {
    Overflow = BaseOverflowAlignUpU32 (
                 Image->SegmentInfo.Segments[Index].UnpaddedSize,
                 Context->FileAlignment,
                 &DataSize
                 );
    if (Overflow) {
      raise ();
      return false;
    }

    Overflow = BaseOverflowAddU32 (*SectionsSize, DataSize, SectionsSize);
    if (Overflow) {
      raise ();
      return false;
    }
  }

  return true;
}

#define EmitPeGetRelocSectionSize  PE_SUFFIX (EmitPeGetRelocSectionSize)
static
bool
EmitPeGetRelocSectionSize (
  const image_tool_image_info_t  *Image,
  uint32_t                       *RelocsSize
  )
{
  uint32_t  RelocTableSize;
  uint32_t  BlockAddress;
  uint32_t  BlockSize;
  uint32_t  Index;
  uint32_t  RelocAddress;

  assert (Image      != NULL);
  assert (RelocsSize != NULL);

  if (Image->RelocInfo.NumRelocs == 0) {
    *RelocsSize = 0;
    return true;
  }

  assert (Image->RelocInfo.NumRelocs <= MAX_UINT32);

  RelocTableSize = 0;
  BlockAddress   = PAGE (Image->RelocInfo.Relocs[0].Target);
  BlockSize      = sizeof (EFI_IMAGE_BASE_RELOCATION_BLOCK);

  for (Index = 0; Index < Image->RelocInfo.NumRelocs; ++Index) {
    RelocAddress = PAGE (Image->RelocInfo.Relocs[Index].Target);
    if (RelocAddress != BlockAddress) {
      BlockSize = ALIGN_VALUE (BlockSize, 4);

      RelocTableSize += BlockSize;

      BlockAddress = RelocAddress;
      BlockSize    = sizeof (EFI_IMAGE_BASE_RELOCATION_BLOCK);
    }

    BlockSize += sizeof (UINT16);
  }

  BlockSize       = ALIGN_VALUE (BlockSize, 4);
  RelocTableSize += BlockSize;

  *RelocsSize = RelocTableSize;

  return true;
}

#define EmitPeGetDebugSectionSize  PE_SUFFIX (EmitPeGetDebugSectionSize)
static
void
EmitPeGetDebugSectionSize (
  const image_tool_image_info_t  *Image,
  uint32_t                       *DebugSize
  )
{
  uint32_t  Size;

  assert (Image     != NULL);
  assert (DebugSize != NULL);

  Size = 0;
  if (Image->DebugInfo.SymbolsPath != NULL) {
    Size = sizeof (DebugData) + Image->DebugInfo.SymbolsPathLen + 1;
  }

  *DebugSize = Size;
}

#define EmitPeGetExtraSectionsSize  PE_SUFFIX (EmitPeGetExtraSectionsSize)
static
bool
EmitPeGetExtraSectionsSize (
  image_tool_pe_emit_context_t  *Context,
  uint32_t                      *SectionsSize
  )
{
  const image_tool_image_info_t  *Image;
  bool                           Result;
  uint32_t                       AlignedRelocTableSize;
  bool                           Overflow;
  uint32_t                       AlignedDebugTableSize;
  uint32_t                       AlignedHiiTableSize;

  assert (Context      != NULL);
  assert (SectionsSize != NULL);

  Image = Context->Image;

  Result = EmitPeGetRelocSectionSize (Image, &Context->RelocTableSize);
  if (!Result) {
    raise ();
    return false;
  }

  EmitPeGetDebugSectionSize (Image, &Context->DebugTableSize);

  Overflow = BaseOverflowAlignUpU32 (
               Context->RelocTableSize,
               Context->FileAlignment,
               &AlignedRelocTableSize
               );
  if (Overflow) {
    raise ();
    return false;
  }

  Overflow = BaseOverflowAlignUpU32 (
               Context->DebugTableSize,
               Context->FileAlignment,
               &AlignedDebugTableSize
               );
  if (Overflow) {
    raise ();
    return false;
  }

  AlignedHiiTableSize = 0;
  if (Context->Image->HiiInfo.DataSize > 0) {
    Overflow = BaseOverflowAddU32 (
                 mHiiResourceSectionHeaderSize,
                 Context->Image->HiiInfo.DataSize,
                 &AlignedHiiTableSize
                 );

    Overflow |= BaseOverflowAlignUpU32 (
                  AlignedHiiTableSize,
                  Context->FileAlignment,
                  &AlignedHiiTableSize
                  );
    if (Overflow) {
      raise ();
      return false;
    }
  }

  Overflow = BaseOverflowAddU32 (
               AlignedRelocTableSize,
               AlignedDebugTableSize,
               SectionsSize
               );
  if (Overflow) {
    raise ();
    return false;
  }

  Overflow = BaseOverflowAddU32 (
               *SectionsSize,
               AlignedHiiTableSize,
               SectionsSize
               );
  if (Overflow) {
    raise ();
    return false;
  }

  return true;
}

#define ToolImageEmitPeSectionHeaders  PE_SUFFIX (ToolImageEmitPeSectionHeaders)
static
bool
ToolImageEmitPeSectionHeaders (
  const image_tool_pe_emit_context_t  *Context,
  uint8_t                             **Buffer,
  uint32_t                            *BufferSize,
  uint32_t                            AlignedHeaderSize
  )
{
  const image_tool_image_info_t  *Image;
  uint16_t                       SectionHeadersSize;
  uint32_t                       SectionOffset;
  EFI_IMAGE_SECTION_HEADER       *Sections;
  uint8_t                        Index;

  assert (Context    != NULL);
  assert (Buffer     != NULL);
  assert (BufferSize != NULL);

  Image              = Context->Image;
  SectionHeadersSize = (uint16_t)(Image->SegmentInfo.NumSegments * sizeof (EFI_IMAGE_SECTION_HEADER));
  SectionOffset      = AlignedHeaderSize;
  Sections           = (void *)*Buffer;

  assert (SectionHeadersSize <= *BufferSize);

  for (Index = 0; Index < Image->SegmentInfo.NumSegments; ++Index) {
    assert (Sections[Index].Characteristics == 0);

    if (Image->SegmentInfo.Segments[Index].Read) {
      Sections[Index].Characteristics |= EFI_IMAGE_SCN_MEM_READ;
    }

    if (Image->SegmentInfo.Segments[Index].Write) {
      Sections[Index].Characteristics |= EFI_IMAGE_SCN_MEM_WRITE;
    }

    if (Image->SegmentInfo.Segments[Index].Execute) {
      Sections[Index].Characteristics |= EFI_IMAGE_SCN_MEM_EXECUTE | EFI_IMAGE_SCN_CNT_CODE;
    } else {
      Sections[Index].Characteristics |= EFI_IMAGE_SCN_CNT_INITIALIZED_DATA;
    }

    Sections[Index].PointerToRawData = SectionOffset;
    Sections[Index].VirtualAddress   = SectionOffset;
    Sections[Index].SizeOfRawData    = ALIGN_VALUE (Image->SegmentInfo.Segments[Index].UnpaddedSize, Context->FileAlignment);
    Sections[Index].VirtualSize      = Image->SegmentInfo.Segments[Index].ImageSize;

    strncpy (
      (char *)Sections[Index].Name,
      Image->SegmentInfo.Segments[Index].Name,
      sizeof (Sections[Index].Name)
      );

    SectionOffset += Sections[Index].SizeOfRawData;
  }

  if (Image->HeaderInfo.FixedAddress) {
    for (Index = 0; Index < Image->SegmentInfo.NumSegments; ++Index) {
      if ((Sections[Index].Characteristics & EFI_IMAGE_SCN_MEM_EXECUTE) == 0) {
        WriteUnaligned64 (
          (VOID *)&Sections[Index].PointerToRelocations,
          Image->HeaderInfo.BaseAddress
          );
        break;
      }
    }

    if (Index == Image->SegmentInfo.NumSegments) {
      raise ();
      return false;
    }
  }

  *BufferSize -= SectionHeadersSize;
  *Buffer     += SectionHeadersSize;

  assert (SectionHeadersSize == Context->HdrInfo.SectionHeadersSize);

  return true;
}

#define ToolImageEmitPeExtraSectionHeaders  PE_SUFFIX (ToolImageEmitPeExtraSectionHeaders)
static
bool
ToolImageEmitPeExtraSectionHeaders (
  image_tool_pe_emit_context_t  *Context,
  uint8_t                       **Buffer,
  uint32_t                      *BufferSize,
  uint32_t                      AlignedHeaderSize
  )
{
  uint32_t                  SectionHeadersSize;
  EFI_IMAGE_SECTION_HEADER  *Section;
  uint32_t                  SectionOffset;
  uint32_t                  HiiSectionSize;

  assert (Context    != NULL);
  assert (Buffer     != NULL);
  assert (BufferSize != NULL);

  SectionHeadersSize = 0;
  SectionOffset      = AlignedHeaderSize + Context->SectionsSize;

  if (Context->Image->HiiInfo.DataSize > 0) {
    ++Context->PeHdr->CommonHeader.FileHeader.NumberOfSections;

    assert (sizeof (EFI_IMAGE_SECTION_HEADER) <= *BufferSize);

    HiiSectionSize = mHiiResourceSectionHeaderSize + Context->Image->HiiInfo.DataSize;

    Section = (void *)*Buffer;

    strncpy ((char *)Section->Name, ".rsrc", sizeof (Section->Name));
    Section->SizeOfRawData    = ALIGN_VALUE (HiiSectionSize, Context->FileAlignment);
    Section->VirtualSize      = ALIGN_VALUE (HiiSectionSize, Context->Image->SegmentInfo.SegmentAlignment);
    Section->Characteristics  = EFI_IMAGE_SCN_CNT_INITIALIZED_DATA | EFI_IMAGE_SCN_MEM_READ;
    Section->PointerToRawData = SectionOffset;
    Section->VirtualAddress   = Section->PointerToRawData;

    Context->HiiSectionAddress = SectionOffset;

    SectionOffset += Section->SizeOfRawData;

    Context->PeHdr->DataDirectory[EFI_IMAGE_DIRECTORY_ENTRY_RESOURCE].Size           = HiiSectionSize;
    Context->PeHdr->DataDirectory[EFI_IMAGE_DIRECTORY_ENTRY_RESOURCE].VirtualAddress = Section->PointerToRawData;

    *BufferSize        -= sizeof (EFI_IMAGE_SECTION_HEADER);
    *Buffer            += sizeof (EFI_IMAGE_SECTION_HEADER);
    SectionHeadersSize += sizeof (EFI_IMAGE_SECTION_HEADER);
  }

  if (Context->RelocTableSize > 0) {
    ++Context->PeHdr->CommonHeader.FileHeader.NumberOfSections;

    assert (sizeof (EFI_IMAGE_SECTION_HEADER) <= *BufferSize);

    Section = (void *)*Buffer;

    strncpy ((char *)Section->Name, ".reloc", sizeof (Section->Name));
    Section->SizeOfRawData   = ALIGN_VALUE (Context->RelocTableSize, Context->FileAlignment);
    Section->VirtualSize     = Section->SizeOfRawData;
    Section->Characteristics = EFI_IMAGE_SCN_CNT_INITIALIZED_DATA
                               | EFI_IMAGE_SCN_MEM_DISCARDABLE | EFI_IMAGE_SCN_MEM_READ;
    Section->PointerToRawData = SectionOffset;
    Section->VirtualAddress   = Section->PointerToRawData;

    SectionOffset += Section->SizeOfRawData;

    Context->PeHdr->DataDirectory[EFI_IMAGE_DIRECTORY_ENTRY_BASERELOC].Size           = Context->RelocTableSize;
    Context->PeHdr->DataDirectory[EFI_IMAGE_DIRECTORY_ENTRY_BASERELOC].VirtualAddress = Section->PointerToRawData;

    *BufferSize        -= sizeof (EFI_IMAGE_SECTION_HEADER);
    *Buffer            += sizeof (EFI_IMAGE_SECTION_HEADER);
    SectionHeadersSize += sizeof (EFI_IMAGE_SECTION_HEADER);
  }

  if (Context->DebugTableSize > 0) {
    ++Context->PeHdr->CommonHeader.FileHeader.NumberOfSections;

    assert (sizeof (EFI_IMAGE_SECTION_HEADER) <= *BufferSize);

    Section = (void *)*Buffer;

    strncpy ((char *)Section->Name, ".debug", sizeof (Section->Name));
    Section->SizeOfRawData    = ALIGN_VALUE (Context->DebugTableSize, Context->FileAlignment);
    Section->VirtualSize      = Section->SizeOfRawData;
    Section->Characteristics  = EFI_IMAGE_SCN_CNT_INITIALIZED_DATA | EFI_IMAGE_SCN_MEM_READ;
    Section->PointerToRawData = SectionOffset;
    Section->VirtualAddress   = Section->PointerToRawData;

    SectionOffset += Section->SizeOfRawData;

    Context->PeHdr->DataDirectory[EFI_IMAGE_DIRECTORY_ENTRY_DEBUG].Size           = sizeof (EFI_IMAGE_DEBUG_DIRECTORY_ENTRY);
    Context->PeHdr->DataDirectory[EFI_IMAGE_DIRECTORY_ENTRY_DEBUG].VirtualAddress = Section->VirtualAddress;

    *BufferSize        -= sizeof (EFI_IMAGE_SECTION_HEADER);
    *Buffer            += sizeof (EFI_IMAGE_SECTION_HEADER);
    SectionHeadersSize += sizeof (EFI_IMAGE_SECTION_HEADER);
  }

  assert (SectionHeadersSize == Context->HdrInfo.ExtraSectionHeadersSize);
  assert (SectionOffset == Context->UnsignedFileSize);

  return true;
}

#define ToolImageEmitPeHeaders  PE_SUFFIX (ToolImageEmitPeHeaders)
static
bool
ToolImageEmitPeHeaders (
  image_tool_pe_emit_context_t  *Context,
  uint8_t                       **Buffer,
  uint32_t                      *BufferSize,
  uint32_t                      AlignedHeaderSize
  )
{
  const image_tool_image_info_t  *Image;
  EFI_IMAGE_DOS_HEADER           *DosHdr;
  EFI_IMAGE_NT_HEADERS           *PePlusHdr;
  bool                           Result;
  uint32_t                       HeaderPadding;

  assert (Context    != NULL);
  assert (Buffer     != NULL);
  assert (BufferSize != NULL);

  assert (sizeof (EFI_IMAGE_DOS_HEADER) <= *BufferSize);

  Image  = Context->Image;
  DosHdr = (void *)*Buffer;

  DosHdr->e_magic  = EFI_IMAGE_DOS_SIGNATURE;
  DosHdr->e_lfanew = sizeof (EFI_IMAGE_DOS_HEADER);

  *BufferSize -= sizeof (EFI_IMAGE_DOS_HEADER);
  *Buffer     += sizeof (EFI_IMAGE_DOS_HEADER);

  assert (sizeof (EFI_IMAGE_NT_HEADERS) <= *BufferSize);

  PePlusHdr = (EFI_IMAGE_NT_HEADERS *)(VOID *)*Buffer;

  PePlusHdr->CommonHeader.Signature                       = EFI_IMAGE_NT_SIGNATURE;
  PePlusHdr->CommonHeader.FileHeader.Machine              = Image->HeaderInfo.Machine;
  PePlusHdr->CommonHeader.FileHeader.NumberOfSections     = (UINT16)Image->SegmentInfo.NumSegments;
  PePlusHdr->CommonHeader.FileHeader.SizeOfOptionalHeader = Context->HdrInfo.SizeOfOptionalHeader;
  PePlusHdr->CommonHeader.FileHeader.Characteristics      =
    EFI_IMAGE_FILE_EXECUTABLE_IMAGE | EFI_IMAGE_FILE_LINE_NUMS_STRIPPED |
    EFI_IMAGE_FILE_LOCAL_SYMS_STRIPPED | EFI_IMAGE_FILE_LARGE_ADDRESS_AWARE;

  if (Image->RelocInfo.RelocsStripped) {
    PePlusHdr->CommonHeader.FileHeader.Characteristics |= EFI_IMAGE_FILE_RELOCS_STRIPPED;
  }

  PePlusHdr->Magic               = EFI_IMAGE_NT_OPTIONAL_HDR_MAGIC;
  PePlusHdr->AddressOfEntryPoint = Image->HeaderInfo.EntryPointAddress;
  PePlusHdr->SectionAlignment    = Image->SegmentInfo.SegmentAlignment;
  PePlusHdr->FileAlignment       = Context->FileAlignment;
  PePlusHdr->SizeOfHeaders       = AlignedHeaderSize;
  PePlusHdr->SizeOfImage         = AlignedHeaderSize;
  PePlusHdr->ImageBase           = (UINTN)Image->HeaderInfo.BaseAddress;
  PePlusHdr->Subsystem           = Image->HeaderInfo.Subsystem;
  PePlusHdr->NumberOfRvaAndSizes = Context->HdrInfo.NumberOfRvaAndSizes;

  STATIC_ASSERT (
    OFFSET_OF (EFI_IMAGE_NT_HEADERS, DataDirectory) == sizeof (EFI_IMAGE_NT_HEADERS),
    "The following code needs to be updated to consider padding."
    );

  Context->PeHdr = PePlusHdr;

  *BufferSize -= sizeof (EFI_IMAGE_NT_HEADERS) + PePlusHdr->NumberOfRvaAndSizes * sizeof (EFI_IMAGE_DATA_DIRECTORY);
  *Buffer     += sizeof (EFI_IMAGE_NT_HEADERS) + PePlusHdr->NumberOfRvaAndSizes * sizeof (EFI_IMAGE_DATA_DIRECTORY);

  Result = ToolImageEmitPeSectionHeaders (Context, Buffer, BufferSize, AlignedHeaderSize);
  if (!Result) {
    return false;
  }

  Result = ToolImageEmitPeExtraSectionHeaders (Context, Buffer, BufferSize, AlignedHeaderSize);
  if (!Result) {
    return false;
  }

  HeaderPadding = AlignedHeaderSize - Context->HdrInfo.SizeOfHeaders;

  assert (HeaderPadding <= *BufferSize);

  *BufferSize -= HeaderPadding;
  *Buffer     += HeaderPadding;

  return true;
}

#define ToolImageEmitPeSections  PE_SUFFIX (ToolImageEmitPeSections)
static
bool
ToolImageEmitPeSections (
  const image_tool_pe_emit_context_t  *Context,
  uint8_t                             **Buffer,
  uint32_t                            *BufferSize
  )
{
  const image_tool_image_info_t  *Image;
  uint32_t                       SectionsSize;
  uint8_t                        Index;
  const image_tool_segment_t     *Segment;
  uint32_t                       SectionPadding;
  bool                           FirstCode;

 #if PE_ARCH == 32
  bool  FirstData;
 #endif

  assert (Context    != NULL);
  assert (Buffer     != NULL);
  assert (BufferSize != NULL);

  assert (Context->SectionsSize <= *BufferSize);

  Image        = Context->Image;
  SectionsSize = 0;
  FirstCode    = true;

 #if PE_ARCH == 32
  FirstData = true;
 #endif

  for (Index = 0; Index < Image->SegmentInfo.NumSegments; ++Index) {
    Segment = &Image->SegmentInfo.Segments[Index];

    Context->PeHdr->SizeOfImage += Segment->ImageSize;

    if (Segment->Execute) {
      if (FirstCode) {
        Context->PeHdr->BaseOfCode = Segment->ImageAddress;
        FirstCode                  = false;
      }
    }

 #if PE_ARCH == 32
    else {
      if (FirstData) {
        Context->PeHdr->BaseOfData = Segment->ImageAddress;
        FirstData                  = false;
      }
    }
 #endif

    assert (Segment->UnpaddedSize <= *BufferSize);

    memmove (*Buffer, Segment->Data, Segment->UnpaddedSize);

    *BufferSize  -= Segment->UnpaddedSize;
    *Buffer      += Segment->UnpaddedSize;
    SectionsSize += Segment->UnpaddedSize;

    SectionPadding = ALIGN_VALUE_ADDEND (
                       Segment->UnpaddedSize,
                       Context->FileAlignment
                       );

    assert (SectionPadding <= *BufferSize);

    *BufferSize  -= SectionPadding;
    *Buffer      += SectionPadding;
    SectionsSize += SectionPadding;

    if (Segment->Execute) {
      Context->PeHdr->BaseOfCode  = MIN (Context->PeHdr->BaseOfCode, Segment->ImageAddress);
      Context->PeHdr->SizeOfCode += Segment->ImageSize;
    } else {
 #if PE_ARCH == 32
      Context->PeHdr->BaseOfData = MIN (Context->PeHdr->BaseOfData, Segment->ImageAddress);
 #endif
      Context->PeHdr->SizeOfInitializedData += Segment->ImageSize;
    }
  }

  assert (SectionsSize == Context->SectionsSize);

  return true;
}

#define ToolImageEmitPeRelocTable  PE_SUFFIX (ToolImageEmitPeRelocTable)
static
bool
ToolImageEmitPeRelocTable (
  const image_tool_pe_emit_context_t  *Context,
  uint8_t                             **Buffer,
  uint32_t                            *BufferSize
  )
{
  const image_tool_image_info_t    *Image;
  uint32_t                         RelocTableSize;
  EFI_IMAGE_BASE_RELOCATION_BLOCK  *RelocBlock;
  uint32_t                         BlockAddress;
  uint32_t                         BlockNumRelocs;
  uint32_t                         Index;
  uint32_t                         RelocAddress;
  uint32_t                         RelocTablePadding;

  assert (Context    != NULL);
  assert (Buffer     != NULL);
  assert (BufferSize != NULL);

  if (Context->RelocTableSize == 0) {
    return true;
  }

  Image = Context->Image;

  Context->PeHdr->SizeOfImage += ALIGN_VALUE (Context->RelocTableSize, Image->SegmentInfo.SegmentAlignment);

  assert (Image->RelocInfo.NumRelocs > 0);
  assert (Image->RelocInfo.NumRelocs <= MAX_UINT32);

  assert (sizeof (EFI_IMAGE_BASE_RELOCATION_BLOCK) <= *BufferSize);

  RelocTableSize = 0;
  RelocBlock     = (void *)*Buffer;
  BlockAddress   = PAGE (Image->RelocInfo.Relocs[0].Target);
  BlockNumRelocs = 0;

  RelocBlock->VirtualAddress = BlockAddress;
  RelocBlock->SizeOfBlock    = sizeof (*RelocBlock);

  for (Index = 0; Index < Image->RelocInfo.NumRelocs; ++Index) {
    RelocAddress = PAGE (Image->RelocInfo.Relocs[Index].Target);
    if (RelocAddress != BlockAddress) {
      RelocBlock->SizeOfBlock = ALIGN_VALUE (RelocBlock->SizeOfBlock, 4);

      assert (RelocBlock->SizeOfBlock <= *BufferSize);

      *BufferSize    -= RelocBlock->SizeOfBlock;
      *Buffer        += RelocBlock->SizeOfBlock;
      RelocTableSize += RelocBlock->SizeOfBlock;

      RelocBlock = (void *)*Buffer;

      BlockAddress   = RelocAddress;
      BlockNumRelocs = 0;

      RelocBlock->VirtualAddress = BlockAddress;
      RelocBlock->SizeOfBlock    = sizeof (*RelocBlock);
    }

    RelocBlock->SizeOfBlock += sizeof (*RelocBlock->Relocations);

    assert (RelocBlock->SizeOfBlock <= *BufferSize);

    RelocBlock->Relocations[BlockNumRelocs]  = PAGE_OFF (Image->RelocInfo.Relocs[Index].Target);
    RelocBlock->Relocations[BlockNumRelocs] |= ((uint16_t)Image->RelocInfo.Relocs[Index].Type) << 12U;

    ++BlockNumRelocs;
  }

  RelocBlock->SizeOfBlock = ALIGN_VALUE (RelocBlock->SizeOfBlock, 4);

  assert (RelocBlock->SizeOfBlock <= *BufferSize);

  *BufferSize    -= RelocBlock->SizeOfBlock;
  *Buffer        += RelocBlock->SizeOfBlock;
  RelocTableSize += RelocBlock->SizeOfBlock;

  assert (RelocTableSize == Context->RelocTableSize);

  RelocTablePadding = ALIGN_VALUE_ADDEND (
                        RelocTableSize,
                        Context->FileAlignment
                        );

  assert (RelocTablePadding <= *BufferSize);

  *BufferSize -= RelocTablePadding;
  *Buffer     += RelocTablePadding;

  return true;
}

typedef struct {
  EFI_IMAGE_DEBUG_DIRECTORY_ENTRY        CodeViewDirEntry;
  EFI_IMAGE_DEBUG_CODEVIEW_RSDS_ENTRY    CodeViewEntry;
  uint8_t                                PdbPath[];
} image_tool_debug_dir_t;

STATIC_ASSERT (
  OFFSET_OF (image_tool_debug_dir_t, PdbPath) == sizeof (image_tool_debug_dir_t),
  "Flexible array aliases padding."
  );

#define ToolImageEmitPeDebugTable  PE_SUFFIX (ToolImageEmitPeDebugTable)
static
bool
ToolImageEmitPeDebugTable (
  const image_tool_pe_emit_context_t  *Context,
  uint8_t                             **Buffer,
  uint32_t                            *BufferSize
  )
{
  const image_tool_image_info_t  *Image;
  uint32_t                       DebugTablePadding;
  DebugData                      *Data;

  assert (Context    != NULL);
  assert (Buffer     != NULL);
  assert (BufferSize != NULL);

  Image = Context->Image;

  if (Context->DebugTableSize == 0) {
    return true;
  }

  Context->PeHdr->SizeOfImage += ALIGN_VALUE (Context->DebugTableSize, Image->SegmentInfo.SegmentAlignment);

  assert (Image->DebugInfo.SymbolsPathLen + 1 <= Context->DebugTableSize);
  assert (Context->DebugTableSize <= *BufferSize);

  Data = (DebugData *)*Buffer;

  Data->Dir.Type       = EFI_IMAGE_DEBUG_TYPE_CODEVIEW;
  Data->Dir.SizeOfData = sizeof (EFI_IMAGE_DEBUG_CODEVIEW_NB10_ENTRY) + Image->DebugInfo.SymbolsPathLen + 1;
  Data->Dir.RVA        = (Context->UnsignedFileSize - ALIGN_VALUE (Context->DebugTableSize, Context->FileAlignment)) + sizeof (EFI_IMAGE_DEBUG_DIRECTORY_ENTRY);
  Data->Dir.FileOffset = Data->Dir.RVA;

  Data->Nb10.Signature = CODEVIEW_SIGNATURE_NB10;
  memmove (Data->Name, Image->DebugInfo.SymbolsPath, Image->DebugInfo.SymbolsPathLen + 1);

  assert (sizeof (*Data) + Image->DebugInfo.SymbolsPathLen + 1 == Context->DebugTableSize);

  *BufferSize -= Context->DebugTableSize;
  *Buffer     += Context->DebugTableSize;

  DebugTablePadding = ALIGN_VALUE_ADDEND (
                        Context->DebugTableSize,
                        Context->FileAlignment
                        );

  assert (DebugTablePadding <= *BufferSize);

  *BufferSize -= DebugTablePadding;
  *Buffer     += DebugTablePadding;

  return true;
}

#define ToolImageEmitPeHiiTable  PE_SUFFIX (ToolImageEmitPeHiiTable)
static
bool
ToolImageEmitPeHiiTable (
  const image_tool_pe_emit_context_t  *Context,
  uint8_t                             **Buffer,
  uint32_t                            *BufferSize
  )
{
  const image_tool_image_info_t  *Image;
  uint32_t                       HiiTablePadding;

  assert (Context    != NULL);
  assert (Buffer     != NULL);
  assert (BufferSize != NULL);

  Image = Context->Image;

  if (Image->HiiInfo.DataSize == 0) {
    return true;
  }

  Context->PeHdr->SizeOfImage += ALIGN_VALUE (mHiiResourceSectionHeaderSize + Image->HiiInfo.DataSize, Image->SegmentInfo.SegmentAlignment);

  assert (mHiiResourceSectionHeaderSize <= *BufferSize);

  InitializeHiiResouceSectionHeader (
    *Buffer,
    Context->HiiSectionAddress,
    Context->Image->HiiInfo.DataSize
    );

  *BufferSize -= mHiiResourceSectionHeaderSize;
  *Buffer     += mHiiResourceSectionHeaderSize;

  assert (Image->HiiInfo.DataSize <= *BufferSize);

  memmove (*Buffer, Image->HiiInfo.Data, Image->HiiInfo.DataSize);

  *BufferSize -= Image->HiiInfo.DataSize;
  *Buffer     += Image->HiiInfo.DataSize;

  HiiTablePadding = ALIGN_VALUE_ADDEND (
                      mHiiResourceSectionHeaderSize + Image->HiiInfo.DataSize,
                      Context->FileAlignment
                      );

  assert (HiiTablePadding <= *BufferSize);

  *BufferSize -= HiiTablePadding;
  *Buffer     += HiiTablePadding;

  return true;
}

#define ToolImageEmitPeExtraSections  PE_SUFFIX (ToolImageEmitPeExtraSections)
static
bool
ToolImageEmitPeExtraSections (
  const image_tool_pe_emit_context_t  *Context,
  uint8_t                             **Buffer,
  uint32_t                            *BufferSize
  )
{
  uint32_t  OldBufferSize;
  bool      Result;

  assert (Context    != NULL);
  assert (Buffer     != NULL);
  assert (BufferSize != NULL);

  OldBufferSize = *BufferSize;

  Result = ToolImageEmitPeHiiTable (Context, Buffer, BufferSize);
  if (!Result) {
    return false;
  }

  Result = ToolImageEmitPeRelocTable (Context, Buffer, BufferSize);
  if (!Result) {
    return false;
  }

  Result = ToolImageEmitPeDebugTable (Context, Buffer, BufferSize);
  if (!Result) {
    return false;
  }

  assert ((OldBufferSize - *BufferSize) == Context->ExtraSectionsSize);

  return true;
}

#define ToolImageEmitPe  PE_SUFFIX (ToolImageEmitPe)
void *
ToolImageEmitPe (
  image_tool_image_info_t  *Image,
  uint32_t                 *FileSize
  )
{
  image_tool_pe_emit_context_t  Context;
  bool                          Result;
  uint32_t                      AlignedHeaderSize;
  bool                          Overflow;
  uint32_t                      SectionsOffset;
  void                          *FileBuffer;
  uint8_t                       *Buffer;
  uint32_t                      RemainingSize;
  uint32_t                      ExpectedSize;

  assert (Image    != NULL);
  assert (FileSize != NULL);

  memset (&Context, 0, sizeof (Context));

  // FIXME: Non-XIP is not well-supported right now.
  Context.FileAlignment   = Image->SegmentInfo.SegmentAlignment;
  Image->HeaderInfo.IsXip = true;

  ImageInitUnpaddedSize (Image);

  Context.Image = Image;

  Result = EmitPeGetHeaderSizes (Image, &Context.HdrInfo);
  if (!Result) {
    raise ();
    return NULL;
  }

  Overflow = BaseOverflowAlignUpU32 (
               Context.HdrInfo.SizeOfHeaders,
               Context.FileAlignment,
               &AlignedHeaderSize
               );
  if (Overflow) {
    raise ();
    return NULL;
  }

  if (AlignedHeaderSize > Image->SegmentInfo.Segments[0].ImageAddress) {
    raise ();
    return NULL;
  }

  AlignedHeaderSize = (uint32_t)Image->SegmentInfo.Segments[0].ImageAddress;

  Result = EmitPeGetSectionsSize (&Context, &Context.SectionsSize);
  if (!Result) {
    raise ();
    return NULL;
  }

  Overflow = BaseOverflowAddU32 (
               AlignedHeaderSize,
               Context.SectionsSize,
               &SectionsOffset
               );
  if (Overflow) {
    raise ();
    return NULL;
  }

  Result = EmitPeGetExtraSectionsSize (&Context, &Context.ExtraSectionsSize);
  if (!Result) {
    raise ();
    return NULL;
  }

  Overflow = BaseOverflowAddU32 (
               SectionsOffset,
               Context.ExtraSectionsSize,
               &Context.UnsignedFileSize
               );
  if (Overflow) {
    raise ();
    return NULL;
  }

  FileBuffer = calloc (1, Context.UnsignedFileSize);
  if (FileBuffer == NULL) {
    raise ();
    return NULL;
  }

  Buffer        = FileBuffer;
  RemainingSize = Context.UnsignedFileSize;
  ExpectedSize  = Context.UnsignedFileSize;

  Result = ToolImageEmitPeHeaders (&Context, &Buffer, &RemainingSize, AlignedHeaderSize);
  if (!Result) {
    raise ();
    free (FileBuffer);
    return NULL;
  }

  ExpectedSize -= AlignedHeaderSize;

  assert (RemainingSize == ExpectedSize);

  Result = ToolImageEmitPeSections (&Context, &Buffer, &RemainingSize);
  if (!Result) {
    raise ();
    free (FileBuffer);
    return NULL;
  }

  ExpectedSize -= Context.SectionsSize;

  assert (RemainingSize == ExpectedSize);

  Result = ToolImageEmitPeExtraSections (&Context, &Buffer, &RemainingSize);
  if (!Result) {
    raise ();
    free (FileBuffer);
    return NULL;
  }

  ExpectedSize -= Context.ExtraSectionsSize;

  assert (RemainingSize == ExpectedSize);
  assert (RemainingSize == 0);

  Context.PeHdr->SizeOfInitializedData += Context.ExtraSectionsSize;

  *FileSize = Context.UnsignedFileSize;

  return FileBuffer;
}
