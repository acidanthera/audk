#include "ImageTool.h"

typedef struct {
  uint8_t  NumExtraSections;
  uint32_t SizeOfHeaders;
  uint8_t  NumberOfRvaAndSizes;
  uint16_t SizeOfOptionalHeader;
  uint32_t SectionHeadersSize;
  uint32_t ExtraSectionHeadersSize;
} image_tool_emit_pe_hdr_info_t;

typedef struct {
  const image_tool_image_info_t *Image;
  EFI_IMAGE_NT_HEADERS          *PeHdr;
  image_tool_emit_pe_hdr_info_t HdrInfo;
  uint32_t                      SectionsSize;
  uint32_t                      ExtraSectionsSize;
  uint32_t                      UnsignedFileSize;
  uint32_t                      RelocTableSize;
  uint32_t                      HiiTableSize;
  uint32_t                      DebugTableSize;
  uint16_t                      FileAlignment;
} image_tool_pe_emit_context_t;

static
bool
EmitPeGetHeaderSizes (
  const image_tool_image_info_t *Image,
  image_tool_emit_pe_hdr_info_t *HdrInfo
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
    // FIXME:
    //HdrInfo->ExtraSectionHeadersSize += sizeof (EFI_IMAGE_SECTION_HEADER);
  }

  HdrInfo->SectionHeadersSize = (uint32_t)Image->SegmentInfo.NumSegments * sizeof (EFI_IMAGE_SECTION_HEADER);

  HdrInfo->NumberOfRvaAndSizes = EFI_IMAGE_NUMBER_OF_DIRECTORY_ENTRIES;
  HdrInfo->SizeOfOptionalHeader = sizeof (EFI_IMAGE_NT_HEADERS) - sizeof (EFI_IMAGE_NT_HEADERS_COMMON_HDR)
    + HdrInfo->NumberOfRvaAndSizes * sizeof (EFI_IMAGE_DATA_DIRECTORY);
  HdrInfo->SizeOfHeaders = sizeof (EFI_IMAGE_DOS_HEADER) + sizeof (EFI_IMAGE_NT_HEADERS)
    + HdrInfo->NumberOfRvaAndSizes * sizeof (EFI_IMAGE_DATA_DIRECTORY)
    + HdrInfo->SectionHeadersSize
    + HdrInfo->ExtraSectionHeadersSize;

  return true;
}

static
bool
EmitPeGetSectionsSize (
  const image_tool_pe_emit_context_t *Context,
  uint32_t                           *SectionsSize
  )
{
  const image_tool_image_info_t *Image;
  uint8_t                       Index;
  uint32_t                      DataSize;
  bool                          Overflow;

  assert (Context      != NULL);
  assert (SectionsSize != NULL);

  Image         = Context->Image;
  *SectionsSize = 0;

  for (Index = 0; Index < Image->SegmentInfo.NumSegments; ++Index) {
    Overflow = BaseOverflowAlignUpU32 (
      Image->SegmentInfo.Segments[Index].DataSize,
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

static
bool
EmitPeGetRelocSectionSize (
  const image_tool_image_info_t *Image,
  uint32_t                      *RelocsSize
  )
{
  uint32_t RelocTableSize;
  uint32_t BlockAddress;
  uint32_t BlockSize;
  uint32_t Index;
  uint32_t RelocAddress;

  assert (Image      != NULL);
  assert (RelocsSize != NULL);

  if (Image->RelocInfo.NumRelocs == 0) {
    *RelocsSize = 0;
    return true;
  }

  assert (Image->RelocInfo.NumRelocs <= MAX_UINT32);

  RelocTableSize = 0;
  BlockAddress   = PAGE(Image->RelocInfo.Relocs[0].Target);
  BlockSize      = sizeof (EFI_IMAGE_BASE_RELOCATION_BLOCK);

  for (Index = 0; Index < Image->RelocInfo.NumRelocs; ++Index) {
    RelocAddress = PAGE(Image->RelocInfo.Relocs[Index].Target);
    if (RelocAddress != BlockAddress) {
      BlockSize = ALIGN_VALUE(BlockSize, 4);

      RelocTableSize += BlockSize;

      BlockAddress = RelocAddress;
      BlockSize    = sizeof (EFI_IMAGE_BASE_RELOCATION_BLOCK);
    }

    BlockSize += sizeof (UINT16);
  }

  RelocTableSize += BlockSize;
  *RelocsSize     = RelocTableSize;

  return true;
}

static
bool
EmitPeGetHiiSectionSize (
  const image_tool_pe_emit_context_t *Context,
  uint32_t                           *HiiSize
  )
{
  assert (Context != NULL);
  assert (HiiSize != NULL);

  return !BaseOverflowAlignUpU32 (
    Context->Image->HiiInfo.DataSize,
    Context->FileAlignment,
    HiiSize
    );
}

static
bool
EmitPeGetDebugSectionSize (
  const image_tool_image_info_t *Image,
  uint32_t                      *DebugSize
  )
{
  assert (Image     != NULL);
  assert (DebugSize != NULL);

  // FIXME:
  *DebugSize = 0;

  return true;
}

static
bool
EmitPeGetExtraSectionsSize (
  image_tool_pe_emit_context_t *Context,
  uint32_t                     *SectionsSize
  )
{
  const image_tool_image_info_t *Image;
  bool                          Result;
  uint32_t                      AlignedRelocTableSize;
  bool                          Overflow;
  uint32_t                      AlignedDebugTableSize;
  uint32_t                      AlignedHiiTableSize;

  assert (Context      != NULL);
  assert (SectionsSize != NULL);

  Image = Context->Image;

  Result = EmitPeGetRelocSectionSize (Image, &Context->RelocTableSize);
  if (!Result) {
    raise ();
    return false;
  }

  Result = EmitPeGetDebugSectionSize (Image, &Context->DebugTableSize);
  if (!Result) {
    raise ();
    return false;
  }

  Result = EmitPeGetHiiSectionSize (Context, &Context->HiiTableSize);
  if (!Result) {
    raise ();
    return false;
  }

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

  Overflow = BaseOverflowAlignUpU32 (
    Context->HiiTableSize,
    Context->FileAlignment,
    &AlignedHiiTableSize
    );
  if (Overflow) {
    raise ();
    return false;
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

static
bool
ToolImageEmitPeSectionHeaders (
  const image_tool_pe_emit_context_t *Context,
  uint8_t                            **Buffer,
  uint32_t                           *BufferSize
  )
{
  const image_tool_image_info_t *Image;
  uint16_t                      SectionHeadersSize;
  uint32_t                      SectionOffset;
  EFI_IMAGE_SECTION_HEADER      *Sections;
  uint8_t                       Index;

  assert (Context    != NULL);
  assert (Buffer     != NULL);
  assert (BufferSize != NULL);

  Image              = Context->Image;
  SectionHeadersSize = (uint16_t) (Image->SegmentInfo.NumSegments * sizeof (EFI_IMAGE_SECTION_HEADER));
  SectionOffset      = Context->HdrInfo.SizeOfHeaders;
  Sections           = (void *) *Buffer;

  assert (SectionHeadersSize <= *BufferSize);

  for (Index = 0; Index < Image->SegmentInfo.NumSegments; ++Index) {
    Sections[Index].VirtualSize = Image->SegmentInfo.Segments[Index].ImageSize;

    if (Image->SegmentInfo.Segments[Index].Read) {
      Sections[Index].Characteristics |= EFI_IMAGE_SCN_MEM_READ;
    }

    if (Image->SegmentInfo.Segments[Index].Write) {
      Sections[Index].Characteristics |= EFI_IMAGE_SCN_MEM_WRITE;
    }

    if (Image->SegmentInfo.Segments[Index].Execute) {
      Sections[Index].Characteristics |= EFI_IMAGE_SCN_MEM_EXECUTE;
    }

    Sections[Index].PointerToRawData = SectionOffset;
    Sections[Index].SizeOfRawData    = Image->SegmentInfo.Segments[Index].DataSize;

    strncpy (
      (char *) Sections[Index].Name,
      Image->SegmentInfo.Segments[Index].Name,
      sizeof (Sections[Index].Name)
      );

    SectionOffset += Sections[Index].SizeOfRawData;
    SectionOffset  = ALIGN_VALUE(SectionOffset, Context->FileAlignment);
  }

  *BufferSize -= SectionHeadersSize;
  *Buffer     += SectionHeadersSize;

  assert (SectionHeadersSize == Context->HdrInfo.SectionHeadersSize);

  return true;
}

static
bool
ToolImageEmitPeExtraSectionHeaders (
  const image_tool_pe_emit_context_t *Context,
  uint8_t                            **Buffer,
  uint32_t                           *BufferSize
  )
{
  uint32_t                 SectionHeadersSize;
  EFI_IMAGE_SECTION_HEADER *Section;

  assert (Context    != NULL);
  assert (Buffer     != NULL);
  assert (BufferSize != NULL);

  SectionHeadersSize = 0;

  if (Context->RelocTableSize > 0) {
    assert (sizeof (EFI_IMAGE_SECTION_HEADER) <= *BufferSize);

    Section = (void *) *Buffer;

    Section->SizeOfRawData = Context->RelocTableSize;
    strncpy ((char *)Section->Name, ".reloc", sizeof (Section->Name));

    *BufferSize        -= sizeof (EFI_IMAGE_SECTION_HEADER);
    *Buffer            += sizeof (EFI_IMAGE_SECTION_HEADER);
    SectionHeadersSize += sizeof (EFI_IMAGE_SECTION_HEADER);
  }

  if (Context->DebugTableSize > 0) {
    assert (sizeof (EFI_IMAGE_SECTION_HEADER) <= *BufferSize);

    Section = (void *) *Buffer;

    Section->SizeOfRawData = Context->DebugTableSize;
    strncpy ((char *)Section->Name, ".debug", sizeof (Section->Name));

    *BufferSize        -= sizeof (EFI_IMAGE_SECTION_HEADER);
    *Buffer            += sizeof (EFI_IMAGE_SECTION_HEADER);
    SectionHeadersSize += sizeof (EFI_IMAGE_SECTION_HEADER);
  }

  if (Context->HiiTableSize > 0) {
    assert (sizeof (EFI_IMAGE_SECTION_HEADER) <= *BufferSize);

    Section = (void *) *Buffer;

    Section->SizeOfRawData = Context->RelocTableSize;
    strncpy ((char *)Section->Name, ".rsrc", sizeof (Section->Name));

    *BufferSize        -= sizeof (EFI_IMAGE_SECTION_HEADER);
    *Buffer            += sizeof (EFI_IMAGE_SECTION_HEADER);
    SectionHeadersSize += sizeof (EFI_IMAGE_SECTION_HEADER);
  }

  assert (Context->HdrInfo.ExtraSectionHeadersSize == SectionHeadersSize);

  return true;
}

static
bool
ToolImageEmitPeHeaders (
  const image_tool_pe_emit_context_t *Context,
  uint8_t                            **Buffer,
  uint32_t                           *BufferSize
  )
{
  const image_tool_image_info_t *Image;
  EFI_IMAGE_DOS_HEADER          *DosHdr;
  EFI_IMAGE_NT_HEADERS          *PePlusHdr;
  bool                          Result;
  uint32_t                      HeaderPadding;

  assert (Context    != NULL);
  assert (Buffer     != NULL);
  assert (BufferSize != NULL);

  assert (sizeof (EFI_IMAGE_DOS_HEADER) <= *BufferSize);

  Image  = Context->Image;
  DosHdr = (void *) *Buffer;

  DosHdr->e_magic  = EFI_IMAGE_DOS_SIGNATURE;
  DosHdr->e_lfanew = sizeof (EFI_IMAGE_DOS_HEADER);

  *BufferSize -= sizeof (EFI_IMAGE_DOS_HEADER);
  *Buffer     += sizeof (EFI_IMAGE_DOS_HEADER);

  assert (sizeof (EFI_IMAGE_NT_HEADERS) <= *BufferSize);

  PePlusHdr = (EFI_IMAGE_NT_HEADERS *)(VOID *) *Buffer;

  PePlusHdr->CommonHeader.Signature = EFI_IMAGE_NT_SIGNATURE;
  // FIXME:
  PePlusHdr->CommonHeader.FileHeader.Machine              = Image->HeaderInfo.Machine;
  PePlusHdr->CommonHeader.FileHeader.NumberOfSections     = Image->SegmentInfo.NumSegments;
  PePlusHdr->CommonHeader.FileHeader.SizeOfOptionalHeader = Context->HdrInfo.SizeOfOptionalHeader;

  if (Image->RelocInfo.RelocsStripped) {
    PePlusHdr->CommonHeader.FileHeader.Characteristics |= EFI_IMAGE_FILE_RELOCS_STRIPPED;
  }

  PePlusHdr->Magic               = EFI_IMAGE_NT_OPTIONAL_HDR_MAGIC;
  PePlusHdr->AddressOfEntryPoint = Image->HeaderInfo.EntryPointAddress;
  PePlusHdr->SectionAlignment    = Image->SegmentInfo.SegmentAlignment;
  PePlusHdr->FileAlignment       = Context->FileAlignment;
  PePlusHdr->ImageBase           = Image->HeaderInfo.PreferredAddress;
  // FIXME:
  PePlusHdr->Subsystem           = Image->HeaderInfo.Subsystem;
  PePlusHdr->NumberOfRvaAndSizes = Context->HdrInfo.NumberOfRvaAndSizes;

  STATIC_ASSERT(
    OFFSET_OF(EFI_IMAGE_NT_HEADERS, DataDirectory) == sizeof (EFI_IMAGE_NT_HEADERS),
    "The following code needs to be updated to consider padding."
    );

  *BufferSize -= sizeof (EFI_IMAGE_NT_HEADERS);
  *Buffer     += sizeof (EFI_IMAGE_NT_HEADERS);

  Result = ToolImageEmitPeSectionHeaders (Context, Buffer, BufferSize);
  if (!Result) {
    return false;
  }

  Result = ToolImageEmitPeExtraSectionHeaders (Context, Buffer, BufferSize);
  if (!Result) {
    return false;
  }

  HeaderPadding = ALIGN_VALUE_ADDEND(
    Context->HdrInfo.SizeOfHeaders,
    Context->FileAlignment
    );

  assert (HeaderPadding <= *BufferSize);

  *BufferSize -= HeaderPadding;
  *Buffer     += HeaderPadding;

  return true;
}

static
bool
ToolImageEmitPeSections (
  const image_tool_pe_emit_context_t *Context,
  uint8_t                            **Buffer,
  uint32_t                           *BufferSize
  )
{
  const image_tool_image_info_t *Image;
  uint32_t                      SectionsSize;
  uint8_t                       Index;
  const image_tool_segment_t    *Segment;
  uint32_t                      SectionPadding;

  assert (Context    != NULL);
  assert (Buffer     != NULL);
  assert (BufferSize != NULL);

  assert (Context->SectionsSize <= *BufferSize);

  Image        = Context->Image;
  SectionsSize = 0;

  for (Index = 0; Index < Image->SegmentInfo.NumSegments; ++Index) {
    Segment = &Image->SegmentInfo.Segments[Index];

    assert (Segment->DataSize <= *BufferSize);

    memmove (*Buffer, Segment->Data, Segment->DataSize);

    *BufferSize  -= Segment->DataSize;
    *Buffer      += Segment->DataSize;
    SectionsSize += Segment->DataSize;

    SectionPadding = ALIGN_VALUE_ADDEND(
      Context->HdrInfo.SizeOfHeaders,
      Context->FileAlignment
      );

    assert (SectionPadding <= *BufferSize);

    *BufferSize -= SectionPadding;
    *Buffer     += SectionPadding;

    switch (Segment->Type) {
      case ToolImageSectionTypeCode:
        Context->PeHdr->BaseOfCode = MIN(
          Context->PeHdr->BaseOfCode,
          Segment->ImageAddress
          );
        Context->PeHdr->SizeOfCode += Segment->ImageSize;
        break;
      case ToolImageSectionTypeInitialisedData:
        Context->PeHdr->SizeOfInitializedData += Segment->ImageSize;
        break;
      case ToolImageSectionTypeUninitialisedData:
        Context->PeHdr->SizeOfUninitializedData += Segment->ImageSize;
        break;
      default:
        assert (false);
        break;
    }
  }

  assert (SectionsSize == Context->SectionsSize);

  return true;
}

static
bool
ToolImageEmitPeRelocTable (
  const image_tool_pe_emit_context_t *Context,
  uint8_t                            **Buffer,
  uint32_t                           *BufferSize
  )
{
  const image_tool_image_info_t   *Image;
  uint32_t                        RelocTableSize;
  EFI_IMAGE_BASE_RELOCATION_BLOCK *RelocBlock;
  uint32_t                        BlockAddress;
  uint32_t                        BlockNumRelocs;
  uint32_t                        Index;
  uint32_t                        RelocAddress;
  uint32_t                        RelocTablePadding;

  assert (Context    != NULL);
  assert (Buffer     != NULL);
  assert (BufferSize != NULL);

  if (Context->RelocTableSize == 0) {
    return true;
  }

  Image = Context->Image;

  assert (Image->RelocInfo.NumRelocs > 0);
  assert (Image->RelocInfo.NumRelocs <= MAX_UINT32);

  assert (sizeof (EFI_IMAGE_BASE_RELOCATION_BLOCK) <= *BufferSize);

  RelocTableSize = 0;
  RelocBlock     = (void *) *Buffer;
  BlockAddress   = PAGE(Image->RelocInfo.Relocs[0].Target);
  BlockNumRelocs = 0;

  RelocBlock->VirtualAddress = BlockAddress;
  RelocBlock->SizeOfBlock    = sizeof (*RelocBlock);

  for (Index = 0; Index < Image->RelocInfo.NumRelocs; ++Index) {
    RelocAddress = PAGE(Image->RelocInfo.Relocs[Index].Target);
    if (RelocAddress != BlockAddress) {
      RelocBlock->SizeOfBlock = ALIGN_VALUE(RelocBlock->SizeOfBlock, 4);

      assert (RelocBlock->SizeOfBlock <= *BufferSize);

      *BufferSize    -= RelocBlock->SizeOfBlock;
      *Buffer        += RelocBlock->SizeOfBlock;
      RelocTableSize += RelocBlock->SizeOfBlock;

      RelocBlock = (void *) *Buffer;

      BlockAddress   = RelocAddress;
      BlockNumRelocs = 0;

      RelocBlock->VirtualAddress = BlockAddress;
      RelocBlock->SizeOfBlock    = sizeof (*RelocBlock);
    }

    RelocBlock->SizeOfBlock += sizeof (*RelocBlock->Relocations);

    assert (RelocBlock->SizeOfBlock <= *BufferSize);

    RelocBlock->Relocations[BlockNumRelocs]  = PAGE_OFF(Image->RelocInfo.Relocs[Index].Target);
    RelocBlock->Relocations[BlockNumRelocs] |= Image->RelocInfo.Relocs[Index].Type << 12U;

    ++BlockNumRelocs;
  }

  RelocBlock->SizeOfBlock = ALIGN_VALUE(RelocBlock->SizeOfBlock, 4);

  assert (RelocBlock->SizeOfBlock <= *BufferSize);

  *BufferSize    -= RelocBlock->SizeOfBlock;
  *Buffer        += RelocBlock->SizeOfBlock;
  RelocTableSize += RelocBlock->SizeOfBlock;

  assert (RelocTableSize == Context->RelocTableSize);

  RelocTablePadding = ALIGN_VALUE_ADDEND(
    RelocTableSize,
    Context->FileAlignment
    );

  assert (RelocTablePadding <= *BufferSize);

  *BufferSize -= RelocTablePadding;
  *Buffer     += RelocTablePadding;

  return true;
}

typedef struct {
  EFI_IMAGE_DEBUG_DIRECTORY_ENTRY     CodeViewDirEntry;
  EFI_IMAGE_DEBUG_CODEVIEW_RSDS_ENTRY CodeViewEntry;
  uint8_t                             PdbPath[];
} image_tool_debug_dir_t;

STATIC_ASSERT(
  OFFSET_OF(image_tool_debug_dir_t, PdbPath) == sizeof (image_tool_debug_dir_t),
  "Flexible array aliases padding."
  );

static
bool
ToolImageEmitPeDebugTable (
  const image_tool_pe_emit_context_t *Context,
  uint8_t                            **Buffer,
  uint32_t                           *BufferSize,
  uint32_t                           FileOffset
  )
{
  assert (Context    != NULL);
  assert (Buffer     != NULL);
  assert (BufferSize != NULL);

  return true;
}

static
bool
ToolImageEmitPeHiiTable (
  const image_tool_pe_emit_context_t *Context,
  uint8_t                            **Buffer,
  uint32_t                           *BufferSize
  )
{
  const image_tool_image_info_t *Image;
  uint32_t                      HiiTablePadding;

  assert (Context    != NULL);
  assert (Buffer     != NULL);
  assert (BufferSize != NULL);

  Image = Context->Image;

  if (Context->HiiTableSize == 0) {
    return true;
  }

  assert (Image->HiiInfo.DataSize <= Context->HiiTableSize);
  assert (Context->HiiTableSize <= *BufferSize);

  memmove (*Buffer, Image->HiiInfo.Data, Image->HiiInfo.DataSize);

  *BufferSize -= Context->HiiTableSize;
  *Buffer     += Context->HiiTableSize;

  HiiTablePadding = ALIGN_VALUE_ADDEND(
    Context->HiiTableSize,
    Context->FileAlignment
    );

  assert (HiiTablePadding <= *BufferSize);

  *BufferSize -= HiiTablePadding;
  *Buffer     += HiiTablePadding;

  return true;
}

static
bool
ToolImageEmitPeExtraSections (
  const image_tool_pe_emit_context_t *Context,
  uint8_t                            **Buffer,
  uint32_t                           *BufferSize
  )
{
  uint32_t OldBufferSize;
  bool     Result;

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

  Result = ToolImageEmitPeDebugTable (
    Context,
    Buffer,
    BufferSize,
    OldBufferSize - *BufferSize
    );
  if (!Result) {
    return false;
  }

  assert ((OldBufferSize - *BufferSize) == Context->ExtraSectionsSize);

  return true;
}

void *
ToolImageEmitPe (
  const image_tool_image_info_t *Image,
  uint32_t                      *FileSize
  )
{
  image_tool_pe_emit_context_t Context;
  bool                         Result;
  uint32_t                     AlignedHeaderSize;
  bool                         Overflow;
  uint32_t                     SectionsOffset;
  void                         *FileBuffer;
  uint8_t                      *Buffer;
  uint32_t                     RemainingSize;
  uint32_t                     ExpectedSize;

  assert (Image    != NULL);
  assert (FileSize != NULL);

  memset (&Context, 0, sizeof (Context));

  Context.Image         = Image;
  Context.FileAlignment = Image->SegmentInfo.SegmentAlignment;

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

  Result = ToolImageEmitPeHeaders (&Context, &Buffer, &RemainingSize);
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

  *FileSize = Context.UnsignedFileSize;

  return FileBuffer;
}
