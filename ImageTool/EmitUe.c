#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include <assert.h>
#include <string.h>

#include <stdio.h>

#include <Base.h>

#include <IndustryStandard/UeImage.h>

#include <Library/UeImageLib.h>

#include "../MdePkg/Library/BasePeCoffLib2/BaseOverflow.h"

#include "ImageTool.h"

#define PAGE(x)     ((x) & ~(uint64_t) 4095ULL)
#define PAGE_OFF(x) ((x) & 4095U)

typedef struct {
  uint8_t  NumSections;
  uint32_t HeaderSize;
  uint32_t SegmentHeadersSize;
  uint32_t SectionHeadersSize;
} image_tool_emit_ue_hdr_info_t;

typedef struct {
  const image_tool_image_info_t *Image;
  image_tool_emit_ue_hdr_info_t HdrInfo;
  uint32_t                      SegmentsSize;
  uint8_t                       SegmentsEndPadding;
  uint32_t                      SectionsSize;
  uint32_t                      UnsignedFileSize;
  uint32_t                      RelocTableSize;
  uint32_t                      HiiTableSize;
  uint32_t                      DebugTableSize;
} image_tool_ue_emit_context_t;

bool EmitUeCheckToolImageHeaderInfo(image_tool_header_info_t *HeaderInfo)
{
  assert(HeaderInfo != NULL);

  if (HeaderInfo->EntryPointAddress > MAX_UINT32) {
    return false;
  }

  return true;
}

bool EmitUeCheckToolImageSegment(
  image_tool_segment_t *Segment,
  uint32_t             *PreviousEndAddress
  ) {
  assert(Segment != NULL);
  assert(PreviousEndAddress != NULL);

  // FIXME: Add guarantee!
  assert(Segment->DataSize <= Segment->ImageSize);

  if (Segment->ImageAddress != *PreviousEndAddress) {
    return false;
  }

  if (Segment->ImageSize > MAX_UINT32) {
    return false;
  }

  assert(Segment->DataSize <= MAX_UINT32);

  if (IS_ALIGNED(Segment->ImageSize, UE_SEGMENT_ALIGNMENT)) {
    return false;
  }

  bool Overflow = BaseOverflowAddU32(
    Segment->ImageAddress,
    Segment->ImageSize,
    PreviousEndAddress
    );
  if (Overflow) {
    return false;
  }

  if (Segment->Write && Segment->Execute) {
    return false;
  }

  return true;
}

bool EmitUeCheckToolImageSegmentInfo(
  image_tool_segment_info_t *SegmentInfo,
  uint32_t                  *ImageSize
  )
{
  assert(SegmentInfo != NULL);
  assert(ImageSize != NULL);

  if (!IS_POW2(SegmentInfo->SegmentAlignment)) {
    return false;
  }

  if (SegmentInfo->NumSegments == 0) {
    return false;
  }

  if (SegmentInfo->NumSegments > MAX_UINT8) {
    return false;
  }

  *ImageSize = 0;
  for (uint8_t Index = 0; (uint8_t) Index < SegmentInfo->NumSegments; ++Index) {
    bool Result = EmitUeCheckToolImageSegment(
      SegmentInfo->Segments + Index,
      ImageSize
      );
    if (!Result) {
      return false;
    }
  }

  return true;
}

bool EmitUeCheckToolImageReloc(
  image_tool_reloc_t *Reloc,
  uint32_t           ImageSize
  )
{
  assert(Reloc != NULL);
  assert(Reloc->Target < ImageSize);

  return true;
}

bool EmitUeCheckToolImageRelocInfo(
  image_tool_reloc_info_t *RelocInfo,
  uint32_t                ImageSize
  )
{
  assert(RelocInfo != NULL);
  assert(!RelocInfo->RelocsStripped || RelocInfo->NumRelocs == 0);

  if (RelocInfo->NumRelocs > MAX_UINT32 / sizeof(UINT16)) {
    return false;
  }

  for (uint32_t Index = 0; (uint32_t) Index < RelocInfo->NumRelocs; ++Index) {
    bool Result = EmitUeCheckToolImageReloc(
      RelocInfo->Relocs + Index,
      ImageSize
      );
    if (!Result) {
      return false;
    }
  }

  return true;
}

bool EmitUeCheckToolImageHiiInfo(image_tool_hii_info_t *HiiInfo)
{
  assert(HiiInfo != NULL);

  if (HiiInfo->DataSize > MAX_UINT32) {
    return false;
  }

  return true;
}

bool EmitUeCheckToolImageDebugInfo(image_tool_debug_info_t *DebugInfo)
{
  assert(DebugInfo != NULL);

  if (DebugInfo->SymbolsPath != NULL) {
    size_t SymbolsPathLen = strlen(DebugInfo->SymbolsPath);
    if (SymbolsPathLen > MAX_UINT8) {
      return false;
    }
  }

  return true;
}

bool EmitUeCheckToolImage(image_tool_image_info_t *Image)
{
  assert(Image != NULL);

  bool Result;

  Result = EmitUeCheckToolImageHeaderInfo(&Image->HeaderInfo);
  if (!Result) {
    return false;
  }

  uint32_t ImageSize;
  Result = EmitUeCheckToolImageSegmentInfo(&Image->SegmentInfo, &ImageSize);
  if (!Result) {
    return false;
  }

  Result = EmitUeCheckToolImageRelocInfo(&Image->RelocInfo, ImageSize);
  if (!Result) {
    return false;
  }

  Result = EmitUeCheckToolImageHiiInfo(&Image->HiiInfo);
  if (!Result) {
    return false;
  }

  Result = EmitUeCheckToolImageDebugInfo(&Image->DebugInfo);
  if (!Result) {
    return false;
  }

  return true;
}

bool EmitUeGetHeaderSizes(
  const image_tool_image_info_t *Image,
  image_tool_emit_ue_hdr_info_t *HdrInfo
  )
{
  assert(Image != NULL);
  assert(HdrInfo != NULL);

  assert(Image->SegmentInfo.NumSegments <= MAX_UINT8);

  if (Image->RelocInfo.NumRelocs > 0) {
    ++HdrInfo->NumSections;
  }

  if (Image->HiiInfo.DataSize > 0) {
    ++HdrInfo->NumSections;
  }
  //
  // A debug section can always be generated; make conditional based on tool arg.
  //
  ++HdrInfo->NumSections;

  HdrInfo->SegmentHeadersSize = (uint32_t) Image->SegmentInfo.NumSegments * sizeof(UE_SEGMENT);
  HdrInfo->SectionHeadersSize = (uint32_t) HdrInfo->NumSections * sizeof(UE_SECTION);

  HdrInfo->HeaderSize = sizeof(UE_HEADER)
    + HdrInfo->SegmentHeadersSize
    + HdrInfo->SectionHeadersSize;

  return true;
}

bool EmitUeGetSegmentsSize(image_tool_image_info_t *Image, uint32_t *SegmentsSize) {
  assert(Image != NULL);
  assert(SegmentsSize != NULL);

  *SegmentsSize = 0;
  for (uint8_t Index = 0; (uint8_t) Index < Image->SegmentInfo.NumSegments; ++Index) {
    *SegmentsSize += Image->SegmentInfo.Segments[Index].DataSize;
  }

  return true;
}

bool EmitUeGetRelocSectionSize(image_tool_image_info_t *Image, uint32_t *RelocsSize)
{
  assert(Image != NULL);
  assert(RelocsSize != NULL);

  if (Image->RelocInfo.NumRelocs == 0) {
    *RelocsSize = 0;
    return true;
  }

  assert(Image->RelocInfo.NumRelocs <= MAX_UINT32);

  uint32_t RelocTableSize = 0;

  uint32_t BlockAddress = (uint32_t) PAGE(Image->RelocInfo.Relocs[0].Target);
  uint32_t BlockSize    = sizeof(UE_RELOCATION_BLOCK);

  for (uint32_t Index = 0; Index < (uint32_t) Image->RelocInfo.NumRelocs; ++Index) {
    uint32_t RelocAddress = PAGE(Image->RelocInfo.Relocs[Index].Target);
    if (RelocAddress != BlockAddress) {
      BlockSize = ALIGN_VALUE(BlockSize, UE_RELOCATION_BLOCK_ALIGNMENT);

      RelocTableSize += BlockSize;

      BlockAddress   = RelocAddress;
      BlockSize      = sizeof(UE_RELOCATION_BLOCK);
    }

    BlockSize += sizeof(UINT16);
  }

  RelocTableSize += BlockSize;

  return !BaseOverflowAlignUpU32(
    RelocTableSize,
    UE_SECTION_ALIGNMENT,
    RelocsSize
    );
}

bool EmitUeGetHiiSectionSize(image_tool_image_info_t *Image, uint32_t *HiiSize)
{
  assert(Image != NULL);
  assert(HiiSize != NULL);

  return !BaseOverflowAlignUpU32(
    Image->HiiInfo.DataSize,
    UE_SECTION_ALIGNMENT,
    HiiSize
    );
}

bool EmitUeGetDebugSectionSize(image_tool_image_info_t *Image, uint32_t *DebugSize)
{
  assert(Image != NULL);
  assert(DebugSize != NULL);

  static_assert(
    MAX_UINT8 <= (MAX_UINT32 - MAX_UINT8 - sizeof(UE_DEBUG_TABLE)) / sizeof(UE_SEGMENT_NAME),
    "The following arithmetics may overflow."
    );

  *DebugSize = sizeof(UE_DEBUG_TABLE) + Image->SegmentInfo.NumSegments * sizeof(UE_SEGMENT_NAME);

  if (Image->DebugInfo.SymbolsPath != NULL) {
    size_t SymbolsPathLen = strlen(Image->DebugInfo.SymbolsPath);
    assert(SymbolsPathLen <= MAX_UINT8);
    *DebugSize += SymbolsPathLen;
  }

  return !BaseOverflowAlignUpU32(
    *DebugSize,
    UE_SECTION_ALIGNMENT,
    DebugSize
    );
}

bool EmitUeGetSectionsSize(image_tool_ue_emit_context_t *Context, uint32_t *SectionsSize)
{
  assert(Context != NULL);
  assert(SectionsSize != NULL);

  image_tool_image_info_t *Image = (image_tool_image_info_t *) Context->Image;

  bool Result = EmitUeGetRelocSectionSize(Image, &Context->RelocTableSize);
  if (!Result) {
    raise();
    return false;
  }

  assert(IS_ALIGNED(Context->RelocTableSize, UE_SECTION_ALIGNMENT));

  Result = EmitUeGetDebugSectionSize(Image, &Context->DebugTableSize);
  if (!Result) {
    raise();
    return false;
  }

  assert(IS_ALIGNED(Context->DebugTableSize, UE_SECTION_ALIGNMENT));

  Result = EmitUeGetHiiSectionSize(Image, &Context->HiiTableSize);
  if (!Result) {
    raise();
    return false;
  }

  assert(IS_ALIGNED(Context->HiiTableSize, UE_SECTION_ALIGNMENT));

  bool Overflow = BaseOverflowAddU32(
    Context->RelocTableSize,
    Context->DebugTableSize,
    SectionsSize
    );
  if (Overflow) {
    raise();
    return false;
  }

  assert(IS_ALIGNED (*SectionsSize, UE_SECTION_ALIGNMENT));

  Overflow = BaseOverflowAddU32(
    *SectionsSize,
    Context->HiiTableSize,
    SectionsSize
    );
  if (Overflow) {
    raise();
    return false;
  }

  assert(IS_ALIGNED(*SectionsSize, UE_SECTION_ALIGNMENT));

  return true;
}

uint8_t AlignmentToExponent(uint64_t Alignment)
{
  assert(IS_POW2(Alignment));

  for (uint8_t Index = 0; Index < 64; ++Index) {
    if ((Alignment & (1U << Index)) == Alignment) {
      return Index;
    }
  }

  return 0;
}

bool ToolImageEmitUeSegmentHeaders (
  const image_tool_ue_emit_context_t *Context,
  unsigned char                      **Buffer,
  uint32_t                           *BufferSize
  )
{
  assert(Context != NULL);
  assert(Buffer != NULL);
  assert(BufferSize != NULL);

  const image_tool_image_info_t *Image = Context->Image;

  assert(Image->SegmentInfo.NumSegments <= MAX_UINT8);

  uint16_t SegmentHeadersSize = (uint16_t) (Image->SegmentInfo.NumSegments * sizeof (UE_SEGMENT));
  assert(SegmentHeadersSize <= *BufferSize);

  UE_SEGMENT *Segments = (void *) *Buffer;

  for (uint8_t Index = 0; Index < (uint8_t) Image->SegmentInfo.NumSegments; ++Index) {
    // FIXME:
    Image->SegmentInfo.Segments[Index].ImageSize = ALIGN_VALUE(Image->SegmentInfo.Segments[Index].ImageSize, Image->SegmentInfo.SegmentAlignment);

    Segments[Index].ImageInfo = Image->SegmentInfo.Segments[Index].ImageSize;

    if (!Image->SegmentInfo.Segments[Index].Read) {
      Segments[Index].ImageInfo |= UE_SEGMENT_INFO_RP;
    }

    if (!Image->SegmentInfo.Segments[Index].Write) {
      Segments[Index].ImageInfo |= UE_SEGMENT_INFO_RO;
    }

    if (!Image->SegmentInfo.Segments[Index].Execute) {
      Segments[Index].ImageInfo |= UE_SEGMENT_INFO_XP;
    }

    assert(UE_SEGMENT_SIZE(Segments[Index].ImageInfo) == Image->SegmentInfo.Segments[Index].ImageSize);

    Segments[Index].FileSize = Image->SegmentInfo.Segments[Index].DataSize;
  }

  *BufferSize -= SegmentHeadersSize;
  *Buffer     += SegmentHeadersSize;

  assert(SegmentHeadersSize == Context->HdrInfo.SegmentHeadersSize);

  return true;
}

bool ToolImageEmitUeSectionHeaders (
  const image_tool_ue_emit_context_t *Context,
  unsigned char                      **Buffer,
  uint32_t                           *BufferSize
  )
{
  assert(Context != NULL);
  assert(Buffer != NULL);
  assert(BufferSize != NULL);

  uint32_t SectionHeadersSize = 0;

  if (Context->RelocTableSize > 0) {
    assert(sizeof(UE_SECTION) <= *BufferSize);

    UE_SECTION *Section = (void *) *Buffer;

    Section->FileInfo  = Context->RelocTableSize;
    Section->FileInfo |= UeSectionIdRelocTable;
    assert(UE_SECTION_ID(Section->FileInfo) == UeSectionIdRelocTable);
    assert(UE_SECTION_SIZE(Section->FileInfo) == Context->RelocTableSize);

    *BufferSize        -= sizeof(UE_SECTION);
    *Buffer            += sizeof(UE_SECTION);
    SectionHeadersSize += sizeof(UE_SECTION);
  }

  if (Context->DebugTableSize > 0) {
    assert(sizeof(UE_SECTION) <= *BufferSize);

    UE_SECTION *Section = (void *) *Buffer;

    Section->FileInfo  = Context->DebugTableSize;
    Section->FileInfo |= UeSectionIdDebugTable;
    assert(UE_SECTION_ID(Section->FileInfo) == UeSectionIdDebugTable);
    assert(UE_SECTION_SIZE(Section->FileInfo) == Context->DebugTableSize);

    *BufferSize        -= sizeof(UE_SECTION);
    *Buffer            += sizeof(UE_SECTION);
    SectionHeadersSize += sizeof(UE_SECTION);
  }

  if (Context->HiiTableSize > 0) {
    assert(sizeof(UE_SECTION) <= *BufferSize);

    UE_SECTION *Section = (void *) *Buffer;

    Section->FileInfo  = Context->HiiTableSize;
    Section->FileInfo |= UeSectionIdHiiTable;
    assert(UE_SECTION_ID(Section->FileInfo) == UeSectionIdHiiTable);
    assert(UE_SECTION_SIZE(Section->FileInfo) == Context->HiiTableSize);

    *BufferSize        -= sizeof(UE_SECTION);
    *Buffer            += sizeof(UE_SECTION);
    SectionHeadersSize += sizeof(UE_SECTION);
  }

  assert(Context->HdrInfo.SectionHeadersSize == SectionHeadersSize);

  return true;
}

bool ToolImageEmitUeHeader (
  const image_tool_ue_emit_context_t *Context,
  unsigned char                      **Buffer,
  uint32_t                           *BufferSize
  )
{
  assert(Context != NULL);
  assert(Buffer != NULL);
  assert(BufferSize != NULL);

  assert(sizeof(UE_HEADER) <= *BufferSize);

  UE_HEADER *UeHdr = (void *) *Buffer;

  UeHdr->Signature = UE_HEADER_SIGNATURE;

  const image_tool_image_info_t *Image = Context->Image;

  uint8_t AlignmentExponent = AlignmentToExponent(
    Image->SegmentInfo.SegmentAlignment
    );
  UeHdr->ImageInfo = AlignmentExponent;

  if (Image->RelocInfo.RelocsStripped) {
    UeHdr->ImageInfo |= UE_HEADER_FLAG_RELOCS_STRIPPED;
  }

  assert(UE_HEADER_ALIGNMENT(UeHdr->ImageInfo) == 1U << AlignmentExponent);

  assert(0 < Image->SegmentInfo.NumSegments);
  UeHdr->LastSegmentIndex  = (UINT8) (Image->SegmentInfo.NumSegments - 1);
  UeHdr->NumSections       = Context->HdrInfo.NumSections;
  UeHdr->Subsystem         = Image->HeaderInfo.Subsystem;
  UeHdr->Machine           = Image->HeaderInfo.Machine;
  UeHdr->PreferredAddress  = Image->HeaderInfo.PreferredAddress;
  UeHdr->EntryPointAddress = Image->HeaderInfo.EntryPointAddress;
  UeHdr->ImageInfo2        = Context->UnsignedFileSize;
  assert(UeHdr->ImageInfo2 == UE_HEADER_UNSIGNED_SIZE(UeHdr->ImageInfo2));

  assert(UeHdr->Reserved == 0);

  *BufferSize -= sizeof(UE_HEADER);
  *Buffer     += sizeof(UE_HEADER);

  bool Result = ToolImageEmitUeSegmentHeaders(Context, Buffer, BufferSize);
  if (!Result) {
    return false;
  }

  Result = ToolImageEmitUeSectionHeaders(Context, Buffer, BufferSize);
  if (!Result) {
    return false;
  }

  return true;
}

bool ToolImageEmitUeSegments (
  const image_tool_ue_emit_context_t *Context,
  unsigned char                      **Buffer,
  uint32_t                           *BufferSize
  )
{
  assert(Context != NULL);
  assert(Buffer != NULL);
  assert(BufferSize != NULL);

  const image_tool_image_info_t *Image = Context->Image;

  uint32_t SegmentsSize = 0;

  assert(Image->SegmentInfo.NumSegments <= MAX_UINT8);

  for (uint8_t Index = 0; Index < (uint8_t) Image->SegmentInfo.NumSegments; ++Index) {
    assert(Image->SegmentInfo.Segments[Index].DataSize <= *BufferSize);

    size_t DataSize = Image->SegmentInfo.Segments[Index].DataSize;

    memcpy(*Buffer, Image->SegmentInfo.Segments[Index].Data, DataSize);

    *BufferSize  -= DataSize;
    *Buffer      += DataSize;
    SegmentsSize += DataSize;
  }

  assert(SegmentsSize == Context->SegmentsSize);

  *BufferSize  -= Context->SegmentsEndPadding;
  *Buffer      += Context->SegmentsEndPadding;

  return true;
}

bool ToolImageEmitUeRelocTable (
  const image_tool_ue_emit_context_t *Context,
  unsigned char                      **Buffer,
  uint32_t                           *BufferSize
  )
{
  assert(Context != NULL);
  assert(Buffer != NULL);
  assert(BufferSize != NULL);

  if (Context->RelocTableSize == 0) {
    return true;
  }

  const image_tool_image_info_t *Image = Context->Image;

  assert(Image->RelocInfo.NumRelocs > 0);
  assert(Image->RelocInfo.NumRelocs <= MAX_UINT32);

  assert(sizeof(UE_RELOCATION_BLOCK) <= *BufferSize);

  uint32_t RelocTableSize = 0;

  UE_RELOCATION_BLOCK *RelocBlock = (void *) *Buffer;

  uint32_t BlockAddress   = (uint32_t) PAGE(Image->RelocInfo.Relocs[0].Target);
  uint32_t BlockNumRelocs = 0;
  uint32_t BlockSize      = sizeof(*RelocBlock);

  RelocBlock->BlockInfo = BlockAddress;

  for (uint32_t Index = 0; Index < (uint32_t) Image->RelocInfo.NumRelocs; ++Index) {
    uint32_t RelocAddress = PAGE(Image->RelocInfo.Relocs[Index].Target);
    if (RelocAddress != BlockAddress) {
      BlockSize = ALIGN_VALUE(BlockSize, UE_RELOCATION_BLOCK_ALIGNMENT);
      assert(BlockSize <= *BufferSize);

      *BufferSize    -= BlockSize;
      *Buffer        += BlockSize;
      RelocTableSize += BlockSize;

      RelocBlock = (void *) *Buffer;

      BlockAddress   = RelocAddress;
      BlockNumRelocs = 0;
      BlockSize      = sizeof(*RelocBlock);

      RelocBlock->BlockInfo = BlockAddress;
    }

    BlockSize += sizeof(*RelocBlock->RelocInfo);
    assert(BlockSize <= *BufferSize);

    RelocBlock->RelocInfo[BlockNumRelocs]  = PAGE_OFF(Image->RelocInfo.Relocs[Index].Target);
    RelocBlock->RelocInfo[BlockNumRelocs] |= Image->RelocInfo.Relocs[Index].Type << 12U;
    assert(UE_RELOC_OFFSET(RelocBlock->RelocInfo[BlockNumRelocs]) == PAGE_OFF(Image->RelocInfo.Relocs[Index].Target));
    assert(UE_RELOC_TYPE(RelocBlock->RelocInfo[BlockNumRelocs]) == Image->RelocInfo.Relocs[Index].Type);

    ++BlockNumRelocs;
    if (BlockNumRelocs > UE_RELOCATION_BLOCK_MAX_RELOCS) {
      return false;
    }

    ++RelocBlock->BlockInfo;
    assert(BlockNumRelocs == UE_RELOC_BLOCK_NUM(RelocBlock->BlockInfo));
    assert(BlockAddress == UE_RELOC_BLOCK_ADDRESS(RelocBlock->BlockInfo));
  }

  *BufferSize    -= BlockSize;
  *Buffer        += BlockSize;
  RelocTableSize += BlockSize;

  uint32_t RelocTablePadding = ALIGN_VALUE_ADDEND(
    RelocTableSize,
    UE_SECTION_ALIGNMENT
    );

  assert(RelocTablePadding <= *BufferSize);

  *BufferSize    -= RelocTablePadding;
  *Buffer        += RelocTablePadding;
  RelocTableSize += RelocTablePadding;

  assert(RelocTableSize == Context->RelocTableSize);

  return true;
}

bool ToolImageEmitDebugTable (
  const image_tool_ue_emit_context_t *Context,
  unsigned char                      **Buffer,
  uint32_t                           *BufferSize
  )
{
  assert(Context != NULL);
  assert(Buffer != NULL);
  assert(BufferSize != NULL);

  assert(sizeof(UE_DEBUG_TABLE) <= *BufferSize);

  uint32_t DebugTableSize = sizeof(UE_DEBUG_TABLE);

  UE_DEBUG_TABLE *DebugTable = (void *) *Buffer;

  assert(DebugTable->SymbolsBaseOffset == 0);
  assert(DebugTable->Reserved == 0);

  const image_tool_image_info_t *Image = Context->Image;

  *BufferSize -= sizeof(UE_DEBUG_TABLE);
  *Buffer     += sizeof(UE_DEBUG_TABLE);

  if (Image->DebugInfo.SymbolsPath != NULL) {
    size_t SymbolsPathSize = strlen(Image->DebugInfo.SymbolsPath);
    assert(SymbolsPathSize <= MAX_UINT8);
    DebugTable->SymbolsPathSize = (uint8_t) SymbolsPathSize;

    assert(SymbolsPathSize <= *BufferSize);

    DebugTableSize += SymbolsPathSize;

    memcpy(*Buffer, Image->DebugInfo.SymbolsPath, SymbolsPathSize);

    *BufferSize -= SymbolsPathSize;
    *Buffer     += SymbolsPathSize;
  } else {
    assert(DebugTable->SymbolsPathSize == 0);
  }

  for (uint8_t Index = 0; Index < (uint8_t) Image->SegmentInfo.NumSegments; ++Index) {
    assert(sizeof(UE_SEGMENT_NAME) <= *BufferSize);

    DebugTableSize += sizeof(UE_SEGMENT_NAME);

    UE_SEGMENT_NAME *SectionName = (void *) *Buffer;

    strncpy(
      (char *) SectionName,
      Image->SegmentInfo.Segments[Index].Name,
      sizeof(*SectionName)
      );

    *BufferSize -= sizeof(*SectionName);
    *Buffer     += sizeof(*SectionName);
  }

  uint32_t DebugTablePadding = ALIGN_VALUE_ADDEND(
    DebugTableSize,
    UE_SECTION_ALIGNMENT
    );

  assert(DebugTablePadding <= *BufferSize);

  *BufferSize -= DebugTablePadding;
  *Buffer     += DebugTablePadding;

  DebugTableSize = DebugTableSize + DebugTablePadding;

  assert(DebugTableSize == Context->DebugTableSize);

  return true;
}

bool ToolImageEmitHiiTable (
  const image_tool_ue_emit_context_t *Context,
  unsigned char                      **Buffer,
  uint32_t                           *BufferSize
  )
{
  assert(Context != NULL);
  assert(Buffer != NULL);
  assert(BufferSize != NULL);

  const image_tool_image_info_t *Image = Context->Image;

  if (Context->HiiTableSize == 0) {
    return true;
  }

  assert(Image->HiiInfo.DataSize <= Context->HiiTableSize);
  assert(IS_ALIGNED(Context->HiiTableSize, UE_SECTION_ALIGNMENT));
  assert(Context->HiiTableSize <= *BufferSize);

  memcpy(*Buffer, Image->HiiInfo.Data, Image->HiiInfo.DataSize);

  *BufferSize -= Context->HiiTableSize;
  *Buffer     += Context->HiiTableSize;

  return true;
}

bool ToolImageEmitUeSections (
  const image_tool_ue_emit_context_t *Context,
  unsigned char                      **Buffer,
  uint32_t                           *BufferSize
  )
{
  assert(Context != NULL);
  assert(Buffer != NULL);
  assert(BufferSize != NULL);

  uint32_t ExpectedSize = *BufferSize;

  bool Result = ToolImageEmitUeRelocTable(Context, Buffer, BufferSize);
  if (!Result) {
    return false;
  }

  ExpectedSize -= Context->RelocTableSize;
  assert(ExpectedSize == *BufferSize);

  Result = ToolImageEmitDebugTable(Context, Buffer, BufferSize);
  if (!Result) {
    return false;
  }

  ExpectedSize -= Context->DebugTableSize;
  assert(ExpectedSize == *BufferSize);

  Result = ToolImageEmitHiiTable(Context, Buffer, BufferSize);
  if (!Result) {
    return false;
  }

  ExpectedSize -= Context->HiiTableSize;
  assert(ExpectedSize == *BufferSize);

  return true;
}

void *ToolImageEmitUe(image_tool_image_info_t *Image, uint32_t *FileSize)
{
  assert(Image != NULL);
  assert(FileSize != NULL);

  image_tool_ue_emit_context_t Context;
  memset(&Context, 0, sizeof(Context));

  Context.Image = Image;

  bool Result = EmitUeGetHeaderSizes(Image, &Context.HdrInfo);
  if (!Result) {
    raise();
    return NULL;
  }

  Result = EmitUeGetSegmentsSize(Image, &Context.SegmentsSize);
  if (!Result) {
    raise();
    return NULL;
  }

  uint32_t SectionsOffset;
  bool Overflow = BaseOverflowAddU32(
    Context.HdrInfo.HeaderSize,
    Context.SegmentsSize,
    &SectionsOffset
    );
  if (Overflow) {
    raise();
    return NULL;
  }

  Context.SegmentsEndPadding = ALIGN_VALUE_ADDEND(
    SectionsOffset,
    UE_SECTION_ALIGNMENT
    );

  Overflow = BaseOverflowAddU32(
    SectionsOffset,
    Context.SegmentsEndPadding,
    &SectionsOffset
    );
  if (Overflow) {
    raise();
    return NULL;
  }

  Result = EmitUeGetSectionsSize(&Context, &Context.SectionsSize);
  if (!Result) {
    raise();
    return NULL;
  }

  assert(IS_ALIGNED(Context.SectionsSize, UE_SECTION_ALIGNMENT));

  Overflow = BaseOverflowAddU32(
    SectionsOffset,
    Context.SectionsSize,
    &Context.UnsignedFileSize
    );
  if (Overflow) {
    raise();
    return NULL;
  }

  assert(IS_ALIGNED(Context.UnsignedFileSize, UE_SECTION_ALIGNMENT));

  void *FileBuffer = calloc(1, Context.UnsignedFileSize);
  if (FileBuffer == NULL) {
    raise();
    return NULL;
  }

  unsigned char *Buffer = FileBuffer;
  uint32_t RemainingSize = Context.UnsignedFileSize;

  uint32_t ExpectedSize = Context.UnsignedFileSize;

  Result = ToolImageEmitUeHeader(
    &Context,
    &Buffer,
    &RemainingSize
    );
  if (!Result) {
    raise();
    free(FileBuffer);
    return NULL;
  }

  ExpectedSize -= Context.HdrInfo.HeaderSize;

  assert(RemainingSize == ExpectedSize);

  Result = ToolImageEmitUeSegments(
    &Context,
    &Buffer,
    &RemainingSize
    );
  if (!Result) {
    raise();
    free(FileBuffer);
    return NULL;
  }

  ExpectedSize -= Context.SegmentsSize + Context.SegmentsEndPadding;

  assert(RemainingSize == ExpectedSize);

  Result = ToolImageEmitUeSections(
    &Context,
    &Buffer,
    &RemainingSize
    );
  if (!Result) {
    raise();
    free(FileBuffer);
    return NULL;
  }

  ExpectedSize -= Context.SectionsSize;

  assert(RemainingSize == ExpectedSize);

  assert(RemainingSize == 0);

  *FileSize = Context.UnsignedFileSize;

  return FileBuffer;
}
