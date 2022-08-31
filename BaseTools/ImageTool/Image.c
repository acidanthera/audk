#include "ImageTool.h"

static
bool
CheckToolImageSegment (
  image_tool_segment_info_t *SegmentInfo,
  image_tool_segment_t      *Segment,
  uint32_t                  *PreviousEndAddress
  )
{
  assert(Segment != NULL);
  assert(PreviousEndAddress != NULL);

  bool Overflow = BaseOverflowAlignUpU32(
    Segment->ImageSize,
    SegmentInfo->SegmentAlignment,
    &Segment->ImageSize
    );
  if (Overflow) {
    raise();
    return false;
  }

  if (Segment->Write && Segment->Execute) {
    raise();
    return false;
  }
  //
  // Shrink segment.
  //
  if (Segment->ImageSize < Segment->DataSize) {
    Segment->DataSize = Segment->ImageSize;
  }

  for (; Segment->DataSize > 0; --Segment->DataSize) {
    if (Segment->Data[Segment->DataSize - 1] != 0) {
      break;
    }
  }
  // FIXME: Expand prior segment
  if (Segment->ImageAddress != *PreviousEndAddress) {
    raise();
    return false;
  }

  Overflow = BaseOverflowAddU32(
    Segment->ImageAddress,
    Segment->ImageSize,
    PreviousEndAddress
    );
  if (Overflow) {
    raise();
    return false;
  }

  return true;
}

static
bool
CheckToolImageSegmentInfo (
  image_tool_segment_info_t *SegmentInfo,
  uint32_t                  *ImageSize
  )
{
  assert(SegmentInfo != NULL);
  assert(ImageSize != NULL);

  if (!IS_POW2(SegmentInfo->SegmentAlignment)) {
    raise();
    return false;
  }

  if (SegmentInfo->NumSegments == 0) {
    raise();
    return false;
  }

  *ImageSize = SegmentInfo->Segments[0].ImageAddress;
  for (uint64_t Index = 0; Index < SegmentInfo->NumSegments; ++Index) {
    bool Result = CheckToolImageSegment(
      SegmentInfo,
      &SegmentInfo->Segments[Index],
      ImageSize
      );
    if (!Result) {
      raise();
      return false;
    }
  }

  return true;
}

static
const image_tool_segment_t *
ImageGetSegmentByAddress (
  const image_tool_segment_info_t *SegmentInfo,
  uint64_t                        Address
  )
{
  assert(SegmentInfo != NULL);

  for (uint64_t Index = 0; Index < SegmentInfo->NumSegments; ++Index) {
    if (SegmentInfo->Segments[Index].ImageAddress <= Address
     && Address < SegmentInfo->Segments[Index].ImageAddress + SegmentInfo->Segments[Index].ImageSize) {
      return &SegmentInfo->Segments[Index];
    }
  }

  return NULL;
}

static
bool
CheckToolImageReloc (
  const image_tool_image_info_t *Image,
  const image_tool_reloc_t      *Reloc
  )
{
  assert(Image != NULL);
  assert(Reloc != NULL);

  const image_tool_segment_t *Segment = ImageGetSegmentByAddress(
    &Image->SegmentInfo,
    Reloc->Target
    );
  if (Segment == NULL) {
    raise();
    return false;
  }

  /*if (Segment->Write) {
    printf("!!! writable reloc at %x !!!\n", Reloc->Target);
  }*/

  return true;
}

static
bool
CheckToolImageRelocInfo (
  const image_tool_image_info_t *Image
  )
{
  assert(Image != NULL);

  const image_tool_reloc_info_t *RelocInfo = &Image->RelocInfo;

  if (RelocInfo->RelocsStripped && RelocInfo->NumRelocs > 0) {
    raise();
    return false;
  }

  if (RelocInfo->NumRelocs > MAX_UINT32 / sizeof(UINT16)) {
    raise();
    return false;
  }

  for (uint32_t Index = 0; (uint32_t) Index < RelocInfo->NumRelocs; ++Index) {
    bool Result = CheckToolImageReloc(Image, &RelocInfo->Relocs[Index]);
    if (!Result) {
      raise();
      return false;
    }
  }

  return true;
}

static
bool
CheckToolImageDebugInfo (
  image_tool_debug_info_t *DebugInfo
  )
{
  assert(DebugInfo != NULL);

  if (DebugInfo->SymbolsPath != NULL) {
    // FIXME: UE-only?
    if (DebugInfo->SymbolsPathLen > MAX_UINT8) {
      raise();
      return false;
    }
  }

  return true;
}

bool
CheckToolImage (
  image_tool_image_info_t *Image
  )
{
  assert(Image != NULL);

  bool Result;

  uint32_t ImageSize;
  Result = CheckToolImageSegmentInfo(&Image->SegmentInfo, &ImageSize);
  if (!Result) {
    raise();
    return false;
  }

  Result = CheckToolImageRelocInfo(Image);
  if (!Result) {
    raise();
    return false;
  }

  Result = CheckToolImageDebugInfo(&Image->DebugInfo);
  if (!Result) {
    raise();
    return false;
  }

  return true;
}

bool
ImageConvertToXip (
  image_tool_image_info_t *Image
  )
{
  assert(Image != NULL);

  image_tool_segment_info_t *SegmentInfo = &Image->SegmentInfo;

  for (uint64_t Index = 0; Index < SegmentInfo->NumSegments; ++Index) {
    image_tool_segment_t *Segment = &SegmentInfo->Segments[Index];
    assert(Segment->DataSize <= Segment->ImageSize);

    if (Segment->DataSize == 0) {
      continue;
    }

    void *Data = calloc(Segment->ImageSize, 1);
    if (Data == NULL) {
      raise();
      return false;
    }

    memmove(Data, Segment->Data, Segment->DataSize);

    void *Memory = Segment->Data;

    Segment->Data     = Data;
    Segment->DataSize = Segment->ImageSize;

    free(Memory);
  }

  Image->HeaderInfo.IsXip = true;

  return true;
}

void
ToolImageDestruct (
  image_tool_image_info_t *Image
  )
{
  assert(Image != NULL);

  for (uint8_t Index = 0; Index < Image->SegmentInfo.NumSegments; ++Index) {
    free(Image->SegmentInfo.Segments[Index].Name);
    if (Image->SegmentInfo.Segments[Index].DataSize != 0) {
      free(Image->SegmentInfo.Segments[Index].Data);
    }
  }

  free(Image->SegmentInfo.Segments);

  if (Image->HiiInfo.Data != NULL) {
    free (Image->HiiInfo.Data);
  }

  if (Image->RelocInfo.Relocs != NULL) {
    free (Image->RelocInfo.Relocs);
  }

  free(Image->DebugInfo.SymbolsPath);

  memset(Image, 0, sizeof(*Image));
}
