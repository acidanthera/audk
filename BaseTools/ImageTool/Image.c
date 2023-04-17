/** @file
  Copyright (c) 2021, Marvin Häuser. All rights reserved.
  Copyright (c) 2022, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause
**/

#include "ImageTool.h"

static
bool
CheckToolImageSegment (
  const image_tool_segment_info_t *SegmentInfo,
  image_tool_segment_t            *Segment,
  uint32_t                        *PreviousEndAddress
  )
{
  bool Overflow;

  assert (Segment            != NULL);
  assert (PreviousEndAddress != NULL);

  Overflow = BaseOverflowAlignUpU32 (
    Segment->ImageSize,
    SegmentInfo->SegmentAlignment,
    &Segment->ImageSize
    );
  if (Overflow) {
    raise ();
    return false;
  }

  if (Segment->Write && Segment->Execute) {
    raise ();
    return false;
  }
  //
  // Shrink segment.
  //
  if (Segment->ImageSize < Segment->DataSize) {
    Segment->DataSize = Segment->ImageSize;
  }

  // FIXME: Expand prior segment
  if (Segment->ImageAddress != *PreviousEndAddress) {
    raise ();
    return false;
  }

  Overflow = BaseOverflowAddU32 (
    (uint32_t)Segment->ImageAddress,
    Segment->ImageSize,
    PreviousEndAddress
    );
  if (Overflow) {
    raise ();
    return false;
  }

  return true;
}

static
bool
CheckToolImageSegmentInfo (
  const image_tool_segment_info_t *SegmentInfo,
  uint32_t                        *ImageSize
  )
{
  uint32_t Index;
  bool     Result;

  assert (SegmentInfo != NULL);
  assert (ImageSize   != NULL);

  if (!IS_POW2 (SegmentInfo->SegmentAlignment)) {
    raise ();
    return false;
  }

  if (SegmentInfo->NumSegments == 0) {
    raise ();
    return false;
  }

  *ImageSize = (uint32_t)SegmentInfo->Segments[0].ImageAddress;
  for (Index = 0; Index < SegmentInfo->NumSegments; ++Index) {
    Result = CheckToolImageSegment (
      SegmentInfo,
      &SegmentInfo->Segments[Index],
      ImageSize
      );
    if (!Result) {
      raise ();
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
  uint64_t Index;

  assert (SegmentInfo != NULL);

  for (Index = 0; Index < SegmentInfo->NumSegments; ++Index) {
    if ((SegmentInfo->Segments[Index].ImageAddress <= Address)
     && (Address < SegmentInfo->Segments[Index].ImageAddress + SegmentInfo->Segments[Index].ImageSize)) {
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
  const image_tool_segment_t *Segment;

  assert (Image != NULL);
  assert (Reloc != NULL);

  Segment = ImageGetSegmentByAddress (&Image->SegmentInfo, Reloc->Target);
  if (Segment == NULL) {
    raise ();
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
  const image_tool_reloc_info_t *RelocInfo;
  uint32_t                      Index;
  bool                          Result;

  assert (Image != NULL);

  RelocInfo = &Image->RelocInfo;

  if (RelocInfo->RelocsStripped && (RelocInfo->NumRelocs > 0)) {
    raise ();
    return false;
  }

  if (RelocInfo->NumRelocs > (MAX_UINT32 / sizeof (UINT16))) {
    raise ();
    return false;
  }

  for (Index = 0; Index < RelocInfo->NumRelocs; ++Index) {
    Result = CheckToolImageReloc (Image, &RelocInfo->Relocs[Index]);
    if (!Result) {
      raise ();
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
  assert (DebugInfo != NULL);

  if (DebugInfo->SymbolsPath != NULL) {
    // FIXME: UE-only?
    if (DebugInfo->SymbolsPathLen > MAX_UINT8) {
      raise ();
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
  bool     Result;
  uint32_t ImageSize;

  assert (Image != NULL);

  Result = CheckToolImageSegmentInfo (&Image->SegmentInfo, &ImageSize);
  if (!Result) {
    raise ();
    return false;
  }

  Result = CheckToolImageRelocInfo (Image);
  if (!Result) {
    raise ();
    return false;
  }

  Result = CheckToolImageDebugInfo (&Image->DebugInfo);
  if (!Result) {
    raise ();
    return false;
  }

  return true;
}

bool
ImageConvertToXip (
  image_tool_image_info_t *Image
  )
{
  image_tool_segment_info_t *SegmentInfo;
  uint64_t                  Index;
  image_tool_segment_t      *Segment;
  void                      *Data;

  assert (Image != NULL);

  SegmentInfo = &Image->SegmentInfo;

  for (Index = 0; Index < SegmentInfo->NumSegments; ++Index) {
    Segment = &SegmentInfo->Segments[Index];

    assert (Segment->DataSize <= Segment->ImageSize);

    Data = realloc (Segment->Data, Segment->ImageSize);
    if (Data == NULL) {
      return false;
    }

    memset (
      (char *)Data + Segment->DataSize,
      0,
      Segment->ImageSize - Segment->DataSize
      );

    Segment->Data     = Data;
    Segment->DataSize = Segment->ImageSize;
  }

  Image->HeaderInfo.IsXip = true;

  return true;
}

void
ImageShrinkSegmentData (
  const image_tool_image_info_t *Image
  )
{
  uint32_t              Index;
  image_tool_segment_t  *Segment;

  for (Index = 0; Index < Image->SegmentInfo.NumSegments; ++Index) {
    Segment = &Image->SegmentInfo.Segments[Index];
    for (; Segment->DataSize > 0; --Segment->DataSize) {
      if (Segment->Data[Segment->DataSize - 1] != 0) {
        break;
      }
    }
  }
}

void
ToolImageDestruct (
  image_tool_image_info_t *Image
  )
{
  uint8_t Index;

  assert (Image != NULL);

  if (Image->SegmentInfo.Segments != NULL) {
    for (Index = 0; Index < Image->SegmentInfo.NumSegments; ++Index) {
      if (Image->SegmentInfo.Segments[Index].Name != NULL) {
        free (Image->SegmentInfo.Segments[Index].Name);
      }
      if (Image->SegmentInfo.Segments[Index].DataSize != 0) {
        free (Image->SegmentInfo.Segments[Index].Data);
      }
    }

    free (Image->SegmentInfo.Segments);
  }

  if (Image->HiiInfo.Data != NULL) {
    free (Image->HiiInfo.Data);
  }

  if (Image->RelocInfo.Relocs != NULL) {
    free (Image->RelocInfo.Relocs);
  }

  if (Image->DebugInfo.SymbolsPath != NULL) {
    free (Image->DebugInfo.SymbolsPath);
  }

  memset (Image, 0, sizeof (*Image));
}
