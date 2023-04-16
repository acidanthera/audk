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
  const image_tool_segment_t      *Segment,
  uint32_t                        *PreviousEndAddress
  )
{
  bool Overflow;

  assert (Segment            != NULL);
  assert (PreviousEndAddress != NULL);

  if (!IS_ALIGNED (Segment->ImageSize, SegmentInfo->SegmentAlignment)) {
    raise ();
    return false;
  }

  if (Segment->Write && Segment->Execute) {
    raise ();
    return false;
  }

  if (Segment->ImageSize < Segment->DataSize) {
    raise ();
    return false;
  }

  // FIXME: Expand prior segment
  if (Segment->ImageAddress != *PreviousEndAddress) {
    raise ();
    return false;
  }

  Overflow = BaseOverflowAddU32 (
    Segment->ImageAddress,
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

  if (!IS_ALIGNED (SegmentInfo->Segments[0].ImageAddress, SegmentInfo->SegmentAlignment)) {
    raise ();
    return false;
  }

  *ImageSize = SegmentInfo->Segments[0].ImageAddress;
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
  uint32_t                        *Address,
  uint32_t                        *RemainingSize,
  const image_tool_segment_info_t *SegmentInfo
  )
{
  uint32_t Index;

  assert (Address != NULL);
  assert (SegmentInfo != NULL);

  for (Index = 0; Index < SegmentInfo->NumSegments; ++Index) {
    if ((SegmentInfo->Segments[Index].ImageAddress <= *Address)
     && (*Address < SegmentInfo->Segments[Index].ImageAddress + SegmentInfo->Segments[Index].ImageSize)) {
      *Address      -= SegmentInfo->Segments[Index].ImageAddress;
      *RemainingSize = SegmentInfo->Segments[Index].ImageSize - *Address;
      return &SegmentInfo->Segments[Index];
    }
  }

  return NULL;
}

static
bool
CheckToolImageReloc (
  const image_tool_image_info_t *Image,
  uint32_t                      ImageSize,
  const image_tool_reloc_t      *Reloc
  )
{
  uint32_t                   RelocOffset;
  uint32_t                   RemainingSize;
  const image_tool_segment_t *Segment;
  uint16_t                   MovHigh;
  uint16_t                   MovLow;

  assert (Image != NULL);
  assert (Reloc != NULL);

  RelocOffset = Reloc->Target;
  Segment     = ImageGetSegmentByAddress (
                  &RelocOffset,
                  &RemainingSize,
                  &Image->SegmentInfo
                  );
  if (Segment == NULL) {
    raise ();
    return false;
  }

  switch (Reloc->Type) {
    case EFI_IMAGE_REL_BASED_HIGHLOW:
    {
      if (RemainingSize < sizeof (UINT32)) {
        raise ();
        return false;
      }

      break;
    }

    case EFI_IMAGE_REL_BASED_DIR64:
    {
      if (RemainingSize < sizeof (UINT64)) {
        raise ();
        return false;
      }

      break;
    }
    
    case EFI_IMAGE_REL_BASED_ARM_MOV32T:
    {
      if (RemainingSize < sizeof (UINT32)) {
        raise ();
        return false;
      }

      if (!IS_ALIGNED (Reloc->Target, ALIGNOF (UINT16))) {
        raise ();
        return false;
      }

      MovHigh = *(const uint16_t *)&Segment->Data[RelocOffset];
      MovLow  = *(const uint16_t *)&Segment->Data[RelocOffset + 2];
      if (((MovHigh & 0xFBF0U) != 0xF200U && (MovHigh & 0xFBF0U) != 0xF2C0U) ||
        (MovLow & 0x8000U) != 0) {
        raise ();
        return false;
      }

      break;
    }
    
    default:
    {
      raise ();
      return false;
    }
  }

  /*if (Segment->Write) {
    printf("!!! writable reloc at %x !!!\n", Reloc->Target);
  }*/

  return true;
}

static
bool
CheckToolImageRelocInfo (
  const image_tool_image_info_t *Image,
  uint32_t                      ImageSize
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
    Result = CheckToolImageReloc (Image, ImageSize, &RelocInfo->Relocs[Index]);
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
  const image_tool_debug_info_t *DebugInfo
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
  const image_tool_image_info_t *Image
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

  Result = CheckToolImageRelocInfo (Image, ImageSize);
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

  assert (Image != NULL);

  SegmentInfo = &Image->SegmentInfo;

  for (Index = 0; Index < SegmentInfo->NumSegments; ++Index) {
    Segment = &SegmentInfo->Segments[Index];

    assert (Segment->DataSize <= Segment->ImageSize);
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

bool
ToolImageRelocate (
  image_tool_image_info_t *Image,
  uint64_t                BaseAddress
  )
{
  uint64_t                   Adjust;
  const image_tool_reloc_t   *Reloc;
  uint32_t                   RelocOffset;
  uint32_t                   RemainingSize;
  const image_tool_segment_t *Segment;
  uint32_t                   Index;
  uint32_t                   RelocTarget32;
  uint64_t                   RelocTarget64;

  Adjust = BaseAddress - Image->HeaderInfo.BaseAddress;

  if (Adjust == 0) {
    return TRUE;
  }

  for (Index = 0; Index < Image->RelocInfo.NumRelocs; ++Index) {
    Reloc = &Image->RelocInfo.Relocs[Index];

    RelocOffset = Reloc->Target;
    Segment = ImageGetSegmentByAddress (
                &RelocOffset,
                &RemainingSize,
                &Image->SegmentInfo
                );
    if (Segment == NULL) {
      raise ();
      return false;
    }

    switch (Reloc->Type) {
      case EFI_IMAGE_REL_BASED_HIGHLOW:
      {
        assert (RemainingSize >= sizeof (UINT32));

        RelocTarget32  = ReadUnaligned32 ((CONST VOID *)&Segment->Data[RelocOffset]);
        RelocTarget32 += (uint32_t)Adjust;
        WriteUnaligned32 ((VOID *)&Segment->Data[RelocOffset], RelocTarget32);
        break;
      }

      case EFI_IMAGE_REL_BASED_DIR64:
      {
        assert (RemainingSize >= sizeof (UINT64));

        RelocTarget64  = ReadUnaligned64 ((CONST VOID *)&Segment->Data[RelocOffset]);
        RelocTarget64 += Adjust;
        WriteUnaligned64 ((VOID *)&Segment->Data[RelocOffset], RelocTarget64);
        break;
      }
      
      case EFI_IMAGE_REL_BASED_ARM_MOV32T:
      {
        assert (RemainingSize >= sizeof (UINT32));
        assert (IS_ALIGNED (Reloc->Target, ALIGNOF (UINT16)));

        PeCoffThumbMovwMovtImmediateFixup (&Segment->Data[RelocOffset], Adjust);
        break;
      }
      
      default:
      {
        raise ();
        return false;
      }
    }
  }

  Image->HeaderInfo.BaseAddress = BaseAddress;

  return true;
}
