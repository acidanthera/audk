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

  // LCOV_EXCL_START
  if (!IS_ALIGNED (Segment->ImageSize, SegmentInfo->SegmentAlignment)) {
    assert (false);
    return false;
  }
  // LCOV_EXCL_STOP

  if (Segment->Write && Segment->Execute) {
    DEBUG_RAISE ();
    return false;
  }

  if (Segment->ImageAddress != *PreviousEndAddress) {
    DEBUG_RAISE ();
    return false;
  }

  Overflow = BaseOverflowAddU32 (
               Segment->ImageAddress,
               Segment->ImageSize,
               PreviousEndAddress
               );
  // LCOV_EXCL_START
  if (Overflow) {
    assert (false);
    return false;
  }
  // LCOV_EXCL_STOP

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

  // LCOV_EXCL_START
  if (!IS_POW2 (SegmentInfo->SegmentAlignment)) {
    assert (false);
    return false;
  }
  // LCOV_EXCL_STOP

  if (SegmentInfo->NumSegments == 0) {
    DEBUG_RAISE ();
    return false;
  }

  // LCOV_EXCL_START
  if (!IS_ALIGNED (SegmentInfo->Segments[0].ImageAddress, SegmentInfo->SegmentAlignment)) {
    assert (false);
    return false;
  }
  // LCOV_EXCL_STOP

  *ImageSize = SegmentInfo->Segments[0].ImageAddress;
  for (Index = 0; Index < SegmentInfo->NumSegments; ++Index) {
    Result = CheckToolImageSegment (
               SegmentInfo,
               &SegmentInfo->Segments[Index],
               ImageSize
               );
    if (!Result) {
      DEBUG_RAISE ();
      return false;
    }
  }

  return true;
}

static
bool
CheckToolImageHeaderInfo (
  const image_tool_header_info_t   *HeaderInfo,
  const image_tool_segment_info_t  *SegmentInfo,
  uint32_t                         ImageSize
  )
{
  if (SegmentInfo->Segments[0].ImageAddress > HeaderInfo->EntryPointAddress ||
      HeaderInfo->EntryPointAddress > ImageSize) {
    DEBUG_RAISE ();
    return false;
  }

  // LCOV_EXCL_START
  if (!IS_ALIGNED (HeaderInfo->BaseAddress, SegmentInfo->SegmentAlignment)) {
    assert (false);
    return false;
  }
  // LCOV_EXCL_STOP

  // LCOV_EXCL_START
  if (HeaderInfo->BaseAddress + ImageSize < HeaderInfo->BaseAddress) {
    assert (false);
    return false;
  }
  // LCOV_EXCL_STOP

  return true;
}

const image_tool_segment_t *
ImageGetSegmentByAddress (
  uint32_t                        *Address,
  uint32_t                        *RemainingSize,
  const image_tool_segment_info_t *SegmentInfo
  )
{
  uint32_t Index;

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

uint8_t
ToolImageGetRelocSize (
  uint8_t  Type
  )
{
  // LCOV_EXCL_START
  switch (Type) {
  // LCOV_EXCL_STOP
    case EFI_IMAGE_REL_BASED_HIGHLOW:
    {
      return sizeof (UINT32);
    }

    case EFI_IMAGE_REL_BASED_DIR64:
    {
      return sizeof (UINT64);
    }

#if 0
    case EFI_IMAGE_REL_BASED_ARM_MOV32T:
    {
      return sizeof (UINT32);
    }
#endif

    // LCOV_EXCL_START
    default:
    {
      break;
    }
    // LCOV_EXCL_STOP
  }

  // LCOV_EXCL_START
  assert (false);
  return 0;
  // LCOV_EXCL_STOP
}

static
bool
CheckToolImageReloc (
  const image_tool_image_info_t *Image,
  const image_tool_reloc_t      *Reloc,
  uint8_t                       RelocSize
  )
{
  uint32_t                   RelocOffset;
  uint32_t                   RemainingSize;
  const image_tool_segment_t *Segment;

#if 0
  uint16_t                   MovHigh;
  uint16_t                   MovLow;
#endif

  RelocOffset = Reloc->Target;
  Segment     = ImageGetSegmentByAddress (
                  &RelocOffset,
                  &RemainingSize,
                  &Image->SegmentInfo
                  );
  if (Segment == NULL) {
    DEBUG_RAISE ();
    return false;
  }

  if (RelocSize > RemainingSize) {
    DEBUG_RAISE ();
    return false;
  }

#if 0
  if (Reloc->Type == EFI_IMAGE_REL_BASED_ARM_MOV32T) {
    if (!IS_ALIGNED (Reloc->Target, ALIGNOF (UINT16))) {
      DEBUG_RAISE ();
      return false;
    }

    MovHigh = *(const uint16_t *)&Segment->Data[RelocOffset];
    MovLow  = *(const uint16_t *)&Segment->Data[RelocOffset + 2];
    if (((MovHigh & 0xFBF0U) != 0xF200U && (MovHigh & 0xFBF0U) != 0xF2C0U) ||
      (MovLow & 0x8000U) != 0) {
      DEBUG_RAISE ();
      return false;
    }
  }
#endif

  // FIXME: Update drivers?
  if (Image->HeaderInfo.Subsystem == EFI_IMAGE_SUBSYSTEM_EFI_RUNTIME_DRIVER &&
       Segment->Write) {
    printf("!!! writable reloc at %x !!!\n", Reloc->Target);
    //DEBUG_RAISE ();
    //return false;
  }

  return true;
}

static
bool
CheckToolImageRelocInfo (
  const image_tool_image_info_t *Image
  )
{
  const image_tool_reloc_info_t *RelocInfo;
  uint8_t                       RelocSize;
  uint32_t                      MinRelocTarget;
  uint32_t                      Index;
  bool                          Result;

  RelocInfo = &Image->RelocInfo;

  if (RelocInfo->NumRelocs == 0) {
    return true;
  }

  // LCOV_EXCL_START
  if (RelocInfo->RelocsStripped) {
    assert (false);
    return false;
  }
  // LCOV_EXCL_STOP

  if (RelocInfo->NumRelocs > (MAX_UINT32 / sizeof (UINT16))) {
    DEBUG_RAISE ();
    return false;
  }

  MinRelocTarget = 0;

  for (Index = 0; Index < RelocInfo->NumRelocs; ++Index) {
    if (RelocInfo->Relocs[Index].Target < MinRelocTarget) {
      DEBUG_RAISE ();
      return false;
    }

    RelocSize = ToolImageGetRelocSize (RelocInfo->Relocs[Index].Type);
    // LCOV_EXCL_START
    if (RelocSize == 0) {
      assert (false);
      return false;
    }
    // LCOV_EXCL_STOP

    Result = CheckToolImageReloc (Image, &RelocInfo->Relocs[Index], RelocSize);
    if (!Result) {
      DEBUG_RAISE ();
      return false;
    }

    MinRelocTarget = RelocInfo->Relocs[Index].Target + RelocSize;
  }

  return true;
}

static
bool
CheckToolImageDebugInfo (
  const image_tool_debug_info_t *DebugInfo
  )
{
  if (DebugInfo->SymbolsPathLen > MAX_UINT8) {
    DEBUG_RAISE ();
    return false;
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

  Result = CheckToolImageSegmentInfo (&Image->SegmentInfo, &ImageSize);
  if (!Result) {
    DEBUG_RAISE ();
    return false;
  }

  Result = CheckToolImageHeaderInfo (
             &Image->HeaderInfo,
             &Image->SegmentInfo,
             ImageSize
             );
  if (!Result) {
    DEBUG_RAISE ();
    return false;
  }

  Result = CheckToolImageRelocInfo (Image);
  if (!Result) {
    DEBUG_RAISE ();
    return false;
  }

  Result = CheckToolImageDebugInfo (&Image->DebugInfo);
  if (!Result) {
    DEBUG_RAISE ();
    return false;
  }

  return true;
}

void
ImageInitUnpaddedSize (
  const image_tool_image_info_t *Image
  )
{
  uint32_t              Index;
  image_tool_segment_t  *Segment;

  for (Index = 0; Index < Image->SegmentInfo.NumSegments; ++Index) {
    Segment = &Image->SegmentInfo.Segments[Index];
    Segment->UnpaddedSize = Segment->ImageSize;

    for (; Segment->UnpaddedSize > 0; --Segment->UnpaddedSize) {
      if (Segment->Data[Segment->UnpaddedSize - 1] != 0) {
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
  uint16_t Index;

  // LCOV_EXCL_START
  if (Image->SegmentInfo.Segments != NULL) {
  // LCOV_EXCL_STOP
    for (Index = 0; Index < Image->SegmentInfo.NumSegments; ++Index) {
      // LCOV_EXCL_START
      if (Image->SegmentInfo.Segments[Index].Name != NULL) {
      // LCOV_EXCL_STOP
        FreePool (Image->SegmentInfo.Segments[Index].Name);
      }

      // LCOV_EXCL_START
      if (Image->SegmentInfo.Segments[Index].Data != NULL) {
      // LCOV_EXCL_STOP
        FreePool (Image->SegmentInfo.Segments[Index].Data);
      }
    }

    // LCOV_EXCL_START
    if (Image->SegmentInfo.Segments != NULL) {
    // LCOV_EXCL_STOP
      FreePool (Image->SegmentInfo.Segments);
    }
  }

  // LCOV_EXCL_START
  if (Image->HiiInfo.Data != NULL) {
  // LCOV_EXCL_STOP
    FreePool (Image->HiiInfo.Data);
  }

  // LCOV_EXCL_START
  if (Image->RelocInfo.Relocs != NULL) {
  // LCOV_EXCL_STOP
    FreePool (Image->RelocInfo.Relocs);
  }

  // LCOV_EXCL_START
  if (Image->DebugInfo.SymbolsPath != NULL) {
  // LCOV_EXCL_STOP
    FreePool (Image->DebugInfo.SymbolsPath);
  }

  memset (Image, 0, sizeof (*Image));
}

bool
ToolImageRelocate (
  image_tool_image_info_t *Image,
  uint64_t                BaseAddress,
  uint32_t                IgnorePrefix
  )
{
  const image_tool_segment_t *LastSegment;
  uint32_t                   ImageSize;
  uint64_t                   Adjust;
  const image_tool_reloc_t   *Reloc;
  uint32_t                   RelocOffset;
  uint32_t                   RemainingSize;
  const image_tool_segment_t *Segment;
  uint32_t                   Index;
  uint32_t                   RelocTarget32;
  uint64_t                   RelocTarget64;

  if (!IS_ALIGNED (BaseAddress, Image->SegmentInfo.SegmentAlignment)) {
    DEBUG_RAISE ();
    return false;
  }

  Adjust = BaseAddress - Image->HeaderInfo.BaseAddress;

  if (Adjust == 0) {
    return true;
  }

  LastSegment = &Image->SegmentInfo.Segments[Image->SegmentInfo.NumSegments - 1];
  ImageSize   = LastSegment->ImageAddress + LastSegment->ImageSize;

  //
  // When removing the image header prefix, BaseAddress + ImageSize may indeed
  // overflow. The important part is that the address starting from the first
  // image segment does not.
  //
  if (BaseAddress + ImageSize < BaseAddress + IgnorePrefix) {
    DEBUG_RAISE ();
    return false;
  }

  for (Index = 0; Index < Image->RelocInfo.NumRelocs; ++Index) {
    Reloc = &Image->RelocInfo.Relocs[Index];

    RelocOffset = Reloc->Target;
    Segment = ImageGetSegmentByAddress (
                &RelocOffset,
                &RemainingSize,
                &Image->SegmentInfo
                );
    assert (Segment != NULL);

    // LCOV_EXCL_START
    switch (Reloc->Type) {
    // LCOV_EXCL_STOP
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

#if 0
      case EFI_IMAGE_REL_BASED_ARM_MOV32T:
      {
        assert (RemainingSize >= sizeof (UINT32));
        assert (IS_ALIGNED (Reloc->Target, ALIGNOF (UINT16)));

        PeCoffThumbMovwMovtImmediateFixup (&Segment->Data[RelocOffset], Adjust);
        break;
      }
#endif

      // LCOV_EXCL_START
      default:
      {
        assert (false);
        return false;
      }
      // LCOV_EXCL_STOP
    }
  }

  Image->HeaderInfo.BaseAddress = BaseAddress;

  return true;
}

static
int
ToolImageRelocCompare (
  IN const void  *Buffer1,
  IN const void  *Buffer2
  )
{
  const image_tool_reloc_t  *Reloc1;
  const image_tool_reloc_t  *Reloc2;

  Reloc1 = (const image_tool_reloc_t *)Buffer1;
  Reloc2 = (const image_tool_reloc_t *)Buffer2;

  if (Reloc1->Target < Reloc2->Target) {
    return -1;
  }

  if (Reloc1->Target > Reloc2->Target) {
    return 1;
  }

  return 0;
}

void
ToolImageSortRelocs (
  image_tool_image_info_t  *Image
  )
{
  if (Image->RelocInfo.Relocs == NULL) {
    return;
  }

  qsort (
    Image->RelocInfo.Relocs,
    Image->RelocInfo.NumRelocs,
    sizeof (*Image->RelocInfo.Relocs),
    ToolImageRelocCompare
    );
}

bool
ToolImageCompare (
  const image_tool_image_info_t  *DestImage,
  const image_tool_image_info_t  *SourceImage
  )
{
  int         CmpResult;
  uint32_t    SegIndex;
  const char  *DestName;
  const char  *SourceName;
  uint32_t    NameIndex;

  //
  // Compare HeaderInfo.
  //

  CmpResult = memcmp (
                &DestImage->HeaderInfo,
                &SourceImage->HeaderInfo,
                sizeof (DestImage->HeaderInfo)
                );
  // LCOV_EXCL_START
  if (CmpResult != 0) {
    DEBUG_RAISE ();
    return false;
  }
  // LCOV_EXCL_STOP

  //
  // Compare SegmentInfo.
  // UnpaddedSize is deliberately omitted, as it's implicit by the equality of
  // ImageSize and Data.
  //

  CmpResult = memcmp (
                &DestImage->SegmentInfo,
                &SourceImage->SegmentInfo,
                OFFSET_OF (image_tool_segment_info_t, Segments)
                );
  // LCOV_EXCL_START
  if (CmpResult != 0) {
    DEBUG_RAISE ();
    return false;
  }
  // LCOV_EXCL_STOP

  for (SegIndex = 0; SegIndex < DestImage->SegmentInfo.NumSegments; ++SegIndex) {
    CmpResult = memcmp (
                  &DestImage->SegmentInfo.Segments[SegIndex],
                  &SourceImage->SegmentInfo.Segments[SegIndex],
                  OFFSET_OF (image_tool_segment_t, Name)
                  );
    // LCOV_EXCL_START
    if (CmpResult != 0) {
      DEBUG_RAISE ();
      return false;
    }
    // LCOV_EXCL_STOP

    //
    // Don't assume images generally support arbitrarily long names or names in
    // general. Check prefix equiality as a best effort.
    //
    DestName   = DestImage->SegmentInfo.Segments[SegIndex].Name;
    SourceName = SourceImage->SegmentInfo.Segments[SegIndex].Name;

    // LCOV_EXCL_START
    if (DestName != NULL && SourceName == NULL) {
      assert (false);
      return false;
    }
    // LCOV_EXCL_STOP

    //
    // When omitting the debug info, some file formats (e.g., UE) may not
    // contain segment names.
    //
    if (DestName != NULL) {
      for (
        NameIndex = 0;
        DestName[NameIndex] != '\0' &&
        // LCOV_EXCL_START
        SourceName[NameIndex] != '\0';
        // LCOV_EXCL_STOP
        ++NameIndex
        ) {
        // LCOV_EXCL_START
        if (DestName[NameIndex] != SourceName[NameIndex]) {
          DEBUG_RAISE ();
          return false;
        }
        // LCOV_EXCL_STOP
      }
    }

    if (DestImage->SegmentInfo.Segments[SegIndex].ImageSize != 0) {
      CmpResult = memcmp (
                    DestImage->SegmentInfo.Segments[SegIndex].Data,
                    SourceImage->SegmentInfo.Segments[SegIndex].Data,
                    DestImage->SegmentInfo.Segments[SegIndex].ImageSize
                    );
      // LCOV_EXCL_START
      if (CmpResult != 0) {
        DEBUG_RAISE ();
        return false;
      }
      // LCOV_EXCL_STOP
    }
  }

  //
  // Compare RelocInfo.
  //

  CmpResult = memcmp (
                &DestImage->RelocInfo,
                &SourceImage->RelocInfo,
                OFFSET_OF (image_tool_reloc_info_t, Relocs)
                );
  // LCOV_EXCL_START
  if (CmpResult != 0) {
    DEBUG_RAISE ();
    return false;
  }
  // LCOV_EXCL_STOP

  if (DestImage->RelocInfo.NumRelocs != 0) {
    CmpResult = memcmp (
                  DestImage->RelocInfo.Relocs,
                  SourceImage->RelocInfo.Relocs,
                  DestImage->RelocInfo.NumRelocs * sizeof (*DestImage->RelocInfo.Relocs)
                  );
    // LCOV_EXCL_START
    if (CmpResult != 0) {
      DEBUG_RAISE ();
      return false;
    }
    // LCOV_EXCL_STOP
  }

  //
  // Compare HiiInfo.
  //

  CmpResult = memcmp (
                &DestImage->HiiInfo,
                &SourceImage->HiiInfo,
                OFFSET_OF (image_tool_hii_info_t, Data)
                );
  // LCOV_EXCL_START
  if (CmpResult != 0) {
    DEBUG_RAISE ();
    return false;
  }
  // LCOV_EXCL_STOP

  // LCOV_EXCL_START
  if (DestImage->HiiInfo.DataSize != 0) {
    CmpResult = memcmp (
                  DestImage->HiiInfo.Data,
                  SourceImage->HiiInfo.Data,
                  DestImage->HiiInfo.DataSize
                  );
    if (CmpResult != 0) {
      DEBUG_RAISE ();
      return false;
    }
  }
  // LCOV_EXCL_STOP

  //
  // Compare DebugInfo.
  //

  CmpResult = memcmp (
                &DestImage->DebugInfo,
                &SourceImage->DebugInfo,
                OFFSET_OF (image_tool_debug_info_t, SymbolsPath)
                );
  // LCOV_EXCL_START
  if (CmpResult != 0) {
    DEBUG_RAISE ();
    return false;
  }
  // LCOV_EXCL_STOP

  // LCOV_EXCL_START
  if ((DestImage->DebugInfo.SymbolsPath != NULL) != (SourceImage->DebugInfo.SymbolsPath != NULL)) {
    DEBUG_RAISE ();
    return false;
  }
  // LCOV_EXCL_STOP

  if (DestImage->DebugInfo.SymbolsPath != NULL) {
    CmpResult = strcmp (
                  DestImage->DebugInfo.SymbolsPath,
                  SourceImage->DebugInfo.SymbolsPath
                  );
    // LCOV_EXCL_START
    if (CmpResult != 0) {
      DEBUG_RAISE ();
      return false;
    }
    // LCOV_EXCL_STOP
  }

  return true;
}

void
ToolImageStripRelocs (
  image_tool_image_info_t  *Image
  )
{
  Image->RelocInfo.NumRelocs = 0;

  if (Image->RelocInfo.Relocs != NULL) {
    FreePool (Image->RelocInfo.Relocs);
  }

  Image->RelocInfo.Relocs = NULL;

  Image->RelocInfo.RelocsStripped = TRUE;
}
