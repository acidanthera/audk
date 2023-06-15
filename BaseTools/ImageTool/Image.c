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

  if (!IS_ALIGNED (Segment->ImageSize, SegmentInfo->SegmentAlignment)) {
    DEBUG_RAISE ();
    return false;
  }

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
  if (Overflow) {
    DEBUG_RAISE ();
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

  if (!IS_POW2 (SegmentInfo->SegmentAlignment)) {
    DEBUG_RAISE ();
    return false;
  }

  if (SegmentInfo->NumSegments == 0) {
    DEBUG_RAISE ();
    return false;
  }

  if (!IS_ALIGNED (SegmentInfo->Segments[0].ImageAddress, SegmentInfo->SegmentAlignment)) {
    DEBUG_RAISE ();
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

  if (!IS_ALIGNED (HeaderInfo->BaseAddress, SegmentInfo->SegmentAlignment)) {
    DEBUG_RAISE ();
    return false;
  }

  if (HeaderInfo->BaseAddress + ImageSize < HeaderInfo->BaseAddress) {
    DEBUG_RAISE ();
    return false;
  }

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
  switch (Type) {
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

    default:
    {
      return 0;
    }
  }
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
  if ((Image->HeaderInfo.Subsystem == EFI_IMAGE_SUBSYSTEM_EFI_RUNTIME_DRIVER ||
       Image->HeaderInfo.Subsystem == EFI_IMAGE_SUBSYSTEM_SAL_RUNTIME_DRIVER) &&
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

  if (RelocInfo->RelocsStripped) {
    DEBUG_RAISE ();
    return false;
  }

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
    if (RelocSize == 0) {
      DEBUG_RAISE ();
      return false;
    }

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
  uint8_t Index;

  if (Image->SegmentInfo.Segments != NULL) {
    for (Index = 0; Index < Image->SegmentInfo.NumSegments; ++Index) {
      if (Image->SegmentInfo.Segments[Index].Name != NULL) {
        FreePool (Image->SegmentInfo.Segments[Index].Name);
      }

      if (Image->SegmentInfo.Segments[Index].Data != NULL) {
        FreePool (Image->SegmentInfo.Segments[Index].Data);
      }
    }

    if (Image->SegmentInfo.Segments != NULL) {
      FreePool (Image->SegmentInfo.Segments);
    }
  }

  if (Image->HiiInfo.Data != NULL) {
    FreePool (Image->HiiInfo.Data);
  }

  if (Image->RelocInfo.Relocs != NULL) {
    FreePool (Image->RelocInfo.Relocs);
  }

  if (Image->DebugInfo.SymbolsPath != NULL) {
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

#if 0
      case EFI_IMAGE_REL_BASED_ARM_MOV32T:
      {
        assert (RemainingSize >= sizeof (UINT32));
        assert (IS_ALIGNED (Reloc->Target, ALIGNOF (UINT16)));

        PeCoffThumbMovwMovtImmediateFixup (&Segment->Data[RelocOffset], Adjust);
        break;
      }
#endif

      default:
      {
        assert (false);
        return false;
      }
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
  const image_tool_image_info_t  *Image1,
  const image_tool_image_info_t  *Image2
  )
{
  int         CmpResult;
  uint32_t    SegIndex;
  const char  *Name1;
  const char  *Name2;
  uint32_t    NameIndex;

  //
  // Compare HeaderInfo.
  //

  CmpResult = memcmp (
                &Image1->HeaderInfo,
                &Image2->HeaderInfo,
                sizeof (Image1->HeaderInfo)
                );
  if (CmpResult != 0) {
    DEBUG_RAISE ();
    return false;
  }

  //
  // Compare SegmentInfo.
  // UnpaddedSize is deliberately omitted, as it's implicit by the equality of
  // ImageSize and Data.
  //

  CmpResult = memcmp (
                &Image1->SegmentInfo,
                &Image2->SegmentInfo,
                OFFSET_OF (image_tool_segment_info_t, Segments)
                );
  if (CmpResult != 0) {
    DEBUG_RAISE ();
    return false;
  }

  for (SegIndex = 0; SegIndex < Image1->SegmentInfo.NumSegments; ++SegIndex) {
    CmpResult = memcmp (
                  &Image1->SegmentInfo.Segments[SegIndex],
                  &Image2->SegmentInfo.Segments[SegIndex],
                  OFFSET_OF (image_tool_segment_t, Name)
                  );
    if (CmpResult != 0) {
      DEBUG_RAISE ();
      return false;
    }

    //
    // Don't assume images generally support arbitrarily long names or names in
    // general. Check prefix equiality as a best effort.
    //
    Name1 = Image1->SegmentInfo.Segments[SegIndex].Name;
    Name2 = Image2->SegmentInfo.Segments[SegIndex].Name;
    if (Name1 != NULL && Name2 != NULL) {
      for (
        NameIndex = 0;
        Name1[NameIndex] != '\0' && Name2[NameIndex] != '\0';
        ++NameIndex
        ) {
        if (Name1[NameIndex] != Name2[NameIndex]) {
          DEBUG_RAISE ();
          return false;
        }
      }
    }

    if (Image1->SegmentInfo.Segments[SegIndex].ImageSize != 0) {
      CmpResult = memcmp (
                    Image1->SegmentInfo.Segments[SegIndex].Data,
                    Image2->SegmentInfo.Segments[SegIndex].Data,
                    Image1->SegmentInfo.Segments[SegIndex].ImageSize
                    );
      if (CmpResult != 0) {
        DEBUG_RAISE ();
        return false;
      }
    }
  }

  //
  // Compare RelocInfo.
  //

  CmpResult = memcmp (
                &Image1->RelocInfo,
                &Image2->RelocInfo,
                OFFSET_OF (image_tool_reloc_info_t, Relocs)
                );
  if (CmpResult != 0) {
    DEBUG_RAISE ();
    return false;
  }

  if (Image1->RelocInfo.NumRelocs != 0) {
    CmpResult = memcmp (
                  Image1->RelocInfo.Relocs,
                  Image2->RelocInfo.Relocs,
                  Image1->RelocInfo.NumRelocs * sizeof (*Image1->RelocInfo.Relocs)
                  );
    if (CmpResult != 0) {
      DEBUG_RAISE ();
      return false;
    }
  }

  //
  // Compare HiiInfo.
  //

  CmpResult = memcmp (
                &Image1->HiiInfo,
                &Image2->HiiInfo,
                OFFSET_OF (image_tool_hii_info_t, Data)
                );
  if (CmpResult != 0) {
    DEBUG_RAISE ();
    return false;
  }

  if (Image1->HiiInfo.DataSize != 0) {
    CmpResult = memcmp (
                  Image1->HiiInfo.Data,
                  Image2->HiiInfo.Data,
                  Image1->HiiInfo.DataSize
                  );
    if (CmpResult != 0) {
      DEBUG_RAISE ();
      return false;
    }
  }

  //
  // Compare DebugInfo.
  //

  CmpResult = memcmp (
                &Image1->DebugInfo,
                &Image2->DebugInfo,
                OFFSET_OF (image_tool_debug_info_t, SymbolsPath)
                );
  if (CmpResult != 0) {
    DEBUG_RAISE ();
    return false;
  }

  if ((Image1->DebugInfo.SymbolsPath != NULL) != (Image2->DebugInfo.SymbolsPath != NULL)) {
    DEBUG_RAISE ();
    return false;
  }

  if (Image1->DebugInfo.SymbolsPath != NULL) {
    CmpResult = strcmp (
                  Image1->DebugInfo.SymbolsPath,
                  Image2->DebugInfo.SymbolsPath
                  );
    if (CmpResult != 0) {
      DEBUG_RAISE ();
      return false;
    }
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
