/** @file
  Copyright (c) 2021 - 2023, Marvin Häuser. All rights reserved.
  Copyright (c) 2022, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-2-Clause-Patent
**/

#include "ImageTool.h"
#include "UeScan.h"
#include "DynamicBuffer.h"

typedef union {
  UINT32    Value32;
  UINT64    Value64;
} UE_RELOC_FIXUP_VALUE;

static
RETURN_STATUS
InternalProcessRelocChain (
  image_tool_dynamic_buffer        *Buffer,
  const image_tool_segment_info_t  *SegmentInfo,
  UINT16                           FirstRelocType,
  UINT32                           *ChainStart
  )
{
  uint32_t                    OffsetInSegment;
  const image_tool_segment_t  *Segment;
  image_tool_reloc_t          Reloc;
  uint32_t                    Offset;

  UINT16  RelocType;
  UINT16  RelocOffset;
  UINT32  RelocTarget;

  UINT32  RemRelocTargetSize;

  VOID                  *Fixup;
  UE_RELOC_FIXUP_VALUE  FixupInfo;
  UINT8                 FixupSize;
  UE_RELOC_FIXUP_VALUE  FixupValue;

  memset (&Reloc, 0, sizeof (Reloc));

  RelocType   = FirstRelocType;
  RelocTarget = *ChainStart;

  while (TRUE) {
    OffsetInSegment = RelocTarget;
    Segment         = ImageGetSegmentByAddress (
                        &OffsetInSegment,
                        &RemRelocTargetSize,
                        SegmentInfo
                        );
    if (Segment == NULL) {
      DEBUG_RAISE ();
      return RETURN_VOLUME_CORRUPTED;
    }

    Fixup = &Segment->Data[OffsetInSegment];

    Reloc.Target = RelocTarget;

    if (RelocType < UeRelocGenericMax) {
      if (RelocType == UeReloc64) {
        FixupSize = sizeof (UINT64);
        //
        // Verify the relocation fixup target is in bounds of the Image buffer.
        //
        if (FixupSize > RemRelocTargetSize) {
          DEBUG_RAISE ();
          return RETURN_VOLUME_CORRUPTED;
        }

        //
        // Relocate the target instruction.
        //
        FixupInfo.Value64  = ReadUnaligned64 (Fixup);
        FixupValue.Value64 = UE_CHAINED_RELOC_FIXUP_VALUE (FixupInfo.Value64);
        WriteUnaligned64 (Fixup, FixupValue.Value64);

        Reloc.Type = EFI_IMAGE_REL_BASED_DIR64;
      } else if (RelocType == UeReloc32) {
        FixupSize = sizeof (UINT32);
        //
        // Verify the image relocation fixup target is in bounds of the image
        // buffer.
        //
        if (FixupSize > RemRelocTargetSize) {
          DEBUG_RAISE ();
          return RETURN_VOLUME_CORRUPTED;
        }

        //
        // Relocate the target instruction.
        //
        FixupInfo.Value32  = ReadUnaligned32 (Fixup);
        FixupValue.Value32 = UE_CHAINED_RELOC_FIXUP_VALUE_32 (FixupInfo.Value32);
        WriteUnaligned32 (Fixup, FixupValue.Value32);

        Reloc.Type = EFI_IMAGE_REL_BASED_HIGHLOW;
        //
        // Imitate the common header of UE chained relocation fixups,
        // as for 32-bit files all relocs have the same type.
        //
        FixupInfo.Value32  = FixupInfo.Value32 << 4;
        FixupInfo.Value32 |= UeReloc32;
      } else {
        //
        // The Image relocation fixup type is unknown, disallow the Image.
        //
        DEBUG_RAISE ();
        return RETURN_UNSUPPORTED;
      }
    } else {
      //
      // The Image relocation fixup type is unknown, disallow the Image.
      //
      DEBUG_RAISE ();
      return RETURN_UNSUPPORTED;
    }

    RelocTarget += FixupSize;

    Offset = ImageToolBufferAppend (Buffer, &Reloc, sizeof (Reloc));
    if (Offset == MAX_UINT32) {
      DEBUG_RAISE ();
      return RETURN_OUT_OF_RESOURCES;
    }

    RelocOffset = UE_CHAINED_RELOC_FIXUP_NEXT_OFFSET (FixupInfo.Value32);
    if (RelocOffset == UE_CHAINED_RELOC_FIXUP_OFFSET_END) {
      *ChainStart = RelocTarget;
      return RETURN_SUCCESS;
    }

    //
    // It holds that ImageSize mod 4 KiB = 0, thus ImageSize <= 0xFFFFF000.
    // Furthermore, it holds that RelocTarget <= ImageSize.
    // Finally, it holds that RelocOffset <= 0xFFE.
    // It follows that this cannot overflow.
    //
    RelocTarget += RelocOffset;
    assert (RelocOffset <= RelocTarget);

    RelocType = UE_CHAINED_RELOC_FIXUP_NEXT_TYPE (FixupInfo.Value32);
  }
}

STATIC
RETURN_STATUS
InternalApplyRelocation (
  image_tool_dynamic_buffer        *Buffer,
  const image_tool_segment_info_t  *SegmentInfo,
  UINT16                           RelocType,
  UINT32                           *RelocTarget
  )
{
  BOOLEAN  Overflow;

  const image_tool_segment_t  *LastSegment;
  uint32_t                    ImageSize;
  UINT32                      RemRelocTargetSize;

  UINT32  FixupTarget;
  UINT8   FixupSize;

  image_tool_reloc_t  Reloc;
  uint32_t            Offset;

  FixupTarget = *RelocTarget;

  LastSegment = &SegmentInfo->Segments[SegmentInfo->NumSegments - 1];
  ImageSize   = LastSegment->ImageAddress + LastSegment->ImageSize;
  //
  // Verify the relocation fixup target address is in bounds of the image buffer.
  //
  Overflow = BaseOverflowSubU32 (ImageSize, FixupTarget, &RemRelocTargetSize);
  if (Overflow) {
    DEBUG_RAISE ();
    return RETURN_VOLUME_CORRUPTED;
  }

  memset (&Reloc, 0, sizeof (Reloc));
  Reloc.Target = FixupTarget;
  //
  // Apply the relocation fixup per type.
  //
  if (RelocType < UeRelocGenericMax) {
    if ((RelocType == UeReloc32) || (RelocType == UeReloc32NoMeta)) {
      FixupSize  = sizeof (UINT32);
      Reloc.Type = EFI_IMAGE_REL_BASED_HIGHLOW;
    } else {
      assert (RelocType == UeReloc64);

      FixupSize  = sizeof (UINT64);
      Reloc.Type = EFI_IMAGE_REL_BASED_DIR64;
    }
  } else {
    //
    // The image relocation fixup type is unknown, disallow the image.
    //
    fprintf (stderr, "ImageTool: Unknown RelocType = 0x%x\n", RelocType);
    ImageToolBufferFree (Buffer);
    return RETURN_UNSUPPORTED;
  }

  //
  // Verify the relocation fixup target is in bounds of the image buffer.
  //
  if (FixupSize > RemRelocTargetSize) {
    DEBUG_RAISE ();
    return RETURN_VOLUME_CORRUPTED;
  }

  Offset = ImageToolBufferAppend (Buffer, &Reloc, sizeof (Reloc));
  if (Offset == MAX_UINT32) {
    DEBUG_RAISE ();
    ImageToolBufferFree (Buffer);
    return RETURN_OUT_OF_RESOURCES;
  }

  *RelocTarget = FixupTarget + FixupSize;

  return RETURN_SUCCESS;
}

RETURN_STATUS
ScanUeGetRelocInfo (
  OUT image_tool_reloc_info_t          *RelocInfo,
  IN  const image_tool_segment_info_t  *SegmentInfo,
  IN  UE_LOADER_IMAGE_CONTEXT          *Context
  )
{
  RETURN_STATUS              Status;
  BOOLEAN                    Overflow;
  CONST UE_HEADER            *UeHdr;
  BOOLEAN                    Chaining;
  UINT32                     RootOffsetMax;
  UINT32                     EntryOffsetMax;
  UINT32                     EndOfRelocTable;
  UINT32                     TableOffset;
  const UE_FIXUP_ROOT        *RelocRoot;
  UINT16                     FixupInfo;
  UINT16                     RelocType;
  UINT16                     RelocOffset;
  UINT32                     RelocTarget;
  image_tool_dynamic_buffer  Buffer;
  uint32_t                   RelocBufferSize;
  UINT32                     OldTableOffset;

  //
  // Verify the Relocation Directory is not empty.
  //
  if (Context->RelocTableSize == 0) {
    return RETURN_SUCCESS;
  }

  ImageToolBufferInit (&Buffer);

  UeHdr    = (CONST UE_HEADER *)Context->FileBuffer;
  Chaining = (UeHdr->ImageInfo & UE_HEADER_IMAGE_INFO_CHAINED_FIXUPS) != 0;

  EndOfRelocTable = Context->LoadTablesFileOffset + Context->RelocTableSize;

  RelocTarget = 0;

  RootOffsetMax  = EndOfRelocTable - MIN_SIZE_OF_UE_FIXUP_ROOT;
  EntryOffsetMax = EndOfRelocTable - sizeof (*RelocRoot->Heads);
  //
  // Apply all Base Relocations of the Image.
  //
  for (TableOffset = Context->LoadTablesFileOffset; TableOffset <= RootOffsetMax;) {
    RelocRoot = (CONST UE_FIXUP_ROOT *)(
                                        (CONST UINT8 *)Context->FileBuffer + TableOffset
                                        );
    //
    // This cannot overflow due to the TableOffset upper bound.
    //
    TableOffset += sizeof (*RelocRoot);

    Overflow = BaseOverflowAddU32 (
                 RelocTarget,
                 RelocRoot->FirstOffset,
                 &RelocTarget
                 );
    if (Overflow) {
      DEBUG_RAISE ();
      ImageToolBufferFree (&Buffer);
      return RETURN_VOLUME_CORRUPTED;
    }

    //
    // Process all relocation fixups of the current root.
    //
    while (TRUE) {
      FixupInfo = *(CONST UINT16 *)((CONST UINT8 *)Context->FileBuffer + TableOffset);
      //
      // This cannot overflow due to the upper bound of TableOffset.
      //
      TableOffset += sizeof (*RelocRoot->Heads);
      //
      // Apply the image relocation fixup.
      //
      RelocType = UE_RELOC_FIXUP_TYPE (FixupInfo);

      if (Chaining && (RelocType != UeReloc32NoMeta)) {
        Status = InternalProcessRelocChain (
                   &Buffer,
                   SegmentInfo,
                   RelocType,
                   &RelocTarget
                   );
      } else {
        Status = InternalApplyRelocation (
                   &Buffer,
                   SegmentInfo,
                   RelocType,
                   &RelocTarget
                   );
      }

      if (RETURN_ERROR (Status)) {
        DEBUG_RAISE ();
        ImageToolBufferFree (&Buffer);
        return Status;
      }

      RelocOffset = UE_RELOC_FIXUP_OFFSET (FixupInfo);
      if (RelocOffset == UE_HEAD_FIXUP_OFFSET_END) {
        break;
      }

      //
      // It holds that ImageSize mod 4 KiB = 0, thus ImageSize <= 0xFFFFF000.
      // Furthermore, it holds that RelocTarget <= ImageSize.
      // Finally, it holds that RelocOffset <= 0xFFE.
      // It follows that this cannot overflow.
      //
      RelocTarget += RelocOffset;
      assert (RelocOffset <= RelocTarget);

      if (TableOffset > EntryOffsetMax) {
        DEBUG_RAISE ();
        ImageToolBufferFree (&Buffer);
        return RETURN_VOLUME_CORRUPTED;
      }
    }

    //
    // This cannot overflow due to the TableOffset upper bounds and the
    // alignment guarantee of RelocTableSize.
    //
    OldTableOffset = TableOffset;
    TableOffset    = ALIGN_VALUE (TableOffset, ALIGNOF (UE_FIXUP_ROOT));
    assert (OldTableOffset <= TableOffset);
  }

  RelocInfo->Relocs = ImageToolBufferDump (&RelocBufferSize, &Buffer);

  ImageToolBufferFree (&Buffer);

  if (RelocInfo->Relocs == NULL) {
    fprintf (stderr, "ImageTool: Could not allocate memory for Relocs[]\n");
    return RETURN_OUT_OF_RESOURCES;
  }

  assert (IS_ALIGNED (RelocBufferSize, sizeof (*RelocInfo->Relocs)));
  RelocInfo->NumRelocs = RelocBufferSize / sizeof (*RelocInfo->Relocs);

  return RETURN_SUCCESS;
}

RETURN_STATUS
ScanUeGetSegmentInfo (
  OUT image_tool_segment_info_t  *SegmentInfo,
  IN  UE_LOADER_IMAGE_CONTEXT    *Context
  )
{
  RETURN_STATUS          Status;
  const UE_SEGMENT       *Segment;
  uint16_t               NumSegments;
  image_tool_segment_t   *ImageSegment;
  const char             *ImageBuffer;
  uint16_t               Index;
  uint32_t               SegmentAddress;
  uint32_t               SegmentSize;
  uint8_t                SegmentPermissions;
  const UE_SEGMENT_NAME  *SegmentNames;

  NumSegments = UeGetSegments (Context, &Segment);

  STATIC_ASSERT (
    sizeof (*SegmentInfo->Segments) <= MAX_UINT16 / UE_HEADER_NUM_SEGMENTS_MAX,
    "The following arithmetics cannot overflow."
    );

  SegmentInfo->Segments = AllocateZeroPool (
                            NumSegments * sizeof (*SegmentInfo->Segments)
                            );
  if (SegmentInfo->Segments == NULL) {
    fprintf (stderr, "ImageTool: Could not allocate memory for Segments[]\n");
    return RETURN_OUT_OF_RESOURCES;
  }

  Status = UeGetSegmentNames (Context, &SegmentNames);
  if (RETURN_ERROR (Status)) {
    if (Status != RETURN_NOT_FOUND) {
      DEBUG_RAISE ();
      return Status;
    }

    SegmentNames = NULL;
  }

  ImageBuffer = (char *)UeLoaderGetImageAddress (Context);

  SegmentAddress = 0;
  ImageSegment   = SegmentInfo->Segments;
  for (Index = 0; Index < NumSegments; ++Index, ++Segment) {
    if (SegmentNames != NULL) {
      ImageSegment->Name = AllocateCopyPool (
                             sizeof (SegmentNames[Index]),
                             SegmentNames[Index]
                             );
      if (ImageSegment->Name == NULL) {
        fprintf (stderr, "ImageTool: Could not allocate memory for Segment Name\n");
        return RETURN_OUT_OF_RESOURCES;
      }
    } else {
      assert (ImageSegment->Name == NULL);
    }

    SegmentSize = UE_SEGMENT_SIZE (Segment->ImageInfo);

    ImageSegment->Data = AllocateCopyPool (
                           SegmentSize,
                           ImageBuffer + SegmentAddress
                           );
    if (ImageSegment->Data == NULL) {
      fprintf (stderr, "ImageTool: Could not allocate memory for Segment Data\n");
      if (ImageSegment->Name != NULL) {
        FreePool (ImageSegment->Name);
      }

      return RETURN_OUT_OF_RESOURCES;
    }

    ImageSegment->ImageAddress = SegmentAddress;
    ImageSegment->ImageSize    = SegmentSize;

    SegmentPermissions = UE_SEGMENT_PERMISSIONS (Segment->ImageInfo);
    switch (SegmentPermissions) {
      case UeSegmentPermX:
      {
        ImageSegment->Execute = true;
        assert (!ImageSegment->Read);
        assert (!ImageSegment->Write);
        break;
      }

      case UeSegmentPermRX:
      {
        ImageSegment->Read    = true;
        ImageSegment->Execute = true;
        assert (!ImageSegment->Write);
        break;
      }

      case UeSegmentPermRW:
      {
        ImageSegment->Read  = true;
        ImageSegment->Write = true;
        assert (!ImageSegment->Execute);
        break;
      }

      default:
      case UeSegmentPermR:
      {
        assert (SegmentPermissions == UeSegmentPermR);
        ImageSegment->Read = true;
        assert (!ImageSegment->Write);
        assert (!ImageSegment->Execute);
        break;
      }
    }

    SegmentAddress += SegmentSize;

    ++SegmentInfo->NumSegments;
    ++ImageSegment;
  }

  return RETURN_SUCCESS;
}
