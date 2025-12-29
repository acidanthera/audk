/** @file
  Copyright (c) 2023, Marvin Häuser. All rights reserved.
  SPDX-License-Identifier: BSD-2-Clause-Patent
**/

#include "ImageTool.h"

#include "DynamicBuffer.h"

static
uint8_t
AlignmentToExponent (
  uint64_t  Alignment
  )
{
  uint8_t  Index;

  assert (IS_POW2 (Alignment));

  for (
       Index = 0;
       // LCOV_EXCL_START
       Index < 64;
       // LCOV_EXCL_STOP
       ++Index
       )
  {
    if ((Alignment & (1ULL << Index)) == Alignment) {
      return Index;
    }
  }

  // LCOV_EXCL_START
  assert (false);
  return 0;
  // LCOV_EXCL_STOP
}

static
bool
ToolImageEmitUeSegmentHeaders (
  image_tool_dynamic_buffer      *Buffer,
  const image_tool_image_info_t  *Image,
  bool                           Xip
  )
{
  uint16_t    Index;
  uint8_t     Permissions;
  UE_SEGMENT  Segment;
  uint32_t    Offset;

  for (Index = 0; Index < Image->SegmentInfo.NumSegments; ++Index) {
    // LCOV_EXCL_START
    if (Image->SegmentInfo.Segments[Index].Write &&
        Image->SegmentInfo.Segments[Index].Execute)
    {
      assert (false);
      return false;
    }

    // LCOV_EXCL_STOP

    if (!Image->SegmentInfo.Segments[Index].Read &&
        !Image->SegmentInfo.Segments[Index].Write &&
        Image->SegmentInfo.Segments[Index].Execute)
    {
      Permissions = UeSegmentPermX;
    } else if (Image->SegmentInfo.Segments[Index].Read &&
               !Image->SegmentInfo.Segments[Index].Write &&
               Image->SegmentInfo.Segments[Index].Execute)
    {
      Permissions = UeSegmentPermRX;
    } else if (Image->SegmentInfo.Segments[Index].Read &&
               Image->SegmentInfo.Segments[Index].Write)
    {
      assert (!Image->SegmentInfo.Segments[Index].Execute);
      Permissions = UeSegmentPermRW;
    } else if (Image->SegmentInfo.Segments[Index].Read) {
      assert (!Image->SegmentInfo.Segments[Index].Write);
      assert (!Image->SegmentInfo.Segments[Index].Execute);
      Permissions = UeSegmentPermR;
    } else {
      DEBUG_RAISE ();
      return false;
    }

    Segment.ImageInfo  = Image->SegmentInfo.Segments[Index].ImageSize >> 12U;
    Segment.ImageInfo |= Permissions << 20U;
    assert (UE_SEGMENT_SIZE (Segment.ImageInfo) == Image->SegmentInfo.Segments[Index].ImageSize);
    assert (UE_SEGMENT_PERMISSIONS (Segment.ImageInfo) == Permissions);

    Segment.FileSize = Xip ? Image->SegmentInfo.Segments[Index].ImageSize : Image->SegmentInfo.Segments[Index].UnpaddedSize;

    Offset = ImageToolBufferAppend (Buffer, &Segment, sizeof (Segment));
    if (Offset == MAX_UINT32) {
      DEBUG_RAISE ();
      return false;
    }
  }

  return true;
}

static
bool
ToolImageUeRelocTableRequired (
  const image_tool_image_info_t  *Image
  )
{
  return Image->RelocInfo.NumRelocs != 0;
}

static
bool
ToolImageUeDebugTableRequired (
  const image_tool_image_info_t  *Image
  )
{
  // FIXME: Segment names when symbols are absent?
  return Image->DebugInfo.SymbolsPath != NULL;
}

static
int8_t
InternalGetUeMachine (
  uint16_t  Machine
  )
{
  switch (Machine) {
    case IMAGE_FILE_MACHINE_I386:
    {
      return UeMachineI386;
    }

    case IMAGE_FILE_MACHINE_X64:
    {
      return UeMachineX64;
    }

    case IMAGE_FILE_MACHINE_ARMTHUMB_MIXED:
    {
      return UeMachineArmThumbMixed;
    }

    case IMAGE_FILE_MACHINE_ARM64:
    {
      return UeMachineArm64;
    }

    case IMAGE_FILE_MACHINE_RISCV32:
    {
      return UeMachineRiscV32;
    }

    case IMAGE_FILE_MACHINE_RISCV64:
    {
      return UeMachineRiscV64;
    }

    case IMAGE_FILE_MACHINE_RISCV128:
    {
      return UeMachineRiscV128;
    }

    default:
    {
      DEBUG_RAISE ();
      return -1;
    }
  }
}

static
bool
ToolImageEmitUeSegments (
  image_tool_dynamic_buffer      *Buffer,
  const image_tool_image_info_t  *Image
  )
{
  uint16_t  Index;
  uint32_t  Offset;

  for (Index = 0; Index < Image->SegmentInfo.NumSegments; ++Index) {
    Offset = ImageToolBufferAppend (
               Buffer,
               Image->SegmentInfo.Segments[Index].Data,
               Image->SegmentInfo.Segments[Index].UnpaddedSize
               );
    if (Offset == MAX_UINT32) {
      DEBUG_RAISE ();
      return false;
    }
  }

  Offset = ImageToolBufferAppendReserveAlign (Buffer, UE_LOAD_TABLE_ALIGNMENT);
  return Offset != MAX_UINT32;
}

static
void
ToolImageEmitUePadChainedRelocs (
  const image_tool_image_info_t  *Image
  )
{
  uint16_t                  SegIndex;
  image_tool_segment_t      *Segment;
  uint32_t                  RelocIndex;
  const image_tool_reloc_t  *Reloc;
  uint32_t                  EndOfReloc;
  bool                      HasReloc;
  uint32_t                  LastRelocEnd;
  uint32_t                  EndOfRelocOffset;

  LastRelocEnd = 0;

  RelocIndex = 0;
  for (SegIndex = 0; SegIndex < Image->SegmentInfo.NumSegments; ++SegIndex) {
    Segment = &Image->SegmentInfo.Segments[SegIndex];

    HasReloc = false;
    for ( ; RelocIndex < Image->RelocInfo.NumRelocs; ++RelocIndex) {
      Reloc      = &Image->RelocInfo.Relocs[RelocIndex];
      EndOfReloc = Reloc->Target + ToolImageGetRelocSize (Reloc->Type);

      if (EndOfReloc > Segment->ImageAddress + Segment->ImageSize) {
        break;
      }

      HasReloc     = true;
      LastRelocEnd = EndOfReloc;
    }

    if (HasReloc) {
      assert (Segment->ImageAddress <= LastRelocEnd);
      EndOfRelocOffset = LastRelocEnd - Segment->ImageAddress;

      if (Segment->UnpaddedSize < EndOfRelocOffset) {
        Segment->UnpaddedSize = EndOfRelocOffset;
      }
    }
  }
}

static
uint32_t
ToolImageEmitUeGetFileOffset (
  const image_tool_dynamic_buffer  *Buffer,
  uint32_t                         SegmentHeadersOffset,
  uint32_t                         SegmentsOffset,
  uint16_t                         NumSegments,
  uint32_t                         Address,
  uint32_t                         *Size
  )
{
  CONST UE_SEGMENT  *Segments;
  uint16_t          Index;
  uint32_t          SegmentAddress;
  uint32_t          SegmentSize;
  uint32_t          SegmentOffset;
  uint32_t          OffsetInSegment;

  Segments = ImageToolBufferGetPointer (Buffer, SegmentHeadersOffset);

  SegmentAddress = 0;
  SegmentOffset  = SegmentsOffset;
  for (
       Index = 0;
       // LCOV_EXCL_START
       Index < NumSegments;
       // LCOV_EXCL_STOP
       ++Index
       )
  {
    // LCOV_EXCL_START
    if (SegmentAddress > Address) {
      break;
    }

    // LCOV_EXCL_STOP

    SegmentSize     = UE_SEGMENT_SIZE (Segments[Index].ImageInfo);
    OffsetInSegment = Address - SegmentAddress;
    if (OffsetInSegment < SegmentSize) {
      assert (OffsetInSegment < Segments[Index].FileSize);
      *Size = Segments[Index].FileSize - OffsetInSegment;
      return SegmentOffset + OffsetInSegment;
    }

    SegmentAddress += SegmentSize;
    SegmentOffset  += Segments[Index].FileSize;
  }

  // LCOV_EXCL_START
  assert (false);
  return MAX_UINT32;
  // LCOV_EXCL_STOP
}

static
bool
ToolImageEmitUeRelocTable (
  image_tool_dynamic_buffer      *Buffer,
  uint32_t                       LoadTableOffset,
  uint32_t                       SegmentHeadersOffset,
  uint32_t                       SegmentsOffset,
  const image_tool_image_info_t  *Image,
  bool                           Chaining
  )
{
  uint32_t  RelocTableOffset;
  uint32_t  RelocTableSize;

  UE_FIXUP_ROOT  RelocRoot;

  uint32_t  EntryFileOffset;
  uint32_t  PrevEntryFileOffset;

  uint8_t   RelocType;
  uint32_t  RelocTarget;
  uint32_t  RelocFileOffset;
  uint64_t  RelocValue;
  uint8_t   RelocSize;

  uint32_t  RelocOffset;

  uint64_t  ChainRelocInfo;
  uint32_t  ChainRelocInfo32;

  uint8_t   PrevRelocType;
  uint32_t  PrevRelocTarget;
  uint32_t  PrevRelocFileOffset;
  uint64_t  PrevRelocValue;
  uint8_t   PrevRelocSize;

  uint64_t  PrevChainRelocInfo;
  uint32_t  PrevChainRelocInfo32;

  bool  ChainInProgress;
  bool  ChainSupported;

  uint16_t  Fixup;

  UE_LOAD_TABLE  LoadTable;

  uint32_t  Index;
  uint32_t  RemainingSize;
  uint32_t  Offset;

  assert (Image->RelocInfo.NumRelocs > 0);

  ChainInProgress = false;

  RelocTableOffset = ImageToolBufferGetSize (Buffer);
  assert (IS_ALIGNED (RelocTableOffset, UE_LOAD_TABLE_ALIGNMENT));

  PrevRelocType       = 0;
  PrevRelocTarget     = 0;
  PrevRelocFileOffset = 0;
  PrevRelocValue      = 0;
  PrevRelocSize       = 0;

  EntryFileOffset     = 0;
  PrevEntryFileOffset = 0;

  for (
       Index = 0;
       Index < Image->RelocInfo.NumRelocs;
       ++Index,
       PrevRelocType       = RelocType,
       PrevRelocTarget     = RelocTarget,
       PrevRelocFileOffset = RelocFileOffset,
       PrevRelocValue      = RelocValue,
       PrevRelocSize       = RelocSize,
       PrevEntryFileOffset = EntryFileOffset
       )
  {
    //
    // Get current UE relocation fixup info.
    //

    RelocTarget = Image->RelocInfo.Relocs[Index].Target;

    RelocFileOffset = ToolImageEmitUeGetFileOffset (
                        Buffer,
                        SegmentHeadersOffset,
                        SegmentsOffset,
                        Image->SegmentInfo.NumSegments,
                        RelocTarget,
                        &RemainingSize
                        );
    assert (RelocFileOffset != MAX_UINT32);

    // LCOV_EXCL_START
    switch (Image->RelocInfo.Relocs[Index].Type) {
      // LCOV_EXCL_STOP
      case EFI_IMAGE_REL_BASED_HIGHLOW:
      {
        RelocSize      = sizeof (UINT32);
        RelocType      = UeReloc32;
        ChainSupported = Chaining;
        break;
      }

      case EFI_IMAGE_REL_BASED_DIR64:
      {
        RelocSize      = sizeof (UINT64);
        RelocType      = UeReloc64;
        ChainSupported = Chaining;
        break;
      }

      // LCOV_EXCL_START
      default:
      {
        assert (false);
        return false;
      }
        // LCOV_EXCL_STOP
    }

    // LCOV_EXCL_START
    if (RemainingSize < RelocSize) {
      assert (false);
      return false;
    }

    // LCOV_EXCL_STOP

    assert (RelocSize <= sizeof (RelocValue));

    RelocValue = 0;
    ImageToolBufferRead (&RelocValue, RelocSize, Buffer, RelocFileOffset);

    assert (RelocTarget >= (PrevRelocTarget + PrevRelocSize));
    RelocOffset = RelocTarget - (PrevRelocTarget + PrevRelocSize);

    //
    // Handle UE relocation fixup chaining.
    //

    if (ChainInProgress) {
      ChainInProgress = ChainSupported && (RelocOffset <= UE_CHAINED_RELOC_FIXUP_MAX_OFFSET) && (PrevRelocType == RelocType);

      if (ChainInProgress && (RelocType == UeReloc32)) {
        ChainRelocInfo32  = UE_CHAINED_RELOC_FIXUP_OFFSET_END;
        ChainRelocInfo32 |= RelocValue << UE_CHAINED_RELOC_FIXUP_VALUE_32_SHIFT;
        if ((ChainRelocInfo32 >> UE_CHAINED_RELOC_FIXUP_VALUE_32_SHIFT) != RelocValue) {
          ChainInProgress = false;
          ChainSupported  = false;
          RelocType       = UeReloc32NoMeta;
        }
      }

      if (ChainInProgress && (RelocType == UeReloc64)) {
        PrevChainRelocInfo  = RelocType;
        PrevChainRelocInfo |= RelocOffset << 4U;
        PrevChainRelocInfo |= PrevRelocValue << 16U;
        assert (UE_CHAINED_RELOC_FIXUP_NEXT_OFFSET (PrevChainRelocInfo) == RelocOffset);
        assert (UE_CHAINED_RELOC_FIXUP_NEXT_TYPE (PrevChainRelocInfo) == RelocType);
        assert (UE_CHAINED_RELOC_FIXUP_VALUE (PrevChainRelocInfo) == PrevRelocValue);

        assert (PrevRelocSize <= sizeof (PrevChainRelocInfo));

        ImageToolBufferWrite (
          Buffer,
          PrevRelocFileOffset,
          &PrevChainRelocInfo,
          PrevRelocSize
          );
      } else if (ChainInProgress && (RelocType == UeReloc32)) {
        PrevChainRelocInfo32  = RelocOffset;
        PrevChainRelocInfo32 |= PrevRelocValue << UE_CHAINED_RELOC_FIXUP_VALUE_32_SHIFT;

        assert (PrevRelocSize <= sizeof (PrevChainRelocInfo32));

        ImageToolBufferWrite (
          Buffer,
          PrevRelocFileOffset,
          &PrevChainRelocInfo32,
          PrevRelocSize
          );
      }
    }

    if (ChainSupported && (RelocType == UeReloc64)) {
      ChainRelocInfo  = UE_CHAINED_RELOC_FIXUP_OFFSET_END << 4U;
      ChainRelocInfo |= RelocValue << 16U;
      if ((ChainRelocInfo >> 16U) != RelocValue) {
        DEBUG_RAISE ();
        return false;
      }

      assert (UE_CHAINED_RELOC_FIXUP_NEXT_OFFSET (ChainRelocInfo) == UE_CHAINED_RELOC_FIXUP_OFFSET_END);
      assert (UE_CHAINED_RELOC_FIXUP_NEXT_TYPE (ChainRelocInfo) == 0);
      assert (UE_CHAINED_RELOC_FIXUP_VALUE (ChainRelocInfo) == RelocValue);

      assert (RelocSize <= sizeof (ChainRelocInfo));

      ImageToolBufferWrite (
        Buffer,
        RelocFileOffset,
        &ChainRelocInfo,
        RelocSize
        );

      if (ChainInProgress) {
        continue;
      }

      ChainInProgress = true;
    } else if (ChainSupported && (RelocType == UeReloc32)) {
      ChainRelocInfo32  = UE_CHAINED_RELOC_FIXUP_OFFSET_END;
      ChainRelocInfo32 |= RelocValue << UE_CHAINED_RELOC_FIXUP_VALUE_32_SHIFT;
      if ((ChainRelocInfo32 >> UE_CHAINED_RELOC_FIXUP_VALUE_32_SHIFT) != RelocValue) {
        ChainInProgress = false;
        ChainSupported  = false;
        RelocType       = UeReloc32NoMeta;
      } else {
        assert (RelocSize <= sizeof (ChainRelocInfo32));

        ImageToolBufferWrite (
          Buffer,
          RelocFileOffset,
          &ChainRelocInfo32,
          RelocSize
          );

        if (ChainInProgress) {
          continue;
        }

        ChainInProgress = true;
      }
    }

    if ((Index > 0) && (RelocOffset <= UE_HEAD_FIXUP_MAX_OFFSET)) {
      Fixup  = PrevRelocType;
      Fixup |= RelocOffset << 4U;
      assert (UE_RELOC_FIXUP_TYPE (Fixup) == PrevRelocType);
      assert (UE_RELOC_FIXUP_OFFSET (Fixup) == RelocOffset);

      ImageToolBufferWrite (
        Buffer,
        PrevEntryFileOffset,
        &Fixup,
        sizeof (Fixup)
        );
    } else {
      Offset = ImageToolBufferAppendReserveAlign (
                 Buffer,
                 UE_FIXUP_ROOT_ALIGNMENT
                 );
      if (Offset == MAX_UINT32) {
        DEBUG_RAISE ();
        return false;
      }

      RelocRoot.FirstOffset = RelocOffset;

      Offset = ImageToolBufferAppend (Buffer, &RelocRoot, sizeof (RelocRoot));
      if (Offset == MAX_UINT32) {
        DEBUG_RAISE ();
        return false;
      }
    }

    Fixup  = RelocType;
    Fixup |= UE_HEAD_FIXUP_OFFSET_END << 4U;
    assert (UE_RELOC_FIXUP_TYPE (Fixup) == RelocType);
    assert (UE_RELOC_FIXUP_OFFSET (Fixup) == UE_HEAD_FIXUP_OFFSET_END);

    EntryFileOffset = ImageToolBufferAppend (Buffer, &Fixup, sizeof (Fixup));
    if (EntryFileOffset == MAX_UINT32) {
      DEBUG_RAISE ();
      return false;
    }
  }

  Offset = ImageToolBufferAppendReserveAlign (Buffer, UE_LOAD_TABLE_ALIGNMENT);
  if (Offset == MAX_UINT32) {
    DEBUG_RAISE ();
    return false;
  }

  RelocTableSize = ImageToolBufferGetSize (Buffer) - RelocTableOffset;

  LoadTable.FileInfo  = RelocTableSize >> 3U;
  LoadTable.FileInfo |= UeLoadTableIdReloc << 29U;
  assert (UE_LOAD_TABLE_ID (LoadTable.FileInfo) == UeLoadTableIdReloc);
  assert (UE_LOAD_TABLE_SIZE (LoadTable.FileInfo) == RelocTableSize);

  ImageToolBufferWrite (
    Buffer,
    LoadTableOffset,
    &LoadTable,
    sizeof (LoadTable)
    );

  return true;
}

static
bool
ToolImageEmitUeDebugTable (
  image_tool_dynamic_buffer      *Buffer,
  uint32_t                       LoadTableOffset,
  const image_tool_image_info_t  *Image,
  uint32_t                       BaseAddressSubtrahend
  )
{
  UE_DEBUG_TABLE   DebugTable;
  uint8_t          SymSubtrahendFactor;
  uint32_t         DebugTableOffset;
  uint32_t         DebugTableSize;
  uint16_t         Index;
  UE_SEGMENT_NAME  SegmentName;
  UE_LOAD_TABLE    LoadTable;
  uint32_t         Offset;

  assert (Image->DebugInfo.SymbolsPathLen <= MAX_UINT8);
  assert (IS_ALIGNED (BaseAddressSubtrahend, Image->SegmentInfo.SegmentAlignment));

  SymSubtrahendFactor = (uint8_t)(BaseAddressSubtrahend / Image->SegmentInfo.SegmentAlignment);
  if (SymSubtrahendFactor > 0x03) {
    DEBUG_RAISE ();
    return false;
  }

  DebugTable.ImageInfo = SymSubtrahendFactor;
  assert (UE_DEBUG_TABLE_IMAGE_INFO_SYM_SUBTRAHEND_FACTOR (DebugTable.ImageInfo) == SymSubtrahendFactor);
  assert ((DebugTable.ImageInfo & 0xFCU) == 0);

  DebugTable.SymbolsPathLength = (uint8_t)Image->DebugInfo.SymbolsPathLen;

  DebugTableOffset = ImageToolBufferAppend (
                       Buffer,
                       &DebugTable,
                       sizeof (DebugTable)
                       );
  if (DebugTableOffset == MAX_UINT32) {
    DEBUG_RAISE ();
    return false;
  }

  assert (IS_ALIGNED (DebugTableOffset, UE_LOAD_TABLE_ALIGNMENT));

  //
  // Currently, this condition is always TRUE. However, it is not clear whether
  // a debug table cannot make sense when debug symbols are stripped.
  //
  assert (Image->DebugInfo.SymbolsPath != NULL);

  Offset = ImageToolBufferAppend (
             Buffer,
             Image->DebugInfo.SymbolsPath,
             Image->DebugInfo.SymbolsPathLen + 1
             );
  if (Offset == MAX_UINT32) {
    DEBUG_RAISE ();
    return false;
  }

  for (Index = 0; Index < Image->SegmentInfo.NumSegments; ++Index) {
    memset (&SegmentName, 0, sizeof (SegmentName));
    strncpy (
      (char *)SegmentName,
      Image->SegmentInfo.Segments[Index].Name,
      sizeof (SegmentName)
      );
    SegmentName[ARRAY_SIZE (SegmentName) - 1] = 0;

    Offset = ImageToolBufferAppend (Buffer, SegmentName, sizeof (SegmentName));
    if (Offset == MAX_UINT32) {
      DEBUG_RAISE ();
      return false;
    }
  }

  Offset = ImageToolBufferAppendReserveAlign (Buffer, UE_LOAD_TABLE_ALIGNMENT);
  if (Offset == MAX_UINT32) {
    DEBUG_RAISE ();
    return false;
  }

  DebugTableSize = ImageToolBufferGetSize (Buffer) - DebugTableOffset;

  LoadTable.FileInfo  = DebugTableSize >> 3U;
  LoadTable.FileInfo |= UeLoadTableIdDebug << 29U;
  assert (UE_LOAD_TABLE_ID (LoadTable.FileInfo) == UeLoadTableIdDebug);
  assert (UE_LOAD_TABLE_SIZE (LoadTable.FileInfo) == DebugTableSize);

  ImageToolBufferWrite (
    Buffer,
    LoadTableOffset,
    &LoadTable,
    sizeof (LoadTable)
    );

  return true;
}

static
bool
ToolImageEmitUeLoadTables (
  image_tool_dynamic_buffer      *Buffer,
  uint32_t                       LoadTablesOffset,
  uint32_t                       SegmentHeadersOffset,
  uint32_t                       SegmentsOffset,
  const image_tool_image_info_t  *Image,
  uint32_t                       BaseAddressSubtrahend,
  bool                           Chaining
  )
{
  bool  Success;

  if (ToolImageUeRelocTableRequired (Image)) {
    Success = ToolImageEmitUeRelocTable (
                Buffer,
                LoadTablesOffset,
                SegmentHeadersOffset,
                SegmentsOffset,
                Image,
                Chaining
                );
    if (!Success) {
      DEBUG_RAISE ();
      return false;
    }

    LoadTablesOffset += sizeof (UE_LOAD_TABLE);
  }

  if (ToolImageUeDebugTableRequired (Image)) {
    Success = ToolImageEmitUeDebugTable (
                Buffer,
                LoadTablesOffset,
                Image,
                BaseAddressSubtrahend
                );
    if (!Success) {
      DEBUG_RAISE ();
      return false;
    }
  }

  return true;
}

static
bool
ToolImageStripEmptyPrefix (
  uint32_t                 *BaseAddressSubtrahend,
  image_tool_image_info_t  *Image
  )
{
  bool      Success;
  uint32_t  Subtrahend;
  uint32_t  Index;

  if (Image->RelocInfo.RelocsStripped) {
    DEBUG_RAISE ();
    return false;
  }

  Subtrahend = Image->SegmentInfo.Segments[0].ImageAddress;

  Success = ToolImageRelocate (
              Image,
              Image->HeaderInfo.BaseAddress - Subtrahend,
              Subtrahend
              );
  // LCOV_EXCL_START
  if (!Success) {
    DEBUG_RAISE ();
    return false;
  }

  // LCOV_EXCL_STOP

  Image->HeaderInfo.BaseAddress += Subtrahend;

  Image->HeaderInfo.EntryPointAddress -= Subtrahend;

  for (Index = 0; Index < Image->SegmentInfo.NumSegments; ++Index) {
    Image->SegmentInfo.Segments[Index].ImageAddress -= Subtrahend;
  }

  for (Index = 0; Index < Image->RelocInfo.NumRelocs; ++Index) {
    Image->RelocInfo.Relocs[Index].Target -= Subtrahend;
  }

  *BaseAddressSubtrahend = Subtrahend;

  return true;
}

static
bool
ToolImageEmitUeFile (
  image_tool_dynamic_buffer      *Buffer,
  const image_tool_image_info_t  *Image,
  uint32_t                       BaseAddressSubtrahend
  )
{
  bool       Success;
  UE_HEADER  UeHdr;
  uint8_t    AlignmentExponent;
  int8_t     Machine;
  uint8_t    Subsystem;
  uint8_t    LastSegmentIndex;
  uint8_t    NumLoadTables;
  uint32_t   Offset;
  bool       Chaining;
  uint32_t   SegmentHeadersOffset;
  uint32_t   LoadTablesOffset;
  uint32_t   SegmentsOffset;

  assert (Image->SegmentInfo.NumSegments > 0);

  if (Image->SegmentInfo.NumSegments > UE_HEADER_NUM_SEGMENTS_MAX) {
    DEBUG_RAISE ();
    return false;
  }

  if (Image->HiiInfo.DataSize > 0) {
    DEBUG_RAISE ();
    return false;
  }

  AlignmentExponent = AlignmentToExponent (Image->SegmentInfo.SegmentAlignment);
  if ((12 > AlignmentExponent) || (AlignmentExponent > 27)) {
    DEBUG_RAISE ();
    return false;
  }

  Machine = InternalGetUeMachine (Image->HeaderInfo.Machine);
  if (Machine < 0) {
    DEBUG_RAISE ();
    return false;
  }

  NumLoadTables  = ToolImageUeRelocTableRequired (Image) ? 1U : 0U;
  NumLoadTables += ToolImageUeDebugTableRequired (Image) ? 1U : 0U;

  Subsystem        = (uint8_t)(Image->HeaderInfo.Subsystem - 10U);
  LastSegmentIndex = (uint8_t)(Image->SegmentInfo.NumSegments - 1U);

  Chaining = Image->HeaderInfo.BaseAddress == 0 &&
             !Image->HeaderInfo.FixedAddress;

  UeHdr.Magic = UE_HEADER_MAGIC;

  UeHdr.Type = (Machine << 3U) | Subsystem;
  assert (UE_HEADER_SUBSYSTEM (UeHdr.Type) == Subsystem);
  assert (UE_HEADER_ARCH (UeHdr.Type) == Machine);

  UeHdr.TableCounts  = NumLoadTables;
  UeHdr.TableCounts |= LastSegmentIndex << 3U;
  assert (UE_HEADER_LAST_SEGMENT_INDEX (UeHdr.TableCounts) == LastSegmentIndex);
  assert (UE_HEADER_NUM_LOAD_TABLES (UeHdr.TableCounts) == NumLoadTables);

  UeHdr.EntryPointAddress = Image->HeaderInfo.EntryPointAddress;

  UeHdr.ImageInfo  = Image->HeaderInfo.BaseAddress >> 12ULL;
  UeHdr.ImageInfo |= (uint64_t)Image->HeaderInfo.FixedAddress << 57ULL;
  UeHdr.ImageInfo |= (uint64_t)Image->RelocInfo.RelocsStripped << 58ULL;
  UeHdr.ImageInfo |= (uint64_t)Chaining << 59ULL;
  UeHdr.ImageInfo |= (uint64_t)(AlignmentExponent - 12U) << 60ULL;
  assert (UE_HEADER_BASE_ADDRESS (UeHdr.ImageInfo) == Image->HeaderInfo.BaseAddress);
  assert ((UeHdr.ImageInfo & (0x1FULL << 52ULL)) == 0);
  assert (((UeHdr.ImageInfo & UE_HEADER_IMAGE_INFO_FIXED_ADDRESS) != 0) == Image->HeaderInfo.FixedAddress);
  assert (((UeHdr.ImageInfo & UE_HEADER_IMAGE_INFO_RELOCATION_FIXUPS_STRIPPED) != 0) == Image->RelocInfo.RelocsStripped);
  assert (((UeHdr.ImageInfo & UE_HEADER_IMAGE_INFO_CHAINED_FIXUPS) != 0) == Chaining);
  assert (UE_HEADER_SEGMENT_ALIGNMENT (UeHdr.ImageInfo) == Image->SegmentInfo.SegmentAlignment);

  Offset = ImageToolBufferAppend (Buffer, &UeHdr, sizeof (UeHdr));
  if (Offset == MAX_UINT32) {
    DEBUG_RAISE ();
    return false;
  }

  SegmentHeadersOffset = ImageToolBufferGetSize (Buffer);

  Success = ToolImageEmitUeSegmentHeaders (Buffer, Image, false);
  if (!Success) {
    DEBUG_RAISE ();
    return false;
  }

  LoadTablesOffset = ImageToolBufferAppendReserve (
                       Buffer,
                       NumLoadTables * sizeof (UE_LOAD_TABLE)
                       );
  if (LoadTablesOffset == MAX_UINT32) {
    DEBUG_RAISE ();
    return false;
  }

  SegmentsOffset = ImageToolBufferGetSize (Buffer);

  Success = ToolImageEmitUeSegments (Buffer, Image);
  if (!Success) {
    DEBUG_RAISE ();
    return false;
  }

  Success = ToolImageEmitUeLoadTables (
              Buffer,
              LoadTablesOffset,
              SegmentHeadersOffset,
              SegmentsOffset,
              Image,
              BaseAddressSubtrahend,
              Chaining
              );
  if (!Success) {
    DEBUG_RAISE ();
    return false;
  }

  return true;
}

// FIXME: Find a better solution. Separate metadata storage?
static
bool
ToolImageEmitUeXipFile (
  image_tool_dynamic_buffer  *Buffer,
  image_tool_image_info_t    *Image,
  bool                       Strip
  )
{
  bool       Success;
  UE_HEADER  UeHdr;
  uint8_t    AlignmentExponent;
  int8_t     Machine;
  uint8_t    Subsystem;
  uint8_t    LastSegmentIndex;
  uint8_t    NumLoadTables;
  uint32_t   Offset;
  uint16_t   Index;
  uint32_t   SegmentHeadersOffset;
  uint32_t   LoadTablesOffset;
  uint32_t   SegmentsOffset;

  assert (Image->SegmentInfo.NumSegments > 0);

  if (Image->SegmentInfo.NumSegments > UE_HEADER_NUM_SEGMENTS_MAX) {
    DEBUG_RAISE ();
    return false;
  }

  if (Image->HiiInfo.DataSize > 0) {
    DEBUG_RAISE ();
    return false;
  }

  AlignmentExponent = AlignmentToExponent (Image->SegmentInfo.SegmentAlignment);
  if ((12 > AlignmentExponent) || (AlignmentExponent > 27)) {
    DEBUG_RAISE ();
    return false;
  }

  Machine = InternalGetUeMachine (Image->HeaderInfo.Machine);
  if (Machine < 0) {
    DEBUG_RAISE ();
    return false;
  }

  NumLoadTables    = (!Strip && ToolImageUeRelocTableRequired (Image)) ? 1U : 0U;
  Subsystem        = (uint8_t)(Image->HeaderInfo.Subsystem - 10U);
  LastSegmentIndex = (uint8_t)(Image->SegmentInfo.NumSegments - 1U);

  UeHdr.Magic = UE_HEADER_MAGIC;

  UeHdr.Type = (Machine << 3U) | Subsystem;
  assert (UE_HEADER_SUBSYSTEM (UeHdr.Type) == Subsystem);
  assert (UE_HEADER_ARCH (UeHdr.Type) == Machine);

  UeHdr.TableCounts  = NumLoadTables;
  UeHdr.TableCounts |= LastSegmentIndex << 3U;
  assert (UE_HEADER_LAST_SEGMENT_INDEX (UeHdr.TableCounts) == LastSegmentIndex);
  assert (UE_HEADER_NUM_LOAD_TABLES (UeHdr.TableCounts) == NumLoadTables);

  UeHdr.ImageInfo  = Image->HeaderInfo.BaseAddress >> 12ULL;
  UeHdr.ImageInfo |= UE_HEADER_IMAGE_INFO_XIP;
  UeHdr.ImageInfo |= (uint64_t)Image->HeaderInfo.FixedAddress << 57ULL;
  UeHdr.ImageInfo |= (uint64_t)Strip << 58ULL;
  UeHdr.ImageInfo |= (uint64_t)(AlignmentExponent - 12U) << 60ULL;
  assert (UE_HEADER_BASE_ADDRESS (UeHdr.ImageInfo) == Image->HeaderInfo.BaseAddress);
  assert ((UeHdr.ImageInfo & (0xFULL << 52ULL)) == 0);
  assert (((UeHdr.ImageInfo & UE_HEADER_IMAGE_INFO_FIXED_ADDRESS) != 0) == Image->HeaderInfo.FixedAddress);
  assert (((UeHdr.ImageInfo & UE_HEADER_IMAGE_INFO_RELOCATION_FIXUPS_STRIPPED) != 0) == Strip);
  assert (((UeHdr.ImageInfo & UE_HEADER_IMAGE_INFO_CHAINED_FIXUPS) != 0) == FALSE);
  assert (((UeHdr.ImageInfo & UE_HEADER_IMAGE_INFO_XIP) != 0) == TRUE);
  assert (UE_HEADER_SEGMENT_ALIGNMENT (UeHdr.ImageInfo) == Image->SegmentInfo.SegmentAlignment);

  Offset = ImageToolBufferAppendReserve (Buffer, sizeof (UeHdr));
  if (Offset == MAX_UINT32) {
    DEBUG_RAISE ();
    return false;
  }

  SegmentHeadersOffset = ImageToolBufferGetSize (Buffer);

  Success = ToolImageEmitUeSegmentHeaders (Buffer, Image, true);
  if (!Success) {
    DEBUG_RAISE ();
    return false;
  }

  LoadTablesOffset = ImageToolBufferAppendReserve (
                       Buffer,
                       NumLoadTables * sizeof (UE_LOAD_TABLE)
                       );
  if (LoadTablesOffset == MAX_UINT32) {
    DEBUG_RAISE ();
    return false;
  }

  Offset = ImageToolBufferAppendReserveAlign (
             Buffer,
             Image->SegmentInfo.SegmentAlignment
             );
  if (Offset == MAX_UINT32) {
    DEBUG_RAISE ();
    return false;
  }

  SegmentsOffset = ImageToolBufferGetSize (Buffer);

  UeHdr.EntryPointAddress = Image->HeaderInfo.EntryPointAddress + SegmentsOffset;
  ImageToolBufferWrite (Buffer, 0, &UeHdr, sizeof (UeHdr));

  Success = ToolImageRelocate (Image, Image->HeaderInfo.BaseAddress + SegmentsOffset, 0);
  if (!Success) {
    DEBUG_RAISE ();
    return false;
  }

  for (Index = 0; Index < Image->SegmentInfo.NumSegments; ++Index) {
    Offset = ImageToolBufferAppend (
               Buffer,
               Image->SegmentInfo.Segments[Index].Data,
               Image->SegmentInfo.Segments[Index].UnpaddedSize
               );
    if (Offset == MAX_UINT32) {
      DEBUG_RAISE ();
      return false;
    }

    Offset = ImageToolBufferAppendReserve (
               Buffer,
               Image->SegmentInfo.Segments[Index].ImageSize - Image->SegmentInfo.Segments[Index].UnpaddedSize
               );
    if (Offset == MAX_UINT32) {
      DEBUG_RAISE ();
      return false;
    }
  }

  if (!Strip && ToolImageUeRelocTableRequired (Image)) {
    Success = ToolImageEmitUeRelocTable (
                Buffer,
                LoadTablesOffset,
                SegmentHeadersOffset,
                SegmentsOffset,
                Image,
                false
                );
    if (!Success) {
      DEBUG_RAISE ();
      return false;
    }
  }

  return true;
}

void *
ToolImageEmitUe (
  image_tool_image_info_t  *Image,
  uint32_t                 *FileSize,
  bool                     Xip,
  bool                     Strip
  )
{
  bool                       Success;
  image_tool_dynamic_buffer  Buffer;
  uint32_t                   BaseAddressSubtrahend;
  void                       *FileBuffer;

  ImageToolBufferInit (&Buffer);

  ImageInitUnpaddedSize (Image);
  ToolImageEmitUePadChainedRelocs (Image);

  if (Xip) {
    Success = ToolImageEmitUeXipFile (&Buffer, Image, Strip);
  } else {
    Success = ToolImageStripEmptyPrefix (&BaseAddressSubtrahend, Image);
    if (!Success) {
      DEBUG_RAISE ();
      return NULL;
    }

    if (Strip) {
      ToolImageStripRelocs (Image);
    }

    Success = ToolImageEmitUeFile (&Buffer, Image, BaseAddressSubtrahend);
  }

  if (!Success) {
    DEBUG_RAISE ();
    ImageToolBufferFree (&Buffer);
    return NULL;
  }

  FileBuffer = ImageToolBufferDump (FileSize, &Buffer);

  ImageToolBufferFree (&Buffer);

  if (FileBuffer == NULL) {
    DEBUG_RAISE ();
    return NULL;
  }

  return FileBuffer;
}
