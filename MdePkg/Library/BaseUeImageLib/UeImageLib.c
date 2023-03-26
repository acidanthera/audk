/** @file
  UEFI Image Loader library implementation for UE Images.

  Copyright (c) 2021, Marvin Häuser. All rights reserved.<BR>

  SPDX-License-Identifier: BSD-3-Clause
**/

#include <Base.h>

#include <IndustryStandard/UeImage.h>

#include <Library/BaseLib.h>
#include <Library/BaseMemoryLib.h>
#include <Library/BaseOverflowLib.h>
#include <Library/DebugLib.h>
#include <Library/PcdLib.h>
#include <Library/UefiImageLib.h>
#include <Library/UeImageLib.h>

VOID
ThumbMovwMovtImmediateFixup (
  IN OUT VOID    *Fixup,
  IN     UINT64  Adjust
  );

STATIC
RETURN_STATUS
InternalVerifySegments (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  CONST UE_SEGMENT *Segments;
  UINT8            LastSegmentIndex;
  UINT8            SegmentIndex;
  UINT32           SegmentEndFileOffset;
  UINT32           SegmentEndImageAddress;
  BOOLEAN          Overflow;
  UINT32           SegmentImageSize;

  Segments         = Context->Segments;
  LastSegmentIndex = Context->LastSegmentIndex;

  SegmentEndFileOffset = Context->SegmentsFileOffset;
  //
  // The first Image segment must begin the Image memory space.
  //
  SegmentEndImageAddress = 0;

  for (SegmentIndex = 0; SegmentIndex <= LastSegmentIndex; ++SegmentIndex) {
    //
    // Verify the Image segment adheres to the W^X principle.
    //
    if ((Segments[SegmentIndex].ImageInfo & (UE_SEGMENT_INFO_XP | UE_SEGMENT_INFO_RO)) == 0) {
      DEBUG_RAISE ();
      return RETURN_UNSUPPORTED;
    }

    SegmentImageSize = UE_SEGMENT_SIZE (Segments[SegmentIndex].ImageInfo);

    if (Segments[SegmentIndex].FileSize > SegmentImageSize) {
      DEBUG_RAISE ();
      return RETURN_UNSUPPORTED;
    }
    //
    // Verify the Image segments are aligned and adjacent.
    //
    if (!IS_ALIGNED (SegmentImageSize, Context->SegmentAlignment)) {
      DEBUG_RAISE ();
      return RETURN_UNSUPPORTED;
    }
    //
    // Verify the Image segment with data are in bounds of the file buffer.
    //
    Overflow = BaseOverflowAddU32 (
                 SegmentEndFileOffset,
                 Segments[SegmentIndex].FileSize,
                 &SegmentEndFileOffset
                 );
    if (Overflow) {
      DEBUG_RAISE ();
      return RETURN_UNSUPPORTED;
    }
    //
    // Determine the end of the current Image segment.
    //
    Overflow = BaseOverflowAddU32 (
                 SegmentEndImageAddress,
                 SegmentImageSize,
                 &SegmentEndImageAddress
                 );
    if (Overflow) {
      DEBUG_RAISE ();
      return RETURN_UNSUPPORTED;
    }
  }

  if (SegmentEndFileOffset > Context->UnsignedFileSize) {
    DEBUG_RAISE ();
    return RETURN_UNSUPPORTED;
  }

  Overflow = BaseOverflowAlignUpU32 (
               SegmentEndFileOffset,
               UE_SECTION_ALIGNMENT,
               &Context->SectionsFileOffset
               );
  if (Overflow) {
    DEBUG_RAISE ();
    return RETURN_UNSUPPORTED;
  }

  Context->ImageSize = SegmentEndImageAddress;

  return RETURN_SUCCESS;
}

STATIC
RETURN_STATUS
InternalVerifySegmentsXip (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  CONST UE_SEGMENT_XIP *Segments;
  UINT8                LastSegmentIndex;
  UINT8                SegmentIndex;
  UINT32               SegmentEndImageAddress;
  BOOLEAN              Overflow;
  UINT32               SegmentImageSize;

  Segments         = Context->Segments;
  LastSegmentIndex = Context->LastSegmentIndex;
  //
  // The first Image segment must begin the Image memory space.
  //
  SegmentEndImageAddress = 0;

  for (SegmentIndex = 0; SegmentIndex <= LastSegmentIndex; ++SegmentIndex) {
    //
    // Verify the Image segment adheres to the W^X principle.
    //
    if ((Segments[SegmentIndex].ImageInfo & (UE_SEGMENT_INFO_XP | UE_SEGMENT_INFO_RO)) == 0) {
      DEBUG_RAISE ();
      return RETURN_UNSUPPORTED;
    }

    SegmentImageSize = UE_SEGMENT_SIZE (Segments[SegmentIndex].ImageInfo);
    //
    // Verify the Image segments are aligned and adjacent.
    //
    if (!IS_ALIGNED (SegmentImageSize, Context->SegmentAlignment)) {
      DEBUG_RAISE ();
      return RETURN_UNSUPPORTED;
    }
    //
    // Determine the end of the current Image segment.
    //
    Overflow = BaseOverflowAddU32 (
                 SegmentEndImageAddress,
                 SegmentImageSize,
                 &SegmentEndImageAddress
                 );
    if (Overflow) {
      DEBUG_RAISE ();
      return RETURN_UNSUPPORTED;
    }
  }

  Context->ImageSize = SegmentEndImageAddress;

  return RETURN_SUCCESS;
}

RETURN_STATUS
InternalVerifySections (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  BOOLEAN          Overflow;
  CONST UE_SECTION *Section;
  UINT8            SectionIndex;
  //INT16            PreviousSectionId;
  UINT32           SectionFileOffset;
  UINT32           SectionFileSize;
  //UINT8            SectionId;
  UINT32           SectionEndFileOffset;
  //UINT8            SectionIndex2;
  UINT8            NumSections;

  Context->RelocTableSize = 0;

  SectionEndFileOffset = Context->SectionsFileOffset;
  NumSections          = Context->NumSections;
  //PreviousSectionId    = -1;

  if (0 < NumSections) {
    SectionIndex = 0;
    do {
      Section = Context->Sections + SectionIndex;

      DEBUG((DEBUG_ERROR, "Found sect id %u\n", UE_SECTION_ID (Section->FileInfo)));

      //SectionId = UE_SECTION_ID (Section->FileInfo);

      // FIXME: Keep?
      /*if (PcdGetBool (PcdImageLoaderExtendedVerification)) {
        if (PreviousSectionId >= SectIdentifier) {
          DEBUG_RAISE ();
          return RETURN_UNSUPPORTED;
        }

        for (
          SectionIndex2 = SectionIndex + 1;
          SectionIndex2 < NumSections;
          ++SectionIndex2
          ) {
          if (UE_SECTION_ID (Context->Sections[SectionIndex2].FileInfo) == SectIdentifier) {
            DEBUG_RAISE ();
            return RETURN_UNSUPPORTED;
          }
        }
      }*/

      SectionFileOffset = SectionEndFileOffset;
      SectionFileSize   = UE_SECTION_SIZE (Section->FileInfo);

      Overflow = BaseOverflowAddU32 (
                   SectionFileOffset,
                   SectionFileSize,
                   &SectionEndFileOffset
                   );
      if (Overflow) {
        DEBUG_RAISE ();
        return RETURN_UNSUPPORTED;
      }

      //PreviousSectionId = SectionId;
      ++SectionIndex;
    } while (SectionIndex < NumSections);

    if (UE_SECTION_ID (Context->Sections[0].FileInfo) == UeSectionIdRelocTable) {
      if ((Context->ImageInfo & UE_HEADER_FLAG_RELOCS_STRIPPED) != 0) {
        DEBUG_RAISE ();
        return RETURN_UNSUPPORTED;
      }

      Context->RelocTableSize = UE_SECTION_SIZE (Context->Sections[0].FileInfo);
    }
  }

  if (SectionEndFileOffset != Context->UnsignedFileSize) {
    DEBUG_RAISE ();
    return RETURN_UNSUPPORTED;
  }

  return RETURN_SUCCESS;
}

RETURN_STATUS
UeInitializeContextPreHash (
  OUT UE_LOADER_IMAGE_CONTEXT  *Context,
  IN  CONST VOID               *FileBuffer,
  IN  UINT32                   FileSize
  )
{
  BOOLEAN         Overflow;
  CONST UE_HEADER *UeHdr;
  UINT32          UnsignedFileSize;

  ASSERT (Context != NULL);
  ASSERT (FileBuffer != NULL || FileSize == 0);

  if (MIN_SIZE_OF_UE_HEADER > FileSize) {
    DEBUG_RAISE ();
    return RETURN_UNSUPPORTED;
  }

  UeHdr = (CONST UE_HEADER *) FileBuffer;

  if (UeHdr->Signature != UE_HEADER_SIGNATURE) {
    DEBUG_RAISE ();
    return RETURN_UNSUPPORTED;
  }

  ZeroMem (Context, sizeof (*Context));

  UnsignedFileSize = UE_HEADER_UNSIGNED_SIZE (UeHdr->ImageInfo2);

  Overflow = BaseOverflowSubU32 (
               FileSize,
               UnsignedFileSize,
               &Context->CertTableSize
               );
  if (Overflow) {
    DEBUG_RAISE ();
    return RETURN_UNSUPPORTED;
  }

  Context->FileBuffer       = UeHdr;
  Context->UnsignedFileSize = UnsignedFileSize;

  return RETURN_SUCCESS;
}

BOOLEAN
UeHashImageDefault (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context,
  IN OUT VOID                     *HashContext,
  IN     UE_LOADER_HASH_UPDATE    HashUpdate
  )
{
  BOOLEAN Result;

  ASSERT (Context != NULL);
  ASSERT (HashContext != NULL);
  ASSERT (HashUpdate != NULL);

  Result = HashUpdate (
             HashContext,
             Context->FileBuffer,
             Context->UnsignedFileSize
             );
  if (!Result) {
    DEBUG_RAISE ();
  }

  return Result;
}

STATIC
RETURN_STATUS
InternalInitializeContextLate (
  OUT UE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  if (Context->EntryPointAddress > Context->ImageSize) {
    DEBUG_RAISE ();
    return RETURN_UNSUPPORTED;
  }

  return InternalVerifySections (Context);
}

RETURN_STATUS
UeInitializeContextPostHash (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  CONST UE_HEADER *UeHdr;
  UINT32          SectionsFileOffset;
  UINT32          HeaderSize;
  RETURN_STATUS   Status;

  ASSERT (Context != NULL);

  UeHdr = (CONST UE_HEADER *) Context->FileBuffer;

  SectionsFileOffset = MIN_SIZE_OF_UE_HEADER
                         + (UINT32) UeHdr->LastSegmentIndex * sizeof (UE_SEGMENT);

  HeaderSize = SectionsFileOffset + (UINT32) UeHdr->NumSections * sizeof (UE_SECTION);

  if (HeaderSize > Context->UnsignedFileSize) {
    DEBUG_RAISE ();
    return RETURN_UNSUPPORTED;
  }

  ASSERT (IS_ALIGNED (SectionsFileOffset, ALIGNOF (UE_SECTION)));

  Context->Sections = (CONST UE_SECTION *) (CONST VOID *) (
                        (CONST CHAR8 *) UeHdr + SectionsFileOffset
                        );

  Context->SegmentsFileOffset       = HeaderSize;
  Context->Segments                 = UeHdr->Segments;
  Context->SegmentImageInfoIterSize = sizeof (*UeHdr->Segments);
  Context->SegmentAlignment         = UE_HEADER_ALIGNMENT (UeHdr->ImageInfo);

  Context->LastSegmentIndex = UeHdr->LastSegmentIndex;
  Context->NumSections      = UeHdr->NumSections;

  if (!IS_ALIGNED (UeHdr->PreferredAddress, Context->SegmentAlignment)) {
    DEBUG_RAISE ();
    return RETURN_UNSUPPORTED;
  }

  Context->FileBuffer = UeHdr;

  Status = InternalVerifySegments (Context);
  if (RETURN_ERROR (Status)) {
    return Status;
  }

  Context->EntryPointAddress = UeHdr->EntryPointAddress;

  return InternalInitializeContextLate (Context);
}

RETURN_STATUS
UeInitializeContext (
  OUT UE_LOADER_IMAGE_CONTEXT  *Context,
  IN  CONST VOID               *FileBuffer,
  IN  UINT32                   FileSize
  )
{
  RETURN_STATUS Status;

  Status = UeInitializeContextPreHash (Context, FileBuffer, FileSize);
  if (RETURN_ERROR (Status)) {
    return Status;
  }

  return UeInitializeContextPostHash(Context);
}

RETURN_STATUS
UeInitializeContextXip (
  OUT UE_LOADER_IMAGE_CONTEXT  *Context,
  IN  CONST VOID               *XipInfoBuffer,
  IN  UINT32                   XipInfoSize,
  IN  CONST VOID               *XipImageBuffer,
  IN  UINT32                   XipImageSize
  )
{
  CONST UE_HEADER_XIP *UeHdrXip;
  UINT32              SectionHeadersFileOffset;
  UINT32              HeaderSize;
  RETURN_STATUS       Status;

  ASSERT (Context != NULL);
  ASSERT (XipInfoBuffer != NULL || XipInfoSize == 0);
  ASSERT (XipImageBuffer != NULL || XipImageSize == 0);

  if (MIN_SIZE_OF_UE_HEADER_XIP > XipInfoSize) {
    DEBUG_RAISE ();
    return RETURN_UNSUPPORTED;
  }

  UeHdrXip = (CONST UE_HEADER_XIP *) XipInfoBuffer;

  SectionHeadersFileOffset = MIN_SIZE_OF_UE_HEADER_XIP
                               + (UINT32) UeHdrXip->LastSegmentIndex * sizeof (UE_SEGMENT);

  HeaderSize = SectionHeadersFileOffset + (UINT32) UeHdrXip->NumSections * sizeof (UE_SECTION);

  if (HeaderSize > XipInfoSize) {
    DEBUG_RAISE ();
    return RETURN_UNSUPPORTED;
  }

  ASSERT (IS_ALIGNED (SectionHeadersFileOffset, ALIGNOF (UE_SECTION)));

  Context->Sections = (CONST UE_SECTION *) (CONST VOID *) (
                        (CONST CHAR8 *) XipInfoBuffer + SectionHeadersFileOffset
                        );

  Context->SectionsFileOffset = HeaderSize;
  Context->SegmentsFileOffset = HeaderSize;
  Context->Segments           = UeHdrXip->Segments;
  Context->SegmentImageInfoIterSize    = sizeof (*UeHdrXip->Segments);
  Context->SegmentAlignment   = UE_HEADER_ALIGNMENT (UeHdrXip->ImageInfo);

  Context->LastSegmentIndex = UeHdrXip->LastSegmentIndex;
  Context->NumSections      = UeHdrXip->NumSections;

  Context->FileBuffer       = UeHdrXip;
  Context->PreferredAddress = (UINTN) XipImageBuffer;

  Context->UnsignedFileSize = XipInfoSize;

  Status = InternalVerifySegmentsXip (Context);
  if (RETURN_ERROR (Status)) {
    return Status;
  }

  Context->EntryPointAddress = UeHdrXip->EntryPointAddress;

  return InternalInitializeContextLate (Context);
}

RETURN_STATUS
UeLoadImage (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context,
  OUT    VOID                     *Destination,
  IN     UINT32                   DestinationSize
  )
{
  UINT8  SegmentIndex;
  UINT32 SegmentFileOffset;
  UINT32 SegmentFileSize;
  UINT32 SegmentImageAddress;
  UINT32 SegmentImageSize;
  UINT32 PrevSegmentDataEnd;

  CONST UE_SEGMENT *Segments;

  ASSERT (Context != NULL);
  ASSERT (Destination != NULL);
  ASSERT (ADDRESS_IS_ALIGNED (Destination, Context->SegmentAlignment));

  Context->ImageBuffer = Destination;

  //
  // Load all Image sections into the memory space.
  //
  Segments = Context->Segments;

  //
  // Start zeroing from the start of the destination buffer.
  //
  PrevSegmentDataEnd = 0;

  SegmentFileOffset   = Context->SegmentsFileOffset;
  SegmentImageAddress = 0;

  SegmentIndex = 0;
  do {
    SegmentFileSize   = Segments[SegmentIndex].FileSize;
    SegmentImageSize = UE_SEGMENT_SIZE (Segments[SegmentIndex].ImageInfo);
    //
    // Zero from the end of the previous segment to the start of this segment.
    //
    ZeroMem (
      (CHAR8 *) Destination + PrevSegmentDataEnd,
      SegmentImageAddress - PrevSegmentDataEnd
      );
    //
    // Load the current Image segment into the memory space.
    //
    ASSERT (SegmentFileSize <= SegmentImageSize);
    CopyMem (
      (CHAR8 *) Destination + SegmentImageAddress,
      (CONST CHAR8 *) Context->FileBuffer + SegmentFileOffset,
      SegmentFileSize
      );
    PrevSegmentDataEnd = SegmentImageAddress + SegmentFileSize;

    SegmentFileOffset   += SegmentFileSize;
    SegmentImageAddress += SegmentImageSize;
    ++SegmentIndex;
  } while (SegmentIndex <= Context->LastSegmentIndex);
  //
  // Zero the trailing data after the last Image segment.
  //
  ZeroMem (
    (CHAR8 *) Destination + PrevSegmentDataEnd,
    DestinationSize - PrevSegmentDataEnd
    );

  return RETURN_SUCCESS;
}

RETURN_STATUS
UeLoaderGetRuntimeContextSize (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context,
  OUT    UINT32                   *Size
  )
{
  ASSERT (Context != NULL);
  ASSERT (Size != NULL);
  //
  // FIXME: Do we need bookkeeping? Can we prevent relocs to writable segments?
  //
  return Context->RelocTableSize;
}

/**
  Apply an Image Base Relocation.

  Only a subset of the PE/COFF Base Relocation types are permited.
  The Base Relocation target must be in bounds, aligned, and must not overlap
  with the Relocation Directory.

  @param[in] Context     The context describing the Image. Must have been
                         loaded by PeCoffLoadImage().
  @param[in] RelocBlock  The Base Relocation Block to apply from.
  @param[in] RelocIndex  The index of the Base Relocation to apply.
  @param[in] Adjust      The delta to add to the addresses.

  @retval RETURN_SUCCESS  The Base Relocation has been applied successfully.
  @retval other           The Base Relocation could not be applied successfully.
**/
STATIC
RETURN_STATUS
InternalApplyRelocation (
  IN CONST UE_LOADER_IMAGE_CONTEXT  *Context,
  IN CONST UE_RELOCATION_BLOCK      *RelocBlock,
  IN UINT32                         RelocIndex,
  IN UINT64                         Adjust
  )
{
  BOOLEAN Overflow;

  UINT16  RelocType;
  UINT16  RelocOffset;
  UINT32  RelocTargetRva;
  UINT32  RemRelocTargetSize;

  CHAR8   *Fixup;
  UINT32  Fixup32;
  UINT64  Fixup64;

  RelocType   = UE_RELOC_TYPE (RelocBlock->RelocInfo[RelocIndex]);
  RelocOffset = UE_RELOC_OFFSET (RelocBlock->RelocInfo[RelocIndex]);
  //
  // Verify the Base Relocation target address is in bounds of the Image buffer.
  //
  RelocTargetRva = UE_RELOC_BLOCK_ADDRESS (RelocBlock->BlockInfo) + RelocOffset;

  Overflow = BaseOverflowSubU32 (
               Context->ImageSize,
               RelocTargetRva,
               &RemRelocTargetSize
               );
  if (Overflow) {
    DEBUG_RAISE ();
    return RETURN_UNSUPPORTED;
  }

  Fixup = (CHAR8 *) Context->ImageBuffer + RelocTargetRva;
  //
  // Apply the Base Relocation fixup per type.
  //
  switch (RelocType) {
    case UeRelocRel32:
      //
      // Verify the Base Relocation target is in bounds of the Image buffer.
      //
      if (sizeof (UINT32) > RemRelocTargetSize) {
        DEBUG_RAISE ();
        return RETURN_UNSUPPORTED;
      }
      //
      // Relocate the target instruction.
      //
      Fixup32  = ReadUnaligned32 ((CONST VOID *) Fixup);
      Fixup32 += (UINT32) Adjust;
      WriteUnaligned32 ((VOID *) Fixup, Fixup32);

      break;

    case UeRelocRel64:
      //
      // Verify the Image Base Relocation target is in bounds of the Image
      // buffer.
      //
      if (sizeof (UINT64) > RemRelocTargetSize) {
        DEBUG_RAISE ();
        return RETURN_UNSUPPORTED;
      }
      //
      // Relocate target the instruction.
      //
      Fixup64  = ReadUnaligned64 ((CONST VOID *) Fixup);
      Fixup64 += Adjust;
      WriteUnaligned64 ((VOID *) Fixup, Fixup64);

      break;

    case UeRelocArmMov32t:
      //
      // Verify ARM Thumb mode Base Relocations are supported.
      //
      if ((PcdGet32 (PcdImageLoaderRelocTypePolicy) & PCD_RELOC_TYPE_POLICY_ARM) == 0) {
        DEBUG_RAISE ();
        return RETURN_UNSUPPORTED;
      }
      //
      // Verify the Base Relocation target is in bounds of the Image buffer.
      //
      if (sizeof (UINT64) > RemRelocTargetSize) {
        DEBUG_RAISE ();
        return RETURN_UNSUPPORTED;
      }
      //
      // Verify the Base Relocation target is sufficiently aligned.
      // The ARM THunb instruction pait must start on a 32-bit boundary.
      //
      if (!IS_ALIGNED (RelocTargetRva, ALIGNOF (UINT32))) {
        DEBUG_RAISE ();
        return RETURN_UNSUPPORTED;
      }
      //
      // Relocate the target instruction.
      //
      ThumbMovwMovtImmediateFixup (Fixup, Adjust);

      break;

    default:
      //
      // The Image Base Relocation type is unknown, disallow the Image.
      //
      DEBUG_RAISE ();
      return RETURN_UNSUPPORTED;
  }

  return RETURN_SUCCESS;
}

RETURN_STATUS
UeRelocateImage (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context,
  IN     UINT64                   BaseAddress
  )
{
  RETURN_STATUS             Status;

  UINT64                    Adjust;

  UINT32                    RelocBlockOffsetMax;
  UINT32                    EndOfRelocTable;

  UINT32                    RelocBlockOffset;
  CONST UE_RELOCATION_BLOCK *RelocBlock;
  UINT32                    RelocBlockSize;
  UINT32                    SizeOfRelocs;
  UINT16                    NumRelocs;
  UINT32                    RelocIndex;

  ASSERT (Context != NULL);
  ASSERT ((Context->ImageInfo & UE_HEADER_FLAG_RELOCS_STRIPPED) == 0 || BaseAddress == Context->PreferredAddress);
  ASSERT (IS_ALIGNED (Context->SectionsFileOffset, UE_SECTION_ALIGNMENT));
  ASSERT (IS_ALIGNED (Context->RelocTableSize, UE_SECTION_ALIGNMENT));
  ASSERT (IS_ALIGNED (BaseAddress, Context->SegmentAlignment));
  //
  // Verify the Relocation Directory is not empty.
  //
  if (Context->RelocTableSize == 0) {
    return RETURN_SUCCESS;
  }
  //
  // Calculate the Image displacement from its prefered load address.
  //
  Adjust = BaseAddress - Context->PreferredAddress;
  //
  // FIXME: RT driver check is removed in the hope we can force no relocs in
  //        writable segments.
  //
  // Skip explicit Relocation when the Image is already loaded at its
  // prefered location.
  //
  if (Adjust == 0) {
    return RETURN_SUCCESS;
  }

  EndOfRelocTable = Context->SectionsFileOffset + Context->RelocTableSize;

  STATIC_ASSERT (
    sizeof (UE_RELOCATION_BLOCK) <= UE_SECTION_ALIGNMENT,
    "The following arithmetic may overflow."
    );

  RelocBlockOffsetMax = EndOfRelocTable - sizeof (UE_RELOCATION_BLOCK);
  //
  // Apply all Base Relocations of the Image.
  //
  // This arithmetic cannot overflow because it has been checked that the Image
  // Base Relocation Block is in bounds of the Image buffer.
  //
  for (
    RelocBlockOffset = Context->SectionsFileOffset;
    RelocBlockOffset <= RelocBlockOffsetMax;
    RelocBlockOffset += RelocBlockSize
    ) {
    RelocBlock = (CONST UE_RELOCATION_BLOCK *) (CONST VOID *) (
                   (CONST CHAR8 *) Context->FileBuffer + RelocBlockOffset
                   );
    //
    // Verify the Base Relocation Block size is well-formed.
    //
    NumRelocs    = UE_RELOC_BLOCK_NUM (RelocBlock->BlockInfo);
    SizeOfRelocs = (UINT32) NumRelocs * sizeof (UINT16);
    //
    // Verify the Base Relocation Block is in bounds of the Relocation
    // Directory.
    //
    if (SizeOfRelocs > RelocBlockOffsetMax - RelocBlockOffset) {
      DEBUG_RAISE ();
      return RETURN_UNSUPPORTED;
    }
    //
    // Advance to the next Base Relocation Block offset based on the alignment
    // policy.
    //
    RelocBlockSize = sizeof (UE_RELOCATION_BLOCK) + SizeOfRelocs;
    //
    // Safe because we checked the Reloc Dir size.
    //
    RelocBlockSize = ALIGN_VALUE (RelocBlockSize, ALIGNOF (UE_RELOCATION_BLOCK));
    //
    // Process all Base Relocations of the current Block.
    //
    for (RelocIndex = 0; RelocIndex < NumRelocs; ++RelocIndex) {
      //
      // Apply the Image Base Relocation fixup.
      // If RuntimeContext is not NULL, store the current value of the fixup
      // target to determine whether it has been changed during runtime
      // execution.
      //
      Status = InternalApplyRelocation (
                 Context,
                 RelocBlock,
                 RelocIndex,
                 Adjust
                 );
      if (!RETURN_ERROR (Status)) {
        return Status;
      }
    }
  }

  STATIC_ASSERT (
    sizeof (UE_RELOCATION_BLOCK) <= UE_SECTION_ALIGNMENT,
    "The following ASSERT may not hold."
    );

  ASSERT (RelocBlockOffset == EndOfRelocTable);

  //
  // FIXME: Alignment to 8 Bytes should just work, zero'd BRB should be no-op.
  //

  return RETURN_SUCCESS;
}

RETURN_STATUS
UeRelocateImageForRuntime (
  IN OUT VOID                             *Image,
  IN     UINT32                           ImageSize,
  IN     UINT64                           BaseAddress,
  IN     CONST UE_LOADER_RUNTIME_CONTEXT  *RuntimeContext
  )
{
  ASSERT (Image != NULL);
  ASSERT (ImageSize != 0);
  ASSERT (RuntimeContext != NULL);

  (VOID) BaseAddress;
  //
  // FIXME:
  // This feature is currently unsupported.
  //
  return RETURN_UNSUPPORTED;
}

RETURN_STATUS
InternalGetDebugTable (
  IN  CONST UE_LOADER_IMAGE_CONTEXT  *Context,
  OUT CONST UE_DEBUG_TABLE           **DebugTable
  )
{
  CONST UE_SECTION *Section;
  UINT8            SectionIndex;
  UINT8            NumSections;
  UINT32           SectionFileOffset;
  UINT32           SectionFileSize;

  ASSERT (Context != NULL);
  ASSERT (DebugTable != NULL);

  SectionFileOffset = Context->SectionsFileOffset;
  NumSections       = Context->NumSections;

  for (SectionIndex = 0; SectionIndex < NumSections; ++SectionIndex) {
    Section = Context->Sections + SectionIndex;
    if (UE_SECTION_ID (Section->FileInfo) != UeSectionIdDebugTable) {
      SectionFileOffset += UE_SECTION_SIZE (Section->FileInfo);
      continue;
    }

    ASSERT (IS_ALIGNED (SectionFileOffset, ALIGNOF (UE_DEBUG_TABLE)));

    SectionFileSize = UE_SECTION_SIZE (Section->FileInfo);

    if (MIN_SIZE_OF_UE_DEBUG_TABLE > SectionFileSize) {
      DEBUG_RAISE ();
      return RETURN_UNSUPPORTED;
    }

    *DebugTable = (CONST UE_DEBUG_TABLE *) (CONST VOID *) (
                    (CONST CHAR8 *) Context->FileBuffer + SectionFileOffset
                    );

    if ((*DebugTable)->SymbolsPathSize > SectionFileSize - MIN_SIZE_OF_UE_DEBUG_TABLE) {
      DEBUG_RAISE ();
      return RETURN_UNSUPPORTED;
    }

    if ((UINT32) (Context->LastSegmentIndex + 1) * sizeof (UE_SEGMENT_NAME) > SectionFileSize - MIN_SIZE_OF_UE_DEBUG_TABLE - (*DebugTable)->SymbolsPathSize) {
      DEBUG_RAISE ();
      return RETURN_UNSUPPORTED;
    }

    return RETURN_SUCCESS;
  }

  return RETURN_NOT_FOUND;
}

RETURN_STATUS
UeGetSymbolsPath (
  IN  CONST UE_LOADER_IMAGE_CONTEXT  *Context,
  OUT CONST CHAR8                    **SymbolsPath,
  OUT UINT32                         *SymbolsPathSize
  )
{
  RETURN_STATUS        Status;
  CONST UE_DEBUG_TABLE *DebugTable;

  ASSERT (Context != NULL);
  ASSERT (SymbolsPath != NULL);
  ASSERT (SymbolsPathSize != NULL);

  Status = InternalGetDebugTable (Context, &DebugTable);
  if (RETURN_ERROR (Status)) {
    return Status;
  }

  if (DebugTable->SymbolsPathSize == 0) {
    return RETURN_NOT_FOUND;
  }

  // FIXME: Do we require termination?

  *SymbolsPath     = (CONST CHAR8 *) DebugTable->SymbolsPath;
  *SymbolsPathSize = DebugTable->SymbolsPathSize;
  return RETURN_SUCCESS;
}

RETURN_STATUS
UeGetFirstCertificate (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context,
  OUT    CONST WIN_CERTIFICATE    **Certificate
  )
{
  ASSERT (Context != NULL);
  ASSERT (Certificate != NULL);
  //
  // FIXME:
  // This feature is currently unsupported.
  //
  return RETURN_NOT_FOUND;
}

RETURN_STATUS
UeGetNextCertificate (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context,
  IN OUT CONST WIN_CERTIFICATE    **Certificate
  )
{
  ASSERT (Context != NULL);
  ASSERT (Certificate != NULL);
  //
  // FIXME:
  // This feature is currently unsupported.
  //
  return RETURN_NOT_FOUND;
}

RETURN_STATUS
UeGetHiiDataRva (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context,
  OUT    UINT32                   *HiiRva,
  OUT    UINT32                   *HiiSize
  )
{
  ASSERT (Context != NULL);
  ASSERT (HiiRva != NULL);
  ASSERT (HiiSize != NULL);
  //
  // This feature is currently unsupported.
  // FIXME: HII data can be stored, but it is not mapped into the Image memory.
  //
  return RETURN_NOT_FOUND;
}

UINT32
UeGetAddressOfEntryPoint (
  IN CONST UE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  ASSERT (Context != NULL);

  return Context->EntryPointAddress;
}

UINT16
UeGetMachine (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  ASSERT (Context != NULL);
  //
  // FIXME: Return UE value and translate PE to not be stuck with PE-value-using
  //        callers later?
  return Context->Machine;
}

UINT16
UeGetSubsystem (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  ASSERT (Context != NULL);

  return Context->Subsystem;
}

UINT32
UeGetSegmentAlignment (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  ASSERT (Context != NULL);

  return Context->SegmentAlignment;
}

UINT32
UeGetImageSize (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  ASSERT (Context != NULL);

  return Context->ImageSize;
}

UINT32
UeGetImageSizeInplace (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  return UeGetImageSize (Context);
}

UINT64
UeGetPreferredAddress (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  ASSERT (Context != NULL);

  return Context->PreferredAddress;
}

BOOLEAN
UeGetRelocsStripped (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  ASSERT (Context != NULL);

  return (Context->ImageInfo & UE_HEADER_FLAG_RELOCS_STRIPPED) != 0;
}

UINTN
UeLoaderGetImageAddress (
  IN CONST UE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  ASSERT (Context != NULL);

  return (UINTN) Context->ImageBuffer;
}

UINT8
UeGetSegments (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context,
  OUT    CONST UE_SEGMENT         **Segments
  )
{
  ASSERT (Context != NULL);
  ASSERT (Segments != NULL);

  *Segments = Context->Segments;
  return Context->LastSegmentIndex;
}

UINT8
UeGetSegmentImageInfos (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context,
  OUT    CONST UINT32             **SegmentImageInfos,
  OUT    UINT8                    *SegmentImageInfoIterSize
  )
{
  ASSERT (Context != NULL);
  ASSERT (SegmentImageInfos != NULL);
  ASSERT (SegmentImageInfoIterSize != NULL);

  ASSERT (IS_ALIGNED (Context->SegmentImageInfoIterSize, ALIGNOF (UINT32)));

  *SegmentImageInfos        = Context->Segments;
  *SegmentImageInfoIterSize = Context->SegmentImageInfoIterSize;
  return Context->LastSegmentIndex;
}

UINT32
UeGetSectionsFileOffset (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  ASSERT (Context != NULL);

  return Context->SectionsFileOffset;
}
