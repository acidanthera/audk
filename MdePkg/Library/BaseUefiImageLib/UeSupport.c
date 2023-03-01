#include <Base.h>
#include <Uefi/UefiBaseType.h>
#include <Uefi/UefiSpec.h>

#include <Library/BaseLib.h>
#include <Library/BaseMemoryLib.h>
#include <Library/BaseOverflowLib.h>
#include <Library/DebugLib.h>
#include <Library/MemoryAllocationLib.h>
#include <Library/PcdLib.h>
#include <Library/UefiImageLib.h>
#include <Library/UeImageLib.h>

STATIC
UINT32
InternalPermissionsToAttributes (
  IN UINT32  ImageInfo
  )
{
  UINT32 Attributes;

  STATIC_ASSERT (
    (UE_SEGMENT_INFO_RP << 13U) == EFI_MEMORY_RP &&
    (UE_SEGMENT_INFO_XP << 13U) == EFI_MEMORY_XP &&
    (UE_SEGMENT_INFO_RO << 15U) == EFI_MEMORY_RO,
    "The following conversion is incorrect."
    );

  Attributes  = (ImageInfo & (UE_SEGMENT_INFO_RP | UE_SEGMENT_INFO_XP)) << 13U;
  Attributes |= (ImageInfo & UE_SEGMENT_INFO_RO) << 15U;

  return Attributes;
}

UEFI_IMAGE_RECORD *
UefiImageLoaderGetImageRecordUe (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  UEFI_IMAGE_RECORD         *ImageRecord;
  UINTN                     ImageAddress;
  UINT32                    NumRecordSegments;
  UEFI_IMAGE_RECORD_SEGMENT *RecordSegment;
  UINT16                    NumSegments;
  UINT8                     SegmentIterSize;
  CONST UINT32              *SegmentImageInfos;
  CONST UINT32              *SegmentImageInfoPtr;
  UINT32                    SegmentImageInfo;
  UINTN                     SegmentImageAddress;
  UINT32                    SegmentSize;
  UINT32                    SegmentPermissions;
  UINT32                    RangeSize;
  UINT32                    Permissions;

  ASSERT (Context != NULL);

  NumSegments = 1 + (UINT16) UeGetSegmentImageInfos (
    Context,
    &SegmentImageInfos,
    &SegmentIterSize
    );

  ImageRecord = AllocatePool (
                  sizeof (*ImageRecord)
                    + NumSegments * sizeof (*ImageRecord->Segments)
                  );
  if (ImageRecord == NULL) {
    DEBUG_RAISE ();
    return NULL;
  }

  ImageRecord->Signature = UEFI_IMAGE_RECORD_SIGNATURE;
  InitializeListHead (&ImageRecord->Link);

  SegmentImageInfo = *SegmentImageInfos;

  RangeSize   = UE_SEGMENT_SIZE (SegmentImageInfo);
  Permissions = UE_SEGMENT_PERMISSIONS (SegmentImageInfo);

  SegmentImageAddress = 0;
  NumRecordSegments   = 0;

  STATIC_ASSERT (
    OFFSET_OF (UE_SEGMENT, ImageInfo) == 0 &&
    OFFSET_OF (UE_SEGMENT, ImageInfo) == OFFSET_OF (UE_SEGMENT_XIP, ImageInfo),
    "Below's logic assumes the given layout."
    );

  for (
    SegmentImageInfoPtr = (CONST VOID *) ((CONST CHAR8 *) SegmentImageInfos + SegmentIterSize);
    (CONST CHAR8 *) SegmentImageInfoPtr < (CONST CHAR8 *) SegmentImageInfos + (UINT32) SegmentIterSize * NumSegments;
    SegmentImageAddress += SegmentSize,
    SegmentImageInfoPtr = (CONST VOID *) ((CONST CHAR8 *) SegmentImageInfoPtr + SegmentIterSize)
    ) {
    SegmentImageInfo = *SegmentImageInfoPtr;

    SegmentSize        = UE_SEGMENT_SIZE (SegmentImageInfo);
    SegmentPermissions = UE_SEGMENT_PERMISSIONS (SegmentImageInfo);
    //
    // Skip Image segments with the same memory permissions as the current range
    // as they can be merged.
    //
    if (SegmentPermissions == Permissions) {
      RangeSize += SegmentSize;
      continue;
    }
    //
    // Create an Image record section for the current memory permission range.
    //
    RecordSegment = &ImageRecord->Segments[NumRecordSegments];
    RecordSegment->Size       = RangeSize;
    RecordSegment->Attributes = InternalPermissionsToAttributes (Permissions);
    ++NumRecordSegments;
    //
    // Start a Image record section with the current Image section.
    //
    RangeSize   = SegmentSize;
    Permissions = SegmentPermissions;
  }

  ImageAddress = UeLoaderGetImageAddress (Context);

  ImageRecord->NumSegments  = NumRecordSegments;
  ImageRecord->StartAddress = ImageAddress;
  ImageRecord->EndAddress   = ImageAddress + SegmentImageAddress;
  //
  // Zero the remaining array entries to avoid uninitialised data.
  //
  ZeroMem (
    ImageRecord->Segments + NumRecordSegments,
    (NumSegments - NumRecordSegments) * sizeof (*ImageRecord->Segments)
    );

  return ImageRecord;
}

RETURN_STATUS
UefiImageDebugLocateImageUe (
  OUT UE_LOADER_IMAGE_CONTEXT  *Context,
  IN  UINTN                    Address
  )
{
  ASSERT (Context != NULL);
  (VOID) Address;
  //
  // FIXME:
  // This feature is currently unsupported.
  //
  DEBUG_RAISE ();
  return RETURN_NOT_FOUND;
}

RETURN_STATUS
UefiImageGetFixedAddressUe (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context,
  OUT    UINT64                   *Address
  )
{
  ASSERT (Context != NULL);
  ASSERT (Address != NULL);
  //
  // This feature is currently unsupported.
  //
  DEBUG_RAISE ();
  return RETURN_NOT_FOUND;
}

// FIXME:
RETURN_STATUS
InternalGetDebugTable (
  IN  CONST UE_LOADER_IMAGE_CONTEXT  *Context,
  OUT CONST UE_DEBUG_TABLE           **DebugTable
  );

RETURN_STATUS
UefiImageDebugPrintSegmentsUe (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  RETURN_STATUS         DebugStatus;
  CONST UE_DEBUG_TABLE  *DebugTable;
  CONST CHAR8           *Name;
  CONST UE_SEGMENT      *Segments;
  UINT8                 LastSegmentIndex;
  UINT8                 SegmentIndex;
  UINT32                SectionFileOffset;
  UINT32                SegmentImageAddress;
  CONST UE_SEGMENT_NAME *NameTable;
  UINT32                ImageSize;

  DebugStatus       = InternalGetDebugTable (Context, &DebugTable);
  LastSegmentIndex  = UeGetSegments (Context, &Segments);
  NameTable         = UE_DEBUG_TABLE_SEGMENT_NAMES (DebugTable);
  SectionFileOffset = UeGetSectionsFileOffset (Context);
  //
  // The first Image segment must begin the Image memory space.
  //
  SegmentImageAddress = 0;

  for (SegmentIndex = 0; SegmentIndex <= LastSegmentIndex; ++SegmentIndex) {
    if (!RETURN_ERROR (DebugStatus)) {
      Name = (CONST CHAR8 *) NameTable[DebugTable->SymbolsPathSize];
    } else {
      STATIC_ASSERT (
        sizeof (*NameTable) == sizeof ("Unknown"),
        "The following may cause prohibited memory accesses."
        );

      Name = "Unknown";
    }

    ImageSize = UE_SEGMENT_SIZE (Segments[SegmentIndex].ImageInfo);

    DEBUG ((
      DEBUG_VERBOSE,
      "  Segment - '%c%c%c%c%c%c%c%c'\n",
      "  ImageSize    - 0x%08x\n"
      "  ImageAddress - 0x%08x\n"
      "  FileSize      - 0x%08x\n"
      "  FileOffset    - 0x%08x\n"
      "  Permissions   - 0x%08x\n",
      Name[0], Name[1], Name[2], Name[3], Name[4], Name[5], Name[6], Name[7],
      ImageSize,
      SegmentImageAddress,
      Segments[SegmentIndex].FileSize,
      SectionFileOffset,
      UE_SEGMENT_PERMISSIONS (Segments[SegmentIndex].ImageInfo)
      ));

    SegmentImageAddress += ImageSize;
    SectionFileOffset   += Segments[SegmentIndex].FileSize;
  }

  return RETURN_SUCCESS;
}
