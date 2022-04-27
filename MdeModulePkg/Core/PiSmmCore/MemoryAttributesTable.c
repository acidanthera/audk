/** @file
  PI SMM MemoryAttributes support

Copyright (c) 2016, Intel Corporation. All rights reserved.<BR>
SPDX-License-Identifier: BSD-2-Clause-Patent

**/

#include <PiDxe.h>
#include <Library/BaseLib.h>
#include <Library/BaseMemoryLib.h>
#include <Library/MemoryAllocationLib.h>
#include <Library/UefiBootServicesTableLib.h>
#include <Library/SmmServicesTableLib.h>
#include <Library/DebugLib.h>
#include <Library/PcdLib.h>

#include <Library/PeCoffLib.h>

#include <Guid/PiSmmMemoryAttributesTable.h>

#include "PiSmmCore.h"
#include "ProcessorBind.h"

#define PREVIOUS_MEMORY_DESCRIPTOR(MemoryDescriptor, Size) \
  ((EFI_MEMORY_DESCRIPTOR *)((UINT8 *)(MemoryDescriptor) - (Size)))

#define IMAGE_PROPERTIES_PRIVATE_DATA_SIGNATURE  SIGNATURE_32 ('I','P','P','D')

typedef struct {
  UINT32        Signature;
  UINTN         ImageRecordCount;
  UINT32                 NumberOfSectionsMax;
  LIST_ENTRY    ImageRecordList;
} IMAGE_PROPERTIES_PRIVATE_DATA;

IMAGE_PROPERTIES_PRIVATE_DATA  mImagePropertiesPrivateData = {
  IMAGE_PROPERTIES_PRIVATE_DATA_SIGNATURE,
  0,
  0,
  INITIALIZE_LIST_HEAD_VARIABLE (mImagePropertiesPrivateData.ImageRecordList)
};

#define EFI_MEMORY_ATTRIBUTES_RUNTIME_MEMORY_PROTECTION_NON_EXECUTABLE_PE_DATA  BIT0

UINT64  mMemoryProtectionAttribute = EFI_MEMORY_ATTRIBUTES_RUNTIME_MEMORY_PROTECTION_NON_EXECUTABLE_PE_DATA;

//
// Below functions are for MemoryMap
//

/**
  Converts a number of EFI_PAGEs to a size in bytes.

  NOTE: Do not use EFI_PAGES_TO_SIZE because it handles UINTN only.

  @param[in]  Pages     The number of EFI_PAGES.

  @return  The number of bytes associated with the number of EFI_PAGEs specified
           by Pages.
**/
STATIC
UINT64
EfiPagesToSize (
  IN UINT64  Pages
  )
{
  return LShiftU64 (Pages, EFI_PAGE_SHIFT);
}

/**
  Converts a size, in bytes, to a number of EFI_PAGESs.

  NOTE: Do not use EFI_SIZE_TO_PAGES because it handles UINTN only.

  @param[in]  Size      A size in bytes.

  @return  The number of EFI_PAGESs associated with the number of bytes specified
           by Size.

**/
STATIC
UINT64
EfiSizeToPages (
  IN UINT64  Size
  )
{
  return RShiftU64 (Size, EFI_PAGE_SHIFT) + ((((UINTN)Size) & EFI_PAGE_MASK) ? 1 : 0);
}

/**
  Sort memory map entries based upon PhysicalStart, from low to high.

  @param[in,out]  MemoryMap         A pointer to the buffer in which firmware places
                                    the current memory map.
  @param[in]      MemoryMapSize     Size, in bytes, of the MemoryMap buffer.
  @param[in]      DescriptorSize    Size, in bytes, of an individual EFI_MEMORY_DESCRIPTOR.
**/
STATIC
VOID
SortMemoryMap (
  IN OUT EFI_MEMORY_DESCRIPTOR  *MemoryMap,
  IN UINTN                      MemoryMapSize,
  IN UINTN                      DescriptorSize
  )
{
  EFI_MEMORY_DESCRIPTOR  *MemoryMapEntry;
  EFI_MEMORY_DESCRIPTOR  *NextMemoryMapEntry;
  EFI_MEMORY_DESCRIPTOR  *MemoryMapEnd;
  EFI_MEMORY_DESCRIPTOR  TempMemoryMap;

  MemoryMapEntry     = MemoryMap;
  NextMemoryMapEntry = NEXT_MEMORY_DESCRIPTOR (MemoryMapEntry, DescriptorSize);
  MemoryMapEnd       = (EFI_MEMORY_DESCRIPTOR *)((UINT8 *)MemoryMap + MemoryMapSize);
  while (MemoryMapEntry < MemoryMapEnd) {
    while (NextMemoryMapEntry < MemoryMapEnd) {
      if (MemoryMapEntry->PhysicalStart > NextMemoryMapEntry->PhysicalStart) {
        CopyMem (&TempMemoryMap, MemoryMapEntry, sizeof (EFI_MEMORY_DESCRIPTOR));
        CopyMem (MemoryMapEntry, NextMemoryMapEntry, sizeof (EFI_MEMORY_DESCRIPTOR));
        CopyMem (NextMemoryMapEntry, &TempMemoryMap, sizeof (EFI_MEMORY_DESCRIPTOR));
      }

      NextMemoryMapEntry = NEXT_MEMORY_DESCRIPTOR (NextMemoryMapEntry, DescriptorSize);
    }

    MemoryMapEntry     = NEXT_MEMORY_DESCRIPTOR (MemoryMapEntry, DescriptorSize);
    NextMemoryMapEntry = NEXT_MEMORY_DESCRIPTOR (MemoryMapEntry, DescriptorSize);
  }

  return;
}

/**
  Merge continuous memory map entries whose have same attributes.

  @param[in, out]  MemoryMap              A pointer to the buffer in which firmware places
                                          the current memory map.
  @param[in, out]  MemoryMapSize          A pointer to the size, in bytes, of the
                                          MemoryMap buffer. On input, this is the size of
                                          the current memory map.  On output,
                                          it is the size of new memory map after merge.
  @param[in]       DescriptorSize         Size, in bytes, of an individual EFI_MEMORY_DESCRIPTOR.
**/
STATIC
VOID
MergeMemoryMap (
  IN OUT EFI_MEMORY_DESCRIPTOR  *MemoryMap,
  IN OUT UINTN                  *MemoryMapSize,
  IN UINTN                      DescriptorSize
  )
{
  EFI_MEMORY_DESCRIPTOR  *MemoryMapEntry;
  EFI_MEMORY_DESCRIPTOR  *MemoryMapEnd;
  UINT64                 MemoryBlockLength;
  EFI_MEMORY_DESCRIPTOR  *NewMemoryMapEntry;
  EFI_MEMORY_DESCRIPTOR  *NextMemoryMapEntry;

  MemoryMapEntry    = MemoryMap;
  NewMemoryMapEntry = MemoryMap;
  MemoryMapEnd      = (EFI_MEMORY_DESCRIPTOR *)((UINT8 *)MemoryMap + *MemoryMapSize);
  while ((UINTN)MemoryMapEntry < (UINTN)MemoryMapEnd) {
    CopyMem (NewMemoryMapEntry, MemoryMapEntry, sizeof (EFI_MEMORY_DESCRIPTOR));
    NextMemoryMapEntry = NEXT_MEMORY_DESCRIPTOR (MemoryMapEntry, DescriptorSize);

    do {
      MemoryBlockLength = (UINT64)(EfiPagesToSize (MemoryMapEntry->NumberOfPages));
      if (((UINTN)NextMemoryMapEntry < (UINTN)MemoryMapEnd) &&
          (MemoryMapEntry->Type == NextMemoryMapEntry->Type) &&
          (MemoryMapEntry->Attribute == NextMemoryMapEntry->Attribute) &&
          ((MemoryMapEntry->PhysicalStart + MemoryBlockLength) == NextMemoryMapEntry->PhysicalStart))
      {
        MemoryMapEntry->NumberOfPages += NextMemoryMapEntry->NumberOfPages;
        if (NewMemoryMapEntry != MemoryMapEntry) {
          NewMemoryMapEntry->NumberOfPages += NextMemoryMapEntry->NumberOfPages;
        }

        NextMemoryMapEntry = NEXT_MEMORY_DESCRIPTOR (NextMemoryMapEntry, DescriptorSize);
        continue;
      } else {
        MemoryMapEntry = PREVIOUS_MEMORY_DESCRIPTOR (NextMemoryMapEntry, DescriptorSize);
        break;
      }
    } while (TRUE);

    MemoryMapEntry    = NEXT_MEMORY_DESCRIPTOR (MemoryMapEntry, DescriptorSize);
    NewMemoryMapEntry = NEXT_MEMORY_DESCRIPTOR (NewMemoryMapEntry, DescriptorSize);
  }

  *MemoryMapSize = (UINTN)NewMemoryMapEntry - (UINTN)MemoryMap;

  return;
}

/**
  Enforce memory map attributes.
  This function will set EfiRuntimeServicesData/EfiMemoryMappedIO/EfiMemoryMappedIOPortSpace to be EFI_MEMORY_XP.

  @param[in, out]  MemoryMap              A pointer to the buffer in which firmware places
                                          the current memory map.
  @param[in]       MemoryMapSize          Size, in bytes, of the MemoryMap buffer.
  @param[in]       DescriptorSize         Size, in bytes, of an individual EFI_MEMORY_DESCRIPTOR.
**/
STATIC
VOID
EnforceMemoryMapAttribute (
  IN OUT EFI_MEMORY_DESCRIPTOR  *MemoryMap,
  IN UINTN                      MemoryMapSize,
  IN UINTN                      DescriptorSize
  )
{
  EFI_MEMORY_DESCRIPTOR  *MemoryMapEntry;
  EFI_MEMORY_DESCRIPTOR  *MemoryMapEnd;

  MemoryMapEntry = MemoryMap;
  MemoryMapEnd   = (EFI_MEMORY_DESCRIPTOR *)((UINT8 *)MemoryMap + MemoryMapSize);
  while ((UINTN)MemoryMapEntry < (UINTN)MemoryMapEnd) {
    if (MemoryMapEntry->Attribute != 0) {
      // It is PE image, the attribute is already set.
    } else {
      switch (MemoryMapEntry->Type) {
        case EfiRuntimeServicesCode:
          MemoryMapEntry->Attribute = EFI_MEMORY_RO;
          break;
        case EfiRuntimeServicesData:
        default:
          MemoryMapEntry->Attribute |= EFI_MEMORY_XP;
          break;
      }
    }

    MemoryMapEntry = NEXT_MEMORY_DESCRIPTOR (MemoryMapEntry, DescriptorSize);
  }

  return;
}

/**
  Return the first image record, whose [ImageBase, ImageSize] covered by [Buffer, Length].

  @param[in] Buffer  Start Address
  @param[in] Length  Address length

  @return first image record covered by [buffer, length]
**/
STATIC
PE_COFF_IMAGE_RECORD *
GetImageRecordByAddress (
  IN EFI_PHYSICAL_ADDRESS  Buffer,
  IN UINT64                Length
  )
{
  PE_COFF_IMAGE_RECORD       *ImageRecord;
  LIST_ENTRY               *ImageRecordLink;
  LIST_ENTRY               *ImageRecordList;

  ImageRecordList = &mImagePropertiesPrivateData.ImageRecordList;

  for (ImageRecordLink = ImageRecordList->ForwardLink;
       ImageRecordLink != ImageRecordList;
       ImageRecordLink = ImageRecordLink->ForwardLink)
  {
    ImageRecord = CR (
                    ImageRecordLink,
                    PE_COFF_IMAGE_RECORD,
                    Link,
                    PE_COFF_IMAGE_RECORD_SIGNATURE
                    );

    if ((Buffer <= ImageRecord->Sections[0].Address) &&
        (Buffer + Length >= ImageRecord->EndAddress))
    {
      return ImageRecord;
    }
  }

  return NULL;
}

/**
  Set the memory map to new entries, according to one old entry,
  based upon PE code section and data section in image record

  @param[in]       ImageRecord            An image record whose [ImageBase, ImageSize] covered
                                          by old memory map entry.
  @param[in, out]  NewRecord              A pointer to several new memory map entries.
                                          The caller guarantee the buffer size be 1 +
                                          (SplitRecordCount * DescriptorSize) calculated
                                          below.
  @param[in]       OldRecord              A pointer to one old memory map entry.
  @param[in]       DescriptorSize         Size, in bytes, of an individual EFI_MEMORY_DESCRIPTOR.
**/
STATIC
UINTN
SetNewRecord (
  IN PE_COFF_IMAGE_RECORD          *ImageRecord,
  IN OUT EFI_MEMORY_DESCRIPTOR  *NewRecord,
  IN EFI_MEMORY_DESCRIPTOR      *OldRecord,
  IN UINTN                      DescriptorSize
  )
{
  PE_COFF_IMAGE_RECORD_SECTION              *ImageRecordSection;
  UINT32                                    Index;
  UINT32                                NewRecordCount;

  NewRecordCount = 0;

  //
  // Always create a new entry for non-PE image record
  //
  if (ImageRecord->Sections[0].Address > OldRecord->PhysicalStart) {
    NewRecord->Type          = OldRecord->Type;
    NewRecord->PhysicalStart = OldRecord->PhysicalStart;
    NewRecord->VirtualStart  = 0;
    NewRecord->NumberOfPages = EfiSizeToPages (ImageRecord->Sections[0].Address - OldRecord->PhysicalStart);
    NewRecord->Attribute     = OldRecord->Attribute;
    NewRecord                = NEXT_MEMORY_DESCRIPTOR (NewRecord, DescriptorSize);
    NewRecordCount++;
  }

  for (Index = 0;    Index < ImageRecord->NumberOfSections; ++Index) {
    ImageRecordSection = &ImageRecord->Sections[Index];
    // FIXME:          Inconsistent with DXE?
    if  ((ImageRecordSection->Attributes & EFI_MEMORY_XP) == 0) {
      NewRecord->Type          = EfiRuntimeServicesCode;
    } else {
      NewRecord->Type          = EfiRuntimeServicesData;
    }
    NewRecord->PhysicalStart = ImageRecordSection->Address;
    NewRecord->VirtualStart  = 0;
    NewRecord->NumberOfPages = EfiSizeToPages (ImageRecordSection->Size);
    NewRecord->Attribute     = (OldRecord->Attribute & ~(UINT64) EFI_MEMORY_ACCESS_MASK) | ImageRecordSection->Attributes;

    NewRecord = NEXT_MEMORY_DESCRIPTOR (NewRecord, DescriptorSize);
  }

  return NewRecordCount + ImageRecord->NumberOfSections;
}

/**
  Return the max number of new splitted entries, according to one old entry,
  based upon PE code section and data section.

  @param[in]  OldRecord              A pointer to one old memory map entry.

  @retval  0 no entry need to be splitted.
  @return  the max number of new splitted entries
**/
STATIC
UINTN
GetMaxSplitRecordCount (
  IN EFI_MEMORY_DESCRIPTOR  *OldRecord
  )
{
  PE_COFF_IMAGE_RECORD    *ImageRecord;
  UINTN                    SplitRecordCount;
  UINT64                   PhysicalStart;
  UINT64                   PhysicalEnd;

  SplitRecordCount = 0;
  PhysicalStart    = OldRecord->PhysicalStart;
  PhysicalEnd      = OldRecord->PhysicalStart + EfiPagesToSize (OldRecord->NumberOfPages);

  do {
    // FIXME: Inline iteration to not always start anew?
    ImageRecord = GetImageRecordByAddress (PhysicalStart, PhysicalEnd - PhysicalStart);
    if (ImageRecord == NULL) {
      break;
    }

    //
    // Per image, they may be one trailer.
    //
    SplitRecordCount += ImageRecord->NumberOfSections + 1;
    PhysicalStart = ImageRecord->EndAddress;
  } while ((ImageRecord != NULL) && (PhysicalStart < PhysicalEnd));

  //
  // There may be additional prefix data.
  //
  return SplitRecordCount + 1;
}

/**
  Split the memory map to new entries, according to one old entry,
  based upon PE code section and data section.

  @param[in]       OldRecord              A pointer to one old memory map entry.
  @param[in, out]  NewRecord              A pointer to several new memory map entries.
                                          The caller guarantee the buffer size be 1 +
                                          (SplitRecordCount * DescriptorSize) calculated
                                          below.
  @param[in]       MaxSplitRecordCount    The max number of splitted entries
  @param[in]       DescriptorSize         Size, in bytes, of an individual EFI_MEMORY_DESCRIPTOR.

  @retval  0 no entry is splitted.
  @return  the real number of splitted record.
**/
STATIC
UINTN
SplitRecord (
  IN EFI_MEMORY_DESCRIPTOR      *OldRecord,
  IN OUT EFI_MEMORY_DESCRIPTOR  *NewRecord,
  IN UINTN                      MaxSplitRecordCount,
  IN UINTN                      DescriptorSize
  )
{
  EFI_MEMORY_DESCRIPTOR    TempRecord;
  PE_COFF_IMAGE_RECORD    *ImageRecord;
  PE_COFF_IMAGE_RECORD    *NewImageRecord;
  UINT64                   PhysicalStart;
  UINT64                   PhysicalEnd;
  UINTN                    NewRecordCount;
  UINTN                    TotalNewRecordCount;

  if (MaxSplitRecordCount == 0) {
    CopyMem (NewRecord, OldRecord, DescriptorSize);
    return 0;
  }

  TotalNewRecordCount = 0;

  //
  // Override previous record
  //
  CopyMem (&TempRecord, OldRecord, sizeof (EFI_MEMORY_DESCRIPTOR));
  PhysicalStart = TempRecord.PhysicalStart;
  PhysicalEnd   = TempRecord.PhysicalStart + EfiPagesToSize (TempRecord.NumberOfPages);

  ImageRecord = NULL;
  do {
    NewImageRecord = GetImageRecordByAddress (PhysicalStart, PhysicalEnd - PhysicalStart);
    if (NewImageRecord == NULL) {
      //
      // No more image covered by this range, stop
      //
      if (PhysicalEnd > PhysicalStart) {
        //
        // Always create a new entry for non-PE image record
        //
        NewRecord->Type          = TempRecord.Type;
        NewRecord->PhysicalStart = TempRecord.PhysicalStart;
        NewRecord->VirtualStart  = 0;
        NewRecord->NumberOfPages = TempRecord.NumberOfPages;
        NewRecord->Attribute     = TempRecord.Attribute;
        TotalNewRecordCount++;
      }

      break;
    }

    ImageRecord = NewImageRecord;

    //
    // Set new record
    //
    NewRecordCount       = SetNewRecord (ImageRecord, NewRecord, &TempRecord, DescriptorSize);
    TotalNewRecordCount += NewRecordCount;
    NewRecord            = (EFI_MEMORY_DESCRIPTOR *)((UINT8 *)NewRecord + NewRecordCount * DescriptorSize);

    //
    // Update PhysicalStart, in order to exclude the image buffer already splitted.
    //
    PhysicalStart = ImageRecord->EndAddress;
    TempRecord.PhysicalStart = PhysicalStart;
    TempRecord.NumberOfPages = EfiSizeToPages (PhysicalEnd - PhysicalStart);
  } while ((ImageRecord != NULL) && (PhysicalStart < PhysicalEnd));

  return TotalNewRecordCount - 1;
}

/**
  Split the original memory map, and add more entries to describe PE code section and data section.
  This function will set EfiRuntimeServicesData to be EFI_MEMORY_XP.
  This function will merge entries with same attributes finally.

  NOTE: It assumes PE code/data section are page aligned.
  NOTE: It assumes enough entry is prepared for new memory map.

  Split table:
   +---------------+
   | Record X      |
   +---------------+
   | Record RtCode |
   +---------------+
   | Record Y      |
   +---------------+
   ==>
   +---------------+
   | Record X      |
   +---------------+
   | Record RtCode |
   +---------------+ ----
   | Record RtData |     |
   +---------------+     |
   | Record RtCode |     |-> PE/COFF1
   +---------------+     |
   | Record RtData |     |
   +---------------+ ----
   | Record RtCode |
   +---------------+ ----
   | Record RtData |     |
   +---------------+     |
   | Record RtCode |     |-> PE/COFF2
   +---------------+     |
   | Record RtData |     |
   +---------------+ ----
   | Record RtCode |
   +---------------+
   | Record Y      |
   +---------------+

  @param[in, out]  MemoryMapSize          A pointer to the size, in bytes, of the
                                          MemoryMap buffer. On input, this is the size of
                                          old MemoryMap before split. The actual buffer
                                          size of MemoryMap is MemoryMapSize +
                                          (AdditionalRecordCount * DescriptorSize) calculated
                                          below. On output, it is the size of new MemoryMap
                                          after split.
  @param[in, out]  MemoryMap              A pointer to the buffer in which firmware places
                                          the current memory map.
  @param[in]       DescriptorSize         Size, in bytes, of an individual EFI_MEMORY_DESCRIPTOR.
**/
STATIC
VOID
SplitTable (
  IN OUT UINTN                  *MemoryMapSize,
  IN OUT EFI_MEMORY_DESCRIPTOR  *MemoryMap,
  IN UINTN                      DescriptorSize
  )
{
  INTN   IndexOld;
  INTN   IndexNew;
  UINTN  MaxSplitRecordCount;
  UINTN  RealSplitRecordCount;
  UINTN  TotalSplitRecordCount;
  UINTN  AdditionalRecordCount;

  //
  // Per image, they may be one trailer. There may be prefixed data.
  //
  AdditionalRecordCount = (mImagePropertiesPrivateData.NumberOfSectionsMax + 1) * mImagePropertiesPrivateData.ImageRecordCount + 1;

  TotalSplitRecordCount = 0;
  //
  // Let old record point to end of valid MemoryMap buffer.
  //
  IndexOld = ((*MemoryMapSize) / DescriptorSize) - 1;
  //
  // Let new record point to end of full MemoryMap buffer.
  //
  IndexNew = ((*MemoryMapSize) / DescriptorSize) - 1 + AdditionalRecordCount;
  for ( ; IndexOld >= 0; IndexOld--) {
    MaxSplitRecordCount = GetMaxSplitRecordCount ((EFI_MEMORY_DESCRIPTOR *)((UINT8 *)MemoryMap + IndexOld * DescriptorSize));
    //
    // Split this MemoryMap record
    //
    IndexNew            -= MaxSplitRecordCount;
    RealSplitRecordCount = SplitRecord (
                             (EFI_MEMORY_DESCRIPTOR *)((UINT8 *)MemoryMap + IndexOld * DescriptorSize),
                             (EFI_MEMORY_DESCRIPTOR *)((UINT8 *)MemoryMap + IndexNew * DescriptorSize),
                             MaxSplitRecordCount,
                             DescriptorSize
                             );
    //
    // Adjust IndexNew according to real split.
    //
    if (MaxSplitRecordCount != RealSplitRecordCount) {
      CopyMem (
        ((UINT8 *)MemoryMap + (IndexNew + MaxSplitRecordCount - RealSplitRecordCount) * DescriptorSize),
        ((UINT8 *)MemoryMap + IndexNew * DescriptorSize),
        (RealSplitRecordCount + 1) * DescriptorSize
        );
    }

    IndexNew               = IndexNew + MaxSplitRecordCount - RealSplitRecordCount;
    TotalSplitRecordCount += RealSplitRecordCount;
    IndexNew--;
  }

  //
  // Move all records to the beginning.
  //
  CopyMem (
    MemoryMap,
    (UINT8 *)MemoryMap + (AdditionalRecordCount - TotalSplitRecordCount) * DescriptorSize,
    (*MemoryMapSize) + TotalSplitRecordCount * DescriptorSize
    );

  *MemoryMapSize = (*MemoryMapSize) + DescriptorSize * TotalSplitRecordCount;

  //
  // Sort from low to high (Just in case)
  //
  SortMemoryMap (MemoryMap, *MemoryMapSize, DescriptorSize);

  //
  // Set RuntimeData to XP
  //
  EnforceMemoryMapAttribute (MemoryMap, *MemoryMapSize, DescriptorSize);

  //
  // Merge same type to save entry size
  //
  MergeMemoryMap (MemoryMap, MemoryMapSize, DescriptorSize);

  return;
}

/**
  This function for GetMemoryMap() with memory attributes table.

  It calls original GetMemoryMap() to get the original memory map information. Then
  plus the additional memory map entries for PE Code/Data separation.

  @param[in, out]  MemoryMapSize          A pointer to the size, in bytes, of the
                                          MemoryMap buffer. On input, this is the size of
                                          the buffer allocated by the caller.  On output,
                                          it is the size of the buffer returned by the
                                          firmware  if the buffer was large enough, or the
                                          size of the buffer needed  to contain the map if
                                          the buffer was too small.
  @param[in, out]  MemoryMap              A pointer to the buffer in which firmware places
                                          the current memory map.
  @param[out]      MapKey                 A pointer to the location in which firmware
                                          returns the key for the current memory map.
  @param[out]      DescriptorSize         A pointer to the location in which firmware
                                          returns the size, in bytes, of an individual
                                          EFI_MEMORY_DESCRIPTOR.
  @param[out]      DescriptorVersion      A pointer to the location in which firmware
                                          returns the version number associated with the
                                          EFI_MEMORY_DESCRIPTOR.

  @retval EFI_SUCCESS            The memory map was returned in the MemoryMap
                                 buffer.
  @retval EFI_BUFFER_TOO_SMALL   The MemoryMap buffer was too small. The current
                                 buffer size needed to hold the memory map is
                                 returned in MemoryMapSize.
  @retval EFI_INVALID_PARAMETER  One of the parameters has an invalid value.

**/
STATIC
EFI_STATUS
EFIAPI
SmmCoreGetMemoryMapMemoryAttributesTable (
  IN OUT UINTN                  *MemoryMapSize,
  IN OUT EFI_MEMORY_DESCRIPTOR  *MemoryMap,
  OUT UINTN                     *MapKey,
  OUT UINTN                     *DescriptorSize,
  OUT UINT32                    *DescriptorVersion
  )
{
  EFI_STATUS  Status;
  UINTN       OldMemoryMapSize;
  UINTN       AdditionalRecordCount;

  //
  // If PE code/data is not aligned, just return.
  //
  if ((mMemoryProtectionAttribute & EFI_MEMORY_ATTRIBUTES_RUNTIME_MEMORY_PROTECTION_NON_EXECUTABLE_PE_DATA) == 0) {
    return SmmCoreGetMemoryMap (MemoryMapSize, MemoryMap, MapKey, DescriptorSize, DescriptorVersion);
  }

  if (MemoryMapSize == NULL) {
    return EFI_INVALID_PARAMETER;
  }

  //
  // Per image, they may be one trailer. There may be prefixed data.
  //
  AdditionalRecordCount = (mImagePropertiesPrivateData.NumberOfSectionsMax + 1) * mImagePropertiesPrivateData.ImageRecordCount + 1;

  OldMemoryMapSize = *MemoryMapSize;
  Status           = SmmCoreGetMemoryMap (MemoryMapSize, MemoryMap, MapKey, DescriptorSize, DescriptorVersion);
  if (Status == EFI_BUFFER_TOO_SMALL) {
    *MemoryMapSize = *MemoryMapSize + (*DescriptorSize) * AdditionalRecordCount;
  } else if (Status == EFI_SUCCESS) {
    if (OldMemoryMapSize - *MemoryMapSize < (*DescriptorSize) * AdditionalRecordCount) {
      *MemoryMapSize = *MemoryMapSize + (*DescriptorSize) * AdditionalRecordCount;
      //
      // Need update status to buffer too small
      //
      Status = EFI_BUFFER_TOO_SMALL;
    } else {
      //
      // Split PE code/data
      //
      ASSERT (MemoryMap != NULL);
      SplitTable (MemoryMapSize, MemoryMap, *DescriptorSize);
    }
  }

  return Status;
}

//
// Below functions are for ImageRecord
//

/**
  Set MemoryProtectionAttribute according to PE/COFF image section alignment.

  @param[in]  SectionAlignment    PE/COFF section alignment
**/
STATIC
VOID
SetMemoryAttributesTableSectionAlignment (
  IN UINT32  SectionAlignment
  )
{
  if (((SectionAlignment & (RUNTIME_PAGE_ALLOCATION_GRANULARITY - 1)) != 0) &&
      ((mMemoryProtectionAttribute & EFI_MEMORY_ATTRIBUTES_RUNTIME_MEMORY_PROTECTION_NON_EXECUTABLE_PE_DATA) != 0))
  {
    DEBUG ((DEBUG_VERBOSE, "SMM SetMemoryAttributesTableSectionAlignment - Clear\n"));
    mMemoryProtectionAttribute &= ~((UINT64)EFI_MEMORY_ATTRIBUTES_RUNTIME_MEMORY_PROTECTION_NON_EXECUTABLE_PE_DATA);
  }
}

/**
  Sort image record based upon the ImageBase from low to high.
**/
STATIC
VOID
InsertSortImageRecord (
  IN PE_COFF_IMAGE_RECORD  *NewImageRecord
  )
{
  PE_COFF_IMAGE_RECORD         *ImageRecord;
  LIST_ENTRY                   *PrevImageRecordLink;
  LIST_ENTRY                   *ImageRecordLink;
  LIST_ENTRY                   *ImageRecordList;

  ImageRecordList = &mImagePropertiesPrivateData.ImageRecordList;

  PrevImageRecordLink = ImageRecordList;
  for (
    ImageRecordLink = GetFirstNode (ImageRecordList);
    !IsNull (ImageRecordLink, ImageRecordList);
    ImageRecordLink = GetNextNode (ImageRecordList, PrevImageRecordLink)
    ) {
    ImageRecord = CR (
                    ImageRecordLink,
                    PE_COFF_IMAGE_RECORD,
                    Link,
                    PE_COFF_IMAGE_RECORD_SIGNATURE
                    );
    if (NewImageRecord->Sections[0].Address < ImageRecord->Sections[0].Address) {
      break;
    }

    PrevImageRecordLink = ImageRecordLink;
  }

  InsertHeadList (PrevImageRecordLink, &NewImageRecord->Link);
  mImagePropertiesPrivateData.ImageRecordCount++;

  if (mImagePropertiesPrivateData.NumberOfSectionsMax < NewImageRecord->NumberOfSections) {
    mImagePropertiesPrivateData.NumberOfSectionsMax = NewImageRecord->NumberOfSections;
  }
}

/**
  Dump image record.
**/
STATIC
VOID
DumpImageRecord (
  VOID
  )
{
  PE_COFF_IMAGE_RECORD         *ImageRecord;
  LIST_ENTRY               *ImageRecordLink;
  LIST_ENTRY               *ImageRecordList;
  UINTN                    Index;

  ImageRecordList = &mImagePropertiesPrivateData.ImageRecordList;

  for (ImageRecordLink = ImageRecordList->ForwardLink, Index = 0;
       ImageRecordLink != ImageRecordList;
       ImageRecordLink = ImageRecordLink->ForwardLink, Index++)
  {
    ImageRecord = CR (
                    ImageRecordLink,
                    PE_COFF_IMAGE_RECORD,
                    Link,
                    PE_COFF_IMAGE_RECORD_SIGNATURE
                    );
    DEBUG ((DEBUG_VERBOSE, "SMM  Image[%d]: 0x%016lx - 0x%016lx\n", Index, ImageRecord->Sections[0].Address, ImageRecord->EndAddress - ImageRecord->Sections[0].Address));
  }
}

/**
  Insert image record.

  @param[in]  DriverEntry    Driver information
**/
VOID
SmmInsertImageRecord (
  IN EFI_LOADED_IMAGE_PROTOCOL  *LoadedImage,
  PE_COFF_LOADER_IMAGE_CONTEXT   *ImageContext
  )
{
  RETURN_STATUS                        PdbStatus;
  PHYSICAL_ADDRESS                     ImageBuffer;
  UINTN                                NumberOfPage;
  UINT32                                SectionAlignment;
  UINTN                                 Index;
  PE_COFF_IMAGE_RECORD              *ImageRecord;
  CONST CHAR8                          *PdbPointer;
  UINT32                               PdbSize;

  ImageBuffer  = (UINTN)LoadedImage->ImageBase;
  NumberOfPage = EFI_SIZE_TO_PAGES((UINTN)LoadedImage->ImageSize);

  DEBUG ((DEBUG_VERBOSE, "SMM InsertImageRecord - 0x%016lx - 0x%08x\n", ImageBuffer, NumberOfPage));

  DEBUG ((DEBUG_VERBOSE, "SMM ImageRecordCount - 0x%x\n", mImagePropertiesPrivateData.ImageRecordCount));

  PdbStatus = PeCoffGetPdbPath (ImageContext, &PdbPointer, &PdbSize);
  if (!RETURN_ERROR (PdbStatus)) {
    DEBUG ((DEBUG_VERBOSE, "SMM   Image - %a\n", PdbPointer));
  }

  //
  // Get SectionAlignment
  //
  SectionAlignment = PeCoffGetSectionAlignment (ImageContext);

  SetMemoryAttributesTableSectionAlignment (SectionAlignment);
  if ((SectionAlignment & (RUNTIME_PAGE_ALLOCATION_GRANULARITY - 1)) != 0) {
    DEBUG ((
      DEBUG_WARN,
      "SMM !!!!!!!!  InsertImageRecord - Section Alignment(0x%x) is not %dK  !!!!!!!!\n",
      SectionAlignment, RUNTIME_PAGE_ALLOCATION_GRANULARITY >> 10));
    if (!RETURN_ERROR (PdbStatus)) {
      DEBUG ((DEBUG_WARN, "SMM !!!!!!!!  Image - %a  !!!!!!!!\n", PdbPointer));
    }

    goto Finish;
  }

  //
  // The image headers are not recorded among the sections, allocate one more.
  //
  ImageRecord = PeCoffLoaderGetImageRecord (ImageContext);
  if (ImageRecord == NULL) {
    return ;
  }

  PeCoffDebugPrintSectionTable (ImageContext);

  for (Index = 0; Index < ImageRecord->NumberOfSections; ++Index) {
    DEBUG ((
      DEBUG_VERBOSE,
      "  RecordSection'\n"
      ));
    DEBUG ((DEBUG_VERBOSE, "  Address              - 0x%16xll\n", (UINT64) ImageRecord->Sections[Index].Address));
    DEBUG ((DEBUG_VERBOSE, "  Size                 - 0x%08x\n", ImageRecord->Sections[Index].Size));
    DEBUG ((DEBUG_VERBOSE, "  Attributes           - 0x%08x\n", ImageRecord->Sections[Index].Attributes));
  }

  InsertSortImageRecord (ImageRecord);

Finish:
  return;
}

/**
  Publish MemoryAttributesTable to SMM configuration table.
**/
VOID
PublishMemoryAttributesTable (
  VOID
  )
{
  UINTN                                 MemoryMapSize;
  EFI_MEMORY_DESCRIPTOR                 *MemoryMap;
  UINTN                                 MapKey;
  UINTN                                 DescriptorSize;
  UINT32                                DescriptorVersion;
  UINTN                                 Index;
  EFI_STATUS                            Status;
  UINTN                                 RuntimeEntryCount;
  EDKII_PI_SMM_MEMORY_ATTRIBUTES_TABLE  *MemoryAttributesTable;
  EFI_MEMORY_DESCRIPTOR                 *MemoryAttributesEntry;
  UINTN                                 MemoryAttributesTableSize;

  MemoryMapSize = 0;
  MemoryMap     = NULL;
  Status        = SmmCoreGetMemoryMapMemoryAttributesTable (
                    &MemoryMapSize,
                    MemoryMap,
                    &MapKey,
                    &DescriptorSize,
                    &DescriptorVersion
                    );
  ASSERT (Status == EFI_BUFFER_TOO_SMALL);

  do {
    DEBUG ((DEBUG_VERBOSE, "MemoryMapSize - 0x%x\n", MemoryMapSize));
    MemoryMap = AllocatePool (MemoryMapSize);
    ASSERT (MemoryMap != NULL);
    DEBUG ((DEBUG_VERBOSE, "MemoryMap - 0x%x\n", MemoryMap));

    Status = SmmCoreGetMemoryMapMemoryAttributesTable (
               &MemoryMapSize,
               MemoryMap,
               &MapKey,
               &DescriptorSize,
               &DescriptorVersion
               );
    if (EFI_ERROR (Status)) {
      FreePool (MemoryMap);
    }
  } while (Status == EFI_BUFFER_TOO_SMALL);

  //
  // Allocate MemoryAttributesTable
  //
  RuntimeEntryCount         = MemoryMapSize/DescriptorSize;
  MemoryAttributesTableSize = sizeof (EDKII_PI_SMM_MEMORY_ATTRIBUTES_TABLE) + DescriptorSize * RuntimeEntryCount;
  MemoryAttributesTable     = AllocatePool (sizeof (EDKII_PI_SMM_MEMORY_ATTRIBUTES_TABLE) + DescriptorSize * RuntimeEntryCount);
  ASSERT (MemoryAttributesTable != NULL);
  MemoryAttributesTable->Version         = EDKII_PI_SMM_MEMORY_ATTRIBUTES_TABLE_VERSION;
  MemoryAttributesTable->NumberOfEntries = (UINT32)RuntimeEntryCount;
  MemoryAttributesTable->DescriptorSize  = (UINT32)DescriptorSize;
  MemoryAttributesTable->Reserved        = 0;
  DEBUG ((DEBUG_VERBOSE, "MemoryAttributesTable:\n"));
  DEBUG ((DEBUG_VERBOSE, "  Version              - 0x%08x\n", MemoryAttributesTable->Version));
  DEBUG ((DEBUG_VERBOSE, "  NumberOfEntries      - 0x%08x\n", MemoryAttributesTable->NumberOfEntries));
  DEBUG ((DEBUG_VERBOSE, "  DescriptorSize       - 0x%08x\n", MemoryAttributesTable->DescriptorSize));
  MemoryAttributesEntry = (EFI_MEMORY_DESCRIPTOR *)(MemoryAttributesTable + 1);
  for (Index = 0; Index < MemoryMapSize/DescriptorSize; Index++) {
    CopyMem (MemoryAttributesEntry, MemoryMap, DescriptorSize);
    DEBUG ((DEBUG_VERBOSE, "Entry (0x%x)\n", MemoryAttributesEntry));
    DEBUG ((DEBUG_VERBOSE, "  Type              - 0x%x\n", MemoryAttributesEntry->Type));
    DEBUG ((DEBUG_VERBOSE, "  PhysicalStart     - 0x%016lx\n", MemoryAttributesEntry->PhysicalStart));
    DEBUG ((DEBUG_VERBOSE, "  VirtualStart      - 0x%016lx\n", MemoryAttributesEntry->VirtualStart));
    DEBUG ((DEBUG_VERBOSE, "  NumberOfPages     - 0x%016lx\n", MemoryAttributesEntry->NumberOfPages));
    DEBUG ((DEBUG_VERBOSE, "  Attribute         - 0x%016lx\n", MemoryAttributesEntry->Attribute));
    MemoryAttributesEntry = NEXT_MEMORY_DESCRIPTOR (MemoryAttributesEntry, DescriptorSize);

    MemoryMap = NEXT_MEMORY_DESCRIPTOR (MemoryMap, DescriptorSize);
  }

  Status = gSmst->SmmInstallConfigurationTable (gSmst, &gEdkiiPiSmmMemoryAttributesTableGuid, MemoryAttributesTable, MemoryAttributesTableSize);
  ASSERT_EFI_ERROR (Status);
}

/**
  Install MemoryAttributesTable.

  @param[in] Protocol   Points to the protocol's unique identifier.
  @param[in] Interface  Points to the interface instance.
  @param[in] Handle     The handle on which the interface was installed.

  @retval EFI_SUCCESS   Notification runs successfully.
**/
EFI_STATUS
EFIAPI
SmmInstallMemoryAttributesTable (
  IN CONST EFI_GUID  *Protocol,
  IN VOID            *Interface,
  IN EFI_HANDLE      Handle
  )
{
  DEBUG ((DEBUG_VERBOSE, "SMM MemoryProtectionAttribute - 0x%016lx\n", mMemoryProtectionAttribute));
  if ((mMemoryProtectionAttribute & EFI_MEMORY_ATTRIBUTES_RUNTIME_MEMORY_PROTECTION_NON_EXECUTABLE_PE_DATA) == 0) {
    return EFI_SUCCESS;
  }

  DEBUG ((DEBUG_VERBOSE, "SMM Total Image Count - 0x%x\n", mImagePropertiesPrivateData.ImageRecordCount));
  DEBUG ((DEBUG_VERBOSE, "SMM Dump ImageRecord:\n"));
  DumpImageRecord ();

  PublishMemoryAttributesTable ();

  return EFI_SUCCESS;
}

/**
  Initialize MemoryAttributesTable support.
**/
VOID
EFIAPI
SmmCoreInitializeMemoryAttributesTable (
  VOID
  )
{
  EFI_STATUS  Status;
  VOID        *Registration;

  Status = gSmst->SmmRegisterProtocolNotify (
                    &gEfiSmmEndOfDxeProtocolGuid,
                    SmmInstallMemoryAttributesTable,
                    &Registration
                    );
  ASSERT_EFI_ERROR (Status);

  return;
}
