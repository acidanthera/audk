/** @file
  UEFI MemoryAttributesTable support

Copyright (c) 2016 - 2018, Intel Corporation. All rights reserved.<BR>
SPDX-License-Identifier: BSD-2-Clause-Patent

**/

#include <PiDxe.h>
#include <Library/BaseLib.h>
#include <Library/BaseMemoryLib.h>
#include <Library/MemoryAllocationLib.h>
#include <Library/UefiBootServicesTableLib.h>
#include <Library/DxeServicesTableLib.h>
#include <Library/DebugLib.h>
#include <Library/UefiLib.h>

#include <Guid/EventGroup.h>

#include <Guid/MemoryAttributesTable.h>

#include "DxeMain.h"
#include "HeapGuard.h"
#include "IndustryStandard/PeImage2.h"
#include "ProcessorBind.h"

/**
  This function for GetMemoryMap() with properties table capability.

  It calls original GetMemoryMap() to get the original memory map information. Then
  plus the additional memory map entries for PE Code/Data seperation.

  @param  MemoryMapSize          A pointer to the size, in bytes, of the
                                 MemoryMap buffer. On input, this is the size of
                                 the buffer allocated by the caller.  On output,
                                 it is the size of the buffer returned by the
                                 firmware  if the buffer was large enough, or the
                                 size of the buffer needed  to contain the map if
                                 the buffer was too small.
  @param  MemoryMap              A pointer to the buffer in which firmware places
                                 the current memory map.
  @param  MapKey                 A pointer to the location in which firmware
                                 returns the key for the current memory map.
  @param  DescriptorSize         A pointer to the location in which firmware
                                 returns the size, in bytes, of an individual
                                 EFI_MEMORY_DESCRIPTOR.
  @param  DescriptorVersion      A pointer to the location in which firmware
                                 returns the version number associated with the
                                 EFI_MEMORY_DESCRIPTOR.

  @retval EFI_SUCCESS            The memory map was returned in the MemoryMap
                                 buffer.
  @retval EFI_BUFFER_TOO_SMALL   The MemoryMap buffer was too small. The current
                                 buffer size needed to hold the memory map is
                                 returned in MemoryMapSize.
  @retval EFI_INVALID_PARAMETER  One of the parameters has an invalid value.

**/
EFI_STATUS
EFIAPI
CoreGetMemoryMapWithSeparatedImageSection (
  IN OUT UINTN                  *MemoryMapSize,
  IN OUT EFI_MEMORY_DESCRIPTOR  *MemoryMap,
  OUT UINTN                     *MapKey,
  OUT UINTN                     *DescriptorSize,
  OUT UINT32                    *DescriptorVersion
  );

#define PREVIOUS_MEMORY_DESCRIPTOR(MemoryDescriptor, Size) \
  ((EFI_MEMORY_DESCRIPTOR *)((UINT8 *)(MemoryDescriptor) - (Size)))

#define IMAGE_PROPERTIES_PRIVATE_DATA_SIGNATURE  SIGNATURE_32 ('I','P','P','D')

typedef struct {
  UINT32        Signature;
  UINTN         ImageRecordCount;
  UINTN                  SectionCountMax;
  LIST_ENTRY    ImageRecordList;
} IMAGE_PROPERTIES_PRIVATE_DATA;

STATIC IMAGE_PROPERTIES_PRIVATE_DATA  mImagePropertiesPrivateData = {
  IMAGE_PROPERTIES_PRIVATE_DATA_SIGNATURE,
  0,
  0,
  INITIALIZE_LIST_HEAD_VARIABLE (mImagePropertiesPrivateData.ImageRecordList)
};

STATIC EFI_LOCK  mMemoryAttributesTableLock = EFI_INITIALIZE_LOCK_VARIABLE (TPL_NOTIFY);

BOOLEAN                      mMemoryAttributesTableEnable      = TRUE;
BOOLEAN                      mMemoryAttributesTableEndOfDxe    = FALSE;
EFI_MEMORY_ATTRIBUTES_TABLE  *mMemoryAttributesTable           = NULL;
BOOLEAN                      mMemoryAttributesTableReadyToBoot = FALSE;

/**
  Install MemoryAttributesTable.

**/
VOID
InstallMemoryAttributesTable (
  VOID
  )
{
  UINTN                        MemoryMapSize;
  EFI_MEMORY_DESCRIPTOR        *MemoryMap;
  EFI_MEMORY_DESCRIPTOR        *MemoryMapStart;
  UINTN                        MapKey;
  UINTN                        DescriptorSize;
  UINT32                       DescriptorVersion;
  UINTN                        Index;
  EFI_STATUS                   Status;
  UINT32                       RuntimeEntryCount;
  EFI_MEMORY_ATTRIBUTES_TABLE  *MemoryAttributesTable;
  EFI_MEMORY_DESCRIPTOR        *MemoryAttributesEntry;

  if (gMemoryMapTerminated) {
    //
    // Directly return after MemoryMap terminated.
    //
    return;
  }

  if (!mMemoryAttributesTableEnable) {
    DEBUG ((DEBUG_VERBOSE, "Cannot install Memory Attributes Table "));
    DEBUG ((DEBUG_VERBOSE, "because Runtime Driver Section Alignment is not %dK.\n", RUNTIME_PAGE_ALLOCATION_GRANULARITY >> 10));
    return;
  }

  if (mMemoryAttributesTable == NULL) {
    //
    // InstallConfigurationTable here to occupy one entry for MemoryAttributesTable
    // before GetMemoryMap below, as InstallConfigurationTable may allocate runtime
    // memory for the new entry.
    //
    Status = gBS->InstallConfigurationTable (&gEfiMemoryAttributesTableGuid, (VOID *)(UINTN)MAX_ADDRESS);
    ASSERT_EFI_ERROR (Status);
  }

  MemoryMapSize = 0;
  MemoryMap     = NULL;
  Status        = CoreGetMemoryMapWithSeparatedImageSection (
                    &MemoryMapSize,
                    MemoryMap,
                    &MapKey,
                    &DescriptorSize,
                    &DescriptorVersion
                    );
  ASSERT (Status == EFI_BUFFER_TOO_SMALL);

  do {
    MemoryMap = AllocatePool (MemoryMapSize);
    ASSERT (MemoryMap != NULL);

    Status = CoreGetMemoryMapWithSeparatedImageSection (
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

  MemoryMapStart    = MemoryMap;
  RuntimeEntryCount = 0;
  for (Index = 0; Index < MemoryMapSize/DescriptorSize; Index++) {
    switch (MemoryMap->Type) {
      case EfiRuntimeServicesCode:
      case EfiRuntimeServicesData:
        RuntimeEntryCount++;
        break;
    }

    MemoryMap = NEXT_MEMORY_DESCRIPTOR (MemoryMap, DescriptorSize);
  }

  //
  // Allocate MemoryAttributesTable
  //
  MemoryAttributesTable = AllocatePool (sizeof (EFI_MEMORY_ATTRIBUTES_TABLE) + DescriptorSize * RuntimeEntryCount);
  ASSERT (MemoryAttributesTable != NULL);
  MemoryAttributesTable->Version         = EFI_MEMORY_ATTRIBUTES_TABLE_VERSION;
  MemoryAttributesTable->NumberOfEntries = RuntimeEntryCount;
  MemoryAttributesTable->DescriptorSize  = (UINT32)DescriptorSize;
  MemoryAttributesTable->Reserved        = 0;
  DEBUG ((DEBUG_VERBOSE, "MemoryAttributesTable:\n"));
  DEBUG ((DEBUG_VERBOSE, "  Version              - 0x%08x\n", MemoryAttributesTable->Version));
  DEBUG ((DEBUG_VERBOSE, "  NumberOfEntries      - 0x%08x\n", MemoryAttributesTable->NumberOfEntries));
  DEBUG ((DEBUG_VERBOSE, "  DescriptorSize       - 0x%08x\n", MemoryAttributesTable->DescriptorSize));
  MemoryAttributesEntry = (EFI_MEMORY_DESCRIPTOR *)(MemoryAttributesTable + 1);
  MemoryMap             = MemoryMapStart;
  for (Index = 0; Index < MemoryMapSize/DescriptorSize; Index++) {
    switch (MemoryMap->Type) {
      case EfiRuntimeServicesCode:
      case EfiRuntimeServicesData:
        CopyMem (MemoryAttributesEntry, MemoryMap, DescriptorSize);
        MemoryAttributesEntry->Attribute &= EFI_MEMORY_ACCESS_MASK;
        DEBUG ((DEBUG_VERBOSE, "Entry (0x%x)\n", MemoryAttributesEntry));
        DEBUG ((DEBUG_VERBOSE, "  Type              - 0x%x\n", MemoryAttributesEntry->Type));
        DEBUG ((DEBUG_VERBOSE, "  PhysicalStart     - 0x%016lx\n", MemoryAttributesEntry->PhysicalStart));
        DEBUG ((DEBUG_VERBOSE, "  VirtualStart      - 0x%016lx\n", MemoryAttributesEntry->VirtualStart));
        DEBUG ((DEBUG_VERBOSE, "  NumberOfPages     - 0x%016lx\n", MemoryAttributesEntry->NumberOfPages));
        DEBUG ((DEBUG_VERBOSE, "  Attribute         - 0x%016lx\n", MemoryAttributesEntry->Attribute));
        MemoryAttributesEntry = NEXT_MEMORY_DESCRIPTOR (MemoryAttributesEntry, DescriptorSize);
        break;
    }

    MemoryMap = NEXT_MEMORY_DESCRIPTOR (MemoryMap, DescriptorSize);
  }

  MemoryMap = MemoryMapStart;
  FreePool (MemoryMap);

  //
  // Update configuratoin table for MemoryAttributesTable.
  //
  Status = gBS->InstallConfigurationTable (&gEfiMemoryAttributesTableGuid, MemoryAttributesTable);
  ASSERT_EFI_ERROR (Status);

  if (mMemoryAttributesTable != NULL) {
    FreePool (mMemoryAttributesTable);
  }

  mMemoryAttributesTable = MemoryAttributesTable;
}

/**
  Install MemoryAttributesTable on memory allocation.

  @param[in] MemoryType EFI memory type.
**/
VOID
InstallMemoryAttributesTableOnMemoryAllocation (
  IN EFI_MEMORY_TYPE  MemoryType
  )
{
  //
  // Install MemoryAttributesTable after ReadyToBoot on runtime memory allocation.
  //
  if (mMemoryAttributesTableReadyToBoot &&
      ((MemoryType == EfiRuntimeServicesCode) || (MemoryType == EfiRuntimeServicesData)))
  {
    InstallMemoryAttributesTable ();
  }
}

/**
  Install MemoryAttributesTable on ReadyToBoot.

  @param[in] Event      The Event this notify function registered to.
  @param[in] Context    Pointer to the context data registered to the Event.
**/
VOID
EFIAPI
InstallMemoryAttributesTableOnReadyToBoot (
  IN EFI_EVENT  Event,
  IN VOID       *Context
  )
{
  InstallMemoryAttributesTable ();
  mMemoryAttributesTableReadyToBoot = TRUE;
}

/**
  Install initial MemoryAttributesTable on EndOfDxe.
  Then SMM can consume this information.

  @param[in] Event      The Event this notify function registered to.
  @param[in] Context    Pointer to the context data registered to the Event.
**/
VOID
EFIAPI
InstallMemoryAttributesTableOnEndOfDxe (
  IN EFI_EVENT  Event,
  IN VOID       *Context
  )
{
  mMemoryAttributesTableEndOfDxe = TRUE;
  InstallMemoryAttributesTable ();
}

/**
  Initialize MemoryAttrubutesTable support.
**/
VOID
EFIAPI
CoreInitializeMemoryAttributesTable (
  VOID
  )
{
  EFI_STATUS  Status;
  EFI_EVENT   ReadyToBootEvent;
  EFI_EVENT   EndOfDxeEvent;

  //
  // Construct the table at ReadyToBoot.
  //
  Status = CoreCreateEventInternal (
             EVT_NOTIFY_SIGNAL,
             TPL_CALLBACK,
             InstallMemoryAttributesTableOnReadyToBoot,
             NULL,
             &gEfiEventReadyToBootGuid,
             &ReadyToBootEvent
             );
  ASSERT_EFI_ERROR (Status);

  //
  // Construct the initial table at EndOfDxe,
  // then SMM can consume this information.
  // Use TPL_NOTIFY here, as such SMM code (TPL_CALLBACK)
  // can run after it.
  //
  Status = CoreCreateEventInternal (
             EVT_NOTIFY_SIGNAL,
             TPL_NOTIFY,
             InstallMemoryAttributesTableOnEndOfDxe,
             NULL,
             &gEfiEndOfDxeEventGroupGuid,
             &EndOfDxeEvent
             );
  ASSERT_EFI_ERROR (Status);
  return;
}

//
// Below functions are for MemoryMap
//

/**
  Converts a number of EFI_PAGEs to a size in bytes.

  NOTE: Do not use EFI_PAGES_TO_SIZE because it handles UINTN only.

  @param  Pages     The number of EFI_PAGES.

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

  @param  Size      A size in bytes.

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
  Acquire memory lock on mMemoryAttributesTableLock.
**/
STATIC
VOID
CoreAcquiremMemoryAttributesTableLock (
  VOID
  )
{
  CoreAcquireLock (&mMemoryAttributesTableLock);
}

/**
  Release memory lock on mMemoryAttributesTableLock.
**/
STATIC
VOID
CoreReleasemMemoryAttributesTableLock (
  VOID
  )
{
  CoreReleaseLock (&mMemoryAttributesTableLock);
}

/**
  Sort memory map entries based upon PhysicalStart, from low to high.

  @param  MemoryMap              A pointer to the buffer in which firmware places
                                 the current memory map.
  @param  MemoryMapSize          Size, in bytes, of the MemoryMap buffer.
  @param  DescriptorSize         Size, in bytes, of an individual EFI_MEMORY_DESCRIPTOR.
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
  Merge continous memory map entries whose have same attributes.

  @param  MemoryMap              A pointer to the buffer in which firmware places
                                 the current memory map.
  @param  MemoryMapSize          A pointer to the size, in bytes, of the
                                 MemoryMap buffer. On input, this is the size of
                                 the current memory map.  On output,
                                 it is the size of new memory map after merge.
  @param  DescriptorSize         Size, in bytes, of an individual EFI_MEMORY_DESCRIPTOR.
**/
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
      MergeGuardPages (NewMemoryMapEntry, NextMemoryMapEntry->PhysicalStart);
      MemoryBlockLength = (UINT64)(EfiPagesToSize (NewMemoryMapEntry->NumberOfPages));
      if (((UINTN)NextMemoryMapEntry < (UINTN)MemoryMapEnd) &&
          (NewMemoryMapEntry->Type == NextMemoryMapEntry->Type) &&
          (NewMemoryMapEntry->Attribute == NextMemoryMapEntry->Attribute) &&
          ((NewMemoryMapEntry->PhysicalStart + MemoryBlockLength) == NextMemoryMapEntry->PhysicalStart))
      {
        NewMemoryMapEntry->NumberOfPages += NextMemoryMapEntry->NumberOfPages;
        NextMemoryMapEntry                = NEXT_MEMORY_DESCRIPTOR (NextMemoryMapEntry, DescriptorSize);
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

  @param  MemoryMap              A pointer to the buffer in which firmware places
                                 the current memory map.
  @param  MemoryMapSize          Size, in bytes, of the MemoryMap buffer.
  @param  DescriptorSize         Size, in bytes, of an individual EFI_MEMORY_DESCRIPTOR.
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
    switch (MemoryMapEntry->Type) {
      case EfiRuntimeServicesCode:
        // do nothing
        break;
      case EfiRuntimeServicesData:
      case EfiMemoryMappedIO:
      case EfiMemoryMappedIOPortSpace:
        MemoryMapEntry->Attribute |= EFI_MEMORY_XP;
        break;
      case EfiReservedMemoryType:
      case EfiACPIMemoryNVS:
        break;
    }

    MemoryMapEntry = NEXT_MEMORY_DESCRIPTOR (MemoryMapEntry, DescriptorSize);
  }

  return;
}

/**
  Return the first image record, whose [ImageBase, ImageSize] covered by [Buffer, Length].

  @param Buffer  Start Address
  @param Length  Address length

  @return first image record covered by [buffer, length]
**/
STATIC
UEFI_IMAGE_RECORD *
GetImageRecordByAddress (
  IN EFI_PHYSICAL_ADDRESS  Buffer,
  IN UINT64                Length
  )
{
  UEFI_IMAGE_RECORD          *ImageRecord;
  LIST_ENTRY               *ImageRecordLink;
  LIST_ENTRY               *ImageRecordList;

  ImageRecordList = &mImagePropertiesPrivateData.ImageRecordList;

  for (ImageRecordLink = ImageRecordList->ForwardLink;
       ImageRecordLink != ImageRecordList;
       ImageRecordLink = ImageRecordLink->ForwardLink)
  {
    ImageRecord = CR (
                    ImageRecordLink,
                    UEFI_IMAGE_RECORD,
                    Link,
                    UEFI_IMAGE_RECORD_SIGNATURE
                    );

    if ((Buffer <= ImageRecord->StartAddress) &&
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

  @param  ImageRecord            An image record whose [ImageBase, ImageSize] covered
                                 by old memory map entry.
  @param  NewRecord              A pointer to several new memory map entries.
                                 The caller gurantee the buffer size be 1 +
                                 (SplitRecordCount * DescriptorSize) calculated
                                 below.
  @param  OldRecord              A pointer to one old memory map entry.
  @param  DescriptorSize         Size, in bytes, of an individual EFI_MEMORY_DESCRIPTOR.
**/
STATIC
UINTN
SetNewRecord (
  IN UEFI_IMAGE_RECORD             *ImageRecord,
  IN OUT EFI_MEMORY_DESCRIPTOR  *NewRecord,
  IN EFI_MEMORY_DESCRIPTOR      *OldRecord,
  IN UINTN                      DescriptorSize
  )
{
  UEFI_IMAGE_RECORD_SEGMENT                 *ImageRecordSegment;
  UINTN                                     SectionAddress;
  UINT32                                    Index;
  UINT32                                    NewRecordCount;

  if (PcdGetBool (PcdMergeRuntimeDataSegments)) {
    ImageRecordSegment = &ImageRecord->Segments[1];
    SectionAddress = ImageRecord->StartAddress + ImageRecord->Segments[0].Size;

    NewRecordCount    = 0;
    if (SectionAddress > OldRecord->PhysicalStart) {
      NewRecord->Type = OldRecord->Type;
      NewRecord->PhysicalStart = OldRecord->PhysicalStart;
      NewRecord->VirtualStart  = 0;
      NewRecord->NumberOfPages = EfiSizeToPages (SectionAddress - OldRecord->PhysicalStart);
      NewRecord->Attribute     = OldRecord->Attribute | EFI_MEMORY_XP;
      NewRecord = NEXT_MEMORY_DESCRIPTOR (NewRecord, DescriptorSize);
      NewRecordCount++;
    }

    NewRecord->Type          = OldRecord->Type;
    NewRecord->PhysicalStart = SectionAddress;
    NewRecord->VirtualStart  = 0;
    NewRecord->NumberOfPages = EfiSizeToPages (ImageRecordSegment->Size);
    NewRecord->Attribute     = (OldRecord->Attribute & ~(UINT64) EFI_MEMORY_ACCESS_MASK) | ImageRecordSegment->Attributes;

    NewRecord= NEXT_MEMORY_DESCRIPTOR (NewRecord, DescriptorSize);
    NewRecordCount++;

    return NewRecordCount;
  }

  //
  // Always create a new entry for non-PE image record
  //
  NewRecordCount    = 0;
  if (ImageRecord->StartAddress > OldRecord->PhysicalStart) {
    NewRecord->Type = OldRecord->Type;
    NewRecord->PhysicalStart = OldRecord->PhysicalStart;
    NewRecord->VirtualStart  = 0;
    NewRecord->NumberOfPages = EfiSizeToPages (ImageRecord->StartAddress - OldRecord->PhysicalStart);
    NewRecord->Attribute     = OldRecord->Attribute;
    NewRecord = NEXT_MEMORY_DESCRIPTOR (NewRecord, DescriptorSize);
    NewRecordCount++;
  }

  SectionAddress = ImageRecord->StartAddress;
  for (Index = 0; Index < ImageRecord->NumSegments; ++Index) {
    ImageRecordSegment = &ImageRecord->Segments[Index];

    NewRecord->Type          = OldRecord->Type;
    NewRecord->PhysicalStart = SectionAddress;
    NewRecord->VirtualStart  = 0;
    NewRecord->NumberOfPages = EfiSizeToPages (ImageRecordSegment->Size);
    NewRecord->Attribute     = (OldRecord->Attribute & ~(UINT64) EFI_MEMORY_ACCESS_MASK) | ImageRecordSegment->Attributes;

    SectionAddress += ImageRecordSegment->Size;
    NewRecord= NEXT_MEMORY_DESCRIPTOR (NewRecord, DescriptorSize);
  }

  return NewRecordCount + ImageRecord->NumSegments;
}

/**
  Return the max number of new splitted entries, according to one old entry,
  based upon PE code section and data section.

  @param  OldRecord              A pointer to one old memory map entry.

  @retval  0 no entry need to be splitted.
  @return  the max number of new splitted entries
**/
STATIC
UINTN
GetMaxSplitRecordCount (
  IN EFI_MEMORY_DESCRIPTOR  *OldRecord
  )
{
  UEFI_IMAGE_RECORD       *ImageRecord;
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
    SplitRecordCount += ImageRecord->NumSegments + 1;
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

  @param  OldRecord              A pointer to one old memory map entry.
  @param  NewRecord              A pointer to several new memory map entries.
                                 The caller gurantee the buffer size be 1 +
                                 (SplitRecordCount * DescriptorSize) calculated
                                 below.
  @param  MaxSplitRecordCount    The max number of splitted entries
  @param  DescriptorSize         Size, in bytes, of an individual EFI_MEMORY_DESCRIPTOR.

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
  UEFI_IMAGE_RECORD       *ImageRecord;
  UEFI_IMAGE_RECORD       *NewImageRecord;
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
        NewRecord->Type = TempRecord.Type;
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
    if (PcdGetBool (PcdMergeRuntimeDataSegments)) {
      //
      // Merge .data (and .reloc) segment of the current driver with
      // header segment of the next one.
      //
      // +---------------------+
      // | Record X            |
      // +---------------------+ ----
      // | header (segment[0]) |     |
      // +---------------------+     |
      // | .code  (segment[1]) |     |
      // +---------------------+     |-> PE/COFF1
      // | .data  (segemtn[2]) |     |
      // +                     +     |
      // | .reloc (segment[3]) |     |
      // +                     + ----
      // | header (segment[0]) |     |
      // +---------------------+     |
      // | .code  (segemtn[1]) |     |-> PE/COFF2
      // +---------------------+     |
      // | ...                 |     |
      // +---------------------+
      //
      PhysicalStart = ImageRecord->StartAddress + ImageRecord->Segments[0].Size + ImageRecord->Segments[1].Size;
    } else {
      PhysicalStart = ImageRecord->EndAddress;
    }

    TempRecord.PhysicalStart = PhysicalStart;
    TempRecord.NumberOfPages = EfiSizeToPages (PhysicalEnd - PhysicalStart);
  } while ((ImageRecord != NULL) && (PhysicalStart < PhysicalEnd));

  //
  // The logic in function SplitTable() ensures that TotalNewRecordCount will not be zero if the
  // code reaches here.
  //
  ASSERT (TotalNewRecordCount != 0);
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
   +---------------+ ----
   | Record RtData |     |
   +---------------+     |
   | Record RtCode |     |-> PE/COFF1
   +---------------+     |
   | Record RtData |     |
   +---------------+ ----
   | Record RtData |     |
   +---------------+     |
   | Record RtCode |     |-> PE/COFF2
   +---------------+     |
   | Record RtData |     |
   +---------------+ ----
   | Record Y      |
   +---------------+

  @param  MemoryMapSize          A pointer to the size, in bytes, of the
                                 MemoryMap buffer. On input, this is the size of
                                 old MemoryMap before split. The actual buffer
                                 size of MemoryMap is MemoryMapSize +
                                 (AdditionalRecordCount * DescriptorSize) calculated
                                 below. On output, it is the size of new MemoryMap
                                 after split.
  @param  MemoryMap              A pointer to the buffer in which firmware places
                                 the current memory map.
  @param  DescriptorSize         Size, in bytes, of an individual EFI_MEMORY_DESCRIPTOR.
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
  AdditionalRecordCount = (mImagePropertiesPrivateData.SectionCountMax + 1) * mImagePropertiesPrivateData.ImageRecordCount + 1;

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
        RealSplitRecordCount * DescriptorSize
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
  This function for GetMemoryMap() with properties table capability.

  It calls original GetMemoryMap() to get the original memory map information. Then
  plus the additional memory map entries for PE Code/Data seperation.

  @param  MemoryMapSize          A pointer to the size, in bytes, of the
                                 MemoryMap buffer. On input, this is the size of
                                 the buffer allocated by the caller.  On output,
                                 it is the size of the buffer returned by the
                                 firmware  if the buffer was large enough, or the
                                 size of the buffer needed  to contain the map if
                                 the buffer was too small.
  @param  MemoryMap              A pointer to the buffer in which firmware places
                                 the current memory map.
  @param  MapKey                 A pointer to the location in which firmware
                                 returns the key for the current memory map.
  @param  DescriptorSize         A pointer to the location in which firmware
                                 returns the size, in bytes, of an individual
                                 EFI_MEMORY_DESCRIPTOR.
  @param  DescriptorVersion      A pointer to the location in which firmware
                                 returns the version number associated with the
                                 EFI_MEMORY_DESCRIPTOR.

  @retval EFI_SUCCESS            The memory map was returned in the MemoryMap
                                 buffer.
  @retval EFI_BUFFER_TOO_SMALL   The MemoryMap buffer was too small. The current
                                 buffer size needed to hold the memory map is
                                 returned in MemoryMapSize.
  @retval EFI_INVALID_PARAMETER  One of the parameters has an invalid value.

**/
EFI_STATUS
EFIAPI
CoreGetMemoryMapWithSeparatedImageSection (
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
  if (!mMemoryAttributesTableEnable) {
    return CoreGetMemoryMap (MemoryMapSize, MemoryMap, MapKey, DescriptorSize, DescriptorVersion);
  }

  if (MemoryMapSize == NULL) {
    return EFI_INVALID_PARAMETER;
  }

  CoreAcquiremMemoryAttributesTableLock ();

  //
  // Per image, they may be one trailer. There may be prefixed data.
  //
  AdditionalRecordCount = (mImagePropertiesPrivateData.SectionCountMax + 1) * mImagePropertiesPrivateData.ImageRecordCount + 1;

  OldMemoryMapSize = *MemoryMapSize;
  Status           = CoreGetMemoryMap (MemoryMapSize, MemoryMap, MapKey, DescriptorSize, DescriptorVersion);
  if (Status == EFI_BUFFER_TOO_SMALL) {
    *MemoryMapSize = *MemoryMapSize + (*DescriptorSize) * AdditionalRecordCount;
  } else if (Status == EFI_SUCCESS) {
    ASSERT (MemoryMap != NULL);
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
      SplitTable (MemoryMapSize, MemoryMap, *DescriptorSize);
    }
  }

  CoreReleasemMemoryAttributesTableLock ();
  return Status;
}

//
// Below functions are for ImageRecord
//

/**
  Set MemoryAttributesTable according to PE/COFF image section alignment.

  @param  SectionAlignment    PE/COFF section alignment
**/
STATIC
VOID
SetMemoryAttributesTableSectionAlignment (
  IN UINT32  SectionAlignment
  )
{
  if (((SectionAlignment & (RUNTIME_PAGE_ALLOCATION_GRANULARITY - 1)) != 0) &&
      mMemoryAttributesTableEnable)
  {
    DEBUG ((DEBUG_VERBOSE, "SetMemoryAttributesTableSectionAlignment - Clear\n"));
    mMemoryAttributesTableEnable = FALSE;
  }
}

/**
  Sort image record based upon the ImageBase from low to high.
**/
STATIC
VOID
InsertSortImageRecord (
  IN UEFI_IMAGE_RECORD        *NewImageRecord
  )
{
  UEFI_IMAGE_RECORD            *ImageRecord;
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
                    UEFI_IMAGE_RECORD,
                    Link,
                    UEFI_IMAGE_RECORD_SIGNATURE
                    );
    if (NewImageRecord->StartAddress < ImageRecord->StartAddress) {
      break;
    }

    PrevImageRecordLink = ImageRecordLink;
  }

  InsertHeadList (PrevImageRecordLink, &NewImageRecord->Link);
  mImagePropertiesPrivateData.ImageRecordCount++;

  if (mImagePropertiesPrivateData.SectionCountMax < NewImageRecord->NumSegments) {
    mImagePropertiesPrivateData.SectionCountMax = NewImageRecord->NumSegments;
  }
}

/**
  Insert image record.

  @param  RuntimeImage    Runtime image information
**/
VOID
InsertImageRecord (
  IN     LOADED_IMAGE_PRIVATE_DATA        *Image,
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *ImageContext
  )
{
  RETURN_STATUS                        PdbStatus;
  EFI_RUNTIME_IMAGE_ENTRY              *RuntimeImage;
  UINT32                                SectionAlignment;
  UEFI_IMAGE_RECORD                    *ImageRecord;
  CONST CHAR8                          *PdbPointer;
  UINT32                               PdbSize;

  RuntimeImage = Image->RuntimeData;

  DEBUG ((DEBUG_VERBOSE, "InsertImageRecord - 0x%x\n", RuntimeImage));
  DEBUG ((DEBUG_VERBOSE, "InsertImageRecord - 0x%016lx - 0x%016lx\n", (EFI_PHYSICAL_ADDRESS)(UINTN)RuntimeImage->ImageBase, RuntimeImage->ImageSize));

  if (mMemoryAttributesTableEndOfDxe) {
    DEBUG ((DEBUG_INFO, "Do not insert runtime image record after EndOfDxe\n"));
    return;
  }

  DEBUG ((DEBUG_VERBOSE, "ImageRecordCount - 0x%x\n", mImagePropertiesPrivateData.ImageRecordCount));

  PdbStatus = UefiImageGetSymbolsPath (ImageContext, &PdbPointer, &PdbSize);
  if (!EFI_ERROR (PdbStatus)) {
    DEBUG ((DEBUG_VERBOSE, "  Image - %a\n", PdbPointer));
  }

  //
  // Get SectionAlignment
  //
  SectionAlignment  = UefiImageGetSegmentAlignment (ImageContext);

  SetMemoryAttributesTableSectionAlignment (SectionAlignment);
  if ((SectionAlignment & (RUNTIME_PAGE_ALLOCATION_GRANULARITY - 1)) != 0) {
    DEBUG ((
      DEBUG_WARN,
      "!!!!!!!!  InsertImageRecord - Section Alignment(0x%x) is not %dK  !!!!!!!!\n",
      SectionAlignment, RUNTIME_PAGE_ALLOCATION_GRANULARITY >> 10));
    if (!EFI_ERROR (PdbStatus)) {
      DEBUG ((DEBUG_WARN, "!!!!!!!!  Image - %a  !!!!!!!!\n", PdbPointer));
    }

    goto Finish;
  }

  ImageRecord = UefiImageLoaderGetImageRecord (ImageContext);
  if (ImageRecord == NULL) {
    return ;
  }

  UefiImageDebugPrintSegments (ImageContext);
  UefiImageDebugPrintImageRecord (ImageRecord);

  //
  // Section order is guaranteed by the PE specification.
  // Section validity (e.g. no overlap) is guaranteed by the PE specification.
  //

  InsertSortImageRecord (ImageRecord);

Finish:
  return;
}

/**
  Find image record according to image base and size.

  @param  ImageBase    Base of PE image
  @param  ImageSize    Size of PE image

  @return image record
**/
STATIC
UEFI_IMAGE_RECORD *
FindImageRecord (
  IN EFI_PHYSICAL_ADDRESS  ImageBase
  )
{
  UEFI_IMAGE_RECORD          *ImageRecord;
  LIST_ENTRY               *ImageRecordLink;
  LIST_ENTRY               *ImageRecordList;

  ImageRecordList = &mImagePropertiesPrivateData.ImageRecordList;

  for (ImageRecordLink = ImageRecordList->ForwardLink;
       ImageRecordLink != ImageRecordList;
       ImageRecordLink = ImageRecordLink->ForwardLink)
  {
    ImageRecord = CR (
                    ImageRecordLink,
                    UEFI_IMAGE_RECORD,
                    Link,
                    UEFI_IMAGE_RECORD_SIGNATURE
                    );

    if (ImageBase == ImageRecord->StartAddress)
    {
      return ImageRecord;
    }
  }

  return NULL;
}

/**
  Remove Image record.

  @param  RuntimeImage    Runtime image information
**/
VOID
RemoveImageRecord (
  IN EFI_RUNTIME_IMAGE_ENTRY  *RuntimeImage
  )
{
  UEFI_IMAGE_RECORD                 *ImageRecord;

  DEBUG ((DEBUG_VERBOSE, "RemoveImageRecord - 0x%x\n", RuntimeImage));
  DEBUG ((DEBUG_VERBOSE, "RemoveImageRecord - 0x%016lx - 0x%016lx\n", (EFI_PHYSICAL_ADDRESS)(UINTN)RuntimeImage->ImageBase, RuntimeImage->ImageSize));

  if (mMemoryAttributesTableEndOfDxe) {
    DEBUG ((DEBUG_INFO, "Do not remove runtime image record after EndOfDxe\n"));
    return;
  }

  ImageRecord = FindImageRecord ((EFI_PHYSICAL_ADDRESS)(UINTN)RuntimeImage->ImageBase);
  if (ImageRecord == NULL) {
    DEBUG ((DEBUG_ERROR, "!!!!!!!! ImageRecord not found !!!!!!!!\n"));
    return;
  }

  RemoveEntryList (&ImageRecord->Link);
  FreePool (ImageRecord);
  mImagePropertiesPrivateData.ImageRecordCount--;
}
