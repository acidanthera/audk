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
#include <Library/ImagePropertiesRecordLib.h>

#include <Library/UefiImageLib.h>

#include <Guid/PiSmmMemoryAttributesTable.h>

#include "PiSmmCore.h"
#include "ProcessorBind.h"

#define PREVIOUS_MEMORY_DESCRIPTOR(MemoryDescriptor, Size) \
  ((EFI_MEMORY_DESCRIPTOR *)((UINT8 *)(MemoryDescriptor) - (Size)))

#define IMAGE_PROPERTIES_PRIVATE_DATA_SIGNATURE  SIGNATURE_32 ('I','P','P','D')

typedef struct {
  UINT32        Signature;
  UINTN         ImageRecordCount;
  UINT32        NumberOfSectionsMax;
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
      MemoryBlockLength = LShiftU64 (MemoryMapEntry->NumberOfPages, EFI_PAGE_SHIFT);
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
      SplitTable (MemoryMapSize, MemoryMap, *DescriptorSize, &mImagePropertiesPrivateData.ImageRecordList, AdditionalRecordCount);

      //
      // Set RuntimeData to XP
      //
      EnforceMemoryMapAttribute (MemoryMap, *MemoryMapSize, *DescriptorSize);

      //
      // Merge same type to save entry size
      //
      MergeMemoryMap (MemoryMap, MemoryMapSize, *DescriptorSize);
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
  IN UEFI_IMAGE_RECORD  *NewImageRecord
  )
{
  UEFI_IMAGE_RECORD  *ImageRecord;
  LIST_ENTRY         *PrevImageRecordLink;
  LIST_ENTRY         *ImageRecordLink;
  LIST_ENTRY         *ImageRecordList;

  ImageRecordList = &mImagePropertiesPrivateData.ImageRecordList;

  PrevImageRecordLink = ImageRecordList;
  for (
       ImageRecordLink = GetFirstNode (ImageRecordList);
       !IsNull (ImageRecordLink, ImageRecordList);
       ImageRecordLink = GetNextNode (ImageRecordList, PrevImageRecordLink)
       )
  {
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

  if (mImagePropertiesPrivateData.NumberOfSectionsMax < NewImageRecord->NumSegments) {
    mImagePropertiesPrivateData.NumberOfSectionsMax = NewImageRecord->NumSegments;
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
  UEFI_IMAGE_RECORD  *ImageRecord;
  LIST_ENTRY         *ImageRecordLink;
  LIST_ENTRY         *ImageRecordList;
  UINTN              Index;

  ImageRecordList = &mImagePropertiesPrivateData.ImageRecordList;

  for (ImageRecordLink = ImageRecordList->ForwardLink, Index = 0;
       ImageRecordLink != ImageRecordList;
       ImageRecordLink = ImageRecordLink->ForwardLink, Index++)
  {
    ImageRecord = CR (
                    ImageRecordLink,
                    UEFI_IMAGE_RECORD,
                    Link,
                    UEFI_IMAGE_RECORD_SIGNATURE
                    );
    DEBUG ((DEBUG_VERBOSE, "SMM  Image[%d]: 0x%016lx - 0x%016lx\n", Index, ImageRecord->StartAddress, ImageRecord->EndAddress - ImageRecord->StartAddress));
  }
}

/**
  Insert image record.

  @param[in]  DriverEntry    Driver information
**/
VOID
SmmInsertImageRecord (
  IN EFI_LOADED_IMAGE_PROTOCOL        *LoadedImage,
  IN UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *ImageContext
  )
{
  RETURN_STATUS      PdbStatus;
  PHYSICAL_ADDRESS   ImageBuffer;
  UINTN              NumberOfPage;
  UINT32             SectionAlignment;
  UEFI_IMAGE_RECORD  *ImageRecord;
  CONST CHAR8        *PdbPointer;
  UINT32             PdbSize;

  ImageBuffer  = (UINTN)LoadedImage->ImageBase;
  NumberOfPage = EFI_SIZE_TO_PAGES ((UINTN)LoadedImage->ImageSize);

  DEBUG ((DEBUG_VERBOSE, "SMM InsertImageRecord - 0x%016lx - 0x%08x\n", ImageBuffer, NumberOfPage));

  DEBUG ((DEBUG_VERBOSE, "SMM ImageRecordCount - 0x%x\n", mImagePropertiesPrivateData.ImageRecordCount));

  PdbStatus = UefiImageGetSymbolsPath (ImageContext, &PdbPointer, &PdbSize);
  if (!RETURN_ERROR (PdbStatus)) {
    DEBUG ((DEBUG_VERBOSE, "SMM   Image - %a\n", PdbPointer));
  }

  //
  // Get SectionAlignment
  //
  SectionAlignment = UefiImageGetSegmentAlignment (ImageContext);

  SetMemoryAttributesTableSectionAlignment (SectionAlignment);
  if ((SectionAlignment & (RUNTIME_PAGE_ALLOCATION_GRANULARITY - 1)) != 0) {
    DEBUG ((
      DEBUG_WARN,
      "SMM !!!!!!!!  InsertImageRecord - Section Alignment(0x%x) is not %dK  !!!!!!!!\n",
      SectionAlignment,
      RUNTIME_PAGE_ALLOCATION_GRANULARITY >> 10
      ));
    if (!RETURN_ERROR (PdbStatus)) {
      DEBUG ((DEBUG_WARN, "SMM !!!!!!!!  Image - %a  !!!!!!!!\n", PdbPointer));
    }

    return;
  }

  //
  // The image headers are not recorded among the sections, allocate one more.
  //
  ImageRecord = UefiImageLoaderGetImageRecord (ImageContext);
  if (ImageRecord == NULL) {
    return;
  }

  UefiImageDebugPrintSegments (ImageContext);
  UefiImageDebugPrintImageRecord (ImageRecord);

  InsertSortImageRecord (ImageRecord);
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

  DEBUG_CODE_BEGIN ();
  if ( mImagePropertiesPrivateData.ImageRecordCount > 0) {
    DEBUG ((DEBUG_INFO, "SMM - Total Runtime Image Count - 0x%x\n", mImagePropertiesPrivateData.ImageRecordCount));
    DEBUG ((DEBUG_INFO, "SMM - Dump Runtime Image Records:\n"));
    DumpImageRecord ();
  }

  DEBUG_CODE_END ();

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
