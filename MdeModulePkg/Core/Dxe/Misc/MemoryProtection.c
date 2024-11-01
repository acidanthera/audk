/** @file
  UEFI Memory Protection support.

  If the UEFI image is page aligned, the image code section is set to read only
  and the image data section is set to non-executable.

  1) This policy is applied for all UEFI image including boot service driver,
     runtime driver or application.
  2) This policy is applied only if the UEFI image meets the page alignment
     requirement.
  3) This policy is applied only if the Source UEFI image matches the
     PcdImageProtectionPolicy definition.

  The DxeCore calls CpuArchProtocol->SetMemoryAttributes() to protect
  the image. If the CpuArch protocol is not installed yet, the DxeCore
  enqueues the protection request. Once the CpuArch is installed, the
  DxeCore dequeues the protection request and applies policy.

  Once the image is unloaded, the protection is removed automatically.

Copyright (c) 2017 - 2018, Intel Corporation. All rights reserved.<BR>
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
#include <Library/ImagePropertiesRecordLib.h>

#include <Guid/EventGroup.h>
#include <Guid/MemoryAttributesTable.h>

#include <Protocol/FirmwareVolume2.h>
#include <Protocol/SimpleFileSystem.h>

#include "Base.h"
#include "DxeMain.h"
#include "Library/UefiImageLib.h"
#include "Mem/HeapGuard.h"
#include "ProcessorBind.h"
#include "Uefi/UefiMultiPhase.h"

#define PREVIOUS_MEMORY_DESCRIPTOR(MemoryDescriptor, Size) \
  ((EFI_MEMORY_DESCRIPTOR *)((UINT8 *)(MemoryDescriptor) - (Size)))

UINT32  mImageProtectionPolicy;

extern LIST_ENTRY  mGcdMemorySpaceMap;

STATIC LIST_ENTRY  mProtectedImageRecordList;

/**
  Set UEFI image memory attributes.

  @param[in]  BaseAddress            Specified start address
  @param[in]  Length                 Specified length
  @param[in]  Attributes             Specified attributes
**/
VOID
SetUefiImageMemoryAttributes (
  IN UINT64  BaseAddress,
  IN UINT64  Length,
  IN UINT64  Attributes
  )
{
  EFI_STATUS                       Status;
  EFI_GCD_MEMORY_SPACE_DESCRIPTOR  Descriptor;
  UINT64                           FinalAttributes;

  Status = CoreGetMemorySpaceDescriptor (BaseAddress, &Descriptor);
  ASSERT_EFI_ERROR (Status);

  FinalAttributes = (Descriptor.Attributes & EFI_CACHE_ATTRIBUTE_MASK) | (Attributes & EFI_MEMORY_ATTRIBUTE_MASK);

  DEBUG ((DEBUG_INFO, "SetUefiImageMemoryAttributes - 0x%016lx - 0x%016lx (0x%016lx)\n", BaseAddress, Length, FinalAttributes));

  ASSERT (gCpu != NULL);
  gCpu->SetMemoryAttributes (gCpu, BaseAddress, Length, FinalAttributes);
}

/**
  Set UEFI image protection attributes.

  @param[in]  ImageRecord    A UEFI image record
  @param[in]  IsUser         Whether UEFI image record is User Image.
**/
VOID
SetUefiImageProtectionAttributes (
  IN UEFI_IMAGE_RECORD  *ImageRecord,
  IN BOOLEAN            IsUser
  )
{
  UEFI_IMAGE_RECORD_SEGMENT  *ImageRecordSegment;
  UINTN                      SectionAddress;
  UINT32                     Index;
  UINT32                     Attribute;

  Attribute = IsUser ? EFI_MEMORY_USER : 0;

  SectionAddress = ImageRecord->StartAddress;
  for (Index = 0; Index < ImageRecord->NumSegments; Index++) {
    ImageRecordSegment = &ImageRecord->Segments[Index];
    SetUefiImageMemoryAttributes (
      SectionAddress,
      ImageRecordSegment->Size,
      ImageRecordSegment->Attributes | Attribute
      );

    SectionAddress += ImageRecordSegment->Size;
  }
}

/**
  Return if the PE image section is aligned.

  @param[in]  SectionAlignment    PE/COFF section alignment
  @param[in]  MemoryType          PE/COFF image memory type

  @retval TRUE  The PE image section is aligned.
  @retval FALSE The PE image section is not aligned.
**/
STATIC
BOOLEAN
IsMemoryProtectionSectionAligned (
  IN UINT32           SectionAlignment,
  IN EFI_MEMORY_TYPE  MemoryType
  )
{
  UINT32  PageAlignment;

  switch (MemoryType) {
    case EfiRuntimeServicesCode:
    case EfiACPIMemoryNVS:
    case EfiReservedMemoryType:
      PageAlignment = RUNTIME_PAGE_ALLOCATION_GRANULARITY;
      break;
    case EfiRuntimeServicesData:
      ASSERT (FALSE);
      PageAlignment = RUNTIME_PAGE_ALLOCATION_GRANULARITY;
      break;
    case EfiBootServicesCode:
    case EfiLoaderCode:
      PageAlignment = EFI_PAGE_SIZE;
      break;
    case EfiACPIReclaimMemory:
    default:
      ASSERT (FALSE);
      PageAlignment = EFI_PAGE_SIZE;
      break;
  }

  if ((SectionAlignment & (PageAlignment - 1)) != 0) {
    return FALSE;
  } else {
    return TRUE;
  }
}

// FIXME: Deduplicate
/**
  Protect UEFI PE/COFF image.

  @param[in]  LoadedImage              The loaded image protocol
  @param[in]  ImageOrigin              Where File comes from.
  @param[in]  LoadedImageDevicePath    The loaded image device path protocol
  @param[in]  IsUserImage              Whether the loaded image is in user space.
**/
VOID
ProtectUefiImage (
  IN EFI_LOADED_IMAGE_PROTOCOL        *LoadedImage,
  IN UINT8                            ImageOrigin,
  IN UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *ImageContext,
  IN BOOLEAN                          IsUserImage
  )
{
  RETURN_STATUS      PdbStatus;
  UINT32             SectionAlignment;
  UEFI_IMAGE_RECORD  *ImageRecord;
  CONST CHAR8        *PdbPointer;
  UINT32             PdbSize;
  BOOLEAN            IsAligned;
  //
  // Do not protect images, if policy allows.
  //
  if ((mImageProtectionPolicy & (BIT30 >> ImageOrigin)) != 0) {
    return;
  }

  DEBUG ((DEBUG_INFO, "ProtectUefiImageCommon - 0x%x\n", LoadedImage));
  DEBUG ((DEBUG_INFO, "  - 0x%016lx - 0x%016lx\n", (EFI_PHYSICAL_ADDRESS)(UINTN)LoadedImage->ImageBase, LoadedImage->ImageSize));

  PdbStatus = UefiImageGetSymbolsPath (ImageContext, &PdbPointer, &PdbSize);
  if (!RETURN_ERROR (PdbStatus)) {
    DEBUG ((DEBUG_VERBOSE, "  Image - %a\n", PdbPointer));
  }

  //
  // Get SectionAlignment
  //
  SectionAlignment = UefiImageGetSegmentAlignment (ImageContext);

  IsAligned = IsMemoryProtectionSectionAligned (SectionAlignment, LoadedImage->ImageCodeType);
  if (!IsAligned) {
    DEBUG ((
      DEBUG_VERBOSE,
      "!!!!!!!!  ProtectUefiImageCommon - Section Alignment(0x%x) is incorrect  !!!!!!!!\n",
      SectionAlignment));
    if (!RETURN_ERROR (PdbStatus)) {
      DEBUG ((DEBUG_VERBOSE, "!!!!!!!!  Image - %a  !!!!!!!!\n", PdbPointer));
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
  // Record the image record in the list so we can undo the protections later
  //
  InsertTailList (&mProtectedImageRecordList, &ImageRecord->Link);

  if (gCpu != NULL) {
    //
    // CPU ARCH present. Update memory attribute directly.
    //
    if (PcdGetBool (PcdEnableUserSpace)) {
      SetUefiImageProtectionAttributes (ImageRecord, IsUserImage);
    } else {
      SetUefiImageProtectionAttributes (ImageRecord, FALSE);
    }
  }

Finish:
  return;
}

/**
  Unprotect UEFI image.

  @param[in]  LoadedImage              The loaded image protocol
  @param[in]  LoadedImageDevicePath    The loaded image device path protocol
**/
VOID
UnprotectUefiImage (
  IN EFI_LOADED_IMAGE_PROTOCOL  *LoadedImage,
  IN EFI_DEVICE_PATH_PROTOCOL   *LoadedImageDevicePath
  )
{
  UEFI_IMAGE_RECORD  *ImageRecord;
  LIST_ENTRY         *ImageRecordLink;

  for (ImageRecordLink = mProtectedImageRecordList.ForwardLink;
        ImageRecordLink != &mProtectedImageRecordList;
        ImageRecordLink = ImageRecordLink->ForwardLink) {
    ImageRecord = CR (
                    ImageRecordLink,
                    UEFI_IMAGE_RECORD,
                    Link,
                    UEFI_IMAGE_RECORD_SIGNATURE
                    );

    if (ImageRecord->StartAddress == (EFI_PHYSICAL_ADDRESS)(UINTN)LoadedImage->ImageBase) {
      // TODO: Revise for removal (e.g. CpuDxe integration)
      if (gCpu != NULL) {
        SetUefiImageMemoryAttributes (
          ImageRecord->StartAddress,
          ImageRecord->EndAddress - ImageRecord->StartAddress,
          0
          );
      }
      RemoveEntryList (&ImageRecord->Link);
      FreePool (ImageRecord);
      return;
    }
  }
}

/**
  Change UEFI image owner: Supervisor / Privileged or User / Unprivileged.

  @param[in]  LoadedImage              The loaded image protocol
  @param[in]  LoadedImageDevicePath    The loaded image device path protocol
  @param[in]  IsUser                   Whether UEFI image record is User Image.
**/
VOID
ChangeUefiImageRing (
  IN EFI_LOADED_IMAGE_PROTOCOL  *LoadedImage,
  IN EFI_DEVICE_PATH_PROTOCOL   *LoadedImageDevicePath,
  IN BOOLEAN                    IsUser
  )
{
  UEFI_IMAGE_RECORD          *ImageRecord;
  LIST_ENTRY                 *ImageRecordLink;

  for (ImageRecordLink = mProtectedImageRecordList.ForwardLink;
        ImageRecordLink != &mProtectedImageRecordList;
        ImageRecordLink = ImageRecordLink->ForwardLink)
    {
    ImageRecord = CR (
                    ImageRecordLink,
                    UEFI_IMAGE_RECORD,
                    Link,
                    UEFI_IMAGE_RECORD_SIGNATURE
                    );

    if (ImageRecord->StartAddress == (EFI_PHYSICAL_ADDRESS)(UINTN)LoadedImage->ImageBase) {
      ASSERT (gCpu != NULL);

      SetUefiImageProtectionAttributes (ImageRecord, IsUser);

      return;
    }
  }
}

/**
  Return the EFI memory permission attribute associated with memory
  type 'MemoryType' under the configured DXE memory protection policy.

  @param MemoryType       Memory type.
**/
STATIC
UINT64
GetPermissionAttributeForMemoryType (
  IN EFI_MEMORY_TYPE  MemoryType
  )
{
  UINT64  TestBit;
  UINT64  Attributes;

  Attributes = 0;

  if ((UINT32)MemoryType >= MEMORY_TYPE_OS_RESERVED_MIN) {
    TestBit = BIT63;
  } else if ((UINT32)MemoryType >= MEMORY_TYPE_OEM_RESERVED_MIN) {
    TestBit = BIT62;
  } else {
    TestBit = LShiftU64 (1, MemoryType);
  }

  if ((PcdGet64 (PcdDxeNxMemoryProtectionPolicy) & TestBit) != 0) {
    Attributes |= EFI_MEMORY_XP;
  }

  if (MemoryType == EfiRing3MemoryType) {
    Attributes |= EFI_MEMORY_USER;
  }

  return Attributes;
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
}

/**
  Merge adjacent memory map entries if they use the same memory protection policy

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
MergeMemoryMapForProtectionPolicy (
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
  UINT64                 Attributes;

  SortMemoryMap (MemoryMap, *MemoryMapSize, DescriptorSize);

  MemoryMapEntry    = MemoryMap;
  NewMemoryMapEntry = MemoryMap;
  MemoryMapEnd      = (EFI_MEMORY_DESCRIPTOR *)((UINT8 *)MemoryMap + *MemoryMapSize);
  while ((UINTN)MemoryMapEntry < (UINTN)MemoryMapEnd) {
    CopyMem (NewMemoryMapEntry, MemoryMapEntry, sizeof (EFI_MEMORY_DESCRIPTOR));
    NextMemoryMapEntry = NEXT_MEMORY_DESCRIPTOR (MemoryMapEntry, DescriptorSize);

    do {
      MemoryBlockLength = (UINT64)(EFI_PAGES_TO_SIZE ((UINTN)MemoryMapEntry->NumberOfPages));
      Attributes        = GetPermissionAttributeForMemoryType (MemoryMapEntry->Type);

      if (((UINTN)NextMemoryMapEntry < (UINTN)MemoryMapEnd) &&
          (Attributes == GetPermissionAttributeForMemoryType (NextMemoryMapEntry->Type)) &&
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
  Remove exec permissions from all regions whose type is identified by
  PcdDxeNxMemoryProtectionPolicy.
**/
VOID
InitializeDxeNxMemoryProtectionPolicy (
  VOID
  )
{
  UINTN                      MemoryMapSize;
  UINTN                      MapKey;
  UINTN                      DescriptorSize;
  UINT32                     DescriptorVersion;
  EFI_MEMORY_DESCRIPTOR      *MemoryMap;
  EFI_MEMORY_DESCRIPTOR      *MemoryMapEntry;
  EFI_MEMORY_DESCRIPTOR      *MemoryMapEnd;
  EFI_STATUS                 Status;
  UINT64                     Attributes;
  LIST_ENTRY                 *Link;
  EFI_GCD_MAP_ENTRY          *Entry;
  EFI_PEI_HOB_POINTERS       Hob;
  EFI_HOB_MEMORY_ALLOCATION  *MemoryHob;
  EFI_PHYSICAL_ADDRESS       StackBase;

  //
  // Get the EFI memory map.
  //
  MemoryMapSize = 0;
  MemoryMap     = NULL;

  Status = gBS->GetMemoryMap (
                  &MemoryMapSize,
                  MemoryMap,
                  &MapKey,
                  &DescriptorSize,
                  &DescriptorVersion
                  );
  ASSERT (Status == EFI_BUFFER_TOO_SMALL);
  do {
    MemoryMap = (EFI_MEMORY_DESCRIPTOR *)AllocatePool (MemoryMapSize);
    ASSERT (MemoryMap != NULL);
    Status = gBS->GetMemoryMap (
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

  ASSERT_EFI_ERROR (Status);

  StackBase = 0;
  if (PcdGetBool (PcdCpuStackGuard)) {
    //
    // Get the base of stack from Hob.
    //
    Hob.Raw = GetHobList ();
    while ((Hob.Raw = GetNextHob (EFI_HOB_TYPE_MEMORY_ALLOCATION, Hob.Raw)) != NULL) {
      MemoryHob = Hob.MemoryAllocation;
      if (CompareGuid (&gEfiHobMemoryAllocStackGuid, &MemoryHob->AllocDescriptor.Name)) {
        DEBUG ((
          DEBUG_INFO,
          "%a: StackBase = 0x%016lx  StackSize = 0x%016lx\n",
          __func__,
          MemoryHob->AllocDescriptor.MemoryBaseAddress,
          MemoryHob->AllocDescriptor.MemoryLength
          ));

        StackBase = MemoryHob->AllocDescriptor.MemoryBaseAddress;
        //
        // Ensure the base of the stack is page-size aligned.
        //
        ASSERT ((StackBase & EFI_PAGE_MASK) == 0);
        break;
      }

      Hob.Raw = GET_NEXT_HOB (Hob);
    }

    //
    // Ensure the base of stack can be found from Hob when stack guard is
    // enabled.
    //
    ASSERT (StackBase != 0);
  }

  DEBUG ((
    DEBUG_INFO,
    "%a: applying strict permissions to active memory regions\n",
    __func__
    ));

  MergeMemoryMapForProtectionPolicy (MemoryMap, &MemoryMapSize, DescriptorSize);

  MemoryMapEntry = MemoryMap;
  MemoryMapEnd   = (EFI_MEMORY_DESCRIPTOR *)((UINT8 *)MemoryMap + MemoryMapSize);
  while ((UINTN)MemoryMapEntry < (UINTN)MemoryMapEnd) {
    Attributes = GetPermissionAttributeForMemoryType (MemoryMapEntry->Type);
    if (Attributes != 0) {
      SetUefiImageMemoryAttributes (
        MemoryMapEntry->PhysicalStart,
        LShiftU64 (MemoryMapEntry->NumberOfPages, EFI_PAGE_SHIFT),
        Attributes
        );

      //
      // Add EFI_MEMORY_RP attribute for page 0 if NULL pointer detection is
      // enabled.
      //
      if ((MemoryMapEntry->PhysicalStart == 0) &&
          (PcdGet8 (PcdNullPointerDetectionPropertyMask) != 0))
      {
        ASSERT (MemoryMapEntry->NumberOfPages > 0);
        SetUefiImageMemoryAttributes (
          0,
          EFI_PAGES_TO_SIZE (1),
          EFI_MEMORY_RP | Attributes
          );
      }

      //
      // Add EFI_MEMORY_RP attribute for the first page of the stack if stack
      // guard is enabled.
      //
      if ((StackBase != 0) &&
          ((StackBase >= MemoryMapEntry->PhysicalStart) &&
           (StackBase <  MemoryMapEntry->PhysicalStart +
            LShiftU64 (MemoryMapEntry->NumberOfPages, EFI_PAGE_SHIFT))) &&
          PcdGetBool (PcdCpuStackGuard))
      {
        SetUefiImageMemoryAttributes (
          StackBase,
          EFI_PAGES_TO_SIZE (1),
          EFI_MEMORY_RP | Attributes
          );
      }
    }

    MemoryMapEntry = NEXT_MEMORY_DESCRIPTOR (MemoryMapEntry, DescriptorSize);
  }

  FreePool (MemoryMap);

  //
  // Apply the policy for RAM regions that we know are present and
  // accessible, but have not been added to the UEFI memory map (yet).
  //
  if (GetPermissionAttributeForMemoryType (EfiConventionalMemory) != 0) {
    DEBUG ((
      DEBUG_INFO,
      "%a: applying strict permissions to inactive memory regions\n",
      __func__
      ));

    CoreAcquireGcdMemoryLock ();

    Link = mGcdMemorySpaceMap.ForwardLink;
    while (Link != &mGcdMemorySpaceMap) {
      Entry = CR (Link, EFI_GCD_MAP_ENTRY, Link, EFI_GCD_MAP_SIGNATURE);

      if ((Entry->GcdMemoryType == EfiGcdMemoryTypeReserved) &&
          (Entry->EndAddress < MAX_ADDRESS) &&
          ((Entry->Capabilities & (EFI_MEMORY_PRESENT | EFI_MEMORY_INITIALIZED | EFI_MEMORY_TESTED)) ==
           (EFI_MEMORY_PRESENT | EFI_MEMORY_INITIALIZED)))
      {
        Attributes = GetPermissionAttributeForMemoryType (EfiConventionalMemory) |
                     (Entry->Attributes & EFI_CACHE_ATTRIBUTE_MASK);

        DEBUG ((
          DEBUG_INFO,
          "Untested GCD memory space region: - 0x%016lx - 0x%016lx (0x%016lx)\n",
          Entry->BaseAddress,
          Entry->EndAddress - Entry->BaseAddress + 1,
          Attributes
          ));

        ASSERT (gCpu != NULL);
        gCpu->SetMemoryAttributes (
                gCpu,
                Entry->BaseAddress,
                Entry->EndAddress - Entry->BaseAddress + 1,
                Attributes
                );
      }

      Link = Link->ForwardLink;
    }

    CoreReleaseGcdMemoryLock ();
  }
}

/**
  A notification for CPU_ARCH protocol.

  @param[in]  Event                 Event whose notification function is being invoked.
  @param[in]  Context               Pointer to the notification function's context,
                                    which is implementation-dependent.

**/
VOID
EFIAPI
MemoryProtectionCpuArchProtocolNotify (
  IN EFI_EVENT  Event,
  IN VOID       *Context
  )
{
  EFI_STATUS         Status;
  LIST_ENTRY         *ImageRecordLink;
  UEFI_IMAGE_RECORD  *ImageRecord;

  DEBUG ((DEBUG_INFO, "MemoryProtectionCpuArchProtocolNotify:\n"));
  Status = CoreLocateProtocol (&gEfiCpuArchProtocolGuid, NULL, (VOID **)&gCpu);
  if (EFI_ERROR (Status)) {
    goto Done;
  }

  //
  // Apply the memory protection policy on non-BScode/RTcode regions.
  //
  if (PcdGet64 (PcdDxeNxMemoryProtectionPolicy) != 0) {
    InitializeDxeNxMemoryProtectionPolicy ();
  }

  //
  // Call notify function meant for Heap Guard.
  //
  HeapGuardCpuArchProtocolNotify ();

  if (mImageProtectionPolicy == 0) {
    goto Done;
  }

  for (ImageRecordLink = mProtectedImageRecordList.ForwardLink;
        ImageRecordLink != &mProtectedImageRecordList;
        ImageRecordLink = ImageRecordLink->ForwardLink) {
    ImageRecord = CR (
                    ImageRecordLink,
                    UEFI_IMAGE_RECORD,
                    Link,
                    UEFI_IMAGE_RECORD_SIGNATURE
                    );

    //
    // CPU ARCH present. Update memory attribute directly.
    //
    SetUefiImageProtectionAttributes (ImageRecord, FALSE);
  }

Done:
  CoreCloseEvent (Event);
}

/**
  ExitBootServices Callback function for memory protection.
**/
VOID
MemoryProtectionExitBootServicesCallback (
  VOID
  )
{
  EFI_RUNTIME_IMAGE_ENTRY  *RuntimeImage;
  LIST_ENTRY               *Link;

  //
  // We need remove the RT protection, because RT relocation need write code segment
  // at SetVirtualAddressMap(). We cannot assume OS/Loader has taken over page table at that time.
  //
  // Firmware does not own page tables after ExitBootServices(), so the OS would
  // have to relax protection of RT code pages across SetVirtualAddressMap(), or
  // delay setting protections on RT code pages until after SetVirtualAddressMap().
  // OS may set protection on RT based upon EFI_MEMORY_ATTRIBUTES_TABLE later.
  //
  if (mImageProtectionPolicy != 0) {
    for (Link = gRuntime->ImageHead.ForwardLink; Link != &gRuntime->ImageHead; Link = Link->ForwardLink) {
      RuntimeImage = BASE_CR (Link, EFI_RUNTIME_IMAGE_ENTRY, Link);
      SetUefiImageMemoryAttributes ((UINT64)(UINTN)RuntimeImage->ImageBase, ALIGN_VALUE (RuntimeImage->ImageSize, EFI_PAGE_SIZE), 0);
    }
  }
}

/**
  Disable NULL pointer detection after EndOfDxe. This is a workaround resort in
  order to skip unfixable NULL pointer access issues detected in OptionROM or
  boot loaders.

  @param[in]  Event     The Event this notify function registered to.
  @param[in]  Context   Pointer to the context data registered to the Event.
**/
VOID
EFIAPI
DisableNullDetectionAtTheEndOfDxe (
  EFI_EVENT  Event,
  VOID       *Context
  )
{
  EFI_STATUS                       Status;
  EFI_GCD_MEMORY_SPACE_DESCRIPTOR  Desc;

  DEBUG ((DEBUG_INFO, "DisableNullDetectionAtTheEndOfDxe(): start\r\n"));
  //
  // Disable NULL pointer detection by enabling first 4K page
  //
  Status = CoreGetMemorySpaceDescriptor (0, &Desc);
  ASSERT_EFI_ERROR (Status);

  if ((Desc.Capabilities & EFI_MEMORY_RP) == 0) {
    Status = CoreSetMemorySpaceCapabilities (
               0,
               EFI_PAGE_SIZE,
               Desc.Capabilities | EFI_MEMORY_RP
               );
    ASSERT_EFI_ERROR (Status);
  }

  Status = CoreSetMemorySpaceAttributes (
             0,
             EFI_PAGE_SIZE,
             Desc.Attributes & ~EFI_MEMORY_RP
             );
  ASSERT_EFI_ERROR (Status);

  //
  // Page 0 might have be allocated to avoid misuses. Free it here anyway.
  //
  CoreFreePages (0, 1);

  CoreCloseEvent (Event);
  DEBUG ((DEBUG_INFO, "DisableNullDetectionAtTheEndOfDxe(): end\r\n"));

  return;
}

/**
  Initialize Memory Protection support.
**/
VOID
EFIAPI
CoreInitializeMemoryProtection (
  VOID
  )
{
  EFI_STATUS  Status;
  EFI_EVENT   Event;
  EFI_EVENT   EndOfDxeEvent;
  VOID        *Registration;

  mImageProtectionPolicy = PcdGet32 (PcdImageProtectionPolicy);

  InitializeListHead (&mProtectedImageRecordList);

  //
  // Sanity check the PcdDxeNxMemoryProtectionPolicy setting:
  // - code regions should have no EFI_MEMORY_XP attribute
  // - EfiConventionalMemory and EfiBootServicesData should use the
  //   same attribute
  //
  ASSERT ((GetPermissionAttributeForMemoryType (EfiBootServicesCode) & EFI_MEMORY_XP) == 0);
  ASSERT ((GetPermissionAttributeForMemoryType (EfiRuntimeServicesCode) & EFI_MEMORY_XP) == 0);
  ASSERT ((GetPermissionAttributeForMemoryType (EfiLoaderCode) & EFI_MEMORY_XP) == 0);
  ASSERT (
    GetPermissionAttributeForMemoryType (EfiBootServicesData) ==
    GetPermissionAttributeForMemoryType (EfiConventionalMemory)
    );

  Status = CoreCreateEvent (
             EVT_NOTIFY_SIGNAL,
             TPL_CALLBACK,
             MemoryProtectionCpuArchProtocolNotify,
             NULL,
             &Event
             );
  ASSERT_EFI_ERROR (Status);

  //
  // Register for protocol notifactions on this event
  //
  Status = CoreRegisterProtocolNotify (
             &gEfiCpuArchProtocolGuid,
             Event,
             &Registration
             );
  ASSERT_EFI_ERROR (Status);

  //
  // Register a callback to disable NULL pointer detection at EndOfDxe
  //
  if ((PcdGet8 (PcdNullPointerDetectionPropertyMask) & (BIT0|BIT7))
      == (BIT0|BIT7))
  {
    Status = CoreCreateEventEx (
               EVT_NOTIFY_SIGNAL,
               TPL_NOTIFY,
               DisableNullDetectionAtTheEndOfDxe,
               NULL,
               &gEfiEndOfDxeEventGroupGuid,
               &EndOfDxeEvent
               );
    ASSERT_EFI_ERROR (Status);
  }

  return;
}

/**
  Returns whether we are currently executing in SMM mode.
**/
STATIC
BOOLEAN
IsInSmm (
  VOID
  )
{
  BOOLEAN  InSmm;

  InSmm = FALSE;
  if (gSmmBase2 != NULL) {
    gSmmBase2->InSmm (gSmmBase2, &InSmm);
  }

  return InSmm;
}

/**
  Manage memory permission attributes on a memory range, according to the
  configured DXE memory protection policy.

  @param  OldType           The old memory type of the range
  @param  NewType           The new memory type of the range
  @param  Memory            The base address of the range
  @param  Length            The size of the range (in bytes)

  @return EFI_SUCCESS       If we are executing in SMM mode. No permission attributes
                            are updated in this case
  @return EFI_SUCCESS       If the the CPU arch protocol is not installed yet
  @return EFI_SUCCESS       If no DXE memory protection policy has been configured
  @return EFI_SUCCESS       If OldType and NewType use the same permission attributes
  @return other             Return value of gCpu->SetMemoryAttributes()

**/
EFI_STATUS
EFIAPI
ApplyMemoryProtectionPolicy (
  IN  EFI_MEMORY_TYPE       OldType,
  IN  EFI_MEMORY_TYPE       NewType,
  IN  EFI_PHYSICAL_ADDRESS  Memory,
  IN  UINT64                Length
  )
{
  UINT64  OldAttributes;
  UINT64  NewAttributes;

  //
  // The policy configured in PcdDxeNxMemoryProtectionPolicy
  // does not apply to allocations performed in SMM mode.
  //
  if (IsInSmm ()) {
    return EFI_SUCCESS;
  }

  //
  // If the CPU arch protocol is not installed yet, we cannot manage memory
  // permission attributes, and it is the job of the driver that installs this
  // protocol to set the permissions on existing allocations.
  //
  if (gCpu == NULL) {
    return EFI_SUCCESS;
  }

  //
  // Check if a DXE memory protection policy has been configured
  //
  if (PcdGet64 (PcdDxeNxMemoryProtectionPolicy) == 0) {
    return EFI_SUCCESS;
  }

  //
  // Don't overwrite Guard pages, which should be the first and/or last page,
  // if any.
  //
  if (IsHeapGuardEnabled (GUARD_HEAP_TYPE_PAGE|GUARD_HEAP_TYPE_POOL)) {
    if (IsGuardPage (Memory)) {
      Memory += EFI_PAGE_SIZE;
      Length -= EFI_PAGE_SIZE;
      if (Length == 0) {
        return EFI_SUCCESS;
      }
    }

    if (IsGuardPage (Memory + Length - EFI_PAGE_SIZE)) {
      Length -= EFI_PAGE_SIZE;
      if (Length == 0) {
        return EFI_SUCCESS;
      }
    }
  }

  //
  // Update the executable permissions according to the DXE memory
  // protection policy, but only if
  // - the policy is different between the old and the new type, or
  // - this is a newly added region (OldType == EfiMaxMemoryType)
  //
  NewAttributes = GetPermissionAttributeForMemoryType (NewType);

  if (OldType != EfiMaxMemoryType) {
    OldAttributes = GetPermissionAttributeForMemoryType (OldType);
    if (OldAttributes == NewAttributes) {
      // policy is the same between OldType and NewType
      return EFI_SUCCESS;
    }
  }

  return gCpu->SetMemoryAttributes (gCpu, Memory, Length, NewAttributes);
}
