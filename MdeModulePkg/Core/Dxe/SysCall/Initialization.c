/** @file

  Copyright (c) 2024 - 2025, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause

**/

#include "DxeMain.h"

VOID        *gRing3EntryPoint;
RING3_DATA  *gRing3Data;
VOID        *gRing3Interfaces;

EXCEPTION_ADDRESSES  *mExceptionAddresses;
extern UINTN         SysCallBase;
extern UINTN         SysCallEnd;

STATIC UEFI_IMAGE_RECORD     *mDxeRing3;
STATIC EFI_PHYSICAL_ADDRESS  mCoreStackBase;
STATIC UINT64                mCoreStackSize;

EFI_STATUS
EFIAPI
MakeUserPageTableTemplate (
  OUT UINTN  *UserPageTableTemplate,
  OUT UINTN  *UserPageTableTemplateSize
  );

EFI_STATUS
EFIAPI
InitializePlatform (
  IN OUT EFI_SYSTEM_TABLE  *System
  );

VOID
EFIAPI
MapPlatform (
  IN OUT UINTN  UserPageTable
  );

EFI_STATUS
EFIAPI
InitializeRing3 (
  IN EFI_HANDLE                 ImageHandle,
  IN LOADED_IMAGE_PRIVATE_DATA  *Image
  )
{
  EFI_STATUS                 Status;
  EFI_PHYSICAL_ADDRESS       Physical;
  EFI_PEI_HOB_POINTERS       PeiHob;
  EFI_HOB_MEMORY_ALLOCATION  *MemoryHob;

  //
  // Set Ring3 EntryPoint and BootServices.
  //
  Status = CoreAllocatePages (
             AllocateAnyPages,
             EfiRing3MemoryType,
             EFI_SIZE_TO_PAGES (sizeof (RING3_DATA)),
             &Physical
             );
  if (EFI_ERROR (Status)) {
    return Status;
  }

  gRing3Data = (RING3_DATA *)(UINTN)Physical;

  CopyMem ((VOID *)gRing3Data, (VOID *)Image->Info.SystemTable, sizeof (EFI_SYSTEM_TABLE));

  SetUefiImageMemoryAttributes (
    (UINTN)gRing3Data,
    ALIGN_VALUE (sizeof (RING3_DATA), EFI_PAGE_SIZE),
    EFI_MEMORY_XP | EFI_MEMORY_USER
    );

  //
  // Initialize DxeRing3 with Supervisor privileges.
  //
  mDxeRing3 = GetUefiImageRecord (Image);
  ASSERT (mDxeRing3 != NULL);

  SetUefiImageProtectionAttributes (mDxeRing3, FALSE);

  Status = Image->EntryPoint (ImageHandle, (EFI_SYSTEM_TABLE *)gRing3Data);

  SetUefiImageProtectionAttributes (mDxeRing3, TRUE);

  gRing3EntryPoint = gRing3Data->EntryPoint;

  gRing3Data->SystemTable.BootServices    = gRing3Data->BootServices;
  gRing3Data->SystemTable.RuntimeServices = gRing3Data->RuntimeServices;

  Status = CoreAllocatePages (
             AllocateAnyPages,
             EfiRing3MemoryType,
             RING3_INTERFACES_PAGES,
             &Physical
             );
  if (EFI_ERROR (Status)) {
    CoreFreePages (
      (EFI_PHYSICAL_ADDRESS)(UINTN)gRing3Data,
      EFI_SIZE_TO_PAGES (sizeof (RING3_DATA))
      );
    return Status;
  }

  gRing3Interfaces = (VOID *)(UINTN)Physical;

  SetUefiImageMemoryAttributes (
    (UINTN)gRing3Interfaces,
    EFI_PAGES_TO_SIZE (RING3_INTERFACES_PAGES),
    EFI_MEMORY_XP | EFI_MEMORY_USER
    );

  Status = InitializePlatform (&gRing3Data->SystemTable);
  if (EFI_ERROR (Status)) {
    CoreFreePages (
      (EFI_PHYSICAL_ADDRESS)(UINTN)gRing3Data,
      EFI_SIZE_TO_PAGES (sizeof (RING3_DATA))
      );
    CoreFreePages (
      (EFI_PHYSICAL_ADDRESS)(UINTN)gRing3Interfaces,
      RING3_INTERFACES_PAGES
      );
    return Status;
  }

  mExceptionAddresses = GetExceptionAddresses ();

  PeiHob.Raw = GetHobList ();
  while ((PeiHob.Raw = GetNextHob (EFI_HOB_TYPE_MEMORY_ALLOCATION, PeiHob.Raw)) != NULL) {
    MemoryHob = PeiHob.MemoryAllocation;
    if (CompareGuid (&gEfiHobMemoryAllocStackGuid, &MemoryHob->AllocDescriptor.Name)) {
      mCoreStackBase = MemoryHob->AllocDescriptor.MemoryBaseAddress;
      mCoreStackSize = MemoryHob->AllocDescriptor.MemoryLength;
      break;
    }

    PeiHob.Raw = GET_NEXT_HOB (PeiHob);
  }

  return Status;
}

UINTN
EFIAPI
InitializeUserPageTable (
  IN LOADED_IMAGE_PRIVATE_DATA  *Image
  )
{
  EFI_STATUS                 Status;
  UINTN                      UserPageTable;
  UINTN                      UserPageTableSize;
  UEFI_IMAGE_RECORD_SEGMENT  *ImageRecordSegment;
  UINTN                      SectionAddress;
  UINT32                     Index;
  UEFI_IMAGE_RECORD          *UserImageRecord;

  Status = MakeUserPageTableTemplate (&UserPageTable, &UserPageTableSize);
  if (EFI_ERROR (Status)) {
    DEBUG ((DEBUG_ERROR, "Core: Failed to initialize User page table - %r.\n", Status));
    CpuDeadLoop ();
  }

  //
  // Map gRing3Data, gRing3Interfaces, DxeRing3
  //
  gCpu->SetUserMemoryAttributes (
          gCpu,
          UserPageTable,
          (UINTN)gRing3Data,
          ALIGN_VALUE (sizeof (RING3_DATA), EFI_PAGE_SIZE),
          EFI_MEMORY_XP | EFI_MEMORY_USER
          );

  gCpu->SetUserMemoryAttributes (
          gCpu,
          UserPageTable,
          (UINTN)gRing3Interfaces,
          EFI_PAGES_TO_SIZE (RING3_INTERFACES_PAGES),
          EFI_MEMORY_XP | EFI_MEMORY_USER
          );

  SectionAddress = mDxeRing3->StartAddress;
  for (Index = 0; Index < mDxeRing3->NumSegments; Index++) {
    ImageRecordSegment = &mDxeRing3->Segments[Index];

    gCpu->SetUserMemoryAttributes (
            gCpu,
            UserPageTable,
            SectionAddress,
            ImageRecordSegment->Size,
            ImageRecordSegment->Attributes | EFI_MEMORY_USER
            );

    SectionAddress += ImageRecordSegment->Size;
  }

  //
  // Map CoreBootServices, CoreStackBase
  //
  gCpu->SetUserMemoryAttributes (
          gCpu,
          UserPageTable,
          (UINTN)&SysCallBase,
          (UINTN)&SysCallEnd - (UINTN)&SysCallBase,
          EFI_MEMORY_RO
          );

  gCpu->SetUserMemoryAttributes (
          gCpu,
          UserPageTable,
          mCoreStackBase,
          mCoreStackSize,
          EFI_MEMORY_XP
          );

  //
  // Map ExceptionHandlers
  //
  gCpu->SetUserMemoryAttributes (
          gCpu,
          UserPageTable,
          mExceptionAddresses->ExceptionHandlerBase,
          mExceptionAddresses->ExceptionHandlerSize,
          EFI_MEMORY_RO
          );

  gCpu->SetUserMemoryAttributes (
          gCpu,
          UserPageTable,
          mExceptionAddresses->ExceptionDataBase,
          SIZE_4KB,
          EFI_MEMORY_XP
          );

  MapPlatform (UserPageTable);

  //
  // Map User Image
  //
  UserImageRecord = GetUefiImageRecord (Image);
  ASSERT (UserImageRecord != NULL);

  SectionAddress = UserImageRecord->StartAddress;
  for (Index = 0; Index < UserImageRecord->NumSegments; Index++) {
    ImageRecordSegment = &UserImageRecord->Segments[Index];

    gCpu->SetUserMemoryAttributes (
            gCpu,
            UserPageTable,
            SectionAddress,
            ImageRecordSegment->Size,
            ImageRecordSegment->Attributes | EFI_MEMORY_USER
            );

    SectionAddress += ImageRecordSegment->Size;
  }

  return UserPageTable;
}
