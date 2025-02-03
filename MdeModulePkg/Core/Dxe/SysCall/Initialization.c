/** @file

  Copyright (c) 2024 - 2025, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause

**/

#include "DxeMain.h"

VOID             *gUserSpaceEntryPoint;
USER_SPACE_DATA  *gUserSpaceData;
VOID             *gUserSpaceInterfaces;

EXCEPTION_ADDRESSES  *mExceptionAddresses;
extern UINTN         SysCallBase;
extern UINTN         SysCallEnd;

STATIC UEFI_IMAGE_RECORD     *mDxeUserSpace;
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
InitializeUserSpace (
  IN EFI_HANDLE                 ImageHandle,
  IN LOADED_IMAGE_PRIVATE_DATA  *Image
  )
{
  EFI_STATUS                 Status;
  EFI_PHYSICAL_ADDRESS       Physical;
  EFI_PEI_HOB_POINTERS       PeiHob;
  EFI_HOB_MEMORY_ALLOCATION  *MemoryHob;

  //
  // Set UserSpace EntryPoint and BootServices.
  //
  Status = CoreAllocatePages (
             AllocateAnyPages,
             EfiUserSpaceMemoryType,
             EFI_SIZE_TO_PAGES (sizeof (USER_SPACE_DATA)),
             &Physical
             );
  if (EFI_ERROR (Status)) {
    return Status;
  }

  gUserSpaceData = (USER_SPACE_DATA *)(UINTN)Physical;

  CopyMem ((VOID *)gUserSpaceData, (VOID *)Image->Info.SystemTable, sizeof (EFI_SYSTEM_TABLE));

  SetUefiImageMemoryAttributes (
    (UINTN)gUserSpaceData,
    ALIGN_VALUE (sizeof (USER_SPACE_DATA), EFI_PAGE_SIZE),
    EFI_MEMORY_XP | EFI_MEMORY_USER
    );

  Status = InitializePlatform (&gUserSpaceData->SystemTable);
  if (EFI_ERROR (Status)) {
    CoreFreePages (
      (EFI_PHYSICAL_ADDRESS)(UINTN)gUserSpaceData,
      EFI_SIZE_TO_PAGES (sizeof (USER_SPACE_DATA))
      );
    return Status;
  }

  //
  // Initialize DxeUserSpace with Supervisor privileges.
  //
  mDxeUserSpace = GetUefiImageRecord (Image);
  ASSERT (mDxeUserSpace != NULL);

  SetUefiImageProtectionAttributes (mDxeUserSpace, FALSE);

  AllowSupervisorAccessToUserMemory ();
  Status = Image->EntryPoint (ImageHandle, (EFI_SYSTEM_TABLE *)gUserSpaceData);

  gUserSpaceEntryPoint = gUserSpaceData->EntryPoint;

  gUserSpaceData->SystemTable.BootServices    = gUserSpaceData->BootServices;
  gUserSpaceData->SystemTable.RuntimeServices = gUserSpaceData->RuntimeServices;
  ForbidSupervisorAccessToUserMemory ();

  SetUefiImageProtectionAttributes (mDxeUserSpace, TRUE);

  Status = CoreAllocatePages (
             AllocateAnyPages,
             EfiUserSpaceMemoryType,
             USER_SPACE_INTERFACES_PAGES,
             &Physical
             );
  if (EFI_ERROR (Status)) {
    CoreFreePages (
      (EFI_PHYSICAL_ADDRESS)(UINTN)gUserSpaceData,
      EFI_SIZE_TO_PAGES (sizeof (USER_SPACE_DATA))
      );
    return Status;
  }

  gUserSpaceInterfaces = (VOID *)(UINTN)Physical;

  SetUefiImageMemoryAttributes (
    (UINTN)gUserSpaceInterfaces,
    EFI_PAGES_TO_SIZE (USER_SPACE_INTERFACES_PAGES),
    EFI_MEMORY_XP | EFI_MEMORY_USER
    );

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
  // Map gUserSpaceData, gUserSpaceInterfaces, DxeUserSpace
  //
  gCpu->SetUserMemoryAttributes (
          gCpu,
          UserPageTable,
          (UINTN)gUserSpaceData,
          ALIGN_VALUE (sizeof (USER_SPACE_DATA), EFI_PAGE_SIZE),
          EFI_MEMORY_XP | EFI_MEMORY_USER
          );

  gCpu->SetUserMemoryAttributes (
          gCpu,
          UserPageTable,
          (UINTN)gUserSpaceInterfaces,
          EFI_PAGES_TO_SIZE (USER_SPACE_INTERFACES_PAGES),
          EFI_MEMORY_XP | EFI_MEMORY_USER
          );

  SectionAddress = mDxeUserSpace->StartAddress;
  for (Index = 0; Index < mDxeUserSpace->NumSegments; Index++) {
    ImageRecordSegment = &mDxeUserSpace->Segments[Index];

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
