/** @file

  Copyright (c) 2024 - 2025, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause

**/

#include <Guid/EarlyPL011BaseAddress.h>

#include "DxeMain.h"

VOID        *gRing3EntryPoint;
RING3_DATA  *gRing3Data;
VOID        *gRing3Interfaces;
UINTN       gUartBaseAddress;

UEFI_IMAGE_RECORD     *mDxeRing3;
EXCEPTION_ADDRESSES   *mExceptionAddresses;
UINTN                 mConfigurationTable;
UINTN                 mConfigurationTableSize;
EFI_PHYSICAL_ADDRESS  mCoreStackBase;
UINT64                mCoreStackSize;

extern UINTN         SysCallBase;
extern UINTN         SysCallEnd;

VOID
EFIAPI
MakeUserPageTableTemplate (
  OUT UINTN  *UserPageTableTemplate,
  OUT UINTN  *UserPageTableTemplateSize
  );

VOID
EFIAPI
InitializeMsr (
  IN OUT EFI_CONFIGURATION_TABLE *Table,
  IN     UINTN                   NumberOfEntries
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
  UINTN                      Index;
  EFI_CONFIGURATION_TABLE    *Conf;
  EARLY_PL011_BASE_ADDRESS   *UartBase;
  CONST VOID                 *Hob;
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
    DEBUG ((DEBUG_ERROR, "Core: Failed to allocate memory for Ring3Data.\n"));
    return Status;
  }

  gRing3Data = (RING3_DATA *)(UINTN)Physical;

  CopyMem ((VOID *)gRing3Data, (VOID *)Image->Info.SystemTable, sizeof (EFI_SYSTEM_TABLE));

  SetUefiImageMemoryAttributes (
    (UINTN)gRing3Data,
    ALIGN_VALUE (sizeof (RING3_DATA), EFI_PAGE_SIZE),
    EFI_MEMORY_XP | EFI_MEMORY_USER
    );

  if (PcdGetBool (PcdSerialUseMmio)) {
    mConfigurationTableSize = (gRing3Data->SystemTable.NumberOfTableEntries + 1) * sizeof (EFI_CONFIGURATION_TABLE);

    Status = CoreAllocatePages (
               AllocateAnyPages,
               EfiRing3MemoryType,
               EFI_SIZE_TO_PAGES (mConfigurationTableSize),
               &Physical
               );
    if (EFI_ERROR (Status)) {
      DEBUG ((DEBUG_ERROR, "Core: Failed to allocate memory for Ring3 ConfigurationTable.\n"));
      return Status;
    }

    Conf = (EFI_CONFIGURATION_TABLE *)(UINTN)Physical;

    for (Index = 0; Index < gRing3Data->SystemTable.NumberOfTableEntries; ++Index) {
      CopyGuid (&(Conf->VendorGuid), &gRing3Data->SystemTable.ConfigurationTable[Index].VendorGuid);

      Conf->VendorTable = gRing3Data->SystemTable.ConfigurationTable[Index].VendorTable;

      ++Conf;
    }

    Hob              = GetFirstGuidHob (&gEarlyPL011BaseAddressGuid);
    UartBase         = GET_GUID_HOB_DATA (Hob);
    gUartBaseAddress = (UINTN)UartBase->DebugAddress;

    CopyGuid (&(Conf->VendorGuid), &gEarlyPL011BaseAddressGuid);
    Conf->VendorTable = (VOID *)gUartBaseAddress;
    ++gRing3Data->SystemTable.NumberOfTableEntries;

    DEBUG ((DEBUG_ERROR, "Core: gUartBaseAddress = 0x%p\n", gUartBaseAddress));

    gRing3Data->SystemTable.ConfigurationTable = (EFI_CONFIGURATION_TABLE *)(UINTN)Physical;
    mConfigurationTable                        = (UINTN)Physical;
  }
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
    DEBUG ((DEBUG_ERROR, "Core: Failed to allocate memory for Ring3Interfaces.\n"));
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

  InitializeMsr (
    gRing3Data->SystemTable.ConfigurationTable,
    gRing3Data->SystemTable.NumberOfTableEntries
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
  IN LOADED_IMAGE_PRIVATE_DATA  *Image,
  IN UINTN                      UserStackBase,
  IN UINTN                      UserStackSize
  )
{
  UINTN                      UserPageTable;
  UINTN                      UserPageTableSize;
  UEFI_IMAGE_RECORD_SEGMENT  *ImageRecordSegment;
  UINTN                      SectionAddress;
  UINT32                     Index;
  UEFI_IMAGE_RECORD          *UserImageRecord;

  //
  // TODO: Remove ASSERTs, add proper checks and return status.
  //
  MakeUserPageTableTemplate (&UserPageTable, &UserPageTableSize);

  //
  // Map gRing3Data, gRing3Interfaces, UserStackBase, DxeRing3
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

  gCpu->SetUserMemoryAttributes (
          gCpu,
          UserPageTable,
          UserStackBase,
          UserStackSize,
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
  // Map ExceptionHandlers, ExceptionStacks, Idt
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

#if defined (MDE_CPU_X64) || defined (MDE_CPU_IA32)
  IA32_DESCRIPTOR  IdtDescriptor;

  gCpu->SetUserMemoryAttributes (
          gCpu,
          UserPageTable,
          (UINTN)&gCorePageTable,
          SIZE_4KB,
          EFI_MEMORY_RO | EFI_MEMORY_XP
          );

  gCpu->SetUserMemoryAttributes (
          gCpu,
          UserPageTable,
          mExceptionAddresses->ExceptionStackBase,
          mExceptionAddresses->ExceptionStackSize,
          EFI_MEMORY_XP
          );

  AsmReadIdtr (&IdtDescriptor);
  gCpu->SetUserMemoryAttributes (
          gCpu,
          UserPageTable,
          IdtDescriptor.Base,
          SIZE_4KB,
          EFI_MEMORY_RO | EFI_MEMORY_XP
          );

  //
  // Necessary fix for ProcessLibraryConstructorList() -> DxeCcProbeLibConstructor()
  //
  gCpu->SetUserMemoryAttributes (
          gCpu,
          UserPageTable,
          FixedPcdGet32 (PcdOvmfWorkAreaBase),
          FixedPcdGet32 (PcdOvmfWorkAreaSize),
          EFI_MEMORY_XP | EFI_MEMORY_USER
          );
#elif defined (MDE_CPU_AARCH64) || defined (MDE_CPU_ARM)
  gCpu->SetUserMemoryAttributes (
          gCpu,
          UserPageTable,
          mConfigurationTable,
          ALIGN_VALUE (mConfigurationTableSize, EFI_PAGE_SIZE),
          EFI_MEMORY_XP | EFI_MEMORY_USER
          );
  //
  // Necessary fix for DEBUG printings.
  //
  gCpu->SetUserMemoryAttributes (
          gCpu,
          UserPageTable,
          gUartBaseAddress,
          SIZE_4KB,
          EFI_MEMORY_XP | EFI_MEMORY_USER
          );
#endif

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
