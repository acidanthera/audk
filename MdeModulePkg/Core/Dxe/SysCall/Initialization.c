/** @file

  Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause

**/

#include <Guid/EarlyPL011BaseAddress.h>

#include "DxeMain.h"

VOID        *gCoreSysCallStackTop;
VOID        *gCoreSysCallStackBase;
VOID        *gRing3CallStackTop;
VOID        *gRing3CallStackBase;
VOID        *gRing3EntryPoint;
RING3_DATA  *gRing3Data;
VOID        *gRing3Interfaces;
UINTN       gUartBaseAddress;

UEFI_IMAGE_RECORD    *mDxeRing3;
VOID                 *mUserPageTableTemplate;
UINTN                mUserPageTableTemplateSize;
EXCEPTION_ADDRESSES  *mExceptionAddresses;

extern UINTN         SysCallBase;
extern UINTN         SysCallEnd;

VOID
EFIAPI
MakeUserPageTableTemplate (
  OUT VOID   **UserPageTableTemplate,
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
  EFI_STATUS               Status;
  VOID                     *TopOfStack;
  UINTN                    SizeOfStack;
  EFI_PHYSICAL_ADDRESS     Physical;
  UINTN                    Index;
  EFI_CONFIGURATION_TABLE  *Conf;
  EARLY_PL011_BASE_ADDRESS *UartBase;
  CONST VOID               *Hob;

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
    Status = CoreAllocatePages (
               AllocateAnyPages,
               EfiRing3MemoryType,
               EFI_SIZE_TO_PAGES ((gRing3Data->SystemTable.NumberOfTableEntries + 1) * sizeof (EFI_CONFIGURATION_TABLE)),
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

  SizeOfStack = EFI_SIZE_TO_PAGES (USER_STACK_SIZE) * EFI_PAGE_SIZE;

  //
  // Allocate 128KB for the Core SysCall Stack.
  //
  gCoreSysCallStackBase = AllocatePages (EFI_SIZE_TO_PAGES (USER_STACK_SIZE));
  ASSERT (gCoreSysCallStackBase != NULL);

  //
  // Compute the top of the allocated stack. Pre-allocate a UINTN for safety.
  //
  TopOfStack = (VOID *)((UINTN)gCoreSysCallStackBase + SizeOfStack - CPU_STACK_ALIGNMENT);
  TopOfStack = ALIGN_POINTER (TopOfStack, CPU_STACK_ALIGNMENT);

  gCoreSysCallStackTop = TopOfStack;

  SetUefiImageMemoryAttributes ((UINTN)gCoreSysCallStackBase, SizeOfStack, EFI_MEMORY_XP);
  DEBUG ((DEBUG_ERROR, "Core: gCoreSysCallStackTop = %p\n", gCoreSysCallStackTop));

  //
  // Allocate 128KB for the User Stack.
  //
  gRing3CallStackBase = AllocatePages (EFI_SIZE_TO_PAGES (USER_STACK_SIZE));
  ASSERT (gRing3CallStackBase != NULL);

  //
  // Compute the top of the allocated stack. Pre-allocate a UINTN for safety.
  //
  TopOfStack = (VOID *)((UINTN)gRing3CallStackBase + SizeOfStack - CPU_STACK_ALIGNMENT);
  TopOfStack = ALIGN_POINTER (TopOfStack, CPU_STACK_ALIGNMENT);

  gRing3CallStackTop = TopOfStack;

  SetUefiImageMemoryAttributes ((UINTN)gRing3CallStackBase, SizeOfStack, EFI_MEMORY_XP | EFI_MEMORY_USER);
  DEBUG ((DEBUG_ERROR, "Core: gRing3CallStackTop = %p\n", gRing3CallStackTop));

  InitializeMsr (
    gRing3Data->SystemTable.ConfigurationTable,
    gRing3Data->SystemTable.NumberOfTableEntries
    );

  MakeUserPageTableTemplate (&mUserPageTableTemplate, &mUserPageTableTemplateSize);

  mExceptionAddresses = GetExceptionAddresses ();

  return Status;
}

UINTN
EFIAPI
InitializeUserPageTable (
  IN LOADED_IMAGE_PRIVATE_DATA  *Image
  )
{
  UINTN                      UserPageTable;
  UEFI_IMAGE_RECORD_SEGMENT  *ImageRecordSegment;
  UINTN                      SectionAddress;
  UINT32                     Index;
  UEFI_IMAGE_RECORD          *UserImageRecord;
  IA32_DESCRIPTOR            IdtDescriptor;

  UserPageTable = (UINTN)AllocatePages (EFI_SIZE_TO_PAGES (mUserPageTableTemplateSize));

  CopyMem ((VOID *)UserPageTable, mUserPageTableTemplate, mUserPageTableTemplateSize);

  //
  // Map gRing3Data, gRing3Interfaces, gRing3CallStackBase, DxeRing3
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
          (UINTN)gRing3CallStackBase,
          EFI_SIZE_TO_PAGES (USER_STACK_SIZE) * EFI_PAGE_SIZE,
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
  // Map CoreBootServices, gCoreSysCallStackBase
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
          (UINTN)&gCorePageTable,
          SIZE_4KB,
          EFI_MEMORY_RO | EFI_MEMORY_XP
          );

  gCpu->SetUserMemoryAttributes (
          gCpu,
          UserPageTable,
          (UINTN)gCoreSysCallStackBase,
          EFI_SIZE_TO_PAGES (USER_STACK_SIZE) * EFI_PAGE_SIZE,
          EFI_MEMORY_XP
          );

  //
  // Map ExceptionHandlers, ExceptionStacks, Idt
  //
  gCpu->SetUserMemoryAttributes (
          gCpu,
          UserPageTable,
          mExceptionAddresses->ExceptionStackBase,
          mExceptionAddresses->ExceptionStackSize,
          EFI_MEMORY_XP
          );

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
