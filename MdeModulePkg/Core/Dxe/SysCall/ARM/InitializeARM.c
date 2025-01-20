/** @file

  Copyright (c) 2024 - 2025, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause

**/

#include <Library/ArmLib.h>
#include <Library/ArmMmuLib.h>
#include <Library/DefaultExceptionHandlerLib.h>

#include "DxeMain.h"

UINTN  gUserPageTable;

EFI_STATUS
EFIAPI
ArmCallRing3 (
  IN RING3_CALL_DATA *Data,
  IN UINTN           UserStackTop,
  IN VOID            *EntryPoint,
  IN UINTN           SysCallStackTop,
  IN UINTN           UserPageTable
  );

STATIC
EFI_STATUS
EFIAPI
SysCallBootService (
  IN EFI_SYSTEM_CONTEXT  Context
  )
{
  EFI_STATUS              Status;
  EFI_PHYSICAL_ADDRESS    Physical;

  ArmEnableInterrupts ();

  Status = CoreAllocatePages (
             AllocateAnyPages,
             EfiRing3MemoryType,
             EFI_SIZE_TO_PAGES (8 * sizeof (UINTN)),
             &Physical
             );
  if (EFI_ERROR (Status)) {
    return Status;
  }

  AllowSupervisorAccessToUserMemory ();
  //
  // First 3 arguments are passed through R1-R3 and copied to SysCall Stack.
  //
  CopyMem ((VOID *)(UINTN)Physical, (VOID *)&(Context.SystemContextArm->R0), 4 * sizeof (UINTN));
  //
  // All remaining arguments are on User Stack.
  //
  CopyMem ((VOID *)((UINTN)Physical + 4 * sizeof (UINTN)), (VOID *)Context.SystemContextArm->SP, 4 * sizeof (UINTN));
  ForbidSupervisorAccessToUserMemory ();

  Status = CallBootService (
             Context.SystemContextArm->R0,
             (UINTN *)(UINTN)Physical,
             *(UINTN *)Context.SystemContextArm->SP_EL1
             );
  //
  // TODO: Fix memory leak for ReturnToCore().
  //
  CoreFreePages (Physical, EFI_SIZE_TO_PAGES (9 * sizeof (UINTN)));

  ArmDisableInterrupts ();

  return Status;
}

VOID
EFIAPI
MakeUserPageTableTemplate (
  OUT UINTN  *UserPageTableTemplate,
  OUT UINTN  *UserPageTableTemplateSize
  )
{
  ARM_MEMORY_REGION_DESCRIPTOR  Descriptor;
  VOID                          *MemorySizeHob;

  MemorySizeHob = GetFirstGuidHob (&gArmVirtSystemMemorySizeGuid);
  ASSERT (MemorySizeHob != NULL);
  if (MemorySizeHob == NULL) {
    return;
  }

  Descriptor.PhysicalBase = PcdGet64 (PcdSystemMemoryBase);
  Descriptor.VirtualBase  = Descriptor.PhysicalBase;
  Descriptor.Length       = *(UINT64 *)GET_GUID_HOB_DATA (MemorySizeHob);
  Descriptor.Attributes   = ARM_MEMORY_REGION_ATTRIBUTE_WRITE_BACK;

  ArmMakeUserPageTableTemplate (
    &Descriptor,
    UserPageTableTemplate,
    UserPageTableTemplateSize
    );
}

VOID
EFIAPI
InitializeMsr (
  IN OUT EFI_CONFIGURATION_TABLE *Table,
  IN     UINTN                   NumberOfEntries
  )
{
  if (ArmHasPan ()) {
    //
    // Enable Privileged Access Never feature.
    //
    ArmSetPan ();
  }

  InitializeSysCallHandler (SysCallBootService);
  SetExceptionAddresses (NULL, 0);
}

VOID
EFIAPI
AllowSupervisorAccessToUserMemory (
  VOID
  )
{
  if (ArmHasPan ()) {
    ArmClearPan ();
  }
}

VOID
EFIAPI
ForbidSupervisorAccessToUserMemory (
  VOID
  )
{
  if (ArmHasPan ()) {
    ArmSetPan ();
  }
}

EFI_STATUS
EFIAPI
CallRing3 (
  IN RING3_CALL_DATA *Data,
  IN UINTN            UserStackTop,
  IN UINTN            SysCallStackTop
  )
{
  return ArmCallRing3 (
            Data,
            UserStackTop,
            gRing3EntryPoint,
            SysCallStackTop,
            gUserPageTable
            );
}
