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
  IN RING3_CALL_DATA  *Data,
  IN UINTN            UserStackTop,
  IN VOID             *EntryPoint,
  IN UINTN            UserPageTable
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
  UINT8                   Type;
  UINT8                   NumberOfArguments;

  ArmEnableInterrupts ();

  Type              = Context.SystemContextArm->R0;
  NumberOfArguments = Context.SystemContextArm->R1;

  if ((Type == SysCallFreePages)
    || (Type == SysCallBlockIoRead)
    || (Type == SysCallBlockIoWrite)
    || (Type == SysCallDiskIoRead)
    || (Type == SysCallDiskIoWrite)) {
    ++NumberOfArguments;
  }

  Status = CoreAllocatePages (
             AllocateAnyPages,
             EfiRing3MemoryType,
             EFI_SIZE_TO_PAGES ((NumberOfArguments + 1) * sizeof (UINTN)),
             &Physical
             );
  if (EFI_ERROR (Status)) {
    return Status;
  }

  AllowSupervisorAccessToUserMemory ();
  if (Type == SysCallFreePages) {
    //
    // R0 == Type, R1 == NumberOfArguments, R2 == NumberOfPages, R3 == NULL
    // [SP] == Memory
    // Memory is passed as 2 words on stack and aligned on 8 bytes.
    //
    CopyMem ((VOID *)(UINTN)Physical, (VOID *)&(Context.SystemContextArm->R1), 2 * sizeof (UINTN));
    CopyMem (
      (VOID *)((UINTN)Physical + 2 * sizeof (UINTN)),
      (VOID *)Context.SystemContextArm->SP,
      2 * sizeof (UINTN)
      );
  } else {
    //
    // First 2 arguments are passed through R2-R3 and copied to SysCall Stack.
    //
    CopyMem ((VOID *)(UINTN)Physical, (VOID *)&(Context.SystemContextArm->R1), 3 * sizeof (UINTN));

    if (NumberOfArguments > 2) {
      //
      // All remaining arguments are on User Stack.
      //
      CopyMem (
        (VOID *)((UINTN)Physical + 3 * sizeof (UINTN)),
        (VOID *)Context.SystemContextArm->SP,
        (NumberOfArguments - 2) * sizeof (UINTN)
        );
    }
  }
  ForbidSupervisorAccessToUserMemory ();

  Status = CallBootService (
             Type,
             NumberOfArguments,
             (UINTN *)(UINTN)Physical,
             Context.SystemContextArm->SP_EL1
             );
  //
  // TODO: Fix memory leak for ReturnToCore().
  //
  CoreFreePages (Physical, EFI_SIZE_TO_PAGES ((NumberOfArguments + 1) * sizeof (UINTN)));

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
  IN OUT EFI_CONFIGURATION_TABLE  *Table,
  IN     UINTN                    NumberOfEntries
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
  IN RING3_CALL_DATA  *Data,
  IN UINTN            UserStackTop
  )
{
  return ArmCallRing3 (
            Data,
            UserStackTop,
            gRing3EntryPoint,
            gUserPageTable
            );
}
