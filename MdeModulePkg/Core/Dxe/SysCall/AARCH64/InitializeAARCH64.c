/** @file

  Copyright (c) 2024 - 2025, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause

**/

#include <Chipset/AArch64.h>
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
  EFI_STATUS  Status;
  UINTN       *UserArguments;

  ArmEnableInterrupts ();

  UserArguments = (UINTN *)(Context.SystemContextAArch64->SP_EL0 - 7 * sizeof (UINTN));

  AllowSupervisorAccessToUserMemory ();
  //
  // First 6 arguments are passed through X2-X7 and copied to Core stack,
  // all the others are on User stack.
  //
  CopyMem (
    (VOID *)UserArguments,
    (VOID *)&(Context.SystemContextAArch64->X1),
    7 * sizeof (UINTN)
    );
  ForbidSupervisorAccessToUserMemory ();

  Status = CallBootService (
             Context.SystemContextAArch64->X0,
             Context.SystemContextAArch64->X1,
             UserArguments,
             Context.SystemContextAArch64->SP
             );

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
  UINTN  Tcr;
  UINTN  Sctlr;
  //
  // Disable Hierarchical permissions just in case.
  //
  Tcr = ArmGetTCR ();
  Tcr |= TCR_EL1_HPD0_MASK | TCR_EL1_HPD1_MASK;
  ArmSetTCR (Tcr);

  if (ArmHasPan ()) {
    //
    // Enable Privileged Access Never feature.
    //
    Sctlr  = ArmReadSctlr ();
    Sctlr |= SCTLR_EPAN;
    ArmWriteSctlr (Sctlr);

    ArmSetPan ();
  }

  InitializeSysCallHandler ((VOID *)SysCallBootService);
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
