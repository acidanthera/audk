/** @file

  Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause

**/

#include <Library/ArmLib.h>
#include <Library/DefaultExceptionHandlerLib.h>

#include "DxeMain.h"

STATIC UINTN  mCoreSp;
extern UINTN  gUartBaseAddress;

EFI_STATUS
EFIAPI
ArmCallRing3 (
  IN RING3_CALL_DATA *Data,
  IN VOID            *StackPointer,
  IN VOID            *EntryPoint,
  IN VOID            *SysCallStack,
  IN VOID            *CoreStack
  );

VOID
EFIAPI
ArmReturnToCore (
  IN EFI_STATUS Status,
  IN UINTN      CoreSp
  );

VOID
EFIAPI
ReturnToCore (
  IN EFI_STATUS Status
  )
{
  ArmReturnToCore (Status, mCoreSp);
}

STATIC
EFI_STATUS
EFIAPI
SysCallBootService (
  IN  UINT8  Type,
  IN  VOID   *CoreRbp,
  IN  VOID   *UserRsp
  )
{
  EFI_STATUS              Status;
  EFI_PHYSICAL_ADDRESS    Physical;

  Status = CoreAllocatePages (
             AllocateAnyPages,
             EfiRing3MemoryType,
             EFI_SIZE_TO_PAGES (9 * sizeof (UINTN)),
             &Physical
             );
  if (EFI_ERROR (Status)) {
    return Status;
  }

  AllowSupervisorAccessToUserMemory ();
  //
  // First 3 arguments are passed through R1-R3 and copied to SysCall Stack.
  //
  CopyMem ((VOID *)((UINTN)Physical + 2 * sizeof (UINTN)), (VOID *)CoreRbp, 3 * sizeof (UINTN));
  //
  // All remaining arguments are on User Stack.
  //
  CopyMem ((VOID *)((UINTN)Physical + 5 * sizeof (UINTN)), (VOID *)UserRsp, 4 * sizeof (UINTN));

  SetUefiImageMemoryAttributes (
    gUartBaseAddress,
    EFI_PAGE_SIZE,
    EFI_MEMORY_XP
    );
  ForbidSupervisorAccessToUserMemory ();

  Status = CallBootService (
             Type,
             (CORE_STACK *)CoreRbp,
             (RING3_STACK *)(UINTN)Physical
             );
  //
  // TODO: Fix memory leak for ReturnToCore().
  //
  CoreFreePages (Physical, EFI_SIZE_TO_PAGES (9 * sizeof (UINTN)));

  SetUefiImageMemoryAttributes (
    gUartBaseAddress,
    EFI_PAGE_SIZE,
    EFI_MEMORY_XP | EFI_MEMORY_USER
    );

  return Status;
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
  IN RING3_CALL_DATA *Data
  )
{
  return ArmCallRing3 (Data, gRing3CallStackTop, gRing3EntryPoint, gCoreSysCallStackTop, &mCoreSp);
}
