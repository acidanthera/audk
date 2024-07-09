/** @file

  Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause

**/

#include <Library/ArmLib.h>
#include <Library/DefaultExceptionHandlerLib.h>

#include "DxeMain.h"

STATIC UINTN  mCoreSp;

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
ReturnToCore (
  IN EFI_STATUS Status,
  IN UINTN      CoreSp
  );

VOID
EFIAPI
ArmSetPan (
  VOID
  );

VOID
EFIAPI
ArmClearPan (
  VOID
  );

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

  if (Type == SysCallReturnToCore) {
    ReturnToCore (*(EFI_STATUS *)CoreRbp, mCoreSp);
  }

  Status = CoreAllocatePages (
             AllocateAnyPages,
             EfiRing3MemoryType,
             EFI_SIZE_TO_PAGES (9 * sizeof (UINTN)),
             &Physical
             );
  if (EFI_ERROR (Status)) {
    return Status;
  }

  DisableSMAP ();
  //
  // First 3 arguments are passed through R1-R3 and copied to SysCall Stack.
  //
  CopyMem ((VOID *)((UINTN)Physical + 2 * sizeof (UINTN)), (VOID *)CoreRbp, 3 * sizeof (UINTN));
  //
  // All remaining arguments are on User Stack.
  //
  CopyMem ((VOID *)((UINTN)Physical + 5 * sizeof (UINTN)), (VOID *)UserRsp, 4 * sizeof (UINTN));
  EnableSMAP ();

  Status = CallBootService (
             Type,
             (CORE_STACK *)CoreRbp,
             (RING3_STACK *)(UINTN)Physical
             );

  CoreFreePages (Physical, EFI_SIZE_TO_PAGES (9 * sizeof (UINTN)));

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
  } else {
    DEBUG ((DEBUG_ERROR, "Core: Failed to initialize MSRs for Ring3.\n"));
    // ASSERT (FALSE);
  }

  InitializeSysCallHandler (SysCallBootService);
}

VOID
EFIAPI
DisableSMAP (
  VOID
  )
{
  if (ArmHasPan ()) {
    ArmClearPan ();
  }
}

VOID
EFIAPI
EnableSMAP (
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
