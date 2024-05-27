/** @file

  Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause

**/

#include <Chipset/AArch64.h>
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
  CopyMem ((VOID *)((UINTN)Physical + sizeof (UINTN)), (VOID *)UserRsp, 8 * sizeof (UINTN));
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
  VOID
  )
{
  UINTN  Tcr;
  //
  // If HCR_EL2.NV is 1 and the current Exception level is EL1,
  // then EL1 read accesses to the CurrentEL register return a value of 0x2 in bits[3:2].
  // CurrentEL == 1 -> HCR_EL2.NV == 0
  //
  // If stage 1 is enabled and stage 1 Base permissions use Direct permissions,
  // then GCS access is not permitted and UnprivGCS and PrivGCS are not present.
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
    ArmSetPan ();
  } else {
    DEBUG ((DEBUG_ERROR, "Core: Failed to initialize MSRs for Ring3.\n"));
    ASSERT (FALSE);
  }

  InitializeSysCallHandler ((VOID *)SysCallBootService);
}

VOID
EFIAPI
DisableSMAP (
  VOID
  )
{
  ArmClearPan ();
}

VOID
EFIAPI
EnableSMAP (
  VOID
  )
{
  ArmSetPan ();
}

EFI_STATUS
EFIAPI
CallRing3 (
  IN RING3_CALL_DATA *Data
  )
{
  return ArmCallRing3 (Data, gRing3CallStackTop, gRing3EntryPoint, gCoreSysCallStackTop, &mCoreSp);
}
