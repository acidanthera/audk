/** @file

  Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause

**/

#include <Library/ArmLib.h>

#include "DxeMain.h"

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
    ASSERT (FALSE);
  }
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
