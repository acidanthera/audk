/** @file

  Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause

**/

#include <Chipset/AArch64.h>
#include <Library/ArmLib.h>

#include "DxeMain.h"

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
}
