/** @file

  Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause

**/

#include "DxeMain.h"

#include <Register/Intel/ArchitecturalMsr.h>

VOID
EFIAPI
InitializeMsr (
  VOID
  )
{
  UINT64                  Msr;
  IA32_CR4                Cr4;
  IA32_EFLAGS32           Eflags;
  UINT32                  Ebx;
  UINT32                  Edx;

  Ebx = 0;
  Edx = 0;

  //
  // Forbid supervisor-mode accesses to any user-mode pages.
  // SMEP and SMAP must be supported.
  //
  AsmCpuidEx (0x07, 0x0, NULL, &Ebx, NULL, NULL);
  //
  // SYSENTER and SYSEXIT must be also supported.
  //
  AsmCpuidEx (0x01, 0x0, NULL, NULL, NULL, &Edx);
  if (((Ebx & BIT20) != 0) && ((Ebx & BIT7) != 0) && ((Edx & BIT11) != 0)) {
    Cr4.UintN     = AsmReadCr4 ();
    Cr4.Bits.SMAP = 1;
    Cr4.Bits.SMEP = 1;
    AsmWriteCr4 (Cr4.UintN);

    Eflags.UintN   = AsmReadEflags ();
    Eflags.Bits.AC = 0;
    AsmWriteEflags (Eflags.UintN);
  } else {
    DEBUG ((DEBUG_ERROR, "Core: Failed to initialize MSRs for Ring3.\n"));
    ASSERT (FALSE);
  }

  //
  // Initialize MSR_IA32_SYSENTER_CS, MSR_IA32_SYSENTER_EIP and
  // MSR_IA32_SYSENTER_ESP for SYSENTER and SYSEXIT.
  //
  Msr = RING0_CODE32_SEL;
  AsmWriteMsr64 (MSR_IA32_SYSENTER_CS, Msr);

  Msr = (UINT64)(UINTN)CoreBootServices;
  AsmWriteMsr64 (MSR_IA32_SYSENTER_EIP, Msr);

  Msr = (UINT64)(UINTN)gCoreSysCallStackTop;
  AsmWriteMsr64 (MSR_IA32_SYSENTER_ESP, Msr);
}
