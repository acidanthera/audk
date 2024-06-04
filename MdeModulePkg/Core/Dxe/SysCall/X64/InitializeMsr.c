/** @file

  Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause

**/

#include "DxeMain.h"

#include <Register/Intel/ArchitecturalMsr.h>

VOID
EFIAPI
InitializeMsr (
  IN OUT EFI_CONFIGURATION_TABLE *Table,
  IN     UINTN                   NumberOfEntries
  )
{
  UINT64                  Msr;
  IA32_CR4                Cr4;
  IA32_EFLAGS32           Eflags;
  UINT32                  Ebx;
  UINT32                  Edx;
  MSR_IA32_EFER_REGISTER  MsrEfer;

  Ebx = 0;
  Edx = 0;

  //
  // Forbid supervisor-mode accesses to any user-mode pages.
  // SMEP and SMAP must be supported.
  //
  AsmCpuidEx (0x07, 0x0, NULL, &Ebx, NULL, NULL);
  //
  // SYSCALL and SYSRET must be also supported.
  //
  AsmCpuidEx (0x80000001, 0x0, NULL, NULL, NULL, &Edx);
  if (((Ebx & BIT20) != 0) && ((Ebx & BIT7) != 0) && ((Edx & BIT11) != 0)) {
    Cr4.UintN     = AsmReadCr4 ();
    Cr4.Bits.SMAP = 1;
    Cr4.Bits.SMEP = 1;
    AsmWriteCr4 (Cr4.UintN);

    Eflags.UintN   = AsmReadEflags ();
    Eflags.Bits.AC = 0;
    AsmWriteEflags (Eflags.UintN);
    //
    // Enable SYSCALL and SYSRET.
    //
    MsrEfer.Uint64   = AsmReadMsr64 (MSR_IA32_EFER);
    MsrEfer.Bits.SCE = 1;
    AsmWriteMsr64 (MSR_IA32_EFER, MsrEfer.Uint64);
  } else {
    DEBUG ((DEBUG_ERROR, "Core: Failed to initialize MSRs for Ring3.\n"));
    ASSERT (FALSE);
  }

  //
  // Initialize MSR_IA32_STAR, MSR_IA32_LSTAR and MSR_IA32_FMASK for SYSCALL and SYSRET.
  //
  Msr = (((((UINT64)RING3_CODE64_SEL - 16) | 3) << 16) | (UINT64)RING0_CODE64_SEL) << 32;
  AsmWriteMsr64 (MSR_IA32_STAR, Msr);

  Msr = (UINT64)(UINTN)CoreBootServices;
  AsmWriteMsr64 (MSR_IA32_LSTAR, Msr);
  //
  // Disable maskable interrupts at SYSCALL.
  //
  Msr = (UINT64)BIT9;
  AsmWriteMsr64 (MSR_IA32_FMASK, Msr);
}
