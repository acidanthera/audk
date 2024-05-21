//------------------------------------------------------------------------------
//
// Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
// SPDX-License-Identifier: BSD-3-Clause
//
//------------------------------------------------------------------------------

#include <AsmMacroIoLibV8.h>

//------------------------------------------------------------------------------
// EFI_STATUS
// EFIAPI
// CallInstallMultipleProtocolInterfaces (
//   IN EFI_HANDLE  *Handle,
//   IN VOID        **ArgList,
//   IN UINT32      ArgListSize,
//   IN VOID        *Function
//   );
//------------------------------------------------------------------------------
ASM_FUNC(CallInstallMultipleProtocolInterfaces)
    ret

//------------------------------------------------------------------------------
// EFI_STATUS
// EFIAPI
// CallRing3 (
//   IN RING3_CALL_DATA *Data
//   );
//
//   (x0) Data
//   (x1) gRing3CallStackTop
//   (x2) gRing3EntryPoint
//------------------------------------------------------------------------------
ASM_FUNC(ArmCallRing3)
  // Disable interrupts
  msr  daifset, #0xf
  isb

  // Use SP_ELx for Exception level ELx.
  msr  SPsel, #1

  msr  sp_el0, x1

  msr  elr_el1, x2

  // Copy PSTATE to SPSR.
  mrs  x1, nzcv
  mrs  x2, pan
  orr  x1, x1, x2
  mrs  x2, daif
  orr  x1, x1, x2
  //
  // M[3:0], bits [3:0] AArch64 Exception level and selected Stack Pointer.
  // 0b0000 - EL0.
  // 0b0100 - EL1 with SP_EL0 (ELt).
  // 0b0101 - EL1 with SP_EL1 (EL1h).
  //
  msr  spsr_el1, x1

  isb
  dsb sy

  eret
