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
    stp	 x29, x30, [sp, #-0x10]!
    mov  x29, sp
    // Save funtion input.
    mov  x9, x1
    mov  x10, x2
    mov  x11, x3
    // Prepare registers for call.
    ldp  x1, x2, [x9]
    ldp  x3, x4, [x9, #0x10]
    ldp  x5, x6, [x9, #0x20]
    ldr  x7, [x9, #0x30]
    // Prepare stack for call.
    cmp  x10, #7
    b.le call
    add  x9, x9, x10, LSL #3
    sub  x10, x10, #7
    tst  x10, #1
    b.eq copy
    // To align stack on 16 bytes.
    add  x9, x9, #0x8
    add  x10, x10, #1
copy:
    ldp  x12, x13, [x9, #-0x10]!
    stp  x12, x13, [sp, #-0x10]!
    subs x10, x10, #2
    b.ne copy

call:
    blr  x11

    mov  sp, x29
    ldp	 x29, x30, [sp]
    add	 sp, sp, #0x10
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
//   (x3) gCoreSysCallStackTop
//   (x4) &CoreSp
//------------------------------------------------------------------------------
ASM_FUNC(ArmCallRing3)
  // Save FP and LR on Core Stack.
  stp	 x29, x30, [sp, #-0x10]!
  // Disable interrupts
  msr  daifset, #0xf
  isb
  // Prepare Ring3 SP and EntryPoint.
  msr  sp_el0, x1
  msr  elr_el1, x2
  // Save Core SP and switch to Ring3Call Stack.
  mov  x5, sp
  str  x5, [x4]
  mov  sp, x3

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

//------------------------------------------------------------------------------
// VOID
// EFIAPI
// ReturnToCore (
//   IN EFI_STATUS Status,
//   IN UINTN      CoreSp
//   );
//------------------------------------------------------------------------------
ASM_FUNC(ReturnToCore)
  // Switch to Core Stack.
  mov  sp, x1
  // Restore Stack.
  ldp	 x29, x30, [sp]
  add	 sp, sp, #0x10
  ret
