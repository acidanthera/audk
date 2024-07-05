//------------------------------------------------------------------------------
//
// Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
// SPDX-License-Identifier: BSD-3-Clause
//
//------------------------------------------------------------------------------

#include <AsmMacroIoLibV8.h>

.cpu cortex-a76

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
  // Save registers.
  sub  sp, sp, #0x100

  stp  q8,  q9,  [sp, #0xe0]
  stp  q10, q11, [sp, #0xc0]
  stp  q12, q13, [sp, #0xa0]
  stp  q14, q15, [sp, #0x80]

  stp  xzr, x16, [sp, #0x70]
  stp  x17, x18, [sp, #0x60]
  stp  x19, x20, [sp, #0x50]
  stp  x21, x22, [sp, #0x40]
  stp  x23, x24, [sp, #0x30]
  stp  x25, x26, [sp, #0x20]
  stp  x27, x28, [sp, #0x10]
  stp  x29, x30, [sp]
  // Disable interrupts.
  msr  daifset, #0xf
  isb
  // Prepare Ring3 SP and EntryPoint.
  msr  sp_el0, x1
  msr  elr_el1, x2
  // Save Core SP and switch to CoreSysCall Stack.
  mov  x5, sp
  str  x5, [x4]
  mov  sp, x3
  // Copy PSTATE to SPSR.
  mrs  x1, nzcv
  mrs  x2, pan
  orr  x1, x1, x2
  //
  // M[3:0], bits [3:0] AArch64 Exception level and selected Stack Pointer.
  // 0b0000 - EL0.
  // 0b0100 - EL1 with SP_EL0 (ELt).
  // 0b0101 - EL1 with SP_EL1 (EL1h).
  //
  msr  spsr_el1, x1
  isb
  dsb  sy
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
  // Zero Exception Syndrome Register to prevent QEMU from random crashing.
  msr  esr_el1, xzr
  msr  spsr_el1, xzr
  msr  elr_el1, xzr
  msr  far_el1, xzr
  // Switch to Core Stack.
  mov  sp, x1
  // Restore registers and Stack.
  ldp  q8,  q9,  [sp, #0xe0]
  ldp  q10, q11, [sp, #0xc0]
  ldp  q12, q13, [sp, #0xa0]
  ldp  q14, q15, [sp, #0x80]

  ldr  x16, [sp, #0x78]
  ldp  x17, x18, [sp, #0x60]
  ldp  x19, x20, [sp, #0x50]
  ldp  x21, x22, [sp, #0x40]
  ldp  x23, x24, [sp, #0x30]
  ldp  x25, x26, [sp, #0x20]
  ldp  x27, x28, [sp, #0x10]
  ldp  x29, x30, [sp]
  add	 sp, sp, #0x100
  // Enable interrupts.
  msr  daifclr, #0xf
  isb
  ret

//------------------------------------------------------------------------------
// VOID
// EFIAPI
// ArmSetPan (
//   VOID
//   );
//------------------------------------------------------------------------------
ASM_FUNC(ArmSetPan)
  msr   pan, #1
  ret

//------------------------------------------------------------------------------
// VOID
// EFIAPI
// ArmClearPan (
//  VOID
//  );
//------------------------------------------------------------------------------
ASM_FUNC(ArmClearPan)
  msr   pan, #0
  ret
