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
    // Save function input.
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
  // Copy PSTATE to SPSR.
  mrs  x6, nzcv
  mrs  x7, pan
  orr  x6, x6, x7
  // Prepare Ring3 SP and EntryPoint.
  msr  sp_el0, x1
  EL1_OR_EL2(x1)
1:msr  elr_el1, x2
  msr  spsr_el1, x6
  b    3f
2:msr  elr_el2, x2
  msr  spsr_el2, x6
  // Save Core SP and switch to CoreSysCall Stack.
3:mov  x5, sp
  str  x5, [x4]
  mov  sp, x3

  isb
  eret

//------------------------------------------------------------------------------
// VOID
// EFIAPI
// ReturnToCore (
//   IN EFI_STATUS Status
//   );
//
//   (x0) Status
//   (x1) mCoreSp
//------------------------------------------------------------------------------
ASM_FUNC(ArmReturnToCore)
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
