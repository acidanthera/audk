//------------------------------------------------------------------------------
//
// Copyright (c) 2024 - 2025, Mikhail Krichanov. All rights reserved.
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
//   IN UINTN       ArgListSize,
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

ASM_FUNC_ALIGN(SysCallBase, 4096)
//------------------------------------------------------------------------------
// EFI_STATUS
// EFIAPI
// CallUserSpace (
//   IN USER_SPACE_CALL_DATA  *Data,
//   IN UINTN                 UserStackTop
//   );
//
//   (x0) Data
//   (x1) UserStackTop
//   (x2) gUserSpaceEntryPoint
//   (x3) gUserPageTable
//------------------------------------------------------------------------------
ASM_FUNC(ArmCallUserSpace)
  // Save registers.
  sub  sp, sp, #0x100

  stp  q8,  q9,  [sp, #0xe0]
  stp  q10, q11, [sp, #0xc0]
  stp  q12, q13, [sp, #0xa0]
  stp  q14, q15, [sp, #0x80]

  mrs  x6, sp_el0
  stp  x6,  x16, [sp, #0x70]
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
  // Prepare UserSpace SP and EntryPoint.
  msr  sp_el0, x1
  EL1_OR_EL2(x1)
1:msr  elr_el1, x2
  msr  spsr_el1, x6
  msr  ttbr0_el1, x3
  tlbi vmalle1
  b    3f
2:msr  elr_el2, x2
  msr  spsr_el2, x6
  msr  ttbr0_el2, x3
  tlbi alle2
3:dsb   sy
  isb
  eret

ASM_FUNC_ALIGN(SysCallEnd, 4096)
//------------------------------------------------------------------------------
// VOID
// EFIAPI
// ReturnToCore (
//   IN EFI_STATUS  Status,
//   IN UINTN       ReturnSP
//   );
//
//   (x0) Status
//   (x1) ReturnSP
//------------------------------------------------------------------------------
ASM_FUNC(ReturnToCore)
  // Switch to Core Stack.
  mov  sp, x1
  // Restore registers and Stack.
  ldp  q8,  q9,  [sp, #0xe0]
  ldp  q10, q11, [sp, #0xc0]
  ldp  q12, q13, [sp, #0xa0]
  ldp  q14, q15, [sp, #0x80]

  ldp  x6,  x16, [sp, #0x70]
  ldp  x17, x18, [sp, #0x60]
  ldp  x19, x20, [sp, #0x50]
  ldp  x21, x22, [sp, #0x40]
  ldp  x23, x24, [sp, #0x30]
  ldp  x25, x26, [sp, #0x20]
  ldp  x27, x28, [sp, #0x10]
  ldp  x29, x30, [sp]
  add	 sp, sp, #0x100
  msr  sp_el0, x6
  // Enable interrupts.
  msr  daifclr, #0xf
  isb
  ret
