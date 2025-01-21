//------------------------------------------------------------------------------
//
// Copyright (c) 2024 - 2025, Mikhail Krichanov. All rights reserved.
// SPDX-License-Identifier: BSD-3-Clause
//
//------------------------------------------------------------------------------

#include <AsmMacroIoLib.h>

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
  push  {R4-R8, LR}
  mov   R7, SP
  // Save function input.
  mov   R4, R3
  mov   R5, R1
  mov   R6, R2
  // Prepare registers for call.
  ldmfd R5, {R1-R3}
  // Prepare stack for call.
  cmp   R6, #3
  ble   call

  add   R5, R5, R6, LSL #2
  sub   R6, R6, #3
  tst   R6, #1
  beq   copy
  // To align stack on 8 bytes.
  add   R5, R5, #0x4
  add   R6, R6, #1
copy:
  sub   R5, R5, #0x4
  ldmfd R5, {R8}
  push  {R8}
  subs  R6, R6, #1
  bne   copy

call:
  blx   R4

  mov   SP, R7
  pop   {R4-R8, LR}
  bx    LR

ASM_FUNC_ALIGN(SysCallBase, 4096)
//------------------------------------------------------------------------------
// EFI_STATUS
// EFIAPI
// CallRing3 (
//   IN RING3_CALL_DATA *Data,
//   IN UINTN            UserStackTop
//   );
//
//   (r0) Data
//   (r1) UserStackTop
//   (r2) gRing3EntryPoint
//   (r3) gUserPageTable
//------------------------------------------------------------------------------
ASM_FUNC(ArmCallRing3)
  // Save registers.
  push  {R4-R12, LR}
  // Save old SP_usr and LR_usr on Core Stack.
  sub   SP, SP, #0x8
  stmia SP, {SP, LR}^

#if (FixedPcdGet32(PcdVFPEnabled))
  // Save vstm registers in case they are used in optimizations.
  vpush {d0-d15}
#endif

  // Disable interrupts.
  mrs   R4, CPSR
  cpsid if
  isb

  // Set SP_usr to UserStackTop.
  push  {R1}
  mov   R1, SP
  ldmia R1, {SP}^
  pop   {R1}
  // Set SPSR M[3:0] bits to User mode.
  and   R4, R4, #0xFFFFFFF0

  // Switch to UserPageTable.
  mrc   p15,0,R8,c2,c0,0   // R8 == TTBR0
  and   R8, R8, #0x7F      // Preserve Core TTBR0 attributes.
  orr   R3, R3, R8         // Assign Core attributes to UserPageTable.
  mcr   p15,0,R3,c2,c0,0   // TTBR0 == UserPageTable
  mcr   p15,0,r0,c8,c7,0   // TLBIALL, TLB Invalidate All.
  mcr   p15,0,r0,c7,c5,6   // BPIALL, Branch Predictor Invalidate All.
  dsb
  isb

  push  {R4}
  push  {R2}
  rfefd SP!

ASM_FUNC_ALIGN(SysCallEnd, 4096)
//------------------------------------------------------------------------------
// VOID
// EFIAPI
// ReturnToCore (
//   IN EFI_STATUS Status,
//   IN UINTN      ReturnSP
//   );
//
//   (r0) Status
//   (r1) ReturnSP
//------------------------------------------------------------------------------
ASM_FUNC(ReturnToCore)
  // Switch to Core Stack.
  mov   SP, R1

  // Restore registers and Stack.
#if (FixedPcdGet32(PcdVFPEnabled))
  vpop  {d0-d15}
#endif

  // Restore old SP_usr and LR_usr.
  ldmia SP, {SP, LR}^
  add   SP, SP, #0x8

  pop   {R4-R12, LR}

  // Enable interrupts.
  cpsie if
  isb

  bx    LR
