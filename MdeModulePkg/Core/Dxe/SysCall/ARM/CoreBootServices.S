//------------------------------------------------------------------------------
//
// Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
// SPDX-License-Identifier: BSD-3-Clause
//
//------------------------------------------------------------------------------

#include <AsmMacroIoLib.h>

.arch armv8.1a

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
    bx    LR

//------------------------------------------------------------------------------
// EFI_STATUS
// EFIAPI
// CallRing3 (
//   IN RING3_CALL_DATA *Data
//   );
//
//   (r0) Data
//   (r1) gRing3CallStackTop
//   (r2) gRing3EntryPoint
//   (r3) gCoreSysCallStackTop
//
//   (On Core Stack) &CoreSp
//------------------------------------------------------------------------------
ASM_FUNC(ArmCallRing3)
  // Save registers.
  push  {R4-R12, LR}
  // R6 is &CoreSp
  ldr   R6, [SP, #0x28]

#if (FixedPcdGet32(PcdVFPEnabled))
  // Save vstm registers in case they are used in optimizations.
  vpush {d0-d15}
#endif

  // Disable interrupts.
  mrs   R4, CPSR
  orr   R5, R4, #0x80
  msr   CPSR_c, R5

  // Set SP_usr to gRing3CallStackTop.
  push  {R1}
  mov   R1, SP
  ldmia R1, {SP}^
  pop   {R1}
  // Set SPSR M[3:0] bits to User mode.
  and   R4, R4, #0xFFFFFFF0

  // Save Core SP and switch to CoreSysCall Stack.
  mov   R5, SP
  str   R5, [R6]
  mov   SP, R3

  push  {R4}
  push  {R2}
  rfefd SP

//------------------------------------------------------------------------------
// VOID
// EFIAPI
// ArmSetPan (
//   VOID
//   );
//------------------------------------------------------------------------------
ASM_FUNC(ArmSetPan)
  setpan #1
  bx     LR

//------------------------------------------------------------------------------
// VOID
// EFIAPI
// ArmClearPan (
//  VOID
//  );
//------------------------------------------------------------------------------
ASM_FUNC(ArmClearPan)
  setpan #0
  bx     LR
