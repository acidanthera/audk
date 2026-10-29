;------------------------------------------------------------------------------
; Copyright (c) 2024 - 2025, Mikhail Krichanov. All rights reserved.
; SPDX-License-Identifier: BSD-3-Clause
;------------------------------------------------------------------------------

extern ASM_PFX(UserSpaceCall)

DEFAULT REL
SECTION .text

;------------------------------------------------------------------------------
; EFI_STATUS
; EFIAPI
; SysCall (
;   IN UINT8  Type,
;   IN UINT8  NumberOfArguments,
;   ...
;   );
;------------------------------------------------------------------------------
global ASM_PFX(SysCall)
ASM_PFX(SysCall):
  ; SysCall() does not use nonvolatile registers RBX, RBP, RDI, RSI, RSP, R12, R13, R14, and R15.
  ; CoreBootServices() - syscall, uses only RBP, RSP and restores them.
  ; CallBootService() uses and restores all nonvolatile registers.
  ; So there is no need for additional operations with them in SysCall().
  ;
  ; Save Type for CoreBootServices().
  mov     r10, rcx
  ; Construct User Arguments[].
  cmp     rdx, 2
  jg      continue
  push    r9
  push    r8
  ; CallBootService() reserves but does not use UserArguments[0].
  lea     r8, [rsp - 8]
  add     rsp, 8*2
  jmp     makecall
continue:
  ; Although first 4 arguments are passed through registers RCX, RDX, R8, R9,
  ; compiler reserves space for them on stack, when total number of arguments
  ; is greater than 4.
  mov     [rsp + 8*4], r9
  mov     [rsp + 8*3], r8
  lea     r8, [rsp + 8*2]
makecall:
  ; SYSCALL saves RFLAGS into R11 and the RIP of the next instruction into RCX.
  syscall
  ; SYSRET copies the value in RCX into RIP and loads RFLAGS from R11.

  ret

;------------------------------------------------------------------------------
; VOID
; EFIAPI
; UserSpaceEntryPoint (
;   IN USER_SPACE_CALL_DATA  *Data
;   );
;
;   (rcx) RIP of UserSpaceEntryPoint saved for SYSRET in CallUserSpace().
;   (rdx) Data
;------------------------------------------------------------------------------
global ASM_PFX(UserSpaceEntryPoint)
ASM_PFX(UserSpaceEntryPoint):
    mov     rcx, rdx

    call ASM_PFX(UserSpaceCall)
