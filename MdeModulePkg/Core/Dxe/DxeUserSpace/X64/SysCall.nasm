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
  ; Save Type for CoreBootServices().
  mov     r10, rcx
  ; Construct User Arguments[].
  cmp     rdx, 2
  jg      continue
  push    r9
  push    r8
  lea     r8, [rsp - 8]
  add     rsp, 8*2
  jmp     makecall
continue:
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
