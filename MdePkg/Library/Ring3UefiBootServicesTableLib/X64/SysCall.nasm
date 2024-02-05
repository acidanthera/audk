;------------------------------------------------------------------------------
; Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
; SPDX-License-Identifier: BSD-3-Clause
;------------------------------------------------------------------------------

    DEFAULT REL
    SECTION .text

;------------------------------------------------------------------------------
; UINTN
; EFIAPI
; SysCall (
;   IN  UINT8  Type,
;   ...
;   );
;------------------------------------------------------------------------------
global ASM_PFX(SysCall)
ASM_PFX(SysCall):
  ; Save Type for CoreBootServices().
  mov     r10, rcx

  ; SYSCALL saves RFLAGS into R11 and the RIP of the next instruction into RCX.
  syscall
  ; SYSRET copies the value in RCX into RIP and loads RFLAGS from R11.

  ret
