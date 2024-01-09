;------------------------------------------------------------------------------
;
; Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
; SPDX-License-Identifier: BSD-3-Clause
;
; Module Name:
;
;   WriteEflags.Asm
;
; Abstract:
;
;   AsmWriteEflags function
;
; Notes:
;
;------------------------------------------------------------------------------

    DEFAULT REL
    SECTION .text

;------------------------------------------------------------------------------
; UINTN
; EFIAPI
; AsmWriteEflags (
;   UINTN  Eflags
;   );
;------------------------------------------------------------------------------
global ASM_PFX(AsmWriteEflags)
ASM_PFX(AsmWriteEflags):
    push    rcx
    popfq
    mov     rax, rcx
    ret
