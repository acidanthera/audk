;------------------------------------------------------------------------------
; Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
; SPDX-License-Identifier: BSD-3-Clause
;
; Copyright (c) 2006 - 2008, Intel Corporation. All rights reserved.<BR>
; SPDX-License-Identifier: BSD-2-Clause-Patent
;
; Module Name:
;
;   SwitchStack.Asm
;
; Abstract:
;
;------------------------------------------------------------------------------

    DEFAULT REL
    SECTION .text

;------------------------------------------------------------------------------
; Routine Description:
;
;   Routine for switching stacks with 2 parameters
;
; Arguments:
;
;   (rcx) EntryPoint    - Entry point with new stack.
;   (rdx) Context1      - Parameter1 for entry point.
;   (r8)  Context2      - Parameter2 for entry point.
;   (r9)  NewStack      - The pointer to new stack.
;
; Returns:
;
;   None
;
;------------------------------------------------------------------------------
global ASM_PFX(InternalSwitchStack)
ASM_PFX(InternalSwitchStack):
    mov     rax, rcx
    mov     rcx, rdx
    mov     rdx, r8
    ;
    ; Reserve space for register parameters (rcx, rdx, r8 & r9) on the stack,
    ; in case the callee wishes to spill them.
    ;
    lea     rsp, [r9 - 0x20]
    call    rax

;------------------------------------------------------------------------------
; Routine Description:
;
;   Routine for transfering control to user image with 2 parameters
;
; Arguments:
;
;   (rcx) EntryPoint    - Entry point with new stack.
;   (rdx) Context1      - Parameter1 for entry point.
;   (r8)  Context2      - Parameter2 for entry point.
;   (r9)  NewStack      - The pointer to new stack.
;On stack CodeSelector  - Segment selector for code.
;On stack DataSelector  - Segment selector for data.
;
; Returns:
;
;   None
;
;------------------------------------------------------------------------------
global ASM_PFX(InternalEnterUserImage)
ASM_PFX(InternalEnterUserImage):
    ; Set Data selectors
    mov     rax, [rsp + 8*6]
    or      rax, 3H ; RPL = 3

o16 mov     ds, ax
o16 mov     es, ax
o16 mov     fs, ax
o16 mov     gs, ax

    ; Save Code selector
    mov     r10, [rsp + 8*5]
    or      r10, 3H ; RPL = 3

    ; Prepare stack before swithcing
    push    rax     ;  ss
    push    r9      ;  rsp
    push    r10     ;  cs
    push    rcx     ;  rip

    ; Save 2 parameters
    mov     rcx, rdx
    mov     rdx, r8

    ; Pass control to user image
    retfq
