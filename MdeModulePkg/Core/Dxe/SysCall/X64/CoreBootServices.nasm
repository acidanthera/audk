;------------------------------------------------------------------------------
;
; Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
; SPDX-License-Identifier: BSD-3-Clause
;
;------------------------------------------------------------------------------

DEFAULT REL
SECTION .text

extern ASM_PFX(CallBootService)
extern ASM_PFX(gCoreSysCallStackTop)

%macro CallSysRet 0
    ; Prepare SYSRET arguments.
    mov     rcx, [rbp + 8*4]
    pop     rdx

    ; Switch from Core to User data segment selectors.
    pop     r11

o16 mov     ds, r11
o16 mov     es, r11
o16 mov     fs, r11
o16 mov     gs, r11

    ; Restore RFLAGS in R11 for SYSRET.
    pushfq
    pop     r11

    ; Switch to User Stack.
    pop     rbp
    pop     rbp
    mov     rsp, rdx

    ; SYSCALL saves RFLAGS into R11 and the RIP of the next instruction into RCX.
o64 sysret
    ; SYSRET copies the value in RCX into RIP and loads RFLAGS from R11.
%endmacro

global ASM_PFX(DisableSMAP)
ASM_PFX(DisableSMAP):
    pushfq
    pop     r10
    or      r10, 0x40000 ; Set AC (bit 18)
    push    r10
    popfq
    ret

global ASM_PFX(EnableSMAP)
ASM_PFX(EnableSMAP):
    pushfq
    pop     r10
    and     r10, ~0x40000 ; Clear AC (bit 18)
    push    r10
    popfq
    ret

;------------------------------------------------------------------------------
; UINTN
; EFIAPI
; CoreBootServices (
;   IN  UINT8  Type,
;   IN  UINTN  FunctionAddress,
;   ...
;   );
;
;   (rcx) RIP of the next instruction saved by SYSCALL in SysCall().
;   (rdx) FunctionAddress.
;   (r8)  Argument 1 of the called function.
;   (r9)  Argument 2 of the called function.
;   (r10) Type.
;   (r11) RFLAGS saved by SYSCALL in SysCall().
;On stack Argument 3, 4, ...
;------------------------------------------------------------------------------
global ASM_PFX(CoreBootServices)
ASM_PFX(CoreBootServices):
    ; Save User data segment selector temporarily in R11.
    mov     r11, ds

    ; Switch from User to Core data segment selectors.
    mov     ax, ss
    mov     ds, ax
    mov     es, ax
    mov     fs, ax
    mov     gs, ax

    ; Save User Stack pointers and switch to Core SysCall Stack.
    mov     rax, [ASM_PFX(gCoreSysCallStackTop)]
    ; Save return address for SYSRET.
    sub     rax, 8
    mov     [rax], rcx
    mov     rcx, r10
    sub     rax, 8
    mov     [rax], r8
    sub     rax, 8
    mov     [rax], rbp
    sub     rax, 8
    mov     [rax], r9
    ; Save User data segment selector on Core SysCall Stack.
    sub     rax, 8
    mov     [rax], r11

    mov     r9, rsp

    mov     rsp, rax

    mov     rbp, rsp
    mov     r8, rbp
    push    r9

    call ASM_PFX(CallBootService)

    CallSysRet

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

    mov     ds, ax
    mov     es, ax
    mov     fs, ax
    mov     gs, ax

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
