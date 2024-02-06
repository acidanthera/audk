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
extern ASM_PFX(gRing3CallStackTop)
extern ASM_PFX(gRing3EntryPoint)

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
; EFI_STATUS
; EFIAPI
; CoreBootServices (
;   IN  UINT8  Type,
;   ...
;   );
;
;   (rcx) RIP of the next instruction saved by SYSCALL in SysCall().
;   (rdx) Argument 1 of the called function.
;   (r8)  Argument 2 of the called function.
;   (r9)  Argument 3 of the called function.
;   (r10) Type.
;   (r11) RFLAGS saved by SYSCALL in SysCall().
;
;   (On User Stack) Argument 4, 5, ...
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
    sub     rax, 8
    mov     [rax], rsp
    mov     rsp, rax
    push    rbp
    ; Save return address for SYSRET.
    push    rcx
    ; Save User data segment selector.
    push    r11
    ; Save User Arguments [1..3].
    push    r9
    push    r8
    push    rdx
    mov     rbp, rsp

    ; Prepare CallBootService arguments.
    mov     rcx, r10
    mov     rdx, rbp
    mov     r8, [rbp + 8*6]

    call ASM_PFX(CallBootService)

    ; Step over Arguments [1..3].
    add     rsp, 8*3

    ; Switch from Core to User data segment selectors.
    pop     r11

o16 mov     ds, r11
o16 mov     es, r11
o16 mov     fs, r11
o16 mov     gs, r11

    ; Prepare SYSRET arguments.
    pop     rcx
    pushfq
    pop     r11

    ; Switch to User Stack.
    pop     rbp
    pop     rsp

    ; SYSCALL saves RFLAGS into R11 and the RIP of the next instruction into RCX.
o64 sysret
    ; SYSRET copies the value in RCX into RIP and loads RFLAGS from R11.

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

;------------------------------------------------------------------------------
; EFI_STATUS
; EFIAPI
; CallRing3 (
;   IN UINT8  Type,
;   IN UINT16 CodeSelector,
;   IN UINT16 DataSelector,
;   IN VOID   *FunctionAddress,
;   ...
;   );
;
;   (rcx) Type.
;   (rdx) CodeSelector  - Segment selector for code.
;   (r8)  DataSelector  - Segment selector for data.
;   (r9)  FunctionAddress
;
;   (On User Stack) Argument 1, 2, 3, ...
;------------------------------------------------------------------------------
global ASM_PFX(CallRing3)
ASM_PFX(CallRing3):
    ; Set Data selectors
    or      r8, 3H ; RPL = 3

o16 mov     ds, r8
o16 mov     es, r8
o16 mov     fs, r8
o16 mov     gs, r8

    ; Save Code selector
    or      rdx, 3H ; RPL = 3

    ; Prepare stack before swithcing
    push    r8                      ;  ss
    push qword [gRing3CallStackTop] ;  rsp
    push    rdx                     ;  cs
    push qword [gRing3EntryPoint]   ;  rip

    ; Copy Arguments from Core Stack to User Stack + return address

    ; Pass control to User driver function.
    retfq
coreReturnAddress:
    ret
