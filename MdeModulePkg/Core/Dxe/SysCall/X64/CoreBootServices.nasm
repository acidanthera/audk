;------------------------------------------------------------------------------
;
; Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
; SPDX-License-Identifier: BSD-3-Clause
;
;------------------------------------------------------------------------------

#include <Register/Intel/ArchitecturalMsr.h>

extern ASM_PFX(CallBootService)
extern ASM_PFX(gCoreSysCallStackTop)
extern ASM_PFX(gRing3CallStackTop)
extern ASM_PFX(gRing3EntryPoint)

extern ASM_PFX(AsmReadMsr64)

DEFAULT REL
SECTION .text

;------------------------------------------------------------------------------
; VOID
; EFIAPI
; DisableSMAP (
;   VOID
;   );
;------------------------------------------------------------------------------
global ASM_PFX(DisableSMAP)
ASM_PFX(DisableSMAP):
    pushfq
    pop     r10
    or      r10, 0x40000 ; Set AC (bit 18)
    push    r10
    popfq
    ret

;------------------------------------------------------------------------------
; VOID
; EFIAPI
; EnableSMAP (
;   VOID
;   );
;------------------------------------------------------------------------------
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
; CallInstallMultipleProtocolInterfaces (
;   IN EFI_HANDLE  *Handle,
;   IN VOID        **ArgList,
;   IN UINT32      ArgListSize,
;   IN VOID        *Function
;   );
;------------------------------------------------------------------------------
global ASM_PFX(CallInstallMultipleProtocolInterfaces)
ASM_PFX(CallInstallMultipleProtocolInterfaces):
    push    r12

    ; Save funtion input.
    mov     rax, rdx
    mov     r10, r8
    mov     r11, r9

    ; Prepare registers for call.
    mov     rdx, [rax]
    mov     r8, [rax + 8]
    mov     r9, [rax + 8*2]

    ; Prepare stack for call.
    lea     rax, [rax + r10 * 8]
    mov     r12, r10
copy:
    sub     rax, 8
    push qword [rax]
    cmp     r10, 0
    sub     r10, 1
    jne     copy
    push    rcx

    call    r11

    ; Step over Function arguments.
    pop     rcx
    lea     rsp, [rsp + r12 * 8]

    pop     r12

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

    ; Special case for SysCallReturnToCore.
    cmp     r10, 0
    je      coreReturnAddress

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
; EFI_STATUS
; EFIAPI
; CallRing3 (
;   IN RING3_CALL_DATA *Data
;   );
;
;   (rcx) Data
;------------------------------------------------------------------------------
global ASM_PFX(CallRing3)
ASM_PFX(CallRing3):
    ; Save input Arguments.
    push    r12
    mov     r12, rcx

    ; Extract User Data selector.
    mov     rcx, MSR_IA32_STAR
    call ASM_PFX(AsmReadMsr64)
    ; rax = ((RING3_CODE64_SEL - 16) << 16 | RING0_CODE64_SEL) << 32
    shr     rax, 48
    add     rax, 8

    ; Set Data selectors
    mov     ds, ax
    mov     es, ax
    mov     fs, ax
    mov     gs, ax

    ; Prepare SYSRET arguments.
    mov     rcx, [gRing3EntryPoint]
    mov     rdx, r12
    pushfq
    pop     r11

    ; Restore stack and registers.
    pop     r12

    ; Save Core Stack pointers and switch to User Stack.
    mov     [ASM_PFX(CoreRsp)], rsp
    mov     [ASM_PFX(CoreRbp)], rbp
    mov     rsp, [ASM_PFX(gRing3CallStackTop)]
    mov     rbp, rsp

    ; Pass control to user image
o64 sysret

coreReturnAddress:
    mov     rsp, [ASM_PFX(CoreRsp)]
    mov     rbp, [ASM_PFX(CoreRbp)]
    mov     rax, rdx
    ret

SECTION .data
ASM_PFX(CoreRsp):
  resq 1

ASM_PFX(CoreRbp):
  resq 1
