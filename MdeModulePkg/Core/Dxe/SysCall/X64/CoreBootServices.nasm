;------------------------------------------------------------------------------
;
; Copyright (c) 2024 - 2025, Mikhail Krichanov. All rights reserved.
; SPDX-License-Identifier: BSD-3-Clause
;
;------------------------------------------------------------------------------

#include <Register/Intel/ArchitecturalMsr.h>

extern ASM_PFX(CallBootService)
extern ASM_PFX(gRing3EntryPoint)

DEFAULT REL
SECTION .text

;------------------------------------------------------------------------------
; VOID
; EFIAPI
; AllowSupervisorAccessToUserMemory (
;   VOID
;   );
;------------------------------------------------------------------------------
global ASM_PFX(AllowSupervisorAccessToUserMemory)
ASM_PFX(AllowSupervisorAccessToUserMemory):
    pushfq
    pop     rax
    or      rax, 0x40000 ; Set AC (bit 18)
    push    rax
    popfq
    ret

;------------------------------------------------------------------------------
; VOID
; EFIAPI
; ForbidSupervisorAccessToUserMemory (
;   VOID
;   );
;------------------------------------------------------------------------------
global ASM_PFX(ForbidSupervisorAccessToUserMemory)
ASM_PFX(ForbidSupervisorAccessToUserMemory):
    pushfq
    pop     rax
    and     rax, ~0x40000 ; Clear AC (bit 18)
    push    rax
    popfq
    ret

;------------------------------------------------------------------------------
; EFI_STATUS
; EFIAPI
; CallInstallMultipleProtocolInterfaces (
;   IN EFI_HANDLE  *Handle,
;   IN VOID        **ArgList,
;   IN UINTN       ArgListSize,
;   IN VOID        *Function
;   );
;------------------------------------------------------------------------------
global ASM_PFX(CallInstallMultipleProtocolInterfaces)
ASM_PFX(CallInstallMultipleProtocolInterfaces):
    push    r12

    ; Save function input.
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
    sub     r10, 1
    jnz     copy
    push    rcx

    call    r11

    ; Step over Function arguments.
    pop     rcx
    lea     rsp, [rsp + r12 * 8]

    pop     r12

    ret

%macro SetRing3DataSegmentSelectors 0
    mov     rcx, MSR_IA32_STAR
    rdmsr
    shl     rdx, 0x20
    or      rax, rdx
    ; rax = ((RING3_CODE64_SEL - 16) << 16 | RING0_CODE64_SEL) << 32
    shr     rax, 48
    add     rax, 8

    mov     ds, ax
    mov     es, ax
    mov     fs, ax
    mov     gs, ax
%endmacro

ALIGN   4096
global ASM_PFX(SysCallBase)
ASM_PFX(SysCallBase):

;------------------------------------------------------------------------------
; EFI_STATUS
; EFIAPI
; CoreBootServices (
;   IN UINT8  Type,
;   ...
;   );
;
;   (rcx) RIP of the next instruction saved by SYSCALL in SysCall().
;   (rdx) Number of User Arguments.
;   (r8)  User Arguments[].
;   (r10) Type.
;   (r11) RFLAGS saved by SYSCALL in SysCall().
;------------------------------------------------------------------------------
global ASM_PFX(CoreBootServices)
ASM_PFX(CoreBootServices):
    mov     rax, [ASM_PFX(gCorePageTable)]
    mov     cr3, rax

    ; Switch from User to Core data segment selectors.
    mov     ax, ss
    mov     ds, ax
    mov     es, ax
    mov     fs, ax
    mov     gs, ax

    ; Save User Stack pointers and switch to Core SysCall Stack.
    mov     rax, [ASM_PFX(SysCallStackTop)]
    sub     rax, 8
    mov     [rax], rsp
    mov     rsp, rax
    push    rbp
    ; Save return address for SYSRET.
    push    rcx
    ; Save User RFLAGS for SYSRET.
    push    r11
    mov     rbp, rsp
    ; Reserve space on stack for 4 CallBootService arguments (NOOPT prerequisite).
    sub     rsp, 8*4

    ; Prepare CallBootService arguments.
    mov     rcx, r10                       ; Type
    mov     r9, [ASM_PFX(SysCallStackTop)] ; ReturnSP

    sti
    call ASM_PFX(CallBootService)
    push    rax
    cli

    SetRing3DataSegmentSelectors

    pop     rax

    ; Step over NOOPT buffer.
    mov     rsp, rbp

    ; Prepare SYSRET arguments.
    pop     r11
    pop     rcx

    ; Switch to User Stack.
    pop     rbp
    pop     rsp

    mov     rdx, [ASM_PFX(gUserPageTable)]
    mov     cr3, rdx
    ; SYSCALL saves RFLAGS into R11 and the RIP of the next instruction into RCX.
o64 sysret
    ; SYSRET copies the value in RCX into RIP and loads RFLAGS from R11.

;------------------------------------------------------------------------------
; EFI_STATUS
; EFIAPI
; CallRing3 (
;   IN RING3_CALL_DATA  *Data,
;   IN UINTN            UserStackTop
;   );
;
;   (rcx) Data
;   (rdx) UserStackTop
;------------------------------------------------------------------------------
global ASM_PFX(CallRing3)
ASM_PFX(CallRing3):
    pushfq
    pop     r11
    cli
    ; Save nonvolatile registers RBX, RBP, RDI, RSI, RSP, R12, R13, R14, and R15.
    push    rbx
    push    rbp
    push    rdi
    push    rsi
    push    r12
    push    r13
    push    r14
    push    r15
    ; Save old SysCallStackTop, set the new one.
    push qword [ASM_PFX(SysCallStackTop)]
    mov     [ASM_PFX(SysCallStackTop)], rsp

    ; Save input Arguments.
    mov     rbx, rdx
    mov     r10, rcx

    SetRing3DataSegmentSelectors

    ; Prepare SYSRET arguments.
    mov     rdx, r10
    mov     rcx, [ASM_PFX(gRing3EntryPoint)]

    ; Switch to User Stack.
    mov     rsp, rbx
    mov     rbp, rsp

    mov     r8, [ASM_PFX(gUserPageTable)]
    mov     cr3, r8
    ; Pass control to user image
o64 sysret

ALIGN   4096
global ASM_PFX(SysCallEnd)
ASM_PFX(SysCallEnd):

;------------------------------------------------------------------------------
; VOID
; EFIAPI
; ReturnToCore (
;   IN EFI_STATUS  Status,
;   IN UINTN       ReturnSP
;   );
;
;   (rcx) Status
;   (rdx) ReturnSP
;------------------------------------------------------------------------------
global ASM_PFX(ReturnToCore)
ASM_PFX(ReturnToCore):
    mov     rsp, rdx
    pop qword [ASM_PFX(SysCallStackTop)]
    pop     r15
    pop     r14
    pop     r13
    pop     r12
    pop     rsi
    pop     rdi
    pop     rbp
    pop     rbx

    mov     rax, rcx
    sti
    ret

SECTION .data
ALIGN   4096

global ASM_PFX(gCorePageTable)
ASM_PFX(gCorePageTable):
  resq 1

global ASM_PFX(gUserPageTable)
ASM_PFX(gUserPageTable):
  resq 1

ALIGN   4096
ASM_PFX(SysCallStackTop):
  resq 1
