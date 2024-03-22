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
    pushfd
    pop     eax
    or      eax, 0x40000 ; Set AC (bit 18)
    push    eax
    popfd
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
    pushfd
    pop     eax
    and     eax, ~0x40000 ; Clear AC (bit 18)
    push    eax
    popfd
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
    push    ebp
    mov     ebp, esp

    ; Prepare stack for call.
    mov     eax, [ebp + 3 * 4]   ; eax = ArgList
    mov     ecx, [ebp + 4 * 4]   ; ecx = ArgListSize
    lea     eax, [eax + ecx * 4]
copy:
    sub     eax, 4
    push dword [eax]
    sub     ecx, 1
    jnz     copy
    push dword [ebp + 2 * 4]

    call    [ebp + 5 * 4]

    ; Step over Function arguments.
    mov     esp, ebp
    pop     ebp

    ret

%macro SetRing3DataSegmentSelectors 0
    push dword MSR_IA32_SYSENTER_CS
    call ASM_PFX(AsmReadMsr64)
    ; eax = RING0_CODE32_SEL
    add     eax, 24  ; GDT: RING0_CODE32, RING0_DATA32, RING3_CODE32, RING3_DATA32
    or      eax, 3   ; RPL = 3

    mov     ds, ax
    mov     es, ax
    mov     fs, ax
    mov     gs, ax

    pop     eax
%endmacro

;------------------------------------------------------------------------------
; EFI_STATUS
; EFIAPI
; CoreBootServices (
;   IN  UINT8  Type,
;   ...
;   );
;
;   (eax) User return address.
;   (ecx) Type.
;   (edx) User Stack Pointer.
;
;   (On User Stack) Argument 1, 2, ...
;------------------------------------------------------------------------------
global ASM_PFX(CoreBootServices)
ASM_PFX(CoreBootServices):
    ; Save User return address and Stack pointers.
    push    edx
    push    ebp
    push    eax

    ; Switch from User to Core data segment selectors.
    mov     ax, ss
    mov     ds, ax
    mov     es, ax
    mov     fs, ax
    mov     gs, ax

    ; Special case for SysCallReturnToCore.
    cmp     ecx, 0
    je      coreReturnAddress

    ; Prepare CallBootService arguments.
    call ASM_PFX(DisableSMAP)
    mov     eax, [edx + 4 * 4] ; User Argument 3
    push    eax
    mov     eax, [edx + 3 * 4] ; User Argument 2
    push    eax
    mov     eax, [edx + 2 * 4] ; User Argument 1
    push    eax
    call ASM_PFX(EnableSMAP)
    mov     ebp, esp
    push    edx
    push    ebp
    push    ecx

    sti
    call ASM_PFX(CallBootService)
    push    eax
    cli

    SetRing3DataSegmentSelectors

    pop     eax

    ; Step over User Arguments [1..3] and CallBootService input.
    add     esp, 4*6

    ; Prepare SYSEXIT arguments.
    pop     edx ; User return address.
    pop     ebp
    pop     ecx ; User Stack Pointer.

    sysexit

;------------------------------------------------------------------------------
; EFI_STATUS
; EFIAPI
; CallRing3 (
;   IN RING3_CALL_DATA *Data
;   );
;
;   (On User Stack) Data
;------------------------------------------------------------------------------
global ASM_PFX(CallRing3)
ASM_PFX(CallRing3):
    cli

    ; Save Core Stack pointers.
    mov     [ASM_PFX(CoreEsp)], esp
    mov     [ASM_PFX(CoreEbp)], ebp

    push dword [ASM_PFX(gRing3EntryPoint)]
    push dword [ASM_PFX(gRing3CallStackTop)]

    SetRing3DataSegmentSelectors

    ; Prepare SYSEXIT arguments.
    pop     ecx
    pop     edx
    mov     eax, [esp + 4] ; Data

    ; Switch to User Stack.
    mov     ebp, ecx

    ; Pass control to user image
    sysexit

coreReturnAddress:
    mov     esp, [ASM_PFX(CoreEsp)]
    mov     ebp, [ASM_PFX(CoreEbp)]

    call ASM_PFX(DisableSMAP)
    mov     eax, [edx + 2 * 4] ; User Argument 1
    push    eax
    call ASM_PFX(EnableSMAP)
    pop     eax

    sti
    ret

SECTION .data
ASM_PFX(CoreEsp):
  resd 1

ASM_PFX(CoreEbp):
  resd 1
