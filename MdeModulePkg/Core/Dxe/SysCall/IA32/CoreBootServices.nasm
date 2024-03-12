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
    ret

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
    ret
