;------------------------------------------------------------------------------
;
; Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
; SPDX-License-Identifier: BSD-3-Clause
;
;------------------------------------------------------------------------------

DEFAULT REL
SECTION .text

;------------------------------------------------------------------------------
; EFI_STATUS
; EFIAPI
; _ModuleEntryPoint (
;   IN EFI_HANDLE        ImageHandle,
;   IN EFI_SYSTEM_TABLE  *SystemTable
;   )
;
;   (rcx) _ModuleEntryPoint  - Used by SYSRET.
;   (rdx) EntryPoint         - Function address in User address space.
;   (r8)  Context1           - Parameter1 for entry point.
;   (r9)  Context2           - Parameter2 for entry point.
;------------------------------------------------------------------------------
global ASM_PFX(_ModuleEntryPoint)
ASM_PFX(_ModuleEntryPoint):
    mov rcx, r8
    mov r8, rdx
    mov rdx, r9

    call r8
    
    ret
