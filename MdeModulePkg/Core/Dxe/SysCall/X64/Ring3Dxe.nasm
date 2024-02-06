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
;------------------------------------------------------------------------------
global ASM_PFX(_ModuleEntryPoint)
ASM_PFX(_ModuleEntryPoint):
  ret
