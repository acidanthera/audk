;------------------------------------------------------------------------------
; Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
; SPDX-License-Identifier: BSD-3-Clause
;------------------------------------------------------------------------------

extern ASM_PFX(Ring3Call)

DEFAULT REL
SECTION .text

;------------------------------------------------------------------------------
; EFI_STATUS
; EFIAPI
; SysCall (
;   IN  UINT8  Type,
;   ...
;   );
;------------------------------------------------------------------------------
global ASM_PFX(SysCall)
ASM_PFX(SysCall):
  mov     edx, esp
  mov     ecx, [esp + 4] ; Type
  lea     eax, [userReturnAddress]

  sysenter
userReturnAddress:
  ; sti
  ret

;------------------------------------------------------------------------------
; VOID
; EFIAPI
; Ring3EntryPoint (
;   IN RING3_CALL_DATA *Data
;   );
;
;   (eax) Data
;------------------------------------------------------------------------------
global ASM_PFX(Ring3EntryPoint)
ASM_PFX(Ring3EntryPoint):
    push    eax
    ; sti

    call ASM_PFX(Ring3Call)
