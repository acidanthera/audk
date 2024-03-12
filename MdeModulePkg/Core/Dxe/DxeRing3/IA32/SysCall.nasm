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
  sysenter

  ret

;------------------------------------------------------------------------------
; VOID
; EFIAPI
; Ring3EntryPoint (
;   IN RING3_CALL_DATA *Data
;   );
;
;   (rcx) RIP of Ring3EntryPoint saved for SYSRET in CallRing3().
;   (rdx) Data
;------------------------------------------------------------------------------
global ASM_PFX(Ring3EntryPoint)
ASM_PFX(Ring3EntryPoint):

    call ASM_PFX(Ring3Call)
