;------------------------------------------------------------------------------
; Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
; SPDX-License-Identifier: BSD-3-Clause
;------------------------------------------------------------------------------

#include <Uefi/UefiSpec.h>

extern ASM_PFX(Ring3Call)

DEFAULT REL
SECTION .text

;------------------------------------------------------------------------------
; EFI_STATUS
; EFIAPI
; SysCall (
;   IN UINT8  Type,
;   IN UINT8  NumberOfArguments,
;   ...
;   );
;------------------------------------------------------------------------------
global ASM_PFX(SysCall)
ASM_PFX(SysCall):
  push    ebx
  mov     edx, esp
  mov     ecx, [esp + 4*2] ; Type
  mov     ebx, [esp + 4*3] ; NumberOfArguments
  lea     eax, [userReturnAddress]
  ; Fixup NumberOfArguments.
  cmp     ecx, SC_FREE_PAGES
  je      fixup
  cmp     ecx, SC_BLOCK_IO_READ
  je      fixup
  cmp     ecx, SC_BLOCK_IO_WRITE
  je      fixup
  cmp     ecx, SC_DISK_IO_READ
  je      fixup
  cmp     ecx, SC_DISK_IO_WRITE
  je      fixup
  jmp     makecall
fixup:
  add     ebx, 1
makecall:
  sysenter
userReturnAddress:
  pop     ebx
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

    call ASM_PFX(Ring3Call)
