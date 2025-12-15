/**
 *  Copyright Notice:
 *  Copyright 2021-2022 DMTF. All rights reserved.
 *  License: BSD 3-Clause License. For full text see link: https://github.com/DMTF/libspdm/blob/main/LICENSE.md
 **/

 #include <Library/BaseLib.h>

/*
 * Divides a 64-bit signed value with a 64-bit signed value and returns
 * a 64-bit signed result.
 */
__declspec(naked) void __cdecl _alldiv(void)
{
  //
  // Wrapper Implementation over EDKII DivS64x64Remainder() routine
  //    INT64
  //    EFIAPI
  //    DivS64x64Remainder (
  //      IN      INT64     Dividend,
  //      IN      INT64     Divisor,
  //      OUT     INT64     *Remainder  OPTIONAL
  //      )
  //
  _asm {

      ; Original local stack when calling _alldiv
      ;               -----------------
      ;               |               |
      ;               |---------------|
      ;               |               |
      ;               |--  Divisor  --|
      ;               |               |
      ;               |---------------|
      ;               |               |
      ;               |--  Dividend --|
      ;               |               |
      ;               |---------------|
      ;               |  ReturnAddr** |
      ;       ESP---->|---------------|
      ;

      ;
      ; Set up the local stack for NULL Reminder pointer
      ;
      xor eax, eax
      push eax

      ;
      ; Set up the local stack for divisor parameter
      ;
      mov eax, [esp + 20]
      push eax
      mov eax, [esp + 20]
      push eax

      ;
      ; Set up the local stack for dividend parameter
      ;
      mov eax, [esp + 20]
      push eax
      mov eax, [esp + 20]
      push eax

      ;
      ; Call native DivS64x64Remainder of BaseLib
      ;
      call DivS64x64Remainder

      ;
      ; Adjust stack
      ;
      add esp, 20

      ret  16
  }
}
