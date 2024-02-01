/** @file
  Switch Stack functions.

  Copyright (c) 2006 - 2018, Intel Corporation. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-2-Clause-Patent

**/

#include "BaseLibInternals.h"

/**
  Transfers control to a function starting with a new stack.

  Transfers control to the function specified by EntryPoint using the
  new stack specified by NewStack and passing in the parameters specified
  by Context1 and Context2.  Context1 and Context2 are optional and may
  be NULL.  The function EntryPoint must never return.  This function
  supports a variable number of arguments following the NewStack parameter.
  These additional arguments are ignored on IA-32, x64, and EBC.
  IPF CPUs expect one additional parameter of type VOID * that specifies
  the new backing store pointer.

  If EntryPoint is NULL, then ASSERT().
  If NewStack is NULL, then ASSERT().

  @param  EntryPoint  A pointer to function to call with the new stack.
  @param  Context1    A pointer to the context to pass into the EntryPoint
                      function.
  @param  Context2    A pointer to the context to pass into the EntryPoint
                      function.
  @param  NewStack    A pointer to the new stack to use for the EntryPoint
                      function.
  @param  ...         This variable argument list is ignored for IA32, x64, and EBC.
                      For IPF, this variable argument list is expected to contain
                      a single parameter of type VOID * that specifies the new backing
                      store pointer.


**/
VOID
EFIAPI
SwitchStack (
  IN      SWITCH_STACK_ENTRY_POINT  EntryPoint,
  IN      VOID                      *Context1   OPTIONAL,
  IN      VOID                      *Context2   OPTIONAL,
  IN      VOID                      *NewStack,
  ...
  )
{
  VA_LIST  Marker;

  ASSERT (EntryPoint != NULL);
  ASSERT (NewStack != NULL);

  //
  // New stack must be aligned with CPU_STACK_ALIGNMENT
  //
  ASSERT (((UINTN)NewStack & (CPU_STACK_ALIGNMENT - 1)) == 0);

  VA_START (Marker, NewStack);

  InternalSwitchStack (EntryPoint, Context1, Context2, NewStack, Marker);

  VA_END (Marker);

  //
  // InternalSwitchStack () will never return
  //
  ASSERT (FALSE);
}

VOID
EFIAPI
EnterUserImage (
  IN SWITCH_STACK_ENTRY_POINT  EntryPoint,
  IN VOID                      *Context1   OPTIONAL,
  IN VOID                      *Context2   OPTIONAL,
  IN VOID                      *NewStack,
  IN UINT16                    CodeSelector,
  IN UINT16                    DataSelector
  )
{
  ASSERT (EntryPoint != NULL);
  ASSERT (NewStack != NULL);

  //
  // New stack must be aligned with CPU_STACK_ALIGNMENT
  //
  ASSERT (((UINTN)NewStack & (CPU_STACK_ALIGNMENT - 1)) == 0);

  InternalEnterUserImage (EntryPoint, Context1, Context2, NewStack, CodeSelector, DataSelector);
}

UINTN
EFIAPI
CallBootService (
  IN UINT8  Type,
  IN VOID   **FunctionAddress,
  IN UINTN  CoreRbp,
  IN UINTN  UserRsp
  )
{
  UINTN      Status;
  VOID       *Pointer;
  VOID * Arg4;
  VOID * Arg5;
  UINT32     Arg6;
  EFI_ALLOCATE_RING3_PAGES Func1;
  EFI_ALLOCATE_CORE_COPY Func2;
  EFI_LOCATE_PROTOCOL Func3;
  EFI_OPEN_PROTOCOL Func4;
  // Stack:
  //  rcx - Rip for SYSCALL
  //  r8  - Argument 1
  //  rbp - User Rbp
  //  r9  - Argument 2
  //  r11 - User data segment selector  <- CoreRbp
  //  rsp - User Rsp
  switch (Type) {
    case SysCallReadMemory:
      return *(UINTN *)FunctionAddress;

    case SysCallAllocateRing3Pages:
      Func1 = (EFI_ALLOCATE_RING3_PAGES)*FunctionAddress;
      Status = Func1 (
                 *((UINTN *)CoreRbp + 3),
                 &Pointer
                 );
      DisableSMAP ();
      *(UINTN *)(*((UINTN *)CoreRbp + 1)) = (UINTN)Pointer;
      EnableSMAP ();
      return (UINTN)Status;

    case SysCallAllocateCoreCopy:
      DisableSMAP ();
      Func2 = (EFI_ALLOCATE_CORE_COPY)*FunctionAddress;
      Status = (UINTN)Func2 (
                 *((UINTN *)CoreRbp + 3),
                 (VOID *)*((UINTN *)CoreRbp + 1)
                 );
      EnableSMAP ();
      return (UINTN)Status;

    case SysCallLocateProtocol:
      Func3 = (EFI_LOCATE_PROTOCOL)*FunctionAddress;
      Status = Func3 (
                 (VOID *)*((UINTN *)CoreRbp + 3),
                 (VOID *)*((UINTN *)CoreRbp + 1),
                 &Pointer
                 );
      DisableSMAP ();
      *((UINTN *)UserRsp + 5) = (UINTN)Pointer;
      EnableSMAP ();
      return (UINTN)Status;

    case SysCallOpenProtocol:
      DisableSMAP ();
      Arg4 = (VOID *)*((UINTN *)UserRsp + 6);
      Arg5 = (VOID *)*((UINTN *)UserRsp + 7);
      Arg6 = (UINT32)*((UINTN *)UserRsp + 8);
      EnableSMAP ();
      Func4 = (EFI_OPEN_PROTOCOL)*FunctionAddress;
      Status = Func4 (
                  (VOID *)*((UINTN *)CoreRbp + 3),
                  (VOID *)*((UINTN *)CoreRbp + 1),
                  &Pointer,
                  Arg4,
                  Arg5,
                  Arg6
                  );
      DisableSMAP ();
      *((UINTN *)UserRsp + 5) = (UINTN)Pointer;
      EnableSMAP ();
      return (UINTN)Status;
    default:
      break;
  }

  return 0;
}
