/** @file

  Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause

**/

#include <Base.h>
#include <Library/BaseLib.h>
#include <Library/BaseMemoryLib.h>
#include <Library/DebugLib.h>
#include <Library/PcdLib.h>

VOID
EFIAPI
DisableSMAP (
  VOID
  );

VOID
EFIAPI
EnableSMAP (
  VOID
  );

VOID
EFIAPI
InternalEnterUserImage (
  IN SWITCH_STACK_ENTRY_POINT  EntryPoint,
  IN VOID                      *Context1   OPTIONAL,
  IN VOID                      *Context2   OPTIONAL,
  IN VOID                      *NewStack,
  IN UINT16                    CodeSelector,
  IN UINT16                    DataSelector
  );

typedef enum {
  SysCallReadMemory         = 0,
  SysCallAllocateRing3Pages = 1,
  SysCallAllocateCoreCopy   = 2,
  SysCallLocateProtocol     = 3,
  SysCallOpenProtocol       = 4,
  SysCallMax
} SYS_CALL_TYPE;

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
