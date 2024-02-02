/** @file

  Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause

**/

#include <Uefi.h>

#include <Library/DebugLib.h>
#include <Library/MemoryAllocationLib.h>
#include <Library/UefiBootServicesTableLib.h>

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

  EFI_GUID    *CoreProtocol;

  // Stack:
  //  rcx - Rip for SYSCALL
  //  r8  - Argument 1
  //  rbp - User Rbp
  //  r9  - Argument 2
  //  r11 - User data segment selector  <- CoreRbp
  //  rsp - User Rsp
  switch (Type) {
    case SysCallAllocateRing3Pages:
      Status = gBS->AllocateRing3Pages (*((UINTN *)CoreRbp + 3), &Pointer);
      DisableSMAP ();
      *(UINTN *)(*((UINTN *)CoreRbp + 1)) = (UINTN)Pointer;
      EnableSMAP ();
      return (UINTN)Status;

    case SysCallLocateProtocol:
      DisableSMAP ();
      CoreProtocol = AllocateCopyPool (sizeof (EFI_GUID), (VOID *)*((UINTN *)CoreRbp + 3));
      EnableSMAP ();
      if (CoreProtocol == NULL) {
        DEBUG ((DEBUG_ERROR, "Ring0: Failed to allocate core copy of the Protocol variable.\n"));
        return EFI_OUT_OF_RESOURCES;
      }

      Status = gBS->LocateProtocol (
                 CoreProtocol,
                 (VOID *)*((UINTN *)CoreRbp + 1),
                 &Pointer
                 );

      FreePool (CoreProtocol);
      DisableSMAP ();
      *((UINTN *)UserRsp + 5) = (UINTN)Pointer;
      EnableSMAP ();
      return (UINTN)Status;

    case SysCallOpenProtocol:
      DisableSMAP ();
      CoreProtocol = AllocateCopyPool (sizeof (EFI_GUID), (VOID *)*((UINTN *)CoreRbp + 1));
      Arg4 = (VOID *)*((UINTN *)UserRsp + 6);
      Arg5 = (VOID *)*((UINTN *)UserRsp + 7);
      Arg6 = (UINT32)*((UINTN *)UserRsp + 8);
      EnableSMAP ();
      if (CoreProtocol == NULL) {
        DEBUG ((DEBUG_ERROR, "Ring0: Failed to allocate core copy of the Protocol variable.\n"));
        return EFI_OUT_OF_RESOURCES;
      }

      Status = gBS->OpenProtocol (
                  (VOID *)*((UINTN *)CoreRbp + 3),
                  CoreProtocol,
                  &Pointer,
                  Arg4,
                  Arg5,
                  Arg6
                  );

      FreePool (CoreProtocol);
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
