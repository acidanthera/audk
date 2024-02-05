/** @file

  Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause

**/

#include "DxeMain.h"

#include <Protocol/DevicePathUtilities.h>

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
  UINT32       MemoryCoreSize;

  // Stack:
  //  rcx - Rip for SYSCALL
  //  rdx - Argument 1
  //  rbp - User Rbp
  //  r8  - Argument 2
  //  r11 - User data segment selector  <- CoreRbp
  //  rsp - User Rsp
  //  r9  - Argument 3
  switch (Type) {
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

      if (CompareGuid (CoreProtocol, &gEfiDevicePathUtilitiesProtocolGuid)) {
        MemoryCoreSize = sizeof (EFI_DEVICE_PATH_UTILITIES_PROTOCOL);
      } else {
        MemoryCoreSize = 0;
      }

      Pointer = AllocateRing3CopyPages (Pointer, MemoryCoreSize);
      if (Pointer == NULL) {
        DEBUG ((DEBUG_ERROR, "Ring0: Failed to allocate pages for Ring3 PROTOCOL structure.\n"));
        FreePool (CoreProtocol);
        return EFI_OUT_OF_RESOURCES;
      }

      DisableSMAP ();
      *(UINTN *)(*((UINTN *)CoreRbp - 2)) = (UINTN)Pointer;
      EnableSMAP ();

      FreePool (CoreProtocol);

      return (UINTN)Status;

    case SysCallOpenProtocol:
      DisableSMAP ();
      CoreProtocol = AllocateCopyPool (sizeof (EFI_GUID), (VOID *)*((UINTN *)CoreRbp + 1));
      Arg4 = (VOID *)*((UINTN *)UserRsp + 5);
      Arg5 = (VOID *)*((UINTN *)UserRsp + 6);
      Arg6 = (UINT32)*((UINTN *)UserRsp + 7);
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

      if (CompareGuid (CoreProtocol, &gEfiLoadedImageProtocolGuid)) {
        MemoryCoreSize = sizeof (EFI_LOADED_IMAGE_PROTOCOL);
      } else {
        MemoryCoreSize = 0;
      }

      Pointer = AllocateRing3CopyPages (Pointer, MemoryCoreSize);
      if (Pointer == NULL) {
        DEBUG ((DEBUG_ERROR, "Ring0: Failed to allocate pages for Ring3 PROTOCOL structure.\n"));
        FreePool (CoreProtocol);
        return EFI_OUT_OF_RESOURCES;
      }

      DisableSMAP ();
      *(UINTN *)(*((UINTN *)CoreRbp - 2)) = (UINTN)Pointer;
      EnableSMAP ();

      FreePool (CoreProtocol);

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
