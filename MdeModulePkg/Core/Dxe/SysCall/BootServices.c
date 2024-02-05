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

typedef struct {
  UINTN  Argument1;
  UINTN  Argument2;
  UINTN  Argument3;
} CORE_STACK;

typedef struct {
  UINTN  Rip;
  UINTN  Arguments[];
} RING3_STACK;
//
// Stack:
//  rsp - User Rsp
//  rbp - User Rbp
//  rcx - Rip for SYSCALL
//  r11 - User data segment selector
//  r9  - Argument 3
//  r8  - Argument 2
//  rdx - Argument 1 <- CoreRbp
//
EFI_STATUS
EFIAPI
CallBootService (
  IN UINT8       Type,
  IN CORE_STACK  *CoreRbp,
  IN RING3_STACK *UserRsp
  )
{
  EFI_STATUS Status;
  UINT64     Attributes;
  VOID       *Interface;
  EFI_GUID   *CoreProtocol;
  UINT32     MemoryCoreSize;
  EFI_HANDLE Argument4;
  EFI_HANDLE Argument5;
  UINT32     Argument6;

  gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)UserRsp, &Attributes);
  ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

  switch (Type) {
    case SysCallLocateProtocol:
      //
      // Argument 1: EFI_GUID  *Protocol
      // Argument 2: VOID      *CoreRegistration
      // Argument 3: VOID      **Interface
      //
      DisableSMAP ();
      CoreProtocol = AllocateCopyPool (sizeof (EFI_GUID), (VOID *)CoreRbp->Argument1);
      EnableSMAP ();
      if (CoreProtocol == NULL) {
        DEBUG ((DEBUG_ERROR, "Ring0: Failed to allocate core copy of the Protocol variable.\n"));
        return EFI_OUT_OF_RESOURCES;
      }

      Status = gBS->LocateProtocol (
                      CoreProtocol,
                      (VOID *)CoreRbp->Argument2,
                      &Interface
                      );

      if (CompareGuid (CoreProtocol, &gEfiDevicePathUtilitiesProtocolGuid)) {
        MemoryCoreSize = sizeof (EFI_DEVICE_PATH_UTILITIES_PROTOCOL);
      } else {
        MemoryCoreSize = 0;
      }

      Interface = AllocateRing3CopyPages (Interface, MemoryCoreSize);
      if (Interface == NULL) {
        DEBUG ((DEBUG_ERROR, "Ring0: Failed to allocate pages for Ring3 PROTOCOL structure.\n"));
        FreePool (CoreProtocol);
        return EFI_OUT_OF_RESOURCES;
      }

      DisableSMAP ();
      *(VOID **)CoreRbp->Argument3 = Interface;
      EnableSMAP ();

      FreePool (CoreProtocol);

      return Status;

    case SysCallOpenProtocol:
      //
      // Argument 1: EFI_HANDLE  CoreUserHandle
      // Argument 2: EFI_GUID    *Protocol
      // Argument 3: VOID        **Interface
      // Argument 4: EFI_HANDLE  CoreImageHandle
      // Argument 5: EFI_HANDLE  CoreControllerHandle
      // Argument 6: UINT32      Attributes
      //
      DisableSMAP ();
      CoreProtocol = AllocateCopyPool (sizeof (EFI_GUID), (VOID *)CoreRbp->Argument2);
      Argument4    = (EFI_HANDLE)UserRsp->Arguments[4];
      Argument5    = (EFI_HANDLE)UserRsp->Arguments[5];
      Argument6    = (UINT32)UserRsp->Arguments[6];
      EnableSMAP ();
      if (CoreProtocol == NULL) {
        DEBUG ((DEBUG_ERROR, "Ring0: Failed to allocate core copy of the Protocol variable.\n"));
        return EFI_OUT_OF_RESOURCES;
      }

      Status = gBS->OpenProtocol (
                      (EFI_HANDLE)CoreRbp->Argument1,
                      CoreProtocol,
                      &Interface,
                      Argument4,
                      Argument5,
                      Argument6
                      );

      if (CompareGuid (CoreProtocol, &gEfiLoadedImageProtocolGuid)) {
        MemoryCoreSize = sizeof (EFI_LOADED_IMAGE_PROTOCOL);
      } else {
        MemoryCoreSize = 0;
      }

      Interface = AllocateRing3CopyPages (Interface, MemoryCoreSize);
      if (Interface == NULL) {
        DEBUG ((DEBUG_ERROR, "Ring0: Failed to allocate pages for Ring3 PROTOCOL structure.\n"));
        FreePool (CoreProtocol);
        return EFI_OUT_OF_RESOURCES;
      }

      DisableSMAP ();
      *(VOID **)CoreRbp->Argument3 = Interface;
      EnableSMAP ();

      FreePool (CoreProtocol);

      return Status;

    default:
      break;
  }

  return EFI_UNSUPPORTED;
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
