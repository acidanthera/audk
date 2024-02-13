/** @file

  Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause

**/

#include "DxeMain.h"
#include "SupportedProtocols.h"

#include <Protocol/ComponentName.h>
#include <Protocol/DevicePathUtilities.h>

VOID
EFIAPI
DisableSMEP (
  VOID
  )
{
  IA32_CR4  Cr4;

  Cr4.UintN     = AsmReadCr4 ();
  Cr4.Bits.SMEP = 0;

  AsmWriteCr4 (Cr4.UintN);
}

VOID
EFIAPI
EnableSMEP (
  VOID
  )
{
  IA32_CR4  Cr4;

  Cr4.UintN     = AsmReadCr4 ();
  Cr4.Bits.SMEP = 1;

  AsmWriteCr4 (Cr4.UintN);
}

EFI_STATUS
EFIAPI
CallInstallMultipleProtocolInterfaces (
  IN EFI_HANDLE  *Handle,
  IN VOID        **ArgList,
  IN UINT32      ArgListSize,
  IN VOID        *Function
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
  UINT32     Index;
  VOID       **UserArgList;
  VOID       *CoreArgList[MAX_LIST];
  EFI_HANDLE CoreHandle;

  EFI_DRIVER_BINDING_PROTOCOL *CoreDriverBinding;
  //
  // TODO: Check User variables.
  //
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
      if (CompareGuid ((EFI_GUID *)CoreRbp->Argument1, &gEfiDevicePathUtilitiesProtocolGuid)) {
        CoreProtocol   = &gEfiDevicePathUtilitiesProtocolGuid;
        MemoryCoreSize = sizeof (EFI_DEVICE_PATH_UTILITIES_PROTOCOL);
      } else {
        DEBUG ((DEBUG_ERROR, "Ring0: Unknown protocol.\n"));
        EnableSMAP ();
        return EFI_INVALID_PARAMETER;
      }
      EnableSMAP ();

      Status = gBS->LocateProtocol (
                      CoreProtocol,
                      (VOID *)CoreRbp->Argument2,
                      &Interface
                      );

      Interface = AllocateRing3CopyPages (Interface, MemoryCoreSize);
      if (Interface == NULL) {
        DEBUG ((DEBUG_ERROR, "Ring0: Failed to allocate pages for Ring3 PROTOCOL structure.\n"));
        return EFI_OUT_OF_RESOURCES;
      }

      DisableSMAP ();
      *(VOID **)CoreRbp->Argument3 = Interface;
      EnableSMAP ();

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
      if (CompareGuid ((EFI_GUID *)CoreRbp->Argument2, &gEfiLoadedImageProtocolGuid)) {
        CoreProtocol   = &gEfiLoadedImageProtocolGuid;
        MemoryCoreSize = sizeof (EFI_LOADED_IMAGE_PROTOCOL);
      } else {
        DEBUG ((DEBUG_ERROR, "Ring0: Unknown protocol.\n"));
        EnableSMAP ();
        return EFI_INVALID_PARAMETER;
      }

      Argument4    = (EFI_HANDLE)UserRsp->Arguments[4];
      Argument5    = (EFI_HANDLE)UserRsp->Arguments[5];
      Argument6    = (UINT32)UserRsp->Arguments[6];
      EnableSMAP ();

      Status = gBS->OpenProtocol (
                      (EFI_HANDLE)CoreRbp->Argument1,
                      CoreProtocol,
                      &Interface,
                      Argument4,
                      Argument5,
                      Argument6
                      );

      Interface = AllocateRing3CopyPages (Interface, MemoryCoreSize);
      if (Interface == NULL) {
        DEBUG ((DEBUG_ERROR, "Ring0: Failed to allocate pages for Ring3 PROTOCOL structure.\n"));
        return EFI_OUT_OF_RESOURCES;
      }

      DisableSMAP ();
      *(VOID **)CoreRbp->Argument3 = Interface;
      EnableSMAP ();

      return Status;

    case SysCallInstallMultipleProtocolInterfaces:
      //
      // Argument 1: EFI_HANDLE  *Handle
      // ...
      //
      DisableSMAP ();
      CoreHandle  = *(EFI_HANDLE *)CoreRbp->Argument1;
      UserArgList = (VOID **)CoreRbp->Argument2;

      for (Index = 0; UserArgList[Index] != NULL; ++Index) {
        if (CompareGuid ((EFI_GUID *)UserArgList[Index], &gEfiDriverBindingProtocolGuid)) {
          CoreArgList[Index] = (VOID *)&gEfiDriverBindingProtocolGuid;
          MemoryCoreSize = sizeof (EFI_DRIVER_BINDING_PROTOCOL);
          continue;
        } else if (CompareGuid ((EFI_GUID *)UserArgList[Index], &gEfiComponentNameProtocolGuid)) {
          CoreArgList[Index] = (VOID *)&gEfiComponentNameProtocolGuid;
          MemoryCoreSize = sizeof (EFI_COMPONENT_NAME_PROTOCOL);
          continue;
        } else if ((Index % 2) == 0) {
          DEBUG ((DEBUG_ERROR, "Ring0: Unknown protocol.\n"));
          EnableSMAP ();
          return EFI_INVALID_PARAMETER;
        }

        CoreArgList[Index] = AllocateCopyPool (MemoryCoreSize, (VOID *)UserArgList[Index]);
      }
      EnableSMAP ();

      ASSERT (Index < MAX_LIST);
      CoreArgList[Index] = NULL;

      for (Index = 0; CoreArgList[Index] != NULL; Index += 2) {
        if (CompareGuid ((EFI_GUID *)CoreArgList[Index], &gEfiDriverBindingProtocolGuid)) {
          CoreDriverBinding = (EFI_DRIVER_BINDING_PROTOCOL *)CoreArgList[Index + 1];

          mUserDriverBindingSupported = CoreDriverBinding->Supported;
          mUserDriverBindingStart     = CoreDriverBinding->Start;
          mUserDriverBindingStop      = CoreDriverBinding->Stop;

          CoreDriverBinding->Supported = CoreDriverBindingSupported;
          CoreDriverBinding->Start     = CoreDriverBindingStart;
          CoreDriverBinding->Stop      = CoreDriverBindingStop;
        }
      }

      Status = CallInstallMultipleProtocolInterfaces (
                 &CoreHandle,
                 CoreArgList,
                 Index + 1,
                 (VOID *)gBS->InstallMultipleProtocolInterfaces
                 );

      return Status;

    default:
      break;
  }

  return EFI_UNSUPPORTED;
}
