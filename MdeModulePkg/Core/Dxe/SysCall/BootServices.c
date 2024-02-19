/** @file

  Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause

**/

#include "DxeMain.h"
#include "SupportedProtocols.h"

EFI_STATUS
EFIAPI
CallInstallMultipleProtocolInterfaces (
  IN EFI_HANDLE  *Handle,
  IN VOID        **ArgList,
  IN UINT32      ArgListSize,
  IN VOID        *Function
  );

EFI_STATUS
EFIAPI
FindGuid (
  IN  EFI_GUID  *Ring3,
  OUT EFI_GUID  **Core,
  OUT UINT32    *CoreSize
  )
{
  ASSERT (Core != NULL);
  ASSERT (CoreSize != NULL);

  if (CompareGuid (Ring3, &gEfiDevicePathUtilitiesProtocolGuid)) {

    *Core     = &gEfiDevicePathUtilitiesProtocolGuid;
    *CoreSize = sizeof (EFI_DEVICE_PATH_UTILITIES_PROTOCOL);

  } else if (CompareGuid (Ring3, &gEfiLoadedImageProtocolGuid)) {

    *Core     = &gEfiLoadedImageProtocolGuid;
    *CoreSize = sizeof (EFI_LOADED_IMAGE_PROTOCOL);

  } else if (CompareGuid (Ring3, &gEfiBlockIoProtocolGuid)) {

    *Core     = &gEfiBlockIoProtocolGuid;
    *CoreSize = sizeof (EFI_BLOCK_IO_PROTOCOL);

  } else if (CompareGuid (Ring3, &gEfiDiskIoProtocolGuid)) {

    *Core     = &gEfiDiskIoProtocolGuid;
    *CoreSize = sizeof (EFI_DISK_IO_PROTOCOL);

  } else if (CompareGuid (Ring3, &gEfiDriverBindingProtocolGuid)) {

    *Core     = &gEfiDriverBindingProtocolGuid;
    *CoreSize = sizeof (EFI_DRIVER_BINDING_PROTOCOL);

  } else if (CompareGuid (Ring3, &gEfiComponentNameProtocolGuid)) {

    *Core     = &gEfiComponentNameProtocolGuid;
    *CoreSize = sizeof (EFI_COMPONENT_NAME_PROTOCOL);

  } else {
    DEBUG ((DEBUG_ERROR, "Ring0: Unknown protocol.\n"));
    return EFI_NOT_FOUND;
  }

  return EFI_SUCCESS;
}

VOID
EFIAPI
FixInterface (
  IN     EFI_GUID  *Guid,
  IN OUT VOID      *Interface
  )
{
  EFI_BLOCK_IO_PROTOCOL  *BlockIo;

  if (CompareGuid (Guid, &gEfiBlockIoProtocolGuid)) {
    BlockIo = (EFI_BLOCK_IO_PROTOCOL *)Interface;

    BlockIo->Media = AllocateRing3Copy (
                       BlockIo->Media,
                       sizeof (EFI_BLOCK_IO_MEDIA),
                       sizeof (EFI_BLOCK_IO_MEDIA)
                       );
  }
}

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
      Status = FindGuid ((EFI_GUID *)CoreRbp->Argument1, &CoreProtocol, &MemoryCoreSize);
      EnableSMAP ();
      if (EFI_ERROR (Status)) {
        return Status;
      }

      Status = gBS->LocateProtocol (
                      CoreProtocol,
                      (VOID *)CoreRbp->Argument2,
                      &Interface
                      );

      DisableSMAP ();
      Interface = AllocateRing3Copy (Interface, MemoryCoreSize, MemoryCoreSize);
      if (Interface == NULL) {
        EnableSMAP ();
        return EFI_OUT_OF_RESOURCES;
      }

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
      Status = FindGuid ((EFI_GUID *)CoreRbp->Argument2, &CoreProtocol, &MemoryCoreSize);
      if (EFI_ERROR (Status)) {
        EnableSMAP ();
        return Status;
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

      DisableSMAP ();
      Interface = AllocateRing3Copy (Interface, MemoryCoreSize, MemoryCoreSize);
      if (Interface == NULL) {
        EnableSMAP ();
        return EFI_OUT_OF_RESOURCES;
      }

      FixInterface (CoreProtocol, Interface);

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

      for (Index = 0; UserArgList[Index] != NULL; Index += 2) {
        Status = FindGuid ((EFI_GUID *)UserArgList[Index], (EFI_GUID **)&CoreArgList[Index], &MemoryCoreSize);
        if (EFI_ERROR (Status)) {
          EnableSMAP ();
          //TODO: Free CoreArgList.
          return Status;
        }

        CoreArgList[Index + 1] = AllocateCopyPool (MemoryCoreSize, (VOID *)UserArgList[Index + 1]);
      }
      EnableSMAP ();

      ASSERT (Index < MAX_LIST);
      CoreArgList[Index] = NULL;

      for (Index = 0; CoreArgList[Index] != NULL; Index += 2) {
        if (CompareGuid ((EFI_GUID *)CoreArgList[Index], &gEfiDriverBindingProtocolGuid)) {
          CoreDriverBinding = (EFI_DRIVER_BINDING_PROTOCOL *)CoreArgList[Index + 1];

          mRing3DriverBindingProtocol.Supported = CoreDriverBinding->Supported;
          mRing3DriverBindingProtocol.Start     = CoreDriverBinding->Start;
          mRing3DriverBindingProtocol.Stop      = CoreDriverBinding->Stop;

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

    case SysCallAllocatePool:
      //
      // Argument 1: EFI_MEMORY_TYPE  PoolType
      // Argument 2: UINTN            Size
      // Argument 3: VOID            **Buffer
      //
      DisableSMAP ();
      Status = gBS->AllocatePool (
                      EfiRing3MemoryType,
                      CoreRbp->Argument2,
                      (VOID **)CoreRbp->Argument3
                      );
      EnableSMAP ();

      return Status;

    case SysCallFreePool:
      //
      // Argument 1: IN VOID  *Buffer
      //
      DisableSMAP ();
      Status = gBS->FreePool (
                      (VOID *)CoreRbp->Argument1
                      );
      EnableSMAP ();

      return Status;
    default:
      break;
  }

  return EFI_UNSUPPORTED;
}
