/** @file

  Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause

**/

#include "DxeMain.h"
#include "SupportedProtocols.h"

LIST_ENTRY mProtocolsHead = INITIALIZE_LIST_HEAD_VARIABLE (mProtocolsHead);

typedef struct {
  VOID        *Core;
  VOID        *Ring3;
  LIST_ENTRY  Link;
} INTERFACE;

UINTN  mRing3InterfacePointer = 0;

EFI_STATUS
EFIAPI
CallInstallMultipleProtocolInterfaces (
  IN EFI_HANDLE  *Handle,
  IN VOID        **ArgList,
  IN UINT32      ArgListSize,
  IN VOID        *Function
  );

VOID
EFIAPI
FreeProtocolsList (
  VOID
  )
{
  LIST_ENTRY  *Link;
  INTERFACE   *Protocol;

  for (Link = mProtocolsHead.BackLink; Link != &mProtocolsHead; Link = mProtocolsHead.BackLink) {
    Protocol = BASE_CR (Link, INTERFACE, Link);
    RemoveEntryList (Link);
    FreePool (Protocol);
  }
}

STATIC
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

  } else if (CompareGuid (Ring3, &gEfiComponentName2ProtocolGuid)) {

    *Core     = &gEfiComponentName2ProtocolGuid;
    *CoreSize = sizeof (EFI_COMPONENT_NAME2_PROTOCOL);

  } else if (CompareGuid (Ring3, &gEfiDevicePathProtocolGuid)) {

    *Core     = &gEfiDevicePathProtocolGuid;
    *CoreSize = sizeof (EFI_DEVICE_PATH_PROTOCOL);

  } else if (CompareGuid (Ring3, &gEfiSimpleFileSystemProtocolGuid)) {

    *Core     = &gEfiSimpleFileSystemProtocolGuid;
    *CoreSize = sizeof (EFI_SIMPLE_FILE_SYSTEM_PROTOCOL);

  } else if (CompareGuid (Ring3, &gEfiUnicodeCollationProtocolGuid)) {

    *Core     = &gEfiUnicodeCollationProtocolGuid;
    *CoreSize = sizeof (EFI_UNICODE_COLLATION_PROTOCOL);

  } else if (CompareGuid (Ring3, &gEfiGlobalVariableGuid)) {

    *Core     = &gEfiGlobalVariableGuid;

  } else {
    DEBUG ((DEBUG_ERROR, "Ring0: Unknown protocol - %g.\n", Ring3));
    return EFI_NOT_FOUND;
  }

  return EFI_SUCCESS;
}

STATIC
VOID *
EFIAPI
FindInterface (
  IN BOOLEAN FindRing3,
  IN VOID    *Interface
  )
{
  LIST_ENTRY  *Link;
  INTERFACE   *Protocol;

  for (Link = mProtocolsHead.ForwardLink; Link != &mProtocolsHead; Link = Link->ForwardLink) {
    Protocol = BASE_CR (Link, INTERFACE, Link);

    if (FindRing3) {
      if (Protocol->Core == Interface) {
        return Protocol->Ring3;
      }
    } else {
      if (Protocol->Ring3 == Interface) {
        return Protocol->Core;
      }
    }
  }

  return NULL;
}

STATIC
VOID *
EFIAPI
PrepareRing3Interface (
  IN EFI_GUID  *Guid,
  IN VOID      *CoreInterface,
  IN UINT32    CoreSize
  )
{
  EFI_STATUS                     Status;
  UINTN                          Ring3Limit;
  VOID                           *Ring3Interface;
  EFI_BLOCK_IO_PROTOCOL          *BlockIo;
  EFI_UNICODE_COLLATION_PROTOCOL *Unicode;
  INTERFACE                      *Protocol;

  ASSERT (Guid != NULL);
  ASSERT (CoreInterface != NULL);

  if (mRing3InterfacePointer == 0) {
    mRing3InterfacePointer = (UINTN)gRing3Interfaces;
  }

  Ring3Interface = FindInterface (TRUE, CoreInterface);

  if (Ring3Interface != NULL) {
    return Ring3Interface;
  }

  Ring3Limit = (UINTN)gRing3Interfaces + EFI_PAGES_TO_SIZE (RING3_INTERFACES_PAGES);

  ASSERT ((mRing3InterfacePointer + CoreSize) <= Ring3Limit);

  Ring3Interface = (VOID *)mRing3InterfacePointer;

  CopyMem ((VOID *)mRing3InterfacePointer, CoreInterface, CoreSize);
  mRing3InterfacePointer += CoreSize;

  Protocol = AllocatePool (sizeof (INTERFACE));

  Protocol->Core  = CoreInterface;
  Protocol->Ring3 = Ring3Interface;

  InsertTailList (&mProtocolsHead, &Protocol->Link);

  if (CompareGuid (Guid, &gEfiBlockIoProtocolGuid)) {
    ASSERT ((mRing3InterfacePointer + sizeof (EFI_BLOCK_IO_MEDIA)) <= Ring3Limit);

    BlockIo = (EFI_BLOCK_IO_PROTOCOL *)Ring3Interface;

    CopyMem ((VOID *)mRing3InterfacePointer, (VOID *)BlockIo->Media, sizeof (EFI_BLOCK_IO_MEDIA));

    BlockIo->Media = (EFI_BLOCK_IO_MEDIA *)mRing3InterfacePointer;

    mRing3InterfacePointer += sizeof (EFI_BLOCK_IO_MEDIA);
  } else if (CompareGuid (Guid, &gEfiUnicodeCollationProtocolGuid)) {

    Unicode = (EFI_UNICODE_COLLATION_PROTOCOL *)Ring3Interface;

    ASSERT ((mRing3InterfacePointer + AsciiStrSize (Unicode->SupportedLanguages)) <= Ring3Limit);

    Status = AsciiStrCpyS (
               (CHAR8 *)mRing3InterfacePointer,
               AsciiStrSize (Unicode->SupportedLanguages),
               Unicode->SupportedLanguages
               );
    if (EFI_ERROR (Status)) {
      return NULL;
    }

    Unicode->SupportedLanguages = (CHAR8 *)mRing3InterfacePointer;

    mRing3InterfacePointer += AsciiStrSize (Unicode->SupportedLanguages);
  }

  return Ring3Interface;
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
//  rcx - User Rip for SYSCALL
//  r11 - User RFLAGS for SYSCALL
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
  EFI_STATUS StatusBS;
  UINT64     Attributes;
  VOID       *Interface;
  EFI_GUID   *CoreProtocol;
  UINT32     MemoryCoreSize;
  UINTN      Argument4;
  UINTN      Argument5;
  UINTN      Argument6;
  UINT32     Index;
  VOID       **UserArgList;
  VOID       *CoreArgList[MAX_LIST];
  EFI_HANDLE CoreHandle;
  VOID       *Ring3Pages;
  UINT32     PagesNumber;

  EFI_DRIVER_BINDING_PROTOCOL      *CoreDriverBinding;
  EFI_SIMPLE_FILE_SYSTEM_PROTOCOL  *CoreSimpleFileSystem;

  EFI_BLOCK_IO_PROTOCOL          *BlockIo;
  EFI_DISK_IO_PROTOCOL           *DiskIo;
  EFI_UNICODE_COLLATION_PROTOCOL *Unicode;

  Argument4 = 0;
  Argument5 = 0;
  Argument6 = 0;
  //
  // Check User variables.
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
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)CoreRbp->Argument1, &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(CoreRbp->Argument1 + sizeof (EFI_GUID) - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)CoreRbp->Argument3, &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(CoreRbp->Argument3 + sizeof (VOID *) - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

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
      if (Interface != NULL) {
        Interface = PrepareRing3Interface (CoreProtocol, Interface, MemoryCoreSize);
      }

      *(VOID **)CoreRbp->Argument3 = Interface;
      EnableSMAP ();

      return Status;

    case SysCallOpenProtocol:
      //
      // Argument 1: EFI_HANDLE  CoreUserHandle
      // Argument 2: EFI_GUID    *Protocol
      // Argument 3: VOID        **Interface  OPTIONAL
      // Argument 4: EFI_HANDLE  CoreImageHandle
      // Argument 5: EFI_HANDLE  CoreControllerHandle
      // Argument 6: UINT32      Attributes
      //
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)CoreRbp->Argument2, &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(CoreRbp->Argument2 + sizeof (EFI_GUID) - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      if ((VOID **)CoreRbp->Argument3 != NULL) {
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)CoreRbp->Argument3, &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(CoreRbp->Argument3 + sizeof (VOID *) - 1), &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      }
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)((UINTN)UserRsp + 8 * sizeof (UINTN) - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

      DisableSMAP ();
      Status = FindGuid ((EFI_GUID *)CoreRbp->Argument2, &CoreProtocol, &MemoryCoreSize);
      if (EFI_ERROR (Status)) {
        EnableSMAP ();
        return Status;
      }

      Argument4 = UserRsp->Arguments[4];
      Argument5 = UserRsp->Arguments[5];
      Argument6 = UserRsp->Arguments[6];
      EnableSMAP ();

      Status = gBS->OpenProtocol (
                      (EFI_HANDLE)CoreRbp->Argument1,
                      CoreProtocol,
                      ((VOID **)CoreRbp->Argument3 != NULL) ? &Interface : NULL,
                      (EFI_HANDLE)Argument4,
                      (EFI_HANDLE)Argument5,
                      (UINT32)Argument6
                      );

      if ((VOID **)CoreRbp->Argument3 != NULL) {
        DisableSMAP ();
        if (Interface != NULL) {
          Interface = PrepareRing3Interface (CoreProtocol, Interface, MemoryCoreSize);
        }

        *(VOID **)CoreRbp->Argument3 = Interface;
        EnableSMAP ();
      }

      return Status;

    case SysCallInstallMultipleProtocolInterfaces:
      //
      // Argument 1: EFI_HANDLE  *Handle
      // ...
      //
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)CoreRbp->Argument1, &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(CoreRbp->Argument1 + sizeof (EFI_HANDLE *) - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)CoreRbp->Argument2, &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(CoreRbp->Argument2 + sizeof (VOID **) - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

      DisableSMAP ();
      CoreHandle  = *(EFI_HANDLE *)CoreRbp->Argument1;
      UserArgList = (VOID **)CoreRbp->Argument2;

      for (Index = 0; UserArgList[Index] != NULL; Index += 2) {
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)((UINTN)&UserArgList[Index + 2] - 1), &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)UserArgList[Index], &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)((UINTN)UserArgList[Index] + sizeof (EFI_GUID) - 1), &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

        Status = FindGuid ((EFI_GUID *)UserArgList[Index], (EFI_GUID **)&CoreArgList[Index], &MemoryCoreSize);
        if (EFI_ERROR (Status)) {
          EnableSMAP ();

          while (Index > 0) {
            FreePool (CoreArgList[Index - 1]);
            Index -= 2;
          }

          return Status;
        }

        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)UserArgList[Index + 1], &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)((UINTN)UserArgList[Index + 1] + MemoryCoreSize - 1), &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

        CoreArgList[Index + 1] = AllocateCopyPool (MemoryCoreSize, (VOID *)UserArgList[Index + 1]);

        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)((UINTN)&UserArgList[Index + 2] + sizeof (VOID *) - 1), &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
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
        } else if (CompareGuid ((EFI_GUID *)CoreArgList[Index], &gEfiSimpleFileSystemProtocolGuid)) {
          CoreSimpleFileSystem = (EFI_SIMPLE_FILE_SYSTEM_PROTOCOL *)CoreArgList[Index + 1];

          mRing3SimpleFileSystemProtocol.OpenVolume = CoreSimpleFileSystem->OpenVolume;

          CoreSimpleFileSystem->OpenVolume = CoreOpenVolume;

          DisableSMAP ();
          mRing3SimpleFileSystemPointer = (EFI_SIMPLE_FILE_SYSTEM_PROTOCOL *)UserArgList[Index + 1];
          EnableSMAP ();
        }
      }

      Status = CallInstallMultipleProtocolInterfaces (
                 &CoreHandle,
                 CoreArgList,
                 Index + 1,
                 (VOID *)gBS->InstallMultipleProtocolInterfaces
                 );

      return Status;

    case SysCallCloseProtocol:
      //
      // Argument 1: EFI_HANDLE  CoreUserHandle
      // Argument 2: EFI_GUID    *Protocol
      // Argument 3: EFI_HANDLE  CoreAgentHandle
      // Argument 4: EFI_HANDLE  CoreControllerHandle
      //
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)CoreRbp->Argument2, &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(CoreRbp->Argument2 + sizeof (EFI_GUID) - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)((UINTN)UserRsp + 6 * sizeof (UINTN) - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

      DisableSMAP ();
      Status = FindGuid ((EFI_GUID *)CoreRbp->Argument2, &CoreProtocol, &MemoryCoreSize);
      if (EFI_ERROR (Status)) {
        EnableSMAP ();
        return Status;
      }

      Argument4 = UserRsp->Arguments[4];
      EnableSMAP ();

      Status = gBS->CloseProtocol (
                      (EFI_HANDLE)CoreRbp->Argument1,
                      CoreProtocol,
                      (EFI_HANDLE)CoreRbp->Argument3,
                      (EFI_HANDLE)Argument4
                      );

      return Status;

    case SysCallHandleProtocol:
      //
      // Argument 1: EFI_HANDLE  CoreUserHandle
      // Argument 2: EFI_GUID    *Protocol
      // Argument 3: VOID        **Interface
      //
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)CoreRbp->Argument2, &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(CoreRbp->Argument2 + sizeof (EFI_GUID) - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)CoreRbp->Argument3, &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(CoreRbp->Argument3 + sizeof (VOID *) - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

      DisableSMAP ();
      Status = FindGuid ((EFI_GUID *)CoreRbp->Argument2, &CoreProtocol, &MemoryCoreSize);
      EnableSMAP ();
      if (EFI_ERROR (Status)) {
        return Status;
      }

      Status = gBS->HandleProtocol (
                      (EFI_HANDLE)CoreRbp->Argument1,
                      CoreProtocol,
                      &Interface
                      );

      DisableSMAP ();
      if (Interface != NULL) {
        Interface = PrepareRing3Interface (CoreProtocol, Interface, MemoryCoreSize);
      }

      *(VOID **)CoreRbp->Argument3 = Interface;
      EnableSMAP ();

      return Status;

    case SysCallAllocatePages:
      //
      // Argument 1: EFI_ALLOCATE_TYPE     Type
      // Argument 2: EFI_MEMORY_TYPE       MemoryType
      // Argument 3: UINTN                 NumberOfPages
      // Argument 4: EFI_PHYSICAL_ADDRESS  *Memory
      //
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)((UINTN)UserRsp + 6 * sizeof (UINTN) - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

      Status = gBS->AllocatePages (
                      (EFI_ALLOCATE_TYPE)CoreRbp->Argument1,
                      (EFI_MEMORY_TYPE)CoreRbp->Argument2,
                      CoreRbp->Argument3,
                      (EFI_PHYSICAL_ADDRESS *)&Argument4
                      );

      DisableSMAP ();
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)UserRsp->Arguments[4], &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)((UINTN)UserRsp->Arguments[4] + sizeof (EFI_PHYSICAL_ADDRESS) - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

      *(EFI_PHYSICAL_ADDRESS *)UserRsp->Arguments[4] = (EFI_PHYSICAL_ADDRESS)Argument4;
      EnableSMAP ();

      return Status;

    case SysCallFreePages:
      //
      // Argument 1: EFI_PHYSICAL_ADDRESS  Memory
      // Argument 2: UINTN                 NumberOfPages
      //
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)CoreRbp->Argument1, &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(CoreRbp->Argument1 + CoreRbp->Argument2 * EFI_PAGE_SIZE - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

      return gBS->FreePages (
                    (EFI_PHYSICAL_ADDRESS)CoreRbp->Argument1,
                    CoreRbp->Argument2
                    );

    case SysCallRaiseTpl:
      //
      // Argument 1: EFI_TPL  NewTpl
      //
      return (EFI_STATUS)gBS->RaiseTPL (
                                (EFI_TPL)CoreRbp->Argument1
                                );

    case SysCallRestoreTpl:
      //
      // Argument 1: EFI_TPL  NewTpl
      //
      gBS->RestoreTPL ((EFI_TPL)CoreRbp->Argument1);

      return EFI_SUCCESS;

    case SysCallLocateHandleBuffer:
      //
      // Argument 1: EFI_LOCATE_SEARCH_TYPE  SearchType
      // Argument 2: EFI_GUID                *Protocol  OPTIONAL
      // Argument 3: VOID                    *SearchKey OPTIONAL
      // Argument 4: UINTN                   *NumberHandles
      // Argument 5: EFI_HANDLE              **Buffer
      //
      if ((EFI_GUID *)CoreRbp->Argument2 != NULL) {
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)CoreRbp->Argument2, &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(CoreRbp->Argument2 + sizeof (EFI_GUID) - 1), &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

        DisableSMAP ();
        Status = FindGuid ((EFI_GUID *)CoreRbp->Argument2, &CoreProtocol, &MemoryCoreSize);
        EnableSMAP ();
        if (EFI_ERROR (Status)) {
          return Status;
        }
      }

      StatusBS = gBS->LocateHandleBuffer (
                        (EFI_LOCATE_SEARCH_TYPE)CoreRbp->Argument1,
                        CoreProtocol,
                        (VOID *)CoreRbp->Argument3,
                        &Argument4,
                        (EFI_HANDLE **)&Argument5
                        );

      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)((UINTN)UserRsp + 7 * sizeof (UINTN) - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

      DisableSMAP ();
      if ((UINTN *)UserRsp->Arguments[4] != NULL) {
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)UserRsp->Arguments[4], &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(UserRsp->Arguments[4] + sizeof (UINTN) - 1), &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

        *(UINTN *)UserRsp->Arguments[4] = Argument4;
      }

      if ((EFI_HANDLE **)UserRsp->Arguments[5] != NULL) {
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)UserRsp->Arguments[5], &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(UserRsp->Arguments[5] + sizeof (EFI_HANDLE *) - 1), &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

        PagesNumber = EFI_SIZE_TO_PAGES (Argument4 * sizeof (EFI_HANDLE *));

        Status = CoreAllocatePages (
                   AllocateAnyPages,
                   EfiRing3MemoryType,
                   PagesNumber,
                   (EFI_PHYSICAL_ADDRESS *)&Ring3Pages
                   );
        if (EFI_ERROR (Status)) {
          return Status;
        }

        CopyMem (Ring3Pages, (VOID *)Argument5, Argument4 * sizeof (EFI_HANDLE *));

        FreePool ((VOID *)Argument5);

        *(EFI_HANDLE **)UserRsp->Arguments[5] = (EFI_HANDLE *)Ring3Pages;
      }
      EnableSMAP ();

      return StatusBS;

    case SysCallCalculateCrc32:
      //
      // Argument 1: VOID    *Data
      // Argument 2: UINTN   DataSize
      // Argument 3: UINT32  *Crc32
      //
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)CoreRbp->Argument1, &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(CoreRbp->Argument1 + CoreRbp->Argument2 - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)CoreRbp->Argument3, &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(CoreRbp->Argument3 + sizeof (UINT32 *) - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

      Argument4 = (UINTN)AllocatePool (CoreRbp->Argument2);
      if ((VOID *)Argument4 == NULL) {
        return EFI_OUT_OF_RESOURCES;
      }

      DisableSMAP ();
      CopyMem ((VOID *)Argument4, (VOID *)CoreRbp->Argument1, CoreRbp->Argument2);
      EnableSMAP ();

      Status = gBS->CalculateCrc32 (
                      (VOID *)Argument4,
                      CoreRbp->Argument2,
                      (UINT32 *)&Argument5
                      );

      DisableSMAP ();
      *(UINT32 *)CoreRbp->Argument3 = (UINT32)Argument5;
      EnableSMAP ();

      return Status;

    case SysCallGetVariable:
      //
      // Argument 1: CHAR16    *VariableName
      // Argument 2: EFI_GUID  *VendorGuid
      // Argument 3: UINT32    *Attributes     OPTIONAL
      // Argument 4: UINTN     *DataSize
      // Argument 5: VOID      *Data           OPTIONAL
      //
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)CoreRbp->Argument1, &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)CoreRbp->Argument2, &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(CoreRbp->Argument2 + sizeof (EFI_GUID) - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      if ((UINT32 *)CoreRbp->Argument3 != NULL) {
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)CoreRbp->Argument3, &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(CoreRbp->Argument3 + sizeof (UINT32) - 1), &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      }
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)((UINTN)UserRsp + 7 * sizeof (UINTN) - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

      DisableSMAP ();
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(CoreRbp->Argument1 + StrSize ((CHAR16 *)CoreRbp->Argument1) - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

      Argument6 = (UINTN)AllocateCopyPool (StrSize ((CHAR16 *)CoreRbp->Argument1), (CHAR16 *)CoreRbp->Argument1);
      if ((VOID *)Argument6 == NULL) {
        EnableSMAP ();
        return EFI_OUT_OF_RESOURCES;
      }

      Status = FindGuid ((EFI_GUID *)CoreRbp->Argument2, &CoreProtocol, &MemoryCoreSize);
      if (EFI_ERROR (Status)) {
        EnableSMAP ();
        FreePool ((VOID *)Argument6);
        return Status;
      }

      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)UserRsp->Arguments[4], &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(UserRsp->Arguments[4] + sizeof (UINTN) - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

      Argument4 = *(UINTN *)UserRsp->Arguments[4];

      if ((VOID *)UserRsp->Arguments[5] != NULL) {
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)UserRsp->Arguments[5], &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(UserRsp->Arguments[5] + Argument4 - 1), &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

        Argument5 = (UINTN)AllocatePool (Argument4);
        if ((VOID *)Argument5 == NULL) {
          EnableSMAP ();
          FreePool ((VOID *)Argument6);
          return EFI_OUT_OF_RESOURCES;
        }
      }
      EnableSMAP ();

      Status = gRT->GetVariable (
                      (CHAR16 *)Argument6,
                      CoreProtocol,
                      (UINT32 *)&Attributes,
                      &Argument4,
                      (VOID *)Argument5
                      );

      DisableSMAP ();
      if ((VOID *)UserRsp->Arguments[5] != NULL) {
        CopyMem ((VOID *)UserRsp->Arguments[5], (VOID *)Argument5, Argument4);
      }

      *(UINTN *)UserRsp->Arguments[4] = Argument4;

      if ((UINT32 *)CoreRbp->Argument3 != NULL) {
        *(UINT32 *)CoreRbp->Argument3 = (UINT32)Attributes;
      }
      EnableSMAP ();

      FreePool ((VOID *)Argument6);

      if ((VOID *)Argument5 != NULL) {
        FreePool ((VOID *)Argument5);
      }

      return Status;

    case SysCallBlockIoReset:
      //
      // Argument 1: EFI_BLOCK_IO_PROTOCOL  *This
      // Argument 2: BOOLEAN                ExtendedVerification
      //
      BlockIo = FindInterface (FALSE, (VOID *)CoreRbp->Argument1);

      if (BlockIo == NULL) {
        return EFI_NOT_FOUND;
      }

      return BlockIo->Reset (
                        BlockIo,
                        (BOOLEAN)CoreRbp->Argument2
                        );

    case SysCallBlockIoRead:
      //
      // Argument 1: EFI_BLOCK_IO_PROTOCOL *This
      // Argument 2: UINT32                MediaId
      // Argument 3: EFI_LBA               Lba
      // Argument 4: UINTN                 BufferSize
      // Argument 5: VOID                 *Buffer
      //
      BlockIo = FindInterface (FALSE, (VOID *)CoreRbp->Argument1);

      if (BlockIo == NULL) {
        return EFI_NOT_FOUND;
      }

      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)((UINTN)UserRsp + 7 * sizeof (UINTN) - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

      DisableSMAP ();
      Argument4 = UserRsp->Arguments[4];
      EnableSMAP ();

      Argument5 = (UINTN)AllocatePool (Argument4);
      if ((VOID *)Argument5 == NULL) {
        return EFI_OUT_OF_RESOURCES;
      }

      Status = BlockIo->ReadBlocks (
                          BlockIo,
                          (UINT32)CoreRbp->Argument2,
                          (EFI_LBA)CoreRbp->Argument3,
                          Argument4,
                          (VOID *)Argument5
                          );
      DisableSMAP ();
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)UserRsp->Arguments[5], &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)((UINTN)UserRsp->Arguments[5] + Argument4 - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

      CopyMem ((VOID *)UserRsp->Arguments[5], (VOID *)Argument5, Argument4);
      EnableSMAP ();

      FreePool ((VOID *)Argument5);

      return Status;

    case SysCallBlockIoWrite:
      //
      // Argument 1: EFI_BLOCK_IO_PROTOCOL *This
      // Argument 2: UINT32                MediaId
      // Argument 3: EFI_LBA               Lba
      // Argument 4: UINTN                 BufferSize
      // Argument 5: VOID                 *Buffer
      //
      BlockIo = FindInterface (FALSE, (VOID *)CoreRbp->Argument1);

      if (BlockIo == NULL) {
        return EFI_NOT_FOUND;
      }

      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)((UINTN)UserRsp + 7 * sizeof (UINTN) - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

      DisableSMAP ();
      Argument4 = UserRsp->Arguments[4];
      EnableSMAP ();

      Argument5 = (UINTN)AllocatePool (Argument4);
      if ((VOID *)Argument5 == NULL) {
        return EFI_OUT_OF_RESOURCES;
      }

      DisableSMAP ();
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)UserRsp->Arguments[5], &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)((UINTN)UserRsp->Arguments[5] + Argument4 - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

      CopyMem ((VOID *)Argument5,(VOID *)UserRsp->Arguments[5], Argument4);
      EnableSMAP ();

      Status = BlockIo->WriteBlocks (
                          BlockIo,
                          (UINT32)CoreRbp->Argument2,
                          (EFI_LBA)CoreRbp->Argument3,
                          Argument4,
                          (VOID *)Argument5
                          );

      FreePool ((VOID *)Argument5);

      return Status;

    case SysCallBlockIoFlush:
      //
      // Argument 1: EFI_BLOCK_IO_PROTOCOL  *This
      //
      BlockIo = FindInterface (FALSE, (VOID *)CoreRbp->Argument1);

      if (BlockIo == NULL) {
        return EFI_NOT_FOUND;
      }

      return BlockIo->FlushBlocks (BlockIo);

    case SysCallDiskIoRead:
      //
      // Argument 1: EFI_DISK_IO_PROTOCOL  *This
      // Argument 2: UINT32                MediaId
      // Argument 3: UINT64                Offset
      // Argument 4: UINTN                 BufferSize
      // Argument 5: VOID                 *Buffer
      //
      DiskIo = FindInterface (FALSE, (VOID *)CoreRbp->Argument1);

      if (DiskIo == NULL) {
        return EFI_NOT_FOUND;
      }

      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)((UINTN)UserRsp + 7 * sizeof (UINTN) - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

      DisableSMAP ();
      Argument4 = UserRsp->Arguments[4];
      EnableSMAP ();

      Argument5 = (UINTN)AllocatePool (Argument4);
      if ((VOID *)Argument5 == NULL) {
        return EFI_OUT_OF_RESOURCES;
      }

      Status = DiskIo->ReadDisk (
                         DiskIo,
                         (UINT32)CoreRbp->Argument2,
                         (UINT64)CoreRbp->Argument3,
                         Argument4,
                         (VOID *)Argument5
                         );
      DisableSMAP ();
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)UserRsp->Arguments[5], &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)((UINTN)UserRsp->Arguments[5] + Argument4 - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

      CopyMem ((VOID *)UserRsp->Arguments[5], (VOID *)Argument5, Argument4);
      EnableSMAP ();

      FreePool ((VOID *)Argument5);

      return Status;

    case SysCallDiskIoWrite:
      //
      // Argument 1: EFI_DISK_IO_PROTOCOL  *This
      // Argument 2: UINT32                MediaId
      // Argument 3: UINT64                Offset
      // Argument 4: UINTN                 BufferSize
      // Argument 5: VOID                 *Buffer
      //
      DiskIo = FindInterface (FALSE, (VOID *)CoreRbp->Argument1);

      if (DiskIo == NULL) {
        return EFI_NOT_FOUND;
      }

      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)((UINTN)UserRsp + 7 * sizeof (UINTN) - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

      DisableSMAP ();
      Argument4 = UserRsp->Arguments[4];
      EnableSMAP ();

      Argument5 = (UINTN)AllocatePool (Argument4);
      if ((VOID *)Argument5 == NULL) {
        return EFI_OUT_OF_RESOURCES;
      }

      DisableSMAP ();
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)UserRsp->Arguments[5], &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)((UINTN)UserRsp->Arguments[5] + Argument4 - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

      CopyMem ((VOID *)Argument5, (VOID *)UserRsp->Arguments[5], Argument4);
      EnableSMAP ();

      Status = DiskIo->WriteDisk (
                         DiskIo,
                         (UINT32)CoreRbp->Argument2,
                         (UINT64)CoreRbp->Argument3,
                         Argument4,
                         (VOID *)Argument5
                         );

      FreePool ((VOID *)Argument5);

      return Status;

    case SysCallUnicodeStriColl:
      //
      // Argument 1: EFI_UNICODE_COLLATION_PROTOCOL  *This
      // Argument 2: CHAR16                          *Str1
      // Argument 3: CHAR16                          *Str2
      //
      Unicode = FindInterface (FALSE, (VOID *)CoreRbp->Argument1);

      if (Unicode == NULL) {
        return EFI_NOT_FOUND;
      }

      if ((CHAR16 *)CoreRbp->Argument2 != NULL) {
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)CoreRbp->Argument2, &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

        DisableSMAP ();
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(CoreRbp->Argument2 + StrSize ((CHAR16 *)CoreRbp->Argument2) - 1), &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

        Argument4 = (UINTN)AllocateCopyPool (StrSize ((CHAR16 *)CoreRbp->Argument2), (CHAR16 *)CoreRbp->Argument2);
        EnableSMAP ();
        if ((VOID *)Argument4 == NULL) {
          return EFI_OUT_OF_RESOURCES;
        }
      }

      if ((CHAR16 *)CoreRbp->Argument3 != NULL) {
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)CoreRbp->Argument3, &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

        DisableSMAP ();
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(CoreRbp->Argument3 + StrSize ((CHAR16 *)CoreRbp->Argument3) - 1), &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

        Argument5 = (UINTN)AllocateCopyPool (StrSize ((CHAR16 *)CoreRbp->Argument3), (CHAR16 *)CoreRbp->Argument3);
        EnableSMAP ();
        if ((VOID *)Argument5 == NULL) {
          if ((VOID *)Argument4 != NULL) {
            FreePool ((VOID *)Argument4);
          }

          return EFI_OUT_OF_RESOURCES;
        }
      }

      Status = (EFI_STATUS)Unicode->StriColl (
                                      Unicode,
                                      (CHAR16 *)Argument4,
                                      (CHAR16 *)Argument5
                                      );

      if ((VOID *)Argument4 != NULL) {
        FreePool ((VOID *)Argument4);
      }

      if ((VOID *)Argument5 != NULL) {
        FreePool ((VOID *)Argument5);
      }

      return Status;

    case SysCallUnicodeMetaiMatch:
      //
      // Argument 1: EFI_UNICODE_COLLATION_PROTOCOL  *This
      // Argument 2: CHAR16                          *String
      // Argument 3: CHAR16                          *Pattern
      //
      Unicode = FindInterface (FALSE, (VOID *)CoreRbp->Argument1);

      if (Unicode == NULL) {
        return EFI_NOT_FOUND;
      }

      if ((CHAR16 *)CoreRbp->Argument2 != NULL) {
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)CoreRbp->Argument2, &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

        DisableSMAP ();
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(CoreRbp->Argument2 + StrSize ((CHAR16 *)CoreRbp->Argument2) - 1), &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

        Argument4 = (UINTN)AllocateCopyPool (StrSize ((CHAR16 *)CoreRbp->Argument2), (CHAR16 *)CoreRbp->Argument2);
        EnableSMAP ();
        if ((VOID *)Argument4 == NULL) {
          return EFI_OUT_OF_RESOURCES;
        }
      }

      if ((CHAR16 *)CoreRbp->Argument3 != NULL) {
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)CoreRbp->Argument3, &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

        DisableSMAP ();
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(CoreRbp->Argument3 + StrSize ((CHAR16 *)CoreRbp->Argument3) - 1), &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

        Argument5 = (UINTN)AllocateCopyPool (StrSize ((CHAR16 *)CoreRbp->Argument3), (CHAR16 *)CoreRbp->Argument3);
        EnableSMAP ();
        if ((VOID *)Argument5 == NULL) {
          if ((VOID *)Argument4 != NULL) {
            FreePool ((VOID *)Argument4);
          }

          return EFI_OUT_OF_RESOURCES;
        }
      }

      Status = (EFI_STATUS)Unicode->MetaiMatch (
                                      Unicode,
                                      (CHAR16 *)Argument4,
                                      (CHAR16 *)Argument5
                                      );

      if ((VOID *)Argument4 != NULL) {
        FreePool ((VOID *)Argument4);
      }

      if ((VOID *)Argument5 != NULL) {
        FreePool ((VOID *)Argument5);
      }

      return Status;

    case SysCallUnicodeStrLwr:
      //
      // Argument 1: EFI_UNICODE_COLLATION_PROTOCOL  *This
      // Argument 2: CHAR16                          *Str
      //
      Unicode = FindInterface (FALSE, (VOID *)CoreRbp->Argument1);

      if (Unicode == NULL) {
        return EFI_NOT_FOUND;
      }

      if ((CHAR16 *)CoreRbp->Argument2 != NULL) {
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)CoreRbp->Argument2, &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

        DisableSMAP ();
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(CoreRbp->Argument2 + StrSize ((CHAR16 *)CoreRbp->Argument2) - 1), &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

        Argument4 = (UINTN)AllocateCopyPool (StrSize ((CHAR16 *)CoreRbp->Argument2), (CHAR16 *)CoreRbp->Argument2);
        EnableSMAP ();
        if ((VOID *)Argument4 == NULL) {
          return EFI_OUT_OF_RESOURCES;
        }
      }

      Unicode->StrLwr (
                 Unicode,
                 (CHAR16 *)Argument4
                 );

      if ((VOID *)Argument4 != NULL) {
        DisableSMAP ();
        Status = StrCpyS ((CHAR16 *)CoreRbp->Argument2, StrLen ((CHAR16 *)CoreRbp->Argument2) + 1, (CHAR16 *)Argument4);
        EnableSMAP ();

        FreePool ((VOID *)Argument4);
      }

      return Status;

    case SysCallUnicodeStrUpr:
      //
      // Argument 1: EFI_UNICODE_COLLATION_PROTOCOL  *This
      // Argument 2: CHAR16                          *Str
      //
      Unicode = FindInterface (FALSE, (VOID *)CoreRbp->Argument1);

      if (Unicode == NULL) {
        return EFI_NOT_FOUND;
      }

      if ((CHAR16 *)CoreRbp->Argument2 != NULL) {
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)CoreRbp->Argument2, &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

        DisableSMAP ();
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(CoreRbp->Argument2 + StrSize ((CHAR16 *)CoreRbp->Argument2) - 1), &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

        Argument4 = (UINTN)AllocateCopyPool (StrSize ((CHAR16 *)CoreRbp->Argument2), (CHAR16 *)CoreRbp->Argument2);
        EnableSMAP ();
        if ((VOID *)Argument4 == NULL) {
          return EFI_OUT_OF_RESOURCES;
        }
      }

      Unicode->StrUpr (
                 Unicode,
                 (CHAR16 *)Argument4
                 );

      if ((VOID *)Argument4 != NULL) {
        DisableSMAP ();
        Status = StrCpyS ((CHAR16 *)CoreRbp->Argument2, StrLen ((CHAR16 *)CoreRbp->Argument2) + 1, (CHAR16 *)Argument4);
        EnableSMAP ();

        FreePool ((VOID *)Argument4);
      }

      return Status;

    case SysCallUnicodeFatToStr:
      //
      // Argument 1: EFI_UNICODE_COLLATION_PROTOCOL  *This
      // Argument 2: UINTN                           FatSize
      // Argument 3: CHAR8                           *Fat
      // Argument 4: CHAR16                          *String
      //
      Unicode = FindInterface (FALSE, (VOID *)CoreRbp->Argument1);

      if (Unicode == NULL) {
        return EFI_NOT_FOUND;
      }

      if ((CHAR8 *)CoreRbp->Argument3 != NULL) {
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)CoreRbp->Argument3, &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(CoreRbp->Argument3 + CoreRbp->Argument2 - 1), &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

        DisableSMAP ();
        Argument4 = (UINTN)AllocateCopyPool (CoreRbp->Argument2, (CHAR8 *)CoreRbp->Argument3);
        EnableSMAP ();
        if ((VOID *)Argument4 == NULL) {
          return EFI_OUT_OF_RESOURCES;
        }
      }

      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)((UINTN)UserRsp + 6 * sizeof (UINTN) - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

      DisableSMAP ();
      if ((CHAR16 *)UserRsp->Arguments[4] != NULL) {
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)UserRsp->Arguments[4], &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(UserRsp->Arguments[4] + 2 * (CoreRbp->Argument2 + 1) - 1), &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

        Argument5 = (UINTN)AllocatePool (2 * (CoreRbp->Argument2 + 1));
        if ((VOID *)Argument5 == NULL) {
          if ((VOID *)Argument4 != NULL) {
            FreePool ((VOID *)Argument4);
          }

          return EFI_OUT_OF_RESOURCES;
        }
      }
      EnableSMAP ();

      Unicode->FatToStr (
                 Unicode,
                 CoreRbp->Argument2,
                 (CHAR8 *)Argument4,
                 (CHAR16 *)Argument5
                 );

      if ((VOID *)Argument4 != NULL) {
        FreePool ((VOID *)Argument4);
      }

      if ((VOID *)Argument5 != NULL) {
        DisableSMAP ();
        CopyMem ((VOID *)UserRsp->Arguments[4], (VOID *)Argument5, 2 * (CoreRbp->Argument2 + 1));
        EnableSMAP ();

        FreePool ((VOID *)Argument5);
      }

      return EFI_SUCCESS;

    case SysCallUnicodeStrToFat:
      //
      // Argument 1: EFI_UNICODE_COLLATION_PROTOCOL  *This
      // Argument 2: CHAR16                          *String
      // Argument 3: UINTN                           FatSize
      // Argument 4: CHAR8                           *Fat
      //
      Unicode = FindInterface (FALSE, (VOID *)CoreRbp->Argument1);

      if (Unicode == NULL) {
        return EFI_NOT_FOUND;
      }

      if ((CHAR16 *)CoreRbp->Argument2 != NULL) {
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)CoreRbp->Argument2, &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

        DisableSMAP ();
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(CoreRbp->Argument2 + StrSize ((CHAR16 *)CoreRbp->Argument2) - 1), &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

        Argument4 = (UINTN)AllocateCopyPool (StrSize ((CHAR16 *)CoreRbp->Argument2), (CHAR16 *)CoreRbp->Argument2);
        EnableSMAP ();
        if ((VOID *)Argument4 == NULL) {
          return EFI_OUT_OF_RESOURCES;
        }
      }

      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)((UINTN)UserRsp + 6 * sizeof (UINTN) - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

      DisableSMAP ();
      if ((CHAR8 *)UserRsp->Arguments[4] != NULL) {
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)UserRsp->Arguments[4], &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(UserRsp->Arguments[4] + CoreRbp->Argument3 - 1), &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

        Argument5 = (UINTN)AllocatePool (CoreRbp->Argument3);
        if ((VOID *)Argument5 == NULL) {
          if ((VOID *)Argument4 != NULL) {
            FreePool ((VOID *)Argument4);
          }

          return EFI_OUT_OF_RESOURCES;
        }
      }
      EnableSMAP ();

      Unicode->StrToFat (
                 Unicode,
                 (CHAR16 *)Argument4,
                 CoreRbp->Argument3,
                 (CHAR8 *)Argument5
                 );

      if ((VOID *)Argument4 != NULL) {
        FreePool ((VOID *)Argument4);
      }

      if ((VOID *)Argument5 != NULL) {
        DisableSMAP ();
        CopyMem ((VOID *)UserRsp->Arguments[4], (VOID *)Argument5, CoreRbp->Argument3);
        EnableSMAP ();

        FreePool ((VOID *)Argument5);
      }

      return EFI_SUCCESS;

    default:
      DEBUG ((DEBUG_ERROR, "Ring0: Unknown syscall type.\n"));
      break;
  }

  return EFI_UNSUPPORTED;
}
