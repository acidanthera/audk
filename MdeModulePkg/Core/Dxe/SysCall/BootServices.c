/** @file

  Copyright (c) 2024 - 2025, Mikhail Krichanov. All rights reserved.
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

CHAR8 *SysCallNames[] = {
  //
  // BootServices
  //
  "SysCallReturnToCore",
  "SysCallLocateProtocol",
  "SysCallOpenProtocol",
  "SysCallInstallMultipleProtocolInterfaces",
  "SysCallCloseProtocol",
  "SysCallHandleProtocol",
  "SysCallAllocatePages",
  "SysCallFreePages",
  "SysCallRaiseTpl",
  "SysCallRestoreTpl",
  "SysCallLocateHandleBuffer",
  "SysCallCalculateCrc32",
  //
  // RuntimeServices
  //
  "SysCallGetVariable",
  //
  // Protocols
  //
  "SysCallBlockIoReset",
  "SysCallBlockIoRead",
  "SysCallBlockIoWrite",
  "SysCallBlockIoFlush",
  "SysCallDiskIoRead",
  "SysCallDiskIoWrite",
  "SysCallUnicodeStriColl",
  "SysCallUnicodeMetaiMatch",
  "SysCallUnicodeStrLwr",
  "SysCallUnicodeStrUpr",
  "SysCallUnicodeFatToStr",
  "SysCallUnicodeStrToFat",
  "SysCallMax"
};

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
ReturnToCore (
  IN EFI_STATUS  Status,
  IN UINTN       ReturnSP
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
  ASSERT (Ring3 != NULL);
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

  } else if (CompareGuid (Ring3, &gEfiUnicodeCollation2ProtocolGuid)) {

    *Core     = &gEfiUnicodeCollation2ProtocolGuid;
    *CoreSize = sizeof (EFI_UNICODE_COLLATION_PROTOCOL);

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
  IN BOOLEAN  FindRing3,
  IN VOID     *Interface
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
      DEBUG ((DEBUG_ERROR, "Could not copy string!\n"));
      return NULL;
    }

    Unicode->SupportedLanguages = (CHAR8 *)mRing3InterfacePointer;

    mRing3InterfacePointer += AsciiStrSize (Unicode->SupportedLanguages);
  }

  return Ring3Interface;
}

STATIC
UINTN *
EFIAPI
CopyUserArguments (
  IN UINT8  NumberOfArguments,
  IN UINTN  *UserArguments
  )
{
  UINTN   *Arguments;
  UINT64  Attributes;
  //
  // Check User variables.
  //
  gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(UINTN)UserArguments, &Attributes);
  ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
  gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)((UINTN)UserArguments + (NumberOfArguments + 1) * sizeof (UINTN) - 1), &Attributes);
  ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

  AllowSupervisorAccessToUserMemory ();
  Arguments = AllocateCopyPool (
                (NumberOfArguments + 1) * sizeof (UINTN),
                (VOID *)UserArguments
                );
  ForbidSupervisorAccessToUserMemory ();

  ASSERT (Arguments != NULL);

  return Arguments;
}

STATIC
USER_SPACE_DRIVER *
EFIAPI
FindUserInfo (
  VOID
  )
{
  LIST_ENTRY         *Link;
  USER_SPACE_DRIVER  *UserDriver;

  for (Link = gUserSpaceDriversHead.ForwardLink; Link != &gUserSpaceDriversHead; Link = Link->ForwardLink) {
    UserDriver = BASE_CR (Link, USER_SPACE_DRIVER, Link);

    if (UserDriver->UserPageTable == gUserPageTable) {
      return UserDriver;
    }
  }

  return NULL;
}

STATIC
VOID
EFIAPI
FreeUserSpaceDriver (
  IN VOID  *CoreWrapper
  )
{
  LIST_ENTRY         *Link;
  USER_SPACE_DRIVER  *UserDriver;

  for (Link = gUserSpaceDriversHead.ForwardLink; Link != &gUserSpaceDriversHead; Link = Link->ForwardLink) {
    UserDriver = BASE_CR (Link, USER_SPACE_DRIVER, Link);

    if (UserDriver->CoreWrapper == CoreWrapper) {
      break;
    }
  }

  RemoveEntryList (&UserDriver->Link);
  FreePool (UserDriver);
}

EFI_STATUS
EFIAPI
CallBootService (
  IN UINT8  Type,
  IN UINT8  NumberOfArguments,
  IN UINTN  *UserArguments,
  IN UINTN  ReturnSP
  )
{
  EFI_STATUS           Status;
  EFI_STATUS           StatusBS;
  UINT64               Attributes;
  VOID                 *Interface;
  EFI_GUID             *CoreProtocol;
  UINT32               MemoryCoreSize;
  UINTN                Argument4;
  UINTN                Argument5;
  UINTN                Argument6;
  UINT32               Index;
  VOID                 **UserArgList;
  VOID                 **CoreArgList;
  EFI_HANDLE           CoreHandle;
  UINT32               PagesNumber;
  EFI_PHYSICAL_ADDRESS Ring3Pages;
  USER_SPACE_DRIVER    *UserDriver;
  USER_SPACE_DRIVER    *NewDriver;
  UINTN                *Arguments;
  EFI_PHYSICAL_ADDRESS PhysAddr;

  EFI_DRIVER_BINDING_PROTOCOL      *CoreDriverBinding;
  EFI_SIMPLE_FILE_SYSTEM_PROTOCOL  *CoreSimpleFileSystem;
  EFI_UNICODE_COLLATION_PROTOCOL   *CoreUnicodeCollation;

  EFI_BLOCK_IO_PROTOCOL          *BlockIo;
  EFI_DISK_IO_PROTOCOL           *DiskIo;
  EFI_UNICODE_COLLATION_PROTOCOL *Unicode;

  CoreProtocol = NULL;
  Argument4    = 0;
  Argument5    = 0;
  Argument6    = 0;
  Interface    = NULL;
  Arguments    = CopyUserArguments (NumberOfArguments, UserArguments);

  DEBUG ((DEBUG_VERBOSE, "Type: %a\n", SysCallNames[Type]));

  switch (Type) {
    case SysCallReturnToCore:
      ReturnToCore (Arguments[1], ReturnSP);
      break;
    case SysCallLocateProtocol:
      //
      // Argument 1: EFI_GUID  *Protocol
      // Argument 2: VOID      *CoreRegistration
      // Argument 3: VOID      **Interface
      //
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)Arguments[1], &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(Arguments[1] + sizeof (EFI_GUID) - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)Arguments[3], &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(Arguments[3] + sizeof (VOID *) - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

      AllowSupervisorAccessToUserMemory ();
      Status = FindGuid ((EFI_GUID *)Arguments[1], &CoreProtocol, &MemoryCoreSize);
      ForbidSupervisorAccessToUserMemory ();
      if (EFI_ERROR (Status)) {
        FreePool (Arguments);
        return Status;
      }

      Status = gBS->LocateProtocol (
                      CoreProtocol,
                      (VOID *)Arguments[2],
                      &Interface
                      );

      AllowSupervisorAccessToUserMemory ();
      if (Interface != NULL) {
        Interface = PrepareRing3Interface (CoreProtocol, Interface, MemoryCoreSize);
        ASSERT (Interface != NULL);

        *(VOID **)Arguments[3] = Interface;
      }
      ForbidSupervisorAccessToUserMemory ();

      FreePool (Arguments);
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
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)Arguments[2], &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(Arguments[2] + sizeof (EFI_GUID) - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      if ((VOID **)Arguments[3] != NULL) {
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)Arguments[3], &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(Arguments[3] + sizeof (VOID *) - 1), &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      }

      AllowSupervisorAccessToUserMemory ();
      Status = FindGuid ((EFI_GUID *)Arguments[2], &CoreProtocol, &MemoryCoreSize);
      ForbidSupervisorAccessToUserMemory ();
      if (EFI_ERROR (Status)) {
        FreePool (Arguments);
        return Status;
      }

      Status = gBS->OpenProtocol (
                      (EFI_HANDLE)Arguments[1],
                      CoreProtocol,
                      ((VOID **)Arguments[3] != NULL) ? &Interface : NULL,
                      (EFI_HANDLE)Arguments[4],
                      (EFI_HANDLE)Arguments[5],
                      (UINT32)Arguments[6]
                      );

      if ((VOID **)Arguments[3] != NULL) {
        AllowSupervisorAccessToUserMemory ();
        if (Interface != NULL) {
          Interface = PrepareRing3Interface (CoreProtocol, Interface, MemoryCoreSize);
        }

        *(VOID **)Arguments[3] = Interface;
        ForbidSupervisorAccessToUserMemory ();
      }

      FreePool (Arguments);
      return Status;

    case SysCallInstallMultipleProtocolInterfaces:
      //
      // Argument 1: EFI_HANDLE  *Handle
      // Argument 2: UINTN       NumberOfArguments
      // Argument 3: VOID        **UserArgList
      //
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)Arguments[1], &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(Arguments[1] + sizeof (EFI_HANDLE *) - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)Arguments[3], &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(Arguments[3] + Arguments[2] * sizeof (VOID *) - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

      CoreArgList = AllocatePool (Arguments[2] * sizeof (VOID *));

      AllowSupervisorAccessToUserMemory ();
      CoreHandle  = *(EFI_HANDLE *)Arguments[1];
      UserArgList = (VOID **)Arguments[3];

      for (Index = 0; UserArgList[Index] != NULL; Index += 2) {
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(UINTN)UserArgList[Index], &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)((UINTN)UserArgList[Index] + sizeof (EFI_GUID) - 1), &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

        Status = FindGuid ((EFI_GUID *)UserArgList[Index], (EFI_GUID **)&CoreArgList[Index], &MemoryCoreSize);
        if (EFI_ERROR (Status)) {
          ForbidSupervisorAccessToUserMemory ();

          while (Index > 0) {
            FreeUserSpaceDriver (CoreArgList[Index - 1]);
            FreePool (CoreArgList[Index - 1]);
            Index -= 2;
          }

          FreePool (CoreArgList);
          FreePool (Arguments);
          return Status;
        }

        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(UINTN)UserArgList[Index + 1], &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)((UINTN)UserArgList[Index + 1] + MemoryCoreSize - 1), &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

        CoreArgList[Index + 1] = AllocateCopyPool (MemoryCoreSize, (VOID *)UserArgList[Index + 1]);

        UserDriver = FindUserInfo ();
        ASSERT (UserDriver != NULL);
        //
        // TODO: Check everywhere that Allocated != NULL
        //
        NewDriver                  = AllocatePool (sizeof (USER_SPACE_DRIVER));
        NewDriver->CoreWrapper     = CoreArgList[Index + 1];
        NewDriver->UserSpaceDriver = UserArgList[Index + 1];
        NewDriver->UserPageTable   = UserDriver->UserPageTable;
        NewDriver->NumberOfCalls   = 0;

        InsertTailList (&gUserSpaceDriversHead, &NewDriver->Link);
      }
      ForbidSupervisorAccessToUserMemory ();

      ASSERT (Index == (Arguments[2] - 1));
      CoreArgList[Index] = NULL;

      for (Index = 0; CoreArgList[Index] != NULL; Index += 2) {
        if (CompareGuid ((EFI_GUID *)CoreArgList[Index], &gEfiDriverBindingProtocolGuid)) {
          CoreDriverBinding = (EFI_DRIVER_BINDING_PROTOCOL *)CoreArgList[Index + 1];

          CoreDriverBinding->Supported = CoreDriverBindingSupported;
          CoreDriverBinding->Start     = CoreDriverBindingStart;
          CoreDriverBinding->Stop      = CoreDriverBindingStop;
        } else if (CompareGuid ((EFI_GUID *)CoreArgList[Index], &gEfiSimpleFileSystemProtocolGuid)) {
          CoreSimpleFileSystem = (EFI_SIMPLE_FILE_SYSTEM_PROTOCOL *)CoreArgList[Index + 1];

          CoreSimpleFileSystem->OpenVolume = CoreSimpleFileSystemOpenVolume;
        } else if ((CompareGuid ((EFI_GUID *)CoreArgList[Index], &gEfiUnicodeCollationProtocolGuid))
            || (CompareGuid ((EFI_GUID *)CoreArgList[Index], &gEfiUnicodeCollation2ProtocolGuid))) {
          CoreUnicodeCollation = (EFI_UNICODE_COLLATION_PROTOCOL *)CoreArgList[Index + 1];

          CoreUnicodeCollation->StriColl   = CoreUnicodeCollationStriColl;
          CoreUnicodeCollation->MetaiMatch = CoreUnicodeCollationMetaiMatch;
          CoreUnicodeCollation->StrLwr     = CoreUnicodeCollationStrLwr;
          CoreUnicodeCollation->StrUpr     = CoreUnicodeCollationStrUpr;
          CoreUnicodeCollation->FatToStr   = CoreUnicodeCollationFatToStr;
          CoreUnicodeCollation->StrToFat   = CoreUnicodeCollationStrToFat;
          AllowSupervisorAccessToUserMemory ();
          CoreUnicodeCollation->SupportedLanguages = AllocateCopyPool (
                                                       AsciiStrSize (CoreUnicodeCollation->SupportedLanguages),
                                                       (VOID *)CoreUnicodeCollation->SupportedLanguages
                                                       );
          ForbidSupervisorAccessToUserMemory ();
        }
      }

      Status = CallInstallMultipleProtocolInterfaces (
                 &CoreHandle,
                 CoreArgList,
                 Index + 1,
                 (VOID *)gBS->InstallMultipleProtocolInterfaces
                 );

      FreePool (CoreArgList);
      FreePool (Arguments);
      return Status;

    case SysCallCloseProtocol:
      //
      // Argument 1: EFI_HANDLE  CoreUserHandle
      // Argument 2: EFI_GUID    *Protocol
      // Argument 3: EFI_HANDLE  CoreAgentHandle
      // Argument 4: EFI_HANDLE  CoreControllerHandle
      //
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)Arguments[2], &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(Arguments[2] + sizeof (EFI_GUID) - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

      AllowSupervisorAccessToUserMemory ();
      Status = FindGuid ((EFI_GUID *)Arguments[2], &CoreProtocol, &MemoryCoreSize);
      ForbidSupervisorAccessToUserMemory ();
      if (EFI_ERROR (Status)) {
        FreePool (Arguments);
        return Status;
      }

      Status = gBS->CloseProtocol (
                      (EFI_HANDLE)Arguments[1],
                      CoreProtocol,
                      (EFI_HANDLE)Arguments[3],
                      (EFI_HANDLE)Arguments[4]
                      );

      FreePool (Arguments);
      return Status;

    case SysCallHandleProtocol:
      //
      // Argument 1: EFI_HANDLE  CoreUserHandle
      // Argument 2: EFI_GUID    *Protocol
      // Argument 3: VOID        **Interface
      //
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)Arguments[2], &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(Arguments[2] + sizeof (EFI_GUID) - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)Arguments[3], &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(Arguments[3] + sizeof (VOID *) - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

      AllowSupervisorAccessToUserMemory ();
      Status = FindGuid ((EFI_GUID *)Arguments[2], &CoreProtocol, &MemoryCoreSize);
      ForbidSupervisorAccessToUserMemory ();
      if (EFI_ERROR (Status)) {
        FreePool (Arguments);
        return Status;
      }

      Status = gBS->HandleProtocol (
                      (EFI_HANDLE)Arguments[1],
                      CoreProtocol,
                      &Interface
                      );

      AllowSupervisorAccessToUserMemory ();
      if (Interface != NULL) {
        Interface = PrepareRing3Interface (CoreProtocol, Interface, MemoryCoreSize);
        ASSERT (Interface != NULL);

        *(VOID **)Arguments[3] = Interface;
      }
      ForbidSupervisorAccessToUserMemory ();

      FreePool (Arguments);
      return Status;

    case SysCallAllocatePages:
      //
      // Argument 1: EFI_ALLOCATE_TYPE     Type
      // Argument 2: EFI_MEMORY_TYPE       MemoryType
      // Argument 3: UINTN                 NumberOfPages
      // Argument 4: EFI_PHYSICAL_ADDRESS  *Memory
      //
      Status = gBS->AllocatePages (
                      (EFI_ALLOCATE_TYPE)Arguments[1],
                      (EFI_MEMORY_TYPE)Arguments[2],
                      Arguments[3],
                      (EFI_PHYSICAL_ADDRESS *)&Argument4
                      );

      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)Arguments[4], &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(Arguments[4] + sizeof (EFI_PHYSICAL_ADDRESS) - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

      AllowSupervisorAccessToUserMemory ();
      *(EFI_PHYSICAL_ADDRESS *)Arguments[4] = (EFI_PHYSICAL_ADDRESS)Argument4;
      ForbidSupervisorAccessToUserMemory ();

      FreePool (Arguments);
      return Status;

    case SysCallFreePages:
      //
      // Argument 1: UINTN                 NumberOfPages
      // Argument 2: EFI_PHYSICAL_ADDRESS  Memory
      //
      PhysAddr = *(EFI_PHYSICAL_ADDRESS *)&Arguments[2];

      gCpu->GetMemoryAttributes (gCpu, PhysAddr, &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, PhysAddr + Arguments[1] * EFI_PAGE_SIZE - 1, &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

      Status = gBS->FreePages (PhysAddr, Arguments[1]);

      FreePool (Arguments);
      return Status;

    case SysCallRaiseTpl:
      //
      // Argument 1: EFI_TPL  NewTpl
      //
      Status = (EFI_STATUS)gBS->RaiseTPL ((EFI_TPL)Arguments[1]);

      FreePool (Arguments);
      return Status;

    case SysCallRestoreTpl:
      //
      // Argument 1: EFI_TPL  NewTpl
      //
      gBS->RestoreTPL ((EFI_TPL)Arguments[1]);

      FreePool (Arguments);
      return EFI_SUCCESS;

    case SysCallLocateHandleBuffer:
      //
      // Argument 1: EFI_LOCATE_SEARCH_TYPE  SearchType
      // Argument 2: EFI_GUID                *Protocol  OPTIONAL
      // Argument 3: VOID                    *SearchKey OPTIONAL
      // Argument 4: UINTN                   *NumberHandles
      // Argument 5: EFI_HANDLE              **Buffer
      //
      if ((EFI_GUID *)Arguments[2] != NULL) {
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)Arguments[2], &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(Arguments[2] + sizeof (EFI_GUID) - 1), &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

        AllowSupervisorAccessToUserMemory ();
        Status = FindGuid ((EFI_GUID *)Arguments[2], &CoreProtocol, &MemoryCoreSize);
        ForbidSupervisorAccessToUserMemory ();
        if (EFI_ERROR (Status)) {
          FreePool (Arguments);
          return Status;
        }
      }

      StatusBS = gBS->LocateHandleBuffer (
                        (EFI_LOCATE_SEARCH_TYPE)Arguments[1],
                        CoreProtocol,
                        (VOID *)Arguments[3],
                        &Argument4,
                        (EFI_HANDLE **)&Argument5
                        );

      if ((UINTN *)Arguments[4] != NULL) {
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)Arguments[4], &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(Arguments[4] + sizeof (UINTN) - 1), &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

        AllowSupervisorAccessToUserMemory ();
        *(UINTN *)Arguments[4] = Argument4;
        ForbidSupervisorAccessToUserMemory ();
      }

      if ((EFI_HANDLE **)Arguments[5] != NULL) {
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)Arguments[5], &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(Arguments[5] + sizeof (EFI_HANDLE *) - 1), &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

        PagesNumber = (UINT32)EFI_SIZE_TO_PAGES (Argument4 * sizeof (EFI_HANDLE *));

        Status = CoreAllocatePages (
                   AllocateAnyPages,
                   EfiRing3MemoryType,
                   PagesNumber,
                   &Ring3Pages
                   );
        if (EFI_ERROR (Status)) {
          FreePool (Arguments);
          return Status;
        }

        AllowSupervisorAccessToUserMemory ();
        CopyMem ((VOID *)(UINTN)Ring3Pages, (VOID *)Argument5, Argument4 * sizeof (EFI_HANDLE *));

        FreePool ((VOID *)Argument5);

        *(EFI_HANDLE **)Arguments[5] = (EFI_HANDLE *)(UINTN)Ring3Pages;
        ForbidSupervisorAccessToUserMemory ();
      }

      FreePool (Arguments);
      return StatusBS;

    case SysCallCalculateCrc32:
      //
      // Argument 1: VOID    *Data
      // Argument 2: UINTN   DataSize
      // Argument 3: UINT32  *Crc32
      //
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)Arguments[1], &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(Arguments[1] + Arguments[2] - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)Arguments[3], &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(Arguments[3] + sizeof (UINT32 *) - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

      Argument4 = (UINTN)AllocatePool (Arguments[2]);
      if ((VOID *)Argument4 == NULL) {
        FreePool (Arguments);
        return EFI_OUT_OF_RESOURCES;
      }

      AllowSupervisorAccessToUserMemory ();
      CopyMem ((VOID *)Argument4, (VOID *)Arguments[1], Arguments[2]);
      ForbidSupervisorAccessToUserMemory ();

      Status = gBS->CalculateCrc32 (
                      (VOID *)Argument4,
                      Arguments[2],
                      (UINT32 *)&Argument5
                      );

      AllowSupervisorAccessToUserMemory ();
      *(UINT32 *)Arguments[3] = (UINT32)Argument5;
      ForbidSupervisorAccessToUserMemory ();

      FreePool (Arguments);
      return Status;

    case SysCallGetVariable:
      //
      // Argument 1: CHAR16    *VariableName
      // Argument 2: EFI_GUID  *VendorGuid
      // Argument 3: UINT32    *Attributes     OPTIONAL
      // Argument 4: UINTN     *DataSize
      // Argument 5: VOID      *Data           OPTIONAL
      //
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)Arguments[1], &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)Arguments[2], &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(Arguments[2] + sizeof (EFI_GUID) - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      if ((UINT32 *)Arguments[3] != NULL) {
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)Arguments[3], &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(Arguments[3] + sizeof (UINT32) - 1), &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      }

      AllowSupervisorAccessToUserMemory ();
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(Arguments[1] + StrSize ((CHAR16 *)Arguments[1]) - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

      Argument6 = (UINTN)AllocateCopyPool (StrSize ((CHAR16 *)Arguments[1]), (CHAR16 *)Arguments[1]);
      if ((VOID *)Argument6 == NULL) {
        ForbidSupervisorAccessToUserMemory ();
        FreePool (Arguments);
        return EFI_OUT_OF_RESOURCES;
      }

      Status = FindGuid ((EFI_GUID *)Arguments[2], &CoreProtocol, &MemoryCoreSize);
      if (EFI_ERROR (Status)) {
        ForbidSupervisorAccessToUserMemory ();
        FreePool ((VOID *)Argument6);
        FreePool (Arguments);
        return Status;
      }

      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)Arguments[4], &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(Arguments[4] + sizeof (UINTN) - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

      Argument4 = *(UINTN *)Arguments[4];

      if ((VOID *)Arguments[5] != NULL) {
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)Arguments[5], &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(Arguments[5] + Argument4 - 1), &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

        Argument5 = (UINTN)AllocatePool (Argument4);
        if ((VOID *)Argument5 == NULL) {
          ForbidSupervisorAccessToUserMemory ();
          FreePool ((VOID *)Argument6);
          FreePool (Arguments);
          return EFI_OUT_OF_RESOURCES;
        }
      }
      ForbidSupervisorAccessToUserMemory ();

      Status = gRT->GetVariable (
                      (CHAR16 *)Argument6,
                      CoreProtocol,
                      (UINT32 *)&Attributes,
                      &Argument4,
                      (VOID *)Argument5
                      );

      AllowSupervisorAccessToUserMemory ();
      if ((VOID *)Arguments[5] != NULL) {
        CopyMem ((VOID *)Arguments[5], (VOID *)Argument5, Argument4);
      }

      *(UINTN *)Arguments[4] = Argument4;

      if ((UINT32 *)Arguments[3] != NULL) {
        *(UINT32 *)Arguments[3] = (UINT32)Attributes;
      }
      ForbidSupervisorAccessToUserMemory ();

      FreePool ((VOID *)Argument6);

      if ((VOID *)Argument5 != NULL) {
        FreePool ((VOID *)Argument5);
      }

      FreePool (Arguments);
      return Status;

    case SysCallBlockIoReset:
      //
      // Argument 1: EFI_BLOCK_IO_PROTOCOL  *This
      // Argument 2: BOOLEAN                ExtendedVerification
      //
      BlockIo = FindInterface (FALSE, (VOID *)Arguments[1]);

      if (BlockIo == NULL) {
        FreePool (Arguments);
        return EFI_NOT_FOUND;
      }

      Status = BlockIo->Reset (
                          BlockIo,
                          (BOOLEAN)Arguments[2]
                          );

      FreePool (Arguments);
      return Status;

    case SysCallBlockIoRead:
      //
      // Argument 1: EFI_BLOCK_IO_PROTOCOL *This
      // Argument 2: UINT32                MediaId
      // Argument 3: UINTN                 BufferSize
      // Argument 4: VOID                  *Buffer
      // Argument 5: EFI_LBA               Lba
      //
      PhysAddr = *(EFI_PHYSICAL_ADDRESS *)&Arguments[5];

      BlockIo = FindInterface (FALSE, (VOID *)Arguments[1]);

      if (BlockIo == NULL) {
        FreePool (Arguments);
        return EFI_NOT_FOUND;
      }

      Argument5 = (UINTN)AllocatePool (Arguments[3]);
      if ((VOID *)Argument5 == NULL) {
        FreePool (Arguments);
        return EFI_OUT_OF_RESOURCES;
      }

      Status = BlockIo->ReadBlocks (
                          BlockIo,
                          (UINT32)Arguments[2],
                          (EFI_LBA)PhysAddr,
                          Arguments[3],
                          (VOID *)Argument5
                          );

      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)Arguments[4], &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(Arguments[4] + Arguments[3] - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

      AllowSupervisorAccessToUserMemory ();
      CopyMem ((VOID *)Arguments[4], (VOID *)Argument5, Arguments[3]);
      ForbidSupervisorAccessToUserMemory ();

      FreePool ((VOID *)Argument5);

      FreePool (Arguments);
      return Status;

    case SysCallBlockIoWrite:
      //
      // Argument 1: EFI_BLOCK_IO_PROTOCOL *This
      // Argument 2: UINT32                MediaId
      // Argument 3: UINTN                 BufferSize
      // Argument 4: VOID                  *Buffer
      // Argument 5: EFI_LBA               Lba
      //
      PhysAddr = *(EFI_PHYSICAL_ADDRESS *)&Arguments[5];

      BlockIo = FindInterface (FALSE, (VOID *)Arguments[1]);

      if (BlockIo == NULL) {
        FreePool (Arguments);
        return EFI_NOT_FOUND;
      }

      Argument5 = (UINTN)AllocatePool (Arguments[3]);
      if ((VOID *)Argument5 == NULL) {
        FreePool (Arguments);
        return EFI_OUT_OF_RESOURCES;
      }

      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)Arguments[4], &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(Arguments[4] + Arguments[3] - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

      AllowSupervisorAccessToUserMemory ();
      CopyMem ((VOID *)Argument5, (VOID *)Arguments[4], Arguments[3]);
      ForbidSupervisorAccessToUserMemory ();

      Status = BlockIo->WriteBlocks (
                          BlockIo,
                          (UINT32)Arguments[2],
                          (EFI_LBA)PhysAddr,
                          Arguments[3],
                          (VOID *)Argument5
                          );

      FreePool ((VOID *)Argument5);

      FreePool (Arguments);
      return Status;

    case SysCallBlockIoFlush:
      //
      // Argument 1: EFI_BLOCK_IO_PROTOCOL  *This
      //
      BlockIo = FindInterface (FALSE, (VOID *)Arguments[1]);

      if (BlockIo == NULL) {
        FreePool (Arguments);
        return EFI_NOT_FOUND;
      }

      Status = BlockIo->FlushBlocks (BlockIo);

      FreePool (Arguments);
      return Status;

    case SysCallDiskIoRead:
      //
      // Argument 1: EFI_DISK_IO_PROTOCOL  *This
      // Argument 2: UINT32                MediaId
      // Argument 3: UINTN                 BufferSize
      // Argument 4: VOID                  *Buffer
      // Argument 5: UINT64                Offset
      //
      PhysAddr = *(EFI_PHYSICAL_ADDRESS *)&Arguments[5];

      DiskIo = FindInterface (FALSE, (VOID *)Arguments[1]);

      if (DiskIo == NULL) {
        FreePool (Arguments);
        return EFI_NOT_FOUND;
      }

      Argument5 = (UINTN)AllocatePool (Arguments[3]);
      if ((VOID *)Argument5 == NULL) {
        FreePool (Arguments);
        return EFI_OUT_OF_RESOURCES;
      }

      Status = DiskIo->ReadDisk (
                         DiskIo,
                         (UINT32)Arguments[2],
                         (UINT64)PhysAddr,
                         Arguments[3],
                         (VOID *)Argument5
                         );

      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)Arguments[4], &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(Arguments[4] + Arguments[3] - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

      AllowSupervisorAccessToUserMemory ();
      CopyMem ((VOID *)Arguments[4], (VOID *)Argument5, Arguments[3]);
      ForbidSupervisorAccessToUserMemory ();

      FreePool ((VOID *)Argument5);

      FreePool (Arguments);
      return Status;

    case SysCallDiskIoWrite:
      //
      // Argument 1: EFI_DISK_IO_PROTOCOL  *This
      // Argument 2: UINT32                MediaId
      // Argument 3: UINTN                 BufferSize
      // Argument 4: VOID                  *Buffer
      // Argument 5: UINT64                Offset
      //
      PhysAddr = *(EFI_PHYSICAL_ADDRESS *)&Arguments[5];

      DiskIo = FindInterface (FALSE, (VOID *)Arguments[1]);

      if (DiskIo == NULL) {
        FreePool (Arguments);
        return EFI_NOT_FOUND;
      }

      Argument5 = (UINTN)AllocatePool (Arguments[3]);
      if ((VOID *)Argument5 == NULL) {
        FreePool (Arguments);
        return EFI_OUT_OF_RESOURCES;
      }

      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)Arguments[4], &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(Arguments[4] + Arguments[3] - 1), &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

      AllowSupervisorAccessToUserMemory ();
      CopyMem ((VOID *)Argument5, (VOID *)Arguments[4], Arguments[3]);
      ForbidSupervisorAccessToUserMemory ();

      Status = DiskIo->WriteDisk (
                         DiskIo,
                         (UINT32)Arguments[2],
                         (UINT64)PhysAddr,
                         Arguments[3],
                         (VOID *)Argument5
                         );

      FreePool ((VOID *)Argument5);

      FreePool (Arguments);
      return Status;

    case SysCallUnicodeStriColl:
      //
      // Argument 1: EFI_UNICODE_COLLATION_PROTOCOL  *This
      // Argument 2: CHAR16                          *Str1
      // Argument 3: CHAR16                          *Str2
      //
      Unicode = FindInterface (FALSE, (VOID *)Arguments[1]);

      if (Unicode == NULL) {
        FreePool (Arguments);
        return EFI_NOT_FOUND;
      }

      if ((CHAR16 *)Arguments[2] != NULL) {
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)Arguments[2], &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

        AllowSupervisorAccessToUserMemory ();
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(Arguments[2] + StrSize ((CHAR16 *)Arguments[2]) - 1), &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

        Argument4 = (UINTN)AllocateCopyPool (StrSize ((CHAR16 *)Arguments[2]), (CHAR16 *)Arguments[2]);
        ForbidSupervisorAccessToUserMemory ();
        if ((VOID *)Argument4 == NULL) {
          FreePool (Arguments);
          return EFI_OUT_OF_RESOURCES;
        }
      }

      if ((CHAR16 *)Arguments[3] != NULL) {
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)Arguments[3], &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

        AllowSupervisorAccessToUserMemory ();
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(Arguments[3] + StrSize ((CHAR16 *)Arguments[3]) - 1), &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

        Argument5 = (UINTN)AllocateCopyPool (StrSize ((CHAR16 *)Arguments[3]), (CHAR16 *)Arguments[3]);
        ForbidSupervisorAccessToUserMemory ();
        if ((VOID *)Argument5 == NULL) {
          if ((VOID *)Argument4 != NULL) {
            FreePool ((VOID *)Argument4);
          }

          FreePool (Arguments);
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

      FreePool (Arguments);
      return Status;

    case SysCallUnicodeMetaiMatch:
      //
      // Argument 1: EFI_UNICODE_COLLATION_PROTOCOL  *This
      // Argument 2: CHAR16                          *String
      // Argument 3: CHAR16                          *Pattern
      //
      Unicode = FindInterface (FALSE, (VOID *)Arguments[1]);

      if (Unicode == NULL) {
        FreePool (Arguments);
        return EFI_NOT_FOUND;
      }

      if ((CHAR16 *)Arguments[2] != NULL) {
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)Arguments[2], &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

        AllowSupervisorAccessToUserMemory ();
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(Arguments[2] + StrSize ((CHAR16 *)Arguments[2]) - 1), &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

        Argument4 = (UINTN)AllocateCopyPool (StrSize ((CHAR16 *)Arguments[2]), (CHAR16 *)Arguments[2]);
        ForbidSupervisorAccessToUserMemory ();
        if ((VOID *)Argument4 == NULL) {
          FreePool (Arguments);
          return EFI_OUT_OF_RESOURCES;
        }
      }

      if ((CHAR16 *)Arguments[3] != NULL) {
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)Arguments[3], &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

        AllowSupervisorAccessToUserMemory ();
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(Arguments[3] + StrSize ((CHAR16 *)Arguments[3]) - 1), &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

        Argument5 = (UINTN)AllocateCopyPool (StrSize ((CHAR16 *)Arguments[3]), (CHAR16 *)Arguments[3]);
        ForbidSupervisorAccessToUserMemory ();
        if ((VOID *)Argument5 == NULL) {
          if ((VOID *)Argument4 != NULL) {
            FreePool ((VOID *)Argument4);
          }

          FreePool (Arguments);
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

      FreePool (Arguments);
      return Status;

    case SysCallUnicodeStrLwr:
      //
      // Argument 1: EFI_UNICODE_COLLATION_PROTOCOL  *This
      // Argument 2: CHAR16                          *Str
      //
      Unicode = FindInterface (FALSE, (VOID *)Arguments[1]);

      if (Unicode == NULL) {
        FreePool (Arguments);
        return EFI_NOT_FOUND;
      }

      if ((CHAR16 *)Arguments[2] != NULL) {
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)Arguments[2], &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

        AllowSupervisorAccessToUserMemory ();
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(Arguments[2] + StrSize ((CHAR16 *)Arguments[2]) - 1), &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

        Argument4 = (UINTN)AllocateCopyPool (StrSize ((CHAR16 *)Arguments[2]), (CHAR16 *)Arguments[2]);
        ForbidSupervisorAccessToUserMemory ();
        if ((VOID *)Argument4 == NULL) {
          FreePool (Arguments);
          return EFI_OUT_OF_RESOURCES;
        }
      }

      Unicode->StrLwr (
                 Unicode,
                 (CHAR16 *)Argument4
                 );

      if ((VOID *)Argument4 != NULL) {
        AllowSupervisorAccessToUserMemory ();
        Status = StrCpyS ((CHAR16 *)Arguments[2], StrLen ((CHAR16 *)Arguments[2]) + 1, (CHAR16 *)Argument4);
        ForbidSupervisorAccessToUserMemory ();

        FreePool ((VOID *)Argument4);
      }

      FreePool (Arguments);
      return EFI_SUCCESS;

    case SysCallUnicodeStrUpr:
      //
      // Argument 1: EFI_UNICODE_COLLATION_PROTOCOL  *This
      // Argument 2: CHAR16                          *Str
      //
      Unicode = FindInterface (FALSE, (VOID *)Arguments[1]);

      if (Unicode == NULL) {
        FreePool (Arguments);
        return EFI_NOT_FOUND;
      }

      if ((CHAR16 *)Arguments[2] != NULL) {
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)Arguments[2], &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

        AllowSupervisorAccessToUserMemory ();
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(Arguments[2] + StrSize ((CHAR16 *)Arguments[2]) - 1), &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

        Argument4 = (UINTN)AllocateCopyPool (StrSize ((CHAR16 *)Arguments[2]), (CHAR16 *)Arguments[2]);
        ForbidSupervisorAccessToUserMemory ();
        if ((VOID *)Argument4 == NULL) {
          FreePool (Arguments);
          return EFI_OUT_OF_RESOURCES;
        }
      }

      Unicode->StrUpr (
                 Unicode,
                 (CHAR16 *)Argument4
                 );

      if ((VOID *)Argument4 != NULL) {
        AllowSupervisorAccessToUserMemory ();
        Status = StrCpyS ((CHAR16 *)Arguments[2], StrLen ((CHAR16 *)Arguments[2]) + 1, (CHAR16 *)Argument4);
        ForbidSupervisorAccessToUserMemory ();

        FreePool ((VOID *)Argument4);
      }

      FreePool (Arguments);
      return EFI_SUCCESS;

    case SysCallUnicodeFatToStr:
      //
      // Argument 1: EFI_UNICODE_COLLATION_PROTOCOL  *This
      // Argument 2: UINTN                           FatSize
      // Argument 3: CHAR8                           *Fat
      // Argument 4: CHAR16                          *String
      //
      Unicode = FindInterface (FALSE, (VOID *)Arguments[1]);

      if (Unicode == NULL) {
        FreePool (Arguments);
        return EFI_NOT_FOUND;
      }

      if ((CHAR8 *)Arguments[3] != NULL) {
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)Arguments[3], &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(Arguments[3] + Arguments[2] - 1), &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

        AllowSupervisorAccessToUserMemory ();
        Argument4 = (UINTN)AllocateCopyPool (Arguments[2], (CHAR8 *)Arguments[3]);
        ForbidSupervisorAccessToUserMemory ();
        if ((VOID *)Argument4 == NULL) {
          FreePool (Arguments);
          return EFI_OUT_OF_RESOURCES;
        }
      }

      if ((CHAR16 *)Arguments[4] != NULL) {
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)Arguments[4], &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(Arguments[4] + 2 * (Arguments[2] + 1) - 1), &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

        Argument5 = (UINTN)AllocatePool (2 * (Arguments[2] + 1));
        if ((VOID *)Argument5 == NULL) {
          if ((VOID *)Argument4 != NULL) {
            FreePool ((VOID *)Argument4);
          }

          FreePool (Arguments);
          return EFI_OUT_OF_RESOURCES;
        }
      }

      Unicode->FatToStr (
                 Unicode,
                 Arguments[2],
                 (CHAR8 *)Argument4,
                 (CHAR16 *)Argument5
                 );

      if ((VOID *)Argument4 != NULL) {
        FreePool ((VOID *)Argument4);
      }

      if ((VOID *)Argument5 != NULL) {
        AllowSupervisorAccessToUserMemory ();
        CopyMem ((VOID *)Arguments[4], (VOID *)Argument5, 2 * (Arguments[2] + 1));
        ForbidSupervisorAccessToUserMemory ();

        FreePool ((VOID *)Argument5);
      }

      FreePool (Arguments);
      return EFI_SUCCESS;

    case SysCallUnicodeStrToFat:
      //
      // Argument 1: EFI_UNICODE_COLLATION_PROTOCOL  *This
      // Argument 2: CHAR16                          *String
      // Argument 3: UINTN                           FatSize
      // Argument 4: CHAR8                           *Fat
      //
      Unicode = FindInterface (FALSE, (VOID *)Arguments[1]);

      if (Unicode == NULL) {
        FreePool (Arguments);
        return EFI_NOT_FOUND;
      }

      if ((CHAR16 *)Arguments[2] != NULL) {
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)Arguments[2], &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

        AllowSupervisorAccessToUserMemory ();
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(Arguments[2] + StrSize ((CHAR16 *)Arguments[2]) - 1), &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

        Argument4 = (UINTN)AllocateCopyPool (StrSize ((CHAR16 *)Arguments[2]), (CHAR16 *)Arguments[2]);
        ForbidSupervisorAccessToUserMemory ();
        if ((VOID *)Argument4 == NULL) {
          FreePool (Arguments);
          return EFI_OUT_OF_RESOURCES;
        }
      }

      if ((CHAR8 *)Arguments[4] != NULL) {
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)Arguments[4], &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);
        gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)(Arguments[4] + Arguments[3] - 1), &Attributes);
        ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

        Argument5 = (UINTN)AllocatePool (Arguments[3]);
        if ((VOID *)Argument5 == NULL) {
          if ((VOID *)Argument4 != NULL) {
            FreePool ((VOID *)Argument4);
          }

          FreePool (Arguments);
          return EFI_OUT_OF_RESOURCES;
        }
      }

      Status = (EFI_STATUS)Unicode->StrToFat (
                                      Unicode,
                                      (CHAR16 *)Argument4,
                                      Arguments[3],
                                      (CHAR8 *)Argument5
                                      );

      if ((VOID *)Argument4 != NULL) {
        FreePool ((VOID *)Argument4);
      }

      if ((VOID *)Argument5 != NULL) {
        AllowSupervisorAccessToUserMemory ();
        CopyMem ((VOID *)Arguments[4], (VOID *)Argument5, Arguments[3]);
        ForbidSupervisorAccessToUserMemory ();

        FreePool ((VOID *)Argument5);
      }

      FreePool (Arguments);
      return Status;

    default:
      DEBUG ((DEBUG_ERROR, "Ring0: Unknown syscall type.\n"));
      break;
  }

  return EFI_UNSUPPORTED;
}
