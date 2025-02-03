/** @file
  This driver constructs User space wrappers for the EFI_BOOT_SERVICES.

  Copyright (c) 2024 - 2025, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause

**/

#include <Uefi.h>

#include <Guid/MemoryProfile.h>

#include <Library/BaseMemoryLib.h>
#include <Library/DebugLib.h>
#include <Library/MemoryPoolLib.h>

#include "Ring3.h"

BOOLEAN  mOnGuarding = FALSE;

STATIC UINTN  mMemoryTypes[MAX_MEMORY_TYPE];
STATIC UINTN  mNumberOfUsers = 0;

STATIC
UINTN
EFIAPI
GetMemoryType (
  IN UINTN  UserPageTable
  )
{
  UINTN  Index;

  for (Index = 0; Index < mNumberOfUsers; ++Index) {
    if (mMemoryTypes[Index] == UserPageTable) {
      return Index;
    }
  }

  ASSERT (mNumberOfUsers < MAX_MEMORY_TYPE);

  mMemoryTypes[mNumberOfUsers] = UserPageTable;
  ++mNumberOfUsers;

  return (mNumberOfUsers - 1);
}

STATIC
EFI_STATUS
EFIAPI
FixInterface (
  IN     EFI_GUID  *Protocol,
  IN OUT VOID      **Interface
  )
{
  EFI_LOADED_IMAGE_PROTOCOL          *LoadedImage;
  EFI_BLOCK_IO_PROTOCOL              *BlockIo;
  EFI_DISK_IO_PROTOCOL               *DiskIo;
  EFI_DEVICE_PATH_UTILITIES_PROTOCOL *DevicePath;
  EFI_UNICODE_COLLATION_PROTOCOL     *Unicode;

  ASSERT (Protocol != NULL);
  ASSERT (Interface != NULL);

  if (CompareGuid (Protocol, &gEfiDevicePathProtocolGuid)) {

  } else if (CompareGuid (Protocol, &gEfiLoadedImageProtocolGuid)) {

    LoadedImage = (EFI_LOADED_IMAGE_PROTOCOL *)*Interface;

    LoadedImage->Unload = NULL;

  } else if (CompareGuid (Protocol, &gEfiBlockIoProtocolGuid)) {

    BlockIo = (EFI_BLOCK_IO_PROTOCOL *)*Interface;

    BlockIo->Reset       = UserSpaceBlockIoReset;
    BlockIo->ReadBlocks  = UserSpaceBlockIoRead;
    BlockIo->WriteBlocks = UserSpaceBlockIoWrite;
    BlockIo->FlushBlocks = UserSpaceBlockIoFlush;

  } else if (CompareGuid (Protocol, &gEfiDiskIoProtocolGuid)) {

    DiskIo = (EFI_DISK_IO_PROTOCOL *)*Interface;

    DiskIo->ReadDisk  = UserSpaceDiskIoRead;
    DiskIo->WriteDisk = UserSpaceDiskIoWrite;

  } else if (CompareGuid (Protocol, &gEfiDevicePathUtilitiesProtocolGuid)) {
    DevicePath = (EFI_DEVICE_PATH_UTILITIES_PROTOCOL *)*Interface;

    DevicePath->GetDevicePathSize = NULL;
    DevicePath->DuplicateDevicePath = NULL;
    DevicePath->AppendDevicePath = NULL;
    DevicePath->AppendDeviceNode = NULL;
    DevicePath->AppendDevicePathInstance = NULL;
    DevicePath->GetNextDevicePathInstance = NULL;
    DevicePath->IsDevicePathMultiInstance = NULL;
    DevicePath->CreateDeviceNode = NULL;

  } else if (CompareGuid (Protocol, &gEfiUnicodeCollationProtocolGuid)) {
    Unicode = (EFI_UNICODE_COLLATION_PROTOCOL *)*Interface;

    Unicode->StriColl   = UserSpaceUnicodeStriColl;
    Unicode->MetaiMatch = UserSpaceUnicodeMetaiMatch;
    Unicode->StrLwr     = UserSpaceUnicodeStrLwr;
    Unicode->StrUpr     = UserSpaceUnicodeStrUpr;
    Unicode->FatToStr   = UserSpaceUnicodeFatToStr;
    Unicode->StrToFat   = UserSpaceUnicodeStrToFat;

  } else {
    return EFI_UNSUPPORTED;
  }

  return EFI_SUCCESS;
}

EFI_TPL
EFIAPI
UserSpaceRaiseTpl (
  IN EFI_TPL  NewTpl
  )
{
  return (EFI_TPL)SysCall (
                    SysCallRaiseTpl,
                    1,
                    NewTpl
                    );
}

VOID
EFIAPI
UserSpaceRestoreTpl (
  IN EFI_TPL  NewTpl
  )
{
  SysCall (
    SysCallRestoreTpl,
    1,
    NewTpl
    );
}

EFI_STATUS
EFIAPI
UserSpaceAllocatePages (
  IN     EFI_ALLOCATE_TYPE     Type,
  IN     EFI_MEMORY_TYPE       MemoryType,
  IN     UINTN                 NumberOfPages,
  IN OUT EFI_PHYSICAL_ADDRESS  *Memory
  )
{
  EFI_STATUS  Status;

  Status = SysCall (
             SysCallAllocatePages,
             4,
             Type,
             EfiUserSpaceMemoryType,
             NumberOfPages,
             Memory
             );
  if (EFI_ERROR (Status)) {
    DEBUG ((DEBUG_ERROR, "UserSpace: Failed to allocate %d pages.\n", NumberOfPages));
  }

  return Status;
}

EFI_STATUS
EFIAPI
UserSpaceFreePages (
  IN EFI_PHYSICAL_ADDRESS  Memory,
  IN UINTN                 NumberOfPages
  )
{
  EFI_STATUS  Status;

  Status = SysCall (
             SysCallFreePages,
             2,
             NumberOfPages,
             Memory
             );
  if (EFI_ERROR (Status)) {
    DEBUG ((DEBUG_ERROR, "UserSpace: Failed to free %d pages.\n", NumberOfPages));
  }

  return Status;
}

EFI_STATUS
EFIAPI
UserSpaceGetMemoryMap (
  IN OUT UINTN                  *MemoryMapSize,
  IN OUT EFI_MEMORY_DESCRIPTOR  *MemoryMap,
     OUT UINTN                  *MapKey,
     OUT UINTN                  *DescriptorSize,
     OUT UINT32                 *DescriptorVersion
  )
{
  DEBUG ((DEBUG_ERROR, "UserSpace: GetMemoryMap is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
UserSpaceAllocatePool (
  IN  EFI_MEMORY_TYPE  PoolType,
  IN  UINTN            Size,
  OUT VOID             **Buffer
  )
{
  UINTN  CurrentUser;

  CurrentUser = (UINTN)SysCall (SysCallGetUserPageTable, 0);

  PoolType = GetMemoryType (CurrentUser);

  return CoreAllocatePool (PoolType, Size, Buffer);
}

EFI_STATUS
EFIAPI
UserSpaceFreePool (
  IN VOID  *Buffer
  )
{
  return CoreFreePool (Buffer);
}

EFI_STATUS
EFIAPI
UserSpaceCreateEvent (
  IN  UINT32            Type,
  IN  EFI_TPL           NotifyTpl,
  IN  EFI_EVENT_NOTIFY  NotifyFunction  OPTIONAL,
  IN  VOID              *NotifyContext  OPTIONAL,
  OUT EFI_EVENT         *Event
  )
{
  DEBUG ((DEBUG_ERROR, "UserSpace: CreateEvent is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
UserSpaceSetTimer (
  IN EFI_EVENT        UserEvent,
  IN EFI_TIMER_DELAY  Type,
  IN UINT64           TriggerTime
  )
{
  DEBUG ((DEBUG_ERROR, "UserSpace: SetTimer is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
UserSpaceWaitForEvent (
  IN  UINTN      NumberOfEvents,
  IN  EFI_EVENT  *UserEvents,
  OUT UINTN      *UserIndex
  )
{
  DEBUG ((DEBUG_ERROR, "UserSpace: WaitForEvent is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
UserSpaceSignalEvent (
  IN EFI_EVENT  UserEvent
  )
{
  DEBUG ((DEBUG_ERROR, "UserSpace: SignalEvent is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
UserSpaceCloseEvent (
  IN EFI_EVENT  UserEvent
  )
{
  DEBUG ((DEBUG_ERROR, "UserSpace: CloseEvent is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
UserSpaceCheckEvent (
  IN EFI_EVENT  UserEvent
  )
{
  DEBUG ((DEBUG_ERROR, "UserSpace: CheckEvent is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
UserSpaceInstallProtocolInterface (
  IN OUT EFI_HANDLE          *UserHandle,
  IN     EFI_GUID            *Protocol,
  IN     EFI_INTERFACE_TYPE  InterfaceType,
  IN     VOID                *Interface
  )
{
  DEBUG ((DEBUG_ERROR, "UserSpace: InstallProtocolInterface is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
UserSpaceReinstallProtocolInterface (
  IN EFI_HANDLE  UserHandle,
  IN EFI_GUID    *Protocol,
  IN VOID        *OldInterface,
  IN VOID        *NewInterface
  )
{
  DEBUG ((DEBUG_ERROR, "UserSpace: ReinstallProtocolInterface is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
UserSpaceUninstallProtocolInterface (
  IN EFI_HANDLE  UserHandle,
  IN EFI_GUID    *Protocol,
  IN VOID        *Interface
  )
{
  DEBUG ((DEBUG_ERROR, "UserSpace: UninstallProtocolInterface is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
UserSpaceHandleProtocol (
  IN  EFI_HANDLE  CoreUserHandle,
  IN  EFI_GUID    *Protocol,
  OUT VOID        **Interface
  )
{
  EFI_STATUS  Status;

  Status = SysCall (
             SysCallHandleProtocol,
             3,
             CoreUserHandle,
             Protocol,
             Interface
             );
  if (EFI_ERROR (Status)) {
    DEBUG ((DEBUG_ERROR, "UserSpace: Failed to get handle of protocol %g - %r\n", Protocol, Status));
    return Status;
  }

  return FixInterface (Protocol, Interface);
}

EFI_STATUS
EFIAPI
UserSpaceRegisterProtocolNotify (
  IN  EFI_GUID   *Protocol,
  IN  EFI_EVENT  Event,
  OUT VOID       **Registration
  )
{
  DEBUG ((DEBUG_ERROR, "UserSpace: RegisterProtocolNotify is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
UserSpaceLocateHandle (
  IN     EFI_LOCATE_SEARCH_TYPE  SearchType,
  IN     EFI_GUID                *Protocol   OPTIONAL,
  IN     VOID                    *SearchKey  OPTIONAL,
  IN OUT UINTN                   *BufferSize,
     OUT EFI_HANDLE              *Buffer
  )
{
  DEBUG ((DEBUG_ERROR, "UserSpace: LocateHandle is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
UserSpaceLocateDevicePath (
  IN     EFI_GUID                  *Protocol,
  IN OUT EFI_DEVICE_PATH_PROTOCOL  **DevicePath,
     OUT EFI_HANDLE                *Device
  )
{
  DEBUG ((DEBUG_ERROR, "UserSpace: LocateDevicePath is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
UserSpaceInstallConfigurationTable (
  IN EFI_GUID  *Guid,
  IN VOID      *Table
  )
{
  DEBUG ((DEBUG_ERROR, "UserSpace: InstallConfigurationTable is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
UserSpaceLoadImage (
  IN  BOOLEAN                   BootPolicy,
  IN  EFI_HANDLE                ParentImageHandle,
  IN  EFI_DEVICE_PATH_PROTOCOL  *FilePath,
  IN  VOID                      *SourceBuffer   OPTIONAL,
  IN  UINTN                     SourceSize,
  OUT EFI_HANDLE                *ImageHandle
  )
{
  DEBUG ((DEBUG_ERROR, "UserSpace: LoadImage is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
UserSpaceStartImage (
  IN  EFI_HANDLE  ImageHandle,
  OUT UINTN       *ExitDataSize,
  OUT CHAR16      **ExitData  OPTIONAL
  )
{
  DEBUG ((DEBUG_ERROR, "UserSpace: StartImage is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
UserSpaceExit (
  IN EFI_HANDLE  ImageHandle,
  IN EFI_STATUS  Status,
  IN UINTN       ExitDataSize,
  IN CHAR16      *ExitData  OPTIONAL
  )
{
  DEBUG ((DEBUG_ERROR, "UserSpace: Exit is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
UserSpaceUnloadImage (
  IN EFI_HANDLE  ImageHandle
  )
{
  DEBUG ((DEBUG_ERROR, "UserSpace: UnloadImage is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
UserSpaceExitBootServices (
  IN EFI_HANDLE  ImageHandle,
  IN UINTN       MapKey
  )
{
  DEBUG ((DEBUG_ERROR, "UserSpace: ExitBootServices is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
UserSpaceGetNextMonotonicCount (
  OUT UINT64  *Count
  )
{
  DEBUG ((DEBUG_ERROR, "UserSpace: GetNextMonotonicCount is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
UserSpaceStall (
  IN UINTN  Microseconds
  )
{
  DEBUG ((DEBUG_ERROR, "UserSpace: Stall is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
UserSpaceSetWatchdogTimer (
  IN UINTN   Timeout,
  IN UINT64  WatchdogCode,
  IN UINTN   DataSize,
  IN CHAR16  *WatchdogData OPTIONAL
  )
{
  DEBUG ((DEBUG_ERROR, "UserSpace: SetWatchdogTimer is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
UserSpaceConnectController (
  IN EFI_HANDLE                ControllerHandle,
  IN EFI_HANDLE                *DriverImageHandle    OPTIONAL,
  IN EFI_DEVICE_PATH_PROTOCOL  *RemainingDevicePath  OPTIONAL,
  IN BOOLEAN                   Recursive
  )
{
  DEBUG ((DEBUG_ERROR, "UserSpace: ConnectController is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
UserSpaceDisconnectController (
  IN EFI_HANDLE  ControllerHandle,
  IN EFI_HANDLE  DriverImageHandle  OPTIONAL,
  IN EFI_HANDLE  ChildHandle        OPTIONAL
  )
{
  DEBUG ((DEBUG_ERROR, "UserSpace: DisconnectController is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
UserSpaceOpenProtocol (
  IN  EFI_HANDLE  CoreUserHandle,
  IN  EFI_GUID    *Protocol,
  OUT VOID        **Interface OPTIONAL,
  IN  EFI_HANDLE  CoreImageHandle,
  IN  EFI_HANDLE  CoreControllerHandle,
  IN  UINT32      Attributes
  )
{
  EFI_STATUS  Status;

  Status = SysCall (
             SysCallOpenProtocol,
             6,
             CoreUserHandle,
             Protocol,
             Interface,
             CoreImageHandle,
             CoreControllerHandle,
             Attributes
             );
  if (EFI_ERROR (Status)) {
    return Status;
  }

  return (Interface != NULL) ? FixInterface (Protocol, Interface) : Status;
}

EFI_STATUS
EFIAPI
UserSpaceCloseProtocol (
  IN EFI_HANDLE  UserHandle,
  IN EFI_GUID    *Protocol,
  IN EFI_HANDLE  AgentHandle,
  IN EFI_HANDLE  ControllerHandle
  )
{
  return SysCall (
           SysCallCloseProtocol,
           4,
           UserHandle,
           Protocol,
           AgentHandle,
           ControllerHandle
           );
}

EFI_STATUS
EFIAPI
UserSpaceOpenProtocolInformation (
  IN  EFI_HANDLE                           UserHandle,
  IN  EFI_GUID                             *Protocol,
  OUT EFI_OPEN_PROTOCOL_INFORMATION_ENTRY  **EntryBuffer,
  OUT UINTN                                *EntryCount
  )
{
  DEBUG ((DEBUG_ERROR, "UserSpace: OpenProtocolInformation is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
UserSpaceProtocolsPerHandle (
  IN  EFI_HANDLE  UserHandle,
  OUT EFI_GUID    ***ProtocolBuffer,
  OUT UINTN       *ProtocolBufferCount
  )
{
  DEBUG ((DEBUG_ERROR, "UserSpace: ProtocolsPerHandle is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
UserSpaceLocateHandleBuffer (
  IN     EFI_LOCATE_SEARCH_TYPE  SearchType,
  IN     EFI_GUID                *Protocol OPTIONAL,
  IN     VOID                    *SearchKey OPTIONAL,
  IN OUT UINTN                   *NumberHandles,
     OUT EFI_HANDLE              **Buffer
  )
{
  EFI_STATUS  Status;
  EFI_STATUS  StatusBS;
  VOID        *Pool;
  UINTN       PoolSize;

  StatusBS = SysCall (
               SysCallLocateHandleBuffer,
               5,
               SearchType,
               Protocol,
               SearchKey,
               NumberHandles,
               Buffer
               );

  if ((!EFI_ERROR (StatusBS)) && (NumberHandles != NULL) && (*NumberHandles != 0)
    && (Buffer != NULL) && (*Buffer != NULL)) {
    PoolSize = *NumberHandles * sizeof (EFI_HANDLE *);

    Status = UserSpaceAllocatePool (EfiUserSpaceMemoryType, PoolSize, &Pool);
    if (EFI_ERROR (Status)) {
      return Status;
    }

    CopyMem (Pool, *Buffer, PoolSize);

    Status = UserSpaceFreePages (
               (EFI_PHYSICAL_ADDRESS)(UINTN)*Buffer,
               EFI_SIZE_TO_PAGES (PoolSize)
               );
    if (EFI_ERROR (Status)) {
      return Status;
    }

    *Buffer = Pool;
  }

  return StatusBS;
}

EFI_STATUS
EFIAPI
UserSpaceLocateProtocol (
  IN  EFI_GUID  *Protocol,
  IN  VOID      *CoreRegistration OPTIONAL,
  OUT VOID      **Interface
  )
{
  EFI_STATUS  Status;

  Status = SysCall (
             SysCallLocateProtocol,
             3,
             Protocol,
             CoreRegistration,
             Interface
             );
  if (EFI_ERROR (Status)) {
    DEBUG ((DEBUG_ERROR, "UserSpace: Failed to loacate protocol %g\n", Protocol));
    return Status;
  }

  return FixInterface (Protocol, Interface);
}

EFI_STATUS
EFIAPI
UserSpaceInstallMultipleProtocolInterfaces (
  IN OUT EFI_HANDLE  *Handle,
  ...
  )
{
  EFI_STATUS  Status;
  VA_LIST     Marker;
  VOID        **Arguments;
  UINTN       NumberOfArguments;
  UINTN       Index;

  VA_START (Marker, Handle);
  NumberOfArguments = 1;
  while (VA_ARG (Marker, VOID *) != NULL) {
    ++NumberOfArguments;
  }
  VA_END (Marker);

  Status = UserSpaceAllocatePool (
             EfiUserSpaceMemoryType,
             NumberOfArguments * sizeof (VOID *),
             (VOID **)&Arguments
             );
  if (EFI_ERROR (Status)) {
    return Status;
  }

  VA_START (Marker, Handle);
  for (Index = 0; Index < NumberOfArguments; ++Index) {
    Arguments[Index] = VA_ARG (Marker, VOID *);
  }
  VA_END (Marker);

  Status = SysCall (
             SysCallInstallMultipleProtocolInterfaces,
             3,
             Handle,
             NumberOfArguments,
             Arguments
             );

  UserSpaceFreePool (Arguments);
  return Status;
}

EFI_STATUS
EFIAPI
UserSpaceUninstallMultipleProtocolInterfaces (
  IN EFI_HANDLE  Handle,
  ...
  )
{
  DEBUG ((DEBUG_ERROR, "UserSpace: UninstallMultipleProtocolInterfaces is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
UserSpaceCalculateCrc32 (
  IN  VOID    *Data,
  IN  UINTN   DataSize,
  OUT UINT32  *Crc32
  )
{
  return SysCall (
           SysCallCalculateCrc32,
           3,
           Data,
           DataSize,
           Crc32
           );
}

EFI_STATUS
EFIAPI
UserSpaceCreateEventEx (
  IN  UINT32            Type,
  IN  EFI_TPL           NotifyTpl,
  IN  EFI_EVENT_NOTIFY  NotifyFunction  OPTIONAL,
  IN  CONST VOID        *NotifyContext  OPTIONAL,
  IN  CONST EFI_GUID    *EventGroup     OPTIONAL,
  OUT EFI_EVENT         *Event
  )
{
  DEBUG ((DEBUG_ERROR, "UserSpace: CreateEventEx is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
CoreUpdateProfile (
  IN EFI_PHYSICAL_ADDRESS   CallerAddress,
  IN MEMORY_PROFILE_ACTION  Action,
  IN EFI_MEMORY_TYPE        MemoryType,
  IN UINTN                  Size,       // Valid for AllocatePages/FreePages/AllocatePool
  IN VOID                   *Buffer,
  IN CHAR8                  *ActionString OPTIONAL
  )
{
  return EFI_SUCCESS;
}

VOID
InstallMemoryAttributesTableOnMemoryAllocation (
  IN EFI_MEMORY_TYPE  MemoryType
  )
{
  return;
}

BOOLEAN
EFIAPI
IsMemoryGuarded (
  IN EFI_PHYSICAL_ADDRESS  Address
  )
{
  return FALSE;
}

VOID *
CoreAllocatePoolPagesI (
  IN EFI_MEMORY_TYPE  PoolType,
  IN UINTN            NoPages,
  IN UINTN            Granularity,
  IN BOOLEAN          NeedGuard
  )
{
  EFI_PHYSICAL_ADDRESS  Memory;

  UserSpaceAllocatePages (AllocateAnyPages, EfiUserSpaceMemoryType, NoPages, &Memory);

  return (VOID *)(UINTN)Memory;
}

VOID
CoreFreePoolPagesI (
  IN EFI_MEMORY_TYPE       PoolType,
  IN EFI_PHYSICAL_ADDRESS  Memory,
  IN UINTN                 NoPages
  )
{
  UserSpaceFreePages (Memory, NoPages);
}

VOID
CoreFreePoolPagesWithGuard (
  IN EFI_MEMORY_TYPE       PoolType,
  IN EFI_PHYSICAL_ADDRESS  Memory,
  IN UINTN                 NoPages
  )
{
  CoreFreePoolPagesI (EfiUserSpaceMemoryType, Memory, NoPages);
}
