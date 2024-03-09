/** @file
  This driver constructs Ring 3 wrappers for the EFI_BOOT_SERVICES.

  Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause

**/

#include <Uefi.h>

#include <Guid/MemoryProfile.h>

#include <Library/BaseMemoryLib.h>
#include <Library/DebugLib.h>

#include "Ring3.h"

BOOLEAN  mOnGuarding = FALSE;

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

    // TODO: Copy User changes to Core? Resembles InstallMultipleProtocolInterfaces().

    LoadedImage->Unload = NULL;

  } else if (CompareGuid (Protocol, &gEfiBlockIoProtocolGuid)) {

    BlockIo = (EFI_BLOCK_IO_PROTOCOL *)*Interface;

    BlockIo->Reset       = Ring3BlockIoReset;
    BlockIo->ReadBlocks  = Ring3BlockIoRead;
    BlockIo->WriteBlocks = Ring3BlockIoWrite;
    BlockIo->FlushBlocks = Ring3BlockIoFlush;

  } else if (CompareGuid (Protocol, &gEfiDiskIoProtocolGuid)) {

    DiskIo = (EFI_DISK_IO_PROTOCOL *)*Interface;

    DiskIo->ReadDisk  = Ring3DiskIoRead;
    DiskIo->WriteDisk = Ring3DiskIoWrite;

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

    Unicode->StriColl   = Ring3UnicodeStriColl;
    Unicode->MetaiMatch = Ring3UnicodeMetaiMatch;
    Unicode->StrLwr     = Ring3UnicodeStrLwr;
    Unicode->StrUpr     = Ring3UnicodeStrUpr;
    Unicode->FatToStr   = Ring3UnicodeFatToStr;
    Unicode->StrToFat   = Ring3UnicodeStrToFat;

  } else {
    return EFI_UNSUPPORTED;
  }

  return EFI_SUCCESS;
}

EFI_TPL
EFIAPI
Ring3RaiseTpl (
  IN EFI_TPL  NewTpl
  )
{
  return (EFI_TPL)SysCall (
                    SysCallRaiseTpl,
                    NewTpl
                    );
}

VOID
EFIAPI
Ring3RestoreTpl (
  IN EFI_TPL  NewTpl
  )
{
  SysCall (
    SysCallRestoreTpl,
    NewTpl
    );
}

EFI_STATUS
EFIAPI
Ring3AllocatePages (
  IN EFI_ALLOCATE_TYPE         Type,
  IN EFI_MEMORY_TYPE           MemoryType,
  IN UINTN                     NumberOfPages,
  IN OUT EFI_PHYSICAL_ADDRESS  *Memory
  )
{
  EFI_STATUS  Status;

  Status = SysCall (
             SysCallAllocatePages,
             Type,
             MemoryType,
             NumberOfPages,
             Memory
             );
  if (EFI_ERROR (Status)) {
    DEBUG ((DEBUG_ERROR, "Ring3: Failed to allocate %d pages.\n", NumberOfPages));
  }

  return Status;
}

EFI_STATUS
EFIAPI
Ring3FreePages (
  IN EFI_PHYSICAL_ADDRESS  Memory,
  IN UINTN                 NumberOfPages
  )
{
  EFI_STATUS  Status;

  Status = SysCall (
             SysCallFreePages,
             Memory,
             NumberOfPages
             );
  if (EFI_ERROR (Status)) {
    DEBUG ((DEBUG_ERROR, "Ring3: Failed to free %d pages.\n", NumberOfPages));
  }

  return Status;
}

EFI_STATUS
EFIAPI
Ring3GetMemoryMap (
  IN OUT UINTN                  *MemoryMapSize,
  IN OUT EFI_MEMORY_DESCRIPTOR  *MemoryMap,
  OUT UINTN                     *MapKey,
  OUT UINTN                     *DescriptorSize,
  OUT UINT32                    *DescriptorVersion
  )
{
  DEBUG ((DEBUG_ERROR, "Ring3: GetMemoryMap is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
Ring3CreateEvent (
  IN UINT32            Type,
  IN EFI_TPL           NotifyTpl,
  IN EFI_EVENT_NOTIFY  NotifyFunction  OPTIONAL,
  IN VOID              *NotifyContext  OPTIONAL,
  OUT EFI_EVENT        *Event
  )
{
  DEBUG ((DEBUG_ERROR, "Ring3: CreateEvent is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
Ring3SetTimer (
  IN EFI_EVENT        UserEvent,
  IN EFI_TIMER_DELAY  Type,
  IN UINT64           TriggerTime
  )
{
  DEBUG ((DEBUG_ERROR, "Ring3: SetTimer is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
Ring3WaitForEvent (
  IN UINTN      NumberOfEvents,
  IN EFI_EVENT  *UserEvents,
  OUT UINTN     *UserIndex
  )
{
  DEBUG ((DEBUG_ERROR, "Ring3: WaitForEvent is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
Ring3SignalEvent (
  IN EFI_EVENT  UserEvent
  )
{
  DEBUG ((DEBUG_ERROR, "Ring3: SignalEvent is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
Ring3CloseEvent (
  IN EFI_EVENT  UserEvent
  )
{
  DEBUG ((DEBUG_ERROR, "Ring3: CloseEvent is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
Ring3CheckEvent (
  IN EFI_EVENT  UserEvent
  )
{
  DEBUG ((DEBUG_ERROR, "Ring3: CheckEvent is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
Ring3InstallProtocolInterface (
  IN OUT EFI_HANDLE      *UserHandle,
  IN EFI_GUID            *Protocol,
  IN EFI_INTERFACE_TYPE  InterfaceType,
  IN VOID                *Interface
  )
{
  DEBUG ((DEBUG_ERROR, "Ring3: InstallProtocolInterface is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
Ring3ReinstallProtocolInterface (
  IN EFI_HANDLE  UserHandle,
  IN EFI_GUID    *Protocol,
  IN VOID        *OldInterface,
  IN VOID        *NewInterface
  )
{
  DEBUG ((DEBUG_ERROR, "Ring3: ReinstallProtocolInterface is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
Ring3UninstallProtocolInterface (
  IN EFI_HANDLE  UserHandle,
  IN EFI_GUID    *Protocol,
  IN VOID        *Interface
  )
{
  DEBUG ((DEBUG_ERROR, "Ring3: UninstallProtocolInterface is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
Ring3HandleProtocol (
  IN EFI_HANDLE  CoreUserHandle,
  IN EFI_GUID    *Protocol,
  OUT VOID       **Interface
  )
{
  EFI_STATUS  Status;

  Status = SysCall (
             SysCallHandleProtocol,
             CoreUserHandle,
             Protocol,
             Interface
             );
  if (EFI_ERROR (Status)) {
    DEBUG ((DEBUG_ERROR, "Ring3: Failed to get handle of protocol %g - %r\n", Protocol, Status));
    return Status;
  }

  return FixInterface (Protocol, Interface);
}

EFI_STATUS
EFIAPI
Ring3RegisterProtocolNotify (
  IN EFI_GUID   *Protocol,
  IN EFI_EVENT  Event,
  OUT  VOID     **Registration
  )
{
  DEBUG ((DEBUG_ERROR, "Ring3: RegisterProtocolNotify is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
Ring3LocateHandle (
  IN EFI_LOCATE_SEARCH_TYPE  SearchType,
  IN EFI_GUID                *Protocol   OPTIONAL,
  IN VOID                    *SearchKey  OPTIONAL,
  IN OUT UINTN               *BufferSize,
  OUT EFI_HANDLE             *Buffer
  )
{
  DEBUG ((DEBUG_ERROR, "Ring3: LocateHandle is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
Ring3LocateDevicePath (
  IN EFI_GUID                      *Protocol,
  IN OUT EFI_DEVICE_PATH_PROTOCOL  **DevicePath,
  OUT EFI_HANDLE                   *Device
  )
{
  DEBUG ((DEBUG_ERROR, "Ring3: LocateDevicePath is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
Ring3InstallConfigurationTable (
  IN EFI_GUID  *Guid,
  IN VOID      *Table
  )
{
  DEBUG ((DEBUG_ERROR, "Ring3: InstallConfigurationTable is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
Ring3LoadImage (
  IN BOOLEAN                   BootPolicy,
  IN EFI_HANDLE                ParentImageHandle,
  IN EFI_DEVICE_PATH_PROTOCOL  *FilePath,
  IN VOID                      *SourceBuffer   OPTIONAL,
  IN UINTN                     SourceSize,
  OUT EFI_HANDLE               *ImageHandle
  )
{
  DEBUG ((DEBUG_ERROR, "Ring3: LoadImage is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
Ring3StartImage (
  IN EFI_HANDLE  ImageHandle,
  OUT UINTN      *ExitDataSize,
  OUT CHAR16     **ExitData  OPTIONAL
  )
{
  DEBUG ((DEBUG_ERROR, "Ring3: StartImage is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
Ring3Exit (
  IN EFI_HANDLE  ImageHandle,
  IN EFI_STATUS  Status,
  IN UINTN       ExitDataSize,
  IN CHAR16      *ExitData  OPTIONAL
  )
{
  DEBUG ((DEBUG_ERROR, "Ring3: Exit is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
Ring3UnloadImage (
  IN EFI_HANDLE  ImageHandle
  )
{
  DEBUG ((DEBUG_ERROR, "Ring3: UnloadImage is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
Ring3ExitBootServices (
  IN EFI_HANDLE  ImageHandle,
  IN UINTN       MapKey
  )
{
  DEBUG ((DEBUG_ERROR, "Ring3: ExitBootServices is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
Ring3GetNextMonotonicCount (
  OUT UINT64  *Count
  )
{
  DEBUG ((DEBUG_ERROR, "Ring3: GetNextMonotonicCount is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
Ring3Stall (
  IN UINTN  Microseconds
  )
{
  DEBUG ((DEBUG_ERROR, "Ring3: Stall is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
Ring3SetWatchdogTimer (
  IN UINTN   Timeout,
  IN UINT64  WatchdogCode,
  IN UINTN   DataSize,
  IN CHAR16  *WatchdogData OPTIONAL
  )
{
  DEBUG ((DEBUG_ERROR, "Ring3: SetWatchdogTimer is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
Ring3ConnectController (
  IN  EFI_HANDLE                ControllerHandle,
  IN  EFI_HANDLE                *DriverImageHandle    OPTIONAL,
  IN  EFI_DEVICE_PATH_PROTOCOL  *RemainingDevicePath  OPTIONAL,
  IN  BOOLEAN                   Recursive
  )
{
  DEBUG ((DEBUG_ERROR, "Ring3: ConnectController is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
Ring3DisconnectController (
  IN  EFI_HANDLE  ControllerHandle,
  IN  EFI_HANDLE  DriverImageHandle  OPTIONAL,
  IN  EFI_HANDLE  ChildHandle        OPTIONAL
  )
{
  DEBUG ((DEBUG_ERROR, "Ring3: DisconnectController is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
Ring3OpenProtocol (
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
Ring3CloseProtocol (
  IN  EFI_HANDLE  UserHandle,
  IN  EFI_GUID    *Protocol,
  IN  EFI_HANDLE  AgentHandle,
  IN  EFI_HANDLE  ControllerHandle
  )
{
  return SysCall (
           SysCallCloseProtocol,
           UserHandle,
           Protocol,
           AgentHandle,
           ControllerHandle
           );
}

EFI_STATUS
EFIAPI
Ring3OpenProtocolInformation (
  IN  EFI_HANDLE                           UserHandle,
  IN  EFI_GUID                             *Protocol,
  OUT EFI_OPEN_PROTOCOL_INFORMATION_ENTRY  **EntryBuffer,
  OUT UINTN                                *EntryCount
  )
{
  DEBUG ((DEBUG_ERROR, "Ring3: OpenProtocolInformation is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
Ring3ProtocolsPerHandle (
  IN EFI_HANDLE  UserHandle,
  OUT EFI_GUID   ***ProtocolBuffer,
  OUT UINTN      *ProtocolBufferCount
  )
{
  DEBUG ((DEBUG_ERROR, "Ring3: ProtocolsPerHandle is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
Ring3LocateHandleBuffer (
  IN EFI_LOCATE_SEARCH_TYPE  SearchType,
  IN EFI_GUID                *Protocol OPTIONAL,
  IN VOID                    *SearchKey OPTIONAL,
  IN OUT UINTN               *NumberHandles,
  OUT EFI_HANDLE             **Buffer
  )
{
  return SysCall (
           SysCallLocateHandleBuffer,
           SearchType,
           Protocol,
           SearchKey,
           NumberHandles,
           Buffer
           );
}

EFI_STATUS
EFIAPI
Ring3LocateProtocol (
  IN  EFI_GUID  *Protocol,
  IN  VOID      *CoreRegistration OPTIONAL,
  OUT VOID      **Interface
  )
{
  EFI_STATUS  Status;

  Status = SysCall (
             SysCallLocateProtocol,
             Protocol,
             CoreRegistration,
             Interface
             );
  if (EFI_ERROR (Status)) {
    DEBUG ((DEBUG_ERROR, "Ring3: Failed to loacate protocol %g\n", Protocol));
    return Status;
  }

  return FixInterface (Protocol, Interface);
}

EFI_STATUS
EFIAPI
Ring3InstallMultipleProtocolInterfaces (
  IN OUT EFI_HANDLE  *Handle,
  ...
  )
{
  VA_LIST Marker;
  VOID    *Argument;
  VOID    *ArgList[MAX_LIST];
  UINTN   Index;

  VA_START (Marker, Handle);
  for (Index = 0; Index < MAX_LIST; ++Index) {
    Argument       = VA_ARG (Marker, VOID *);
    ArgList[Index] = Argument;

    if (Argument == NULL) {
      break;
    }
  }
  VA_END (Marker);

  if (Index == MAX_LIST) {
    DEBUG ((DEBUG_ERROR, "Ring3: Too many arguments\n"));
    return EFI_INVALID_PARAMETER;
  }

  return SysCall (
           SysCallInstallMultipleProtocolInterfaces,
           Handle,
           ArgList
           );
}

EFI_STATUS
EFIAPI
Ring3UninstallMultipleProtocolInterfaces (
  IN EFI_HANDLE  Handle,
  ...
  )
{
  DEBUG ((DEBUG_ERROR, "Ring3: UninstallMultipleProtocolInterfaces is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
Ring3CalculateCrc32 (
  IN  VOID                              *Data,
  IN  UINTN                             DataSize,
  OUT UINT32                            *Crc32
  )
{
  DEBUG ((DEBUG_ERROR, "Ring3: CalculateCrc32 is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
Ring3CreateEventEx (
  IN UINT32            Type,
  IN EFI_TPL           NotifyTpl,
  IN EFI_EVENT_NOTIFY  NotifyFunction  OPTIONAL,
  IN CONST VOID        *NotifyContext  OPTIONAL,
  IN CONST EFI_GUID    *EventGroup     OPTIONAL,
  OUT EFI_EVENT        *Event
  )
{
  DEBUG ((DEBUG_ERROR, "Ring3: CreateEventEx is not supported\n"));

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

  Ring3AllocatePages (AllocateAnyPages, EfiRing3MemoryType, NoPages, &Memory);

  return (VOID *)Memory;
}

VOID
CoreFreePoolPagesI (
  IN EFI_MEMORY_TYPE       PoolType,
  IN EFI_PHYSICAL_ADDRESS  Memory,
  IN UINTN                 NoPages
  )
{
  Ring3FreePages (Memory, NoPages);
}

VOID
CoreFreePoolPagesWithGuard (
  IN EFI_MEMORY_TYPE       PoolType,
  IN EFI_PHYSICAL_ADDRESS  Memory,
  IN UINTN                 NoPages
  )
{
  CoreFreePoolPagesI (PoolType, Memory, NoPages);
}
