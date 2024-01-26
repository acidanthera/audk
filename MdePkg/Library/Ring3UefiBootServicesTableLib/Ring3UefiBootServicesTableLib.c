/** @file
  This library constructs Ring 3 wrappers for the EFI_BOOT_SERVICES.

  Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause

**/

#include <Uefi.h>

#include <Library/BaseMemoryLib.h>
#include <Library/DebugLib.h>

#include "Ring3.h"

EFI_BOOT_SERVICES  mBootServices = {
  {
    EFI_BOOT_SERVICES_SIGNATURE,                                                          // Signature
    EFI_BOOT_SERVICES_REVISION,                                                           // Revision
    sizeof (EFI_BOOT_SERVICES),                                                           // HeaderSize
    0,                                                                                    // CRC32
    0                                                                                     // Reserved
  },
  (EFI_RAISE_TPL)Ring3RaiseTpl,                                                            // RaiseTPL
  (EFI_RESTORE_TPL)Ring3RestoreTpl,                                                        // RestoreTPL
  (EFI_ALLOCATE_PAGES)Ring3AllocatePages,                                                  // AllocatePages
  (EFI_FREE_PAGES)Ring3FreePages,                                                          // FreePages
  (EFI_GET_MEMORY_MAP)Ring3GetMemoryMap,                                                   // GetMemoryMap
  (EFI_ALLOCATE_POOL)Ring3AllocatePool,                                                    // AllocatePool
  (EFI_FREE_POOL)Ring3FreePool,                                                            // FreePool
  (EFI_CREATE_EVENT)Ring3CreateEvent,                                                      // CreateEvent
  (EFI_SET_TIMER)Ring3SetTimer,                                                            // SetTimer
  (EFI_WAIT_FOR_EVENT)Ring3WaitForEvent,                                                   // WaitForEvent
  (EFI_SIGNAL_EVENT)Ring3SignalEvent,                                                      // SignalEvent
  (EFI_CLOSE_EVENT)Ring3CloseEvent,                                                        // CloseEvent
  (EFI_CHECK_EVENT)Ring3CheckEvent,                                                        // CheckEvent
  (EFI_INSTALL_PROTOCOL_INTERFACE)Ring3InstallProtocolInterface,                           // InstallProtocolInterface
  (EFI_REINSTALL_PROTOCOL_INTERFACE)Ring3ReinstallProtocolInterface,                       // ReinstallProtocolInterface
  (EFI_UNINSTALL_PROTOCOL_INTERFACE)Ring3UninstallProtocolInterface,                       // UninstallProtocolInterface
  (EFI_HANDLE_PROTOCOL)Ring3HandleProtocol,                                                // HandleProtocol
  (VOID *)NULL,                                                                            // Reserved
  (EFI_REGISTER_PROTOCOL_NOTIFY)Ring3RegisterProtocolNotify,                               // RegisterProtocolNotify
  (EFI_LOCATE_HANDLE)Ring3LocateHandle,                                                    // LocateHandle
  (EFI_LOCATE_DEVICE_PATH)Ring3LocateDevicePath,                                           // LocateDevicePath
  (EFI_INSTALL_CONFIGURATION_TABLE)Ring3InstallConfigurationTable,                         // InstallConfigurationTable
  (EFI_IMAGE_LOAD)Ring3LoadImage,                                                          // LoadImage
  (EFI_IMAGE_START)Ring3StartImage,                                                        // StartImage
  (EFI_EXIT)Ring3Exit,                                                                     // Exit
  (EFI_IMAGE_UNLOAD)Ring3UnloadImage,                                                      // UnloadImage
  (EFI_EXIT_BOOT_SERVICES)Ring3ExitBootServices,                                           // ExitBootServices
  (EFI_GET_NEXT_MONOTONIC_COUNT)Ring3GetNextMonotonicCount,                                // GetNextMonotonicCount
  (EFI_STALL)Ring3Stall,                                                                   // Stall
  (EFI_SET_WATCHDOG_TIMER)Ring3SetWatchdogTimer,                                           // SetWatchdogTimer
  (EFI_CONNECT_CONTROLLER)Ring3ConnectController,                                          // ConnectController
  (EFI_DISCONNECT_CONTROLLER)Ring3DisconnectController,                                    // DisconnectController
  (EFI_OPEN_PROTOCOL)Ring3OpenProtocol,                                                    // OpenProtocol
  (EFI_CLOSE_PROTOCOL)Ring3CloseProtocol,                                                  // CloseProtocol
  (EFI_OPEN_PROTOCOL_INFORMATION)Ring3OpenProtocolInformation,                             // OpenProtocolInformation
  (EFI_PROTOCOLS_PER_HANDLE)Ring3ProtocolsPerHandle,                                       // ProtocolsPerHandle
  (EFI_LOCATE_HANDLE_BUFFER)Ring3LocateHandleBuffer,                                       // LocateHandleBuffer
  (EFI_LOCATE_PROTOCOL)Ring3LocateProtocol,                                                // LocateProtocol
  (EFI_INSTALL_MULTIPLE_PROTOCOL_INTERFACES)Ring3InstallMultipleProtocolInterfaces,        // InstallMultipleProtocolInterfaces
  (EFI_UNINSTALL_MULTIPLE_PROTOCOL_INTERFACES)Ring3UninstallMultipleProtocolInterfaces,    // UninstallMultipleProtocolInterfaces
  (EFI_CALCULATE_CRC32)Ring3CalculateCrc32,                                                // CalculateCrc32
  (EFI_COPY_MEM)CopyMem,                                                                   // CopyMem
  (EFI_SET_MEM)SetMem,                                                                     // SetMem
  (EFI_CREATE_EVENT_EX)Ring3CreateEventEx                                                  // CreateEventEx
};

EFI_BOOT_SERVICES  *gBS     = &mBootServices;
EFI_BOOT_SERVICES  *mCoreBS = NULL;

/**
  The function constructs Ring 3 wrappers for the EFI_BOOT_SERVICES.

  @param  ImageHandle   The firmware allocated handle for the EFI image.
  @param  SystemTable   A pointer to the EFI System Table.

  @retval EFI_SUCCESS   The constructor always returns EFI_SUCCESS.

**/
EFI_STATUS
EFIAPI
UefiBootServicesTableLibConstructor (
  IN EFI_HANDLE        ImageHandle,
  IN EFI_SYSTEM_TABLE  *SystemTable
  )
{
  //
  // Cache pointer to the EFI Boot Services Table
  //
  mCoreBS = (EFI_BOOT_SERVICES *)SysCall (
                                   0,
                                   (UINTN)SystemTable + OFFSET_OF (EFI_SYSTEM_TABLE, BootServices)
                                   );
  ASSERT (mCoreBS != NULL);
  DEBUG ((DEBUG_ERROR, "User: BootServices = 0x%lx\n", (UINTN)mCoreBS));

  return EFI_SUCCESS;
}

EFI_TPL
EFIAPI
Ring3RaiseTpl (
  IN EFI_TPL  NewTpl
  )
{
  return NewTpl;
}

VOID
EFIAPI
Ring3RestoreTpl (
  IN EFI_TPL  NewTpl
  )
{

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
  return EFI_SUCCESS;
}

EFI_STATUS
EFIAPI
Ring3FreePages (
  IN EFI_PHYSICAL_ADDRESS  Memory,
  IN UINTN                 NumberOfPages
  )
{
  return EFI_SUCCESS;
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
  return EFI_SUCCESS;
}

EFI_STATUS
EFIAPI
Ring3AllocatePool (
  IN EFI_MEMORY_TYPE  PoolType,
  IN UINTN            Size,
  OUT VOID            **Buffer
  )
{
  return EFI_SUCCESS;
}

EFI_STATUS
EFIAPI
Ring3FreePool (
  IN VOID  *Buffer
  )
{
  return EFI_SUCCESS;
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
  return EFI_SUCCESS;
}

EFI_STATUS
EFIAPI
Ring3SetTimer (
  IN EFI_EVENT        UserEvent,
  IN EFI_TIMER_DELAY  Type,
  IN UINT64           TriggerTime
  )
{
  return EFI_SUCCESS;
}

EFI_STATUS
EFIAPI
Ring3WaitForEvent (
  IN UINTN      NumberOfEvents,
  IN EFI_EVENT  *UserEvents,
  OUT UINTN     *UserIndex
  )
{
  return EFI_SUCCESS;
}

EFI_STATUS
EFIAPI
Ring3SignalEvent (
  IN EFI_EVENT  UserEvent
  )
{
  return EFI_SUCCESS;
}

EFI_STATUS
EFIAPI
Ring3CloseEvent (
  IN EFI_EVENT  UserEvent
  )
{
  return EFI_SUCCESS;
}

EFI_STATUS
EFIAPI
Ring3CheckEvent (
  IN EFI_EVENT  UserEvent
  )
{
  return EFI_SUCCESS;
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
  return EFI_SUCCESS;
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
  return EFI_SUCCESS;
}

EFI_STATUS
EFIAPI
Ring3UninstallProtocolInterface (
  IN EFI_HANDLE  UserHandle,
  IN EFI_GUID    *Protocol,
  IN VOID        *Interface
  )
{
  return EFI_SUCCESS;
}

EFI_STATUS
EFIAPI
Ring3HandleProtocol (
  IN EFI_HANDLE  UserHandle,
  IN EFI_GUID    *Protocol,
  OUT VOID       **Interface
  )
{
  return EFI_SUCCESS;
}

EFI_STATUS
EFIAPI
Ring3RegisterProtocolNotify (
  IN EFI_GUID   *Protocol,
  IN EFI_EVENT  Event,
  OUT  VOID     **Registration
  )
{
  return EFI_SUCCESS;
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
  return EFI_SUCCESS;
}

EFI_STATUS
EFIAPI
Ring3LocateDevicePath (
  IN EFI_GUID                      *Protocol,
  IN OUT EFI_DEVICE_PATH_PROTOCOL  **DevicePath,
  OUT EFI_HANDLE                   *Device
  )
{
  return EFI_SUCCESS;
}

EFI_STATUS
EFIAPI
Ring3InstallConfigurationTable (
  IN EFI_GUID  *Guid,
  IN VOID      *Table
  )
{
  return EFI_SUCCESS;
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
  return EFI_SUCCESS;
}

EFI_STATUS
EFIAPI
Ring3StartImage (
  IN EFI_HANDLE  ImageHandle,
  OUT UINTN      *ExitDataSize,
  OUT CHAR16     **ExitData  OPTIONAL
  )
{
  return EFI_SUCCESS;
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
  return EFI_SUCCESS;
}

EFI_STATUS
EFIAPI
Ring3UnloadImage (
  IN EFI_HANDLE  ImageHandle
  )
{
  return EFI_SUCCESS;
}

EFI_STATUS
EFIAPI
Ring3ExitBootServices (
  IN EFI_HANDLE  ImageHandle,
  IN UINTN       MapKey
  )
{
  return EFI_SUCCESS;
}

EFI_STATUS
EFIAPI
Ring3GetNextMonotonicCount (
  OUT UINT64  *Count
  )
{
  return EFI_SUCCESS;
}

EFI_STATUS
EFIAPI
Ring3Stall (
  IN UINTN  Microseconds
  )
{
  return EFI_SUCCESS;
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
  return EFI_SUCCESS;
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
  return EFI_SUCCESS;
}

EFI_STATUS
EFIAPI
Ring3DisconnectController (
  IN  EFI_HANDLE  ControllerHandle,
  IN  EFI_HANDLE  DriverImageHandle  OPTIONAL,
  IN  EFI_HANDLE  ChildHandle        OPTIONAL
  )
{
  return EFI_SUCCESS;
}

EFI_STATUS
EFIAPI
Ring3OpenProtocol (
  IN  EFI_HANDLE  UserHandle,
  IN  EFI_GUID    *Protocol,
  OUT VOID        **Interface OPTIONAL,
  IN  EFI_HANDLE  ImageHandle,
  IN  EFI_HANDLE  ControllerHandle,
  IN  UINT32      Attributes
  )
{
  return EFI_SUCCESS;
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
  return EFI_SUCCESS;
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
  return EFI_SUCCESS;
}

EFI_STATUS
EFIAPI
Ring3ProtocolsPerHandle (
  IN EFI_HANDLE  UserHandle,
  OUT EFI_GUID   ***ProtocolBuffer,
  OUT UINTN      *ProtocolBufferCount
  )
{
  return EFI_SUCCESS;
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
  return EFI_SUCCESS;
}

EFI_STATUS
EFIAPI
Ring3LocateProtocol (
  IN  EFI_GUID  *Protocol,
  IN  VOID      *Registration OPTIONAL,
  OUT VOID      **Interface
  )
{
  EFI_STATUS Status;

  Status = (EFI_STATUS)SysCall (
                         (UINTN)mCoreBS + OFFSET_OF (EFI_BOOT_SERVICES, LocateProtocol),
                         Protocol,
                         Registration,
                         Interface
                         );

  return Status;
}

EFI_STATUS
EFIAPI
Ring3InstallMultipleProtocolInterfaces (
  IN OUT EFI_HANDLE  *Handle,
  ...
  )
{
  return EFI_SUCCESS;
}

EFI_STATUS
EFIAPI
Ring3UninstallMultipleProtocolInterfaces (
  IN EFI_HANDLE  Handle,
  ...
  )
{
  return EFI_SUCCESS;
}

EFI_STATUS
EFIAPI
Ring3CalculateCrc32 (
  IN  VOID                              *Data,
  IN  UINTN                             DataSize,
  OUT UINT32                            *Crc32
  )
{
  return EFI_SUCCESS;
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
  return EFI_SUCCESS;
}
