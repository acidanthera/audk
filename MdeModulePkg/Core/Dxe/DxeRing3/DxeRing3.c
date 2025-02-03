/** @file
  This driver constructs User space wrappers for the EFI_BOOT_SERVICES,
  EFI_RUNTIME_SERVICES and EFI_*_PROTOCOLs.

  Copyright (c) 2024 - 2025, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause

**/

#include <Uefi.h>
#include <Library/BaseMemoryLib.h>
#include <Library/MemoryPoolLib.h>
#include <Library/UefiBootServicesTableLib.h>
#include <Library/UefiRuntimeServicesTableLib.h>

#include "Ring3.h"

EFI_BOOT_SERVICES  mBootServices = {
  {
    EFI_BOOT_SERVICES_SIGNATURE,                                                             // Signature
    EFI_BOOT_SERVICES_REVISION,                                                              // Revision
    sizeof (EFI_BOOT_SERVICES),                                                              // HeaderSize
    0,                                                                                       // CRC32
    0                                                                                        // Reserved
  },
  (EFI_RAISE_TPL)UserSpaceRaiseTpl,                                                          // RaiseTPL
  (EFI_RESTORE_TPL)UserSpaceRestoreTpl,                                                      // RestoreTPL
  (EFI_ALLOCATE_PAGES)UserSpaceAllocatePages,                                                // AllocatePages
  (EFI_FREE_PAGES)UserSpaceFreePages,                                                        // FreePages
  (EFI_GET_MEMORY_MAP)UserSpaceGetMemoryMap,                                                 // GetMemoryMap
  (EFI_ALLOCATE_POOL)UserSpaceAllocatePool,                                                  // AllocatePool
  (EFI_FREE_POOL)UserSpaceFreePool,                                                          // FreePool
  (EFI_CREATE_EVENT)UserSpaceCreateEvent,                                                    // CreateEvent
  (EFI_SET_TIMER)UserSpaceSetTimer,                                                          // SetTimer
  (EFI_WAIT_FOR_EVENT)UserSpaceWaitForEvent,                                                 // WaitForEvent
  (EFI_SIGNAL_EVENT)UserSpaceSignalEvent,                                                    // SignalEvent
  (EFI_CLOSE_EVENT)UserSpaceCloseEvent,                                                      // CloseEvent
  (EFI_CHECK_EVENT)UserSpaceCheckEvent,                                                      // CheckEvent
  (EFI_INSTALL_PROTOCOL_INTERFACE)UserSpaceInstallProtocolInterface,                         // InstallProtocolInterface
  (EFI_REINSTALL_PROTOCOL_INTERFACE)UserSpaceReinstallProtocolInterface,                     // ReinstallProtocolInterface
  (EFI_UNINSTALL_PROTOCOL_INTERFACE)UserSpaceUninstallProtocolInterface,                     // UninstallProtocolInterface
  (EFI_HANDLE_PROTOCOL)UserSpaceHandleProtocol,                                              // HandleProtocol
  (VOID *)NULL,                                                                              // Reserved
  (EFI_REGISTER_PROTOCOL_NOTIFY)UserSpaceRegisterProtocolNotify,                             // RegisterProtocolNotify
  (EFI_LOCATE_HANDLE)UserSpaceLocateHandle,                                                  // LocateHandle
  (EFI_LOCATE_DEVICE_PATH)UserSpaceLocateDevicePath,                                         // LocateDevicePath
  (EFI_INSTALL_CONFIGURATION_TABLE)UserSpaceInstallConfigurationTable,                       // InstallConfigurationTable
  (EFI_IMAGE_LOAD)UserSpaceLoadImage,                                                        // LoadImage
  (EFI_IMAGE_START)UserSpaceStartImage,                                                      // StartImage
  (EFI_EXIT)UserSpaceExit,                                                                   // Exit
  (EFI_IMAGE_UNLOAD)UserSpaceUnloadImage,                                                    // UnloadImage
  (EFI_EXIT_BOOT_SERVICES)UserSpaceExitBootServices,                                         // ExitBootServices
  (EFI_GET_NEXT_MONOTONIC_COUNT)UserSpaceGetNextMonotonicCount,                              // GetNextMonotonicCount
  (EFI_STALL)UserSpaceStall,                                                                 // Stall
  (EFI_SET_WATCHDOG_TIMER)UserSpaceSetWatchdogTimer,                                         // SetWatchdogTimer
  (EFI_CONNECT_CONTROLLER)UserSpaceConnectController,                                        // ConnectController
  (EFI_DISCONNECT_CONTROLLER)UserSpaceDisconnectController,                                  // DisconnectController
  (EFI_OPEN_PROTOCOL)UserSpaceOpenProtocol,                                                  // OpenProtocol
  (EFI_CLOSE_PROTOCOL)UserSpaceCloseProtocol,                                                // CloseProtocol
  (EFI_OPEN_PROTOCOL_INFORMATION)UserSpaceOpenProtocolInformation,                           // OpenProtocolInformation
  (EFI_PROTOCOLS_PER_HANDLE)UserSpaceProtocolsPerHandle,                                     // ProtocolsPerHandle
  (EFI_LOCATE_HANDLE_BUFFER)UserSpaceLocateHandleBuffer,                                     // LocateHandleBuffer
  (EFI_LOCATE_PROTOCOL)UserSpaceLocateProtocol,                                              // LocateProtocol
  (EFI_INSTALL_MULTIPLE_PROTOCOL_INTERFACES)UserSpaceInstallMultipleProtocolInterfaces,      // InstallMultipleProtocolInterfaces
  (EFI_UNINSTALL_MULTIPLE_PROTOCOL_INTERFACES)UserSpaceUninstallMultipleProtocolInterfaces,  // UninstallMultipleProtocolInterfaces
  (EFI_CALCULATE_CRC32)UserSpaceCalculateCrc32,                                              // CalculateCrc32
  (EFI_COPY_MEM)CopyMem,                                                                     // CopyMem
  (EFI_SET_MEM)SetMem,                                                                       // SetMem
  (EFI_CREATE_EVENT_EX)UserSpaceCreateEventEx,                                               // CreateEventEx
};

EFI_RUNTIME_SERVICES  mRuntimeServices = {
  {
    EFI_RUNTIME_SERVICES_SIGNATURE,                                   // Signature
    EFI_RUNTIME_SERVICES_REVISION,                                    // Revision
    sizeof (EFI_RUNTIME_SERVICES),                                    // HeaderSize
    0,                                                                // CRC32
    0                                                                 // Reserved
  },
  (EFI_GET_TIME)UserSpaceGetTime,                                     // GetTime
  (EFI_SET_TIME)UserSpaceSetTime,                                     // SetTime
  (EFI_GET_WAKEUP_TIME)UserSpaceGetWakeupTime,                        // GetWakeupTime
  (EFI_SET_WAKEUP_TIME)UserSpaceSetWakeupTime,                        // SetWakeupTime
  (EFI_SET_VIRTUAL_ADDRESS_MAP)UserSpaceSetVirtualAddressMap,         // SetVirtualAddressMap
  (EFI_CONVERT_POINTER)UserSpaceConvertPointer,                       // ConvertPointer
  (EFI_GET_VARIABLE)UserSpaceGetVariable,                             // GetVariable
  (EFI_GET_NEXT_VARIABLE_NAME)UserSpaceGetNextVariableName,           // GetNextVariableName
  (EFI_SET_VARIABLE)UserSpaceSetVariable,                             // SetVariable
  (EFI_GET_NEXT_HIGH_MONO_COUNT)UserSpaceGetNextHighMonotonicCount,   // GetNextHighMonotonicCount
  (EFI_RESET_SYSTEM)UserSpaceResetSystem,                             // ResetSystem
  (EFI_UPDATE_CAPSULE)UserSpaceUpdateCapsule,                         // UpdateCapsule
  (EFI_QUERY_CAPSULE_CAPABILITIES)UserSpaceQueryCapsuleCapabilities,  // QueryCapsuleCapabilities
  (EFI_QUERY_VARIABLE_INFO)UserSpaceQueryVariableInfo                 // QueryVariableInfo
};

VOID
EFIAPI
UserSpaceEntryPoint (
 IN USER_SPACE_CALL_DATA  *Data
 );

typedef
EFI_STATUS
(EFIAPI *FUNCTION_0)(
  VOID
  );

typedef
EFI_STATUS
(EFIAPI *FUNCTION_1)(
  IN UINTN Argument1
  );

typedef
EFI_STATUS
(EFIAPI *FUNCTION_2)(
  IN UINTN Argument1,
  IN UINTN Argument2
  );

typedef
EFI_STATUS
(EFIAPI *FUNCTION_3)(
  IN UINTN Argument1,
  IN UINTN Argument2,
  IN UINTN Argument3
  );

typedef
EFI_STATUS
(EFIAPI *FUNCTION_4)(
  IN UINTN Argument1,
  IN UINTN Argument2,
  IN UINTN Argument3,
  IN UINTN Argument4
  );

typedef
EFI_STATUS
(EFIAPI *FUNCTION_5)(
  IN UINTN Argument1,
  IN UINTN Argument2,
  IN UINTN Argument3,
  IN UINTN Argument4,
  IN UINTN Argument5
  );

typedef
EFI_STATUS
(EFIAPI *FUNCTION_6)(
  IN UINTN Argument1,
  IN UINTN Argument2,
  IN UINTN Argument3,
  IN UINTN Argument4,
  IN UINTN Argument5,
  IN UINTN Argument6
  );

typedef
EFI_STATUS
(EFIAPI *FUNCTION_7)(
  IN UINTN Argument1,
  IN UINTN Argument2,
  IN UINTN Argument3,
  IN UINTN Argument4,
  IN UINTN Argument5,
  IN UINTN Argument6,
  IN UINTN Argument7
  );

typedef
EFI_STATUS
(EFIAPI *FUNCTION_8)(
  IN UINTN Argument1,
  IN UINTN Argument2,
  IN UINTN Argument3,
  IN UINTN Argument4,
  IN UINTN Argument5,
  IN UINTN Argument6,
  IN UINTN Argument7,
  IN UINTN Argument8
  );

VOID
EFIAPI
UserSpaceCall (
  IN USER_SPACE_CALL_DATA  *Data
  )
{
  EFI_STATUS  Status;
  FUNCTION_0  Function0;
  FUNCTION_1  Function1;
  FUNCTION_2  Function2;
  FUNCTION_3  Function3;
  FUNCTION_4  Function4;
  FUNCTION_5  Function5;
  FUNCTION_6  Function6;
  FUNCTION_7  Function7;
  FUNCTION_8  Function8;

  switch (Data->NumberOfArguments) {
    case 0:
      Function0 = (FUNCTION_0)Data->EntryPoint;
      Status = Function0 ();
      break;
    case 1:
      Function1 = (FUNCTION_1)Data->EntryPoint;
      Status = Function1 (Data->Arguments[0]);
      break;
    case 2:
      Function2 = (FUNCTION_2)Data->EntryPoint;
      Status = Function2 (Data->Arguments[0], Data->Arguments[1]);
      break;
    case 3:
      Function3 = (FUNCTION_3)Data->EntryPoint;
      Status = Function3 (Data->Arguments[0], Data->Arguments[1], Data->Arguments[2]);
      break;
    case 4:
      Function4 = (FUNCTION_4)Data->EntryPoint;
      Status = Function4 (Data->Arguments[0], Data->Arguments[1], Data->Arguments[2], Data->Arguments[3]);
      break;
    case 5:
      Function5 = (FUNCTION_5)Data->EntryPoint;
      Status = Function5 (Data->Arguments[0], Data->Arguments[1], Data->Arguments[2], Data->Arguments[3], Data->Arguments[4]);
      break;
    case 6:
      Function6 = (FUNCTION_6)Data->EntryPoint;
      Status = Function6 (Data->Arguments[0], Data->Arguments[1], Data->Arguments[2], Data->Arguments[3], Data->Arguments[4], Data->Arguments[5]);
      break;
    case 7:
      Function7 = (FUNCTION_7)Data->EntryPoint;
      Status = Function7 (Data->Arguments[0], Data->Arguments[1], Data->Arguments[2], Data->Arguments[3], Data->Arguments[4], Data->Arguments[5], Data->Arguments[6]);
      break;
    case 8:
      Function8 = (FUNCTION_8)Data->EntryPoint;
      Status = Function8 (Data->Arguments[0], Data->Arguments[1], Data->Arguments[2], Data->Arguments[3], Data->Arguments[4], Data->Arguments[5], Data->Arguments[6], Data->Arguments[7]);
      break;
    default:
      Status = EFI_UNSUPPORTED;
      break;
  }

  SysCall (SysCallReturnToCore, 1, Status);
}

EFI_STATUS
EFIAPI
UserSpaceInitialization (
  IN EFI_HANDLE        ImageHandle,
  IN EFI_SYSTEM_TABLE  *SystemTable
  )
{
  USER_SPACE_DATA  *UserSpaceData;

  UserSpaceData = (USER_SPACE_DATA *)SystemTable;

  UserSpaceData->EntryPoint      = (VOID *)UserSpaceEntryPoint;
  UserSpaceData->BootServices    = &mBootServices;
  UserSpaceData->RuntimeServices = &mRuntimeServices;

  gBS = &mBootServices;
  gRT = &mRuntimeServices;

  CoreInitializePool (FALSE);

  return EFI_SUCCESS;
}
