/** @file

  Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
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
  (EFI_ALLOCATE_POOL)CoreAllocatePool,                                                     // AllocatePool
  (EFI_FREE_POOL)CoreFreePool,                                                             // FreePool
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
  (EFI_CREATE_EVENT_EX)Ring3CreateEventEx,                                                 // CreateEventEx
};

EFI_RUNTIME_SERVICES  mRuntimeServices = {
  {
    EFI_RUNTIME_SERVICES_SIGNATURE,                               // Signature
    EFI_RUNTIME_SERVICES_REVISION,                                // Revision
    sizeof (EFI_RUNTIME_SERVICES),                                // HeaderSize
    0,                                                            // CRC32
    0                                                             // Reserved
  },
  (EFI_GET_TIME)Ring3GetTime,                                     // GetTime
  (EFI_SET_TIME)Ring3SetTime,                                     // SetTime
  (EFI_GET_WAKEUP_TIME)Ring3GetWakeupTime,                        // GetWakeupTime
  (EFI_SET_WAKEUP_TIME)Ring3SetWakeupTime,                        // SetWakeupTime
  (EFI_SET_VIRTUAL_ADDRESS_MAP)Ring3SetVirtualAddressMap,         // SetVirtualAddressMap
  (EFI_CONVERT_POINTER)Ring3ConvertPointer,                       // ConvertPointer
  (EFI_GET_VARIABLE)Ring3GetVariable,                             // GetVariable
  (EFI_GET_NEXT_VARIABLE_NAME)Ring3GetNextVariableName,           // GetNextVariableName
  (EFI_SET_VARIABLE)Ring3SetVariable,                             // SetVariable
  (EFI_GET_NEXT_HIGH_MONO_COUNT)Ring3GetNextHighMonotonicCount,   // GetNextHighMonotonicCount
  (EFI_RESET_SYSTEM)Ring3ResetSystem,                             // ResetSystem
  (EFI_UPDATE_CAPSULE)Ring3UpdateCapsule,                         // UpdateCapsule
  (EFI_QUERY_CAPSULE_CAPABILITIES)Ring3QueryCapsuleCapabilities,  // QueryCapsuleCapabilities
  (EFI_QUERY_VARIABLE_INFO)Ring3QueryVariableInfo                 // QueryVariableInfo
};

VOID
EFIAPI
Ring3EntryPoint (
 IN RING3_CALL_DATA *Data
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
Ring3Call (
  IN RING3_CALL_DATA *Data
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

  SysCall (SysCallReturnToCore, Status);
}

EFI_STATUS
EFIAPI
Ring3Initialization (
  IN EFI_HANDLE        ImageHandle,
  IN EFI_SYSTEM_TABLE  *SystemTable
  )
{
  RING3_DATA  *Ring3Data;

  Ring3Data = (RING3_DATA *)SystemTable;

  Ring3Data->EntryPoint      = (VOID *)Ring3EntryPoint;
  Ring3Data->BootServices    = &mBootServices;
  Ring3Data->RuntimeServices = &mRuntimeServices;

  gBS = &mBootServices;
  gRT = &mRuntimeServices;

  CoreInitializePool ();

  return EFI_SUCCESS;
}
