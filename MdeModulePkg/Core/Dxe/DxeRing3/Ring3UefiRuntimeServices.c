/** @file
  This driver constructs User space wrappers for the EFI_RUNTIME_SERVICES.

  Copyright (c) 2024 - 2025, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause

**/

#include <Uefi.h>

#include <Library/BaseMemoryLib.h>
#include <Library/DebugLib.h>

#include "Ring3.h"

EFI_STATUS
EFIAPI
UserSpaceGetTime (
  OUT EFI_TIME               *Time,
  OUT EFI_TIME_CAPABILITIES  *Capabilities OPTIONAL
  )
{
  DEBUG ((DEBUG_ERROR, "UserSpace: GetTime is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
UserSpaceSetTime (
  IN EFI_TIME  *Time
  )
{
  DEBUG ((DEBUG_ERROR, "UserSpace: SetTime is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
UserSpaceGetWakeupTime (
  OUT BOOLEAN   *Enabled,
  OUT BOOLEAN   *Pending,
  OUT EFI_TIME  *Time
  )
{
  DEBUG ((DEBUG_ERROR, "UserSpace: GetWakeupTime is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
UserSpaceSetWakeupTime (
  IN BOOLEAN   Enable,
  IN EFI_TIME  *Time   OPTIONAL
  )
{
  DEBUG ((DEBUG_ERROR, "UserSpace: SetWakeupTime is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
UserSpaceSetVirtualAddressMap (
  IN UINTN                  MemoryMapSize,
  IN UINTN                  DescriptorSize,
  IN UINT32                 DescriptorVersion,
  IN EFI_MEMORY_DESCRIPTOR  *VirtualMap
  )
{
  DEBUG ((DEBUG_ERROR, "UserSpace: SetVirtualAddressMap is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
UserSpaceConvertPointer (
  IN     UINTN  DebugDisposition,
  IN OUT VOID   **Address
  )
{
  DEBUG ((DEBUG_ERROR, "UserSpace: ConvertPointer is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
UserSpaceGetVariable (
  IN     CHAR16    *VariableName,
  IN     EFI_GUID  *VendorGuid,
     OUT UINT32    *Attributes     OPTIONAL,
  IN OUT UINTN     *DataSize,
     OUT VOID      *Data           OPTIONAL
  )
{
  return SysCall (
           SysCallGetVariable,
           5,
           VariableName,
           VendorGuid,
           Attributes,
           DataSize,
           Data
           );
}

EFI_STATUS
EFIAPI
UserSpaceGetNextVariableName (
  IN OUT UINTN     *VariableNameSize,
  IN OUT CHAR16    *VariableName,
  IN OUT EFI_GUID  *VendorGuid
  )
{
  DEBUG ((DEBUG_ERROR, "UserSpace: GetNextVariableName is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
UserSpaceSetVariable (
  IN CHAR16    *VariableName,
  IN EFI_GUID  *VendorGuid,
  IN UINT32    Attributes,
  IN UINTN     DataSize,
  IN VOID      *Data
  )
{
  DEBUG ((DEBUG_ERROR, "UserSpace: SetVariable is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
UserSpaceGetNextHighMonotonicCount (
  OUT UINT32  *HighCount
  )
{
  DEBUG ((DEBUG_ERROR, "UserSpace: GetNextHighMonotonicCount is not supported\n"));

  return EFI_UNSUPPORTED;
}

VOID
EFIAPI
UserSpaceResetSystem (
  IN EFI_RESET_TYPE  ResetType,
  IN EFI_STATUS      ResetStatus,
  IN UINTN           DataSize,
  IN VOID            *ResetData OPTIONAL
  )
{
  DEBUG ((DEBUG_ERROR, "UserSpace: ResetSystem is not supported\n"));

  return;
}

EFI_STATUS
EFIAPI
UserSpaceUpdateCapsule (
  IN EFI_CAPSULE_HEADER    **CapsuleHeaderArray,
  IN UINTN                 CapsuleCount,
  IN EFI_PHYSICAL_ADDRESS  ScatterGatherList   OPTIONAL
  )
{
  DEBUG ((DEBUG_ERROR, "UserSpace: UpdateCapsule is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
UserSpaceQueryCapsuleCapabilities (
  IN  EFI_CAPSULE_HEADER  **CapsuleHeaderArray,
  IN  UINTN               CapsuleCount,
  OUT UINT64              *MaximumCapsuleSize,
  OUT EFI_RESET_TYPE      *ResetType
  )
{
  DEBUG ((DEBUG_ERROR, "UserSpace: QueryCapsuleCapabilities is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
UserSpaceQueryVariableInfo (
  IN  UINT32  Attributes,
  OUT UINT64  *MaximumVariableStorageSize,
  OUT UINT64  *RemainingVariableStorageSize,
  OUT UINT64  *MaximumVariableSize
  )
{
  DEBUG ((DEBUG_ERROR, "UserSpace: QueryVariableInfo is not supported\n"));

  return EFI_UNSUPPORTED;
}
