#include <Uefi.h>

#include <Library/BaseMemoryLib.h>
#include <Library/DebugLib.h>

#include "Ring3.h"

EFI_STATUS
EFIAPI
Ring3GetTime (
  OUT  EFI_TIME                    *Time,
  OUT  EFI_TIME_CAPABILITIES       *Capabilities OPTIONAL
  )
{
  DEBUG ((DEBUG_ERROR, "Ring3: GetTime is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
Ring3SetTime (
  IN  EFI_TIME                     *Time
  )
{
  DEBUG ((DEBUG_ERROR, "Ring3: SetTime is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
Ring3GetWakeupTime (
  OUT BOOLEAN                     *Enabled,
  OUT BOOLEAN                     *Pending,
  OUT EFI_TIME                    *Time
  )
{
  DEBUG ((DEBUG_ERROR, "Ring3: GetWakeupTime is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
Ring3SetWakeupTime (
  IN  BOOLEAN                      Enable,
  IN  EFI_TIME                     *Time   OPTIONAL
  )
{
  DEBUG ((DEBUG_ERROR, "Ring3: SetWakeupTime is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
Ring3SetVirtualAddressMap (
  IN  UINTN                        MemoryMapSize,
  IN  UINTN                        DescriptorSize,
  IN  UINT32                       DescriptorVersion,
  IN  EFI_MEMORY_DESCRIPTOR        *VirtualMap
  )
{
  DEBUG ((DEBUG_ERROR, "Ring3: SetVirtualAddressMap is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
Ring3ConvertPointer (
  IN     UINTN                      DebugDisposition,
  IN OUT VOID                       **Address
  )
{
  DEBUG ((DEBUG_ERROR, "Ring3: ConvertPointer is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
Ring3GetVariable (
  IN     CHAR16                      *VariableName,
  IN     EFI_GUID                    *VendorGuid,
  OUT    UINT32                      *Attributes     OPTIONAL,
  IN OUT UINTN                       *DataSize,
  OUT    VOID                        *Data           OPTIONAL
  )
{
  return SysCall (
           SysCallGetVariable,
           VariableName,
           VendorGuid,
           Attributes,
           DataSize,
           Data
           );
}

EFI_STATUS
EFIAPI
Ring3GetNextVariableName (
  IN OUT UINTN                    *VariableNameSize,
  IN OUT CHAR16                   *VariableName,
  IN OUT EFI_GUID                 *VendorGuid
  )
{
  DEBUG ((DEBUG_ERROR, "Ring3: GetNextVariableName is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
Ring3SetVariable (
  IN  CHAR16                       *VariableName,
  IN  EFI_GUID                     *VendorGuid,
  IN  UINT32                       Attributes,
  IN  UINTN                        DataSize,
  IN  VOID                         *Data
  )
{
  DEBUG ((DEBUG_ERROR, "Ring3: SetVariable is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
Ring3GetNextHighMonotonicCount (
  OUT UINT32                  *HighCount
  )
{
  DEBUG ((DEBUG_ERROR, "Ring3: GetNextHighMonotonicCount is not supported\n"));

  return EFI_UNSUPPORTED;
}

VOID
EFIAPI
Ring3ResetSystem (
  IN EFI_RESET_TYPE           ResetType,
  IN EFI_STATUS               ResetStatus,
  IN UINTN                    DataSize,
  IN VOID                     *ResetData OPTIONAL
  )
{
  DEBUG ((DEBUG_ERROR, "Ring3: ResetSystem is not supported\n"));

  return;
}

EFI_STATUS
EFIAPI
Ring3UpdateCapsule (
  IN EFI_CAPSULE_HEADER     **CapsuleHeaderArray,
  IN UINTN                  CapsuleCount,
  IN EFI_PHYSICAL_ADDRESS   ScatterGatherList   OPTIONAL
  )
{
  DEBUG ((DEBUG_ERROR, "Ring3: UpdateCapsule is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
Ring3QueryCapsuleCapabilities (
  IN  EFI_CAPSULE_HEADER     **CapsuleHeaderArray,
  IN  UINTN                  CapsuleCount,
  OUT UINT64                 *MaximumCapsuleSize,
  OUT EFI_RESET_TYPE         *ResetType
  )
{
  DEBUG ((DEBUG_ERROR, "Ring3: QueryCapsuleCapabilities is not supported\n"));

  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
Ring3QueryVariableInfo (
  IN  UINT32            Attributes,
  OUT UINT64            *MaximumVariableStorageSize,
  OUT UINT64            *RemainingVariableStorageSize,
  OUT UINT64            *MaximumVariableSize
  )
{
  DEBUG ((DEBUG_ERROR, "Ring3: QueryVariableInfo is not supported\n"));

  return EFI_UNSUPPORTED;
}
