// FIXME: Docs, more general libclass for DXE?

#include <Base.h>

#include <Library/StandaloneMmMmuLib.h>

EFI_STATUS
SetMemoryRegionNoExec (
  IN EFI_PHYSICAL_ADDRESS  BaseAddress,
  IN UINT64                Length
  )
{
  return ArmSetMemoryRegionNoExec (BaseAddress, Length);
}

EFI_STATUS
ClearMemoryRegionNoExec (
  IN EFI_PHYSICAL_ADDRESS  BaseAddress,
  IN UINT64                Length
  )
{
  return ArmClearMemoryRegionNoExec (BaseAddress, Length);
}

EFI_STATUS
SetMemoryRegionReadOnly (
  IN EFI_PHYSICAL_ADDRESS  BaseAddress,
  IN UINT64                Length
  )
{
  return ArmSetMemoryRegionReadOnly (BaseAddress, Length);
}

EFI_STATUS
ClearMemoryRegionReadOnly (
  IN EFI_PHYSICAL_ADDRESS  BaseAddress,
  IN UINT64                Length
  )
{
  return ArmClearMemoryRegionReadOnly (BaseAddress, Length);
}
