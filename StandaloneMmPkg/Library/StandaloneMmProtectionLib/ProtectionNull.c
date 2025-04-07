#include <Base.h>

EFI_STATUS
SetMemoryRegionNoExec (
  IN EFI_PHYSICAL_ADDRESS  BaseAddress,
  IN UINT64                Length
  )
{
  (VOID)BaseAddress;
  (VOID)Length;

  return RETURN_SUCCESS;
}

EFI_STATUS
ClearMemoryRegionNoExec (
  IN EFI_PHYSICAL_ADDRESS  BaseAddress,
  IN UINT64                Length
  )
{
  (VOID)BaseAddress;
  (VOID)Length;

  return RETURN_SUCCESS;
}

EFI_STATUS
SetMemoryRegionReadOnly (
  IN EFI_PHYSICAL_ADDRESS  BaseAddress,
  IN UINT64                Length
  )
{
  (VOID)BaseAddress;
  (VOID)Length;

  return RETURN_SUCCESS;
}

EFI_STATUS
ClearMemoryRegionReadOnly (
  IN EFI_PHYSICAL_ADDRESS  BaseAddress,
  IN UINT64                Length
  )
{
  (VOID)BaseAddress;
  (VOID)Length;

  return RETURN_SUCCESS;
}
