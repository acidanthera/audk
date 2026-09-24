// FIXME: docs

#ifndef STANDALONE_MM_PROTECTION_LIB_H_
#define STANDALONE_MM_PROTECTION_LIB_H_

EFI_STATUS
SetMemoryRegionNoExec (
  IN EFI_PHYSICAL_ADDRESS  BaseAddress,
  IN UINT64                Length
  );

EFI_STATUS
ClearMemoryRegionNoExec (
  IN EFI_PHYSICAL_ADDRESS  BaseAddress,
  IN UINT64                Length
  );

EFI_STATUS
SetMemoryRegionReadOnly (
  IN EFI_PHYSICAL_ADDRESS  BaseAddress,
  IN UINT64                Length
  );

EFI_STATUS
ClearMemoryRegionReadOnly (
  IN EFI_PHYSICAL_ADDRESS  BaseAddress,
  IN UINT64                Length
  );

#endif // STANDALONE_MM_PROTECTION_LIB_H_
