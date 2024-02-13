/** @file

  Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause

**/

#include <Uefi.h>
#include <Library/UefiBootServicesTableLib.h>

EFI_STATUS
EFIAPI
Ring3Call (
  IN VOID  *Dummy,
  IN VOID  *EntryPoint,
  IN EFI_HANDLE        ImageHandle,
  IN EFI_SYSTEM_TABLE  *SystemTable
  );

EFI_STATUS
EFIAPI
SysCall (
  IN UINT8 Type,
  ...
  );

EFI_STATUS
EFIAPI
Ring3EntryPoint (
  IN EFI_HANDLE        ImageHandle,
  IN EFI_SYSTEM_TABLE  *SystemTable
  )
{
  RING3_DATA  *Ring3Data;

  Ring3Data = (RING3_DATA *)SystemTable;

  Ring3Data->EntryPoint = (VOID *)Ring3Call;
  Ring3Data->BootServices = gBS;

  return EFI_SUCCESS;
}

EFI_STATUS
EFIAPI
Ring3Call (
  IN VOID  *Dummy,
  IN VOID  *EntryPoint,
  IN EFI_HANDLE        ImageHandle,
  IN EFI_SYSTEM_TABLE  *SystemTable
  )
{
  EFI_IMAGE_ENTRY_POINT  Function;

  Function = (EFI_IMAGE_ENTRY_POINT)EntryPoint;

  Function (ImageHandle, SystemTable);

  SysCall (SysCallReturnToCore);

  return EFI_UNSUPPORTED;
}
