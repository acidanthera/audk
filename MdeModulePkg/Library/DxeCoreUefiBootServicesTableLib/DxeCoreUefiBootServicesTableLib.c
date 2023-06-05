/** @file
  Dummy instance of UEFI Boot Services Table Library for DxeCore.

  Relies on and sanity-checks that DxeCore provides the variables itself.

  Copyright (c) 2021, Marvin Häuser. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-2-Clause-Patent

**/

#include <Uefi.h>

#include <Library/UefiBootServicesTableLib.h>
#include <Library/DebugLib.h>

/**
  The constructor function sanity-checks the variables set by DxeCore.
  It will always return EFI_SUCCESS.

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
  // ASSERT that DxeCore provides the services correctly and in time
  //
  ASSERT (gImageHandle == ImageHandle);
  ASSERT (gImageHandle != NULL);
  ASSERT (gST == SystemTable);
  ASSERT (gST != NULL);
  ASSERT (gBS == gST->BootServices);
  ASSERT (gBS != NULL);

  return EFI_SUCCESS;
}
