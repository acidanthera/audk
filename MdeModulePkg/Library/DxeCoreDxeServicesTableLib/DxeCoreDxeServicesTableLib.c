/** @file
  Dummy instance of DXE Services Table Library for DxeCore.

  Relies on and sanity-checks that DxeCore provides the variables itself.

  Copyright (c) 2021, Marvin Häuser. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-2-Clause-Patent

**/

#include <PiDxe.h>
#include <Guid/DxeServices.h>
#include <Library/DxeServicesTableLib.h>
#include <Library/DebugLib.h>
#include <Library/UefiLib.h>

/**
  The constructor function sanity-checks the variables set by DxeCore.
  It will always return EFI_SUCCESS.

  @param  ImageHandle   The firmware allocated handle for the EFI image.
  @param  SystemTable   A pointer to the EFI System Table.

  @retval EFI_SUCCESS   The constructor always returns EFI_SUCCESS.

**/
EFI_STATUS
EFIAPI
DxeServicesTableLibConstructor (
  IN EFI_HANDLE        ImageHandle,
  IN EFI_SYSTEM_TABLE  *SystemTable
  )
{
  EFI_STATUS       Status;
  EFI_DXE_SERVICES *DS;

  //
  // ASSERT that DxeCore provides the services correctly and in time
  //
  DEBUG_CODE_BEGIN ();
  Status = EfiGetSystemConfigurationTable (&gEfiDxeServicesTableGuid, (VOID **) &DS);
  ASSERT_EFI_ERROR (Status);
  ASSERT (gDS == DS);
  DEBUG_CODE_END ();
  ASSERT (gDS != NULL);

  return EFI_SUCCESS;
}
