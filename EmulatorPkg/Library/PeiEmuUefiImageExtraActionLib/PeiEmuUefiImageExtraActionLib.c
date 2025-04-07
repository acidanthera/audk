/** @file
  Provides services to perform additional actions to relocate and unload
  PE/Coff image for Emu environment specific purpose such as souce level debug.
  This version only works for PEI phase

Copyright (c) 2006 - 2009, Intel Corporation. All rights reserved.<BR>
Portions copyright (c) 2008 - 2011, Apple Inc. All rights reserved.<BR>
SPDX-License-Identifier: BSD-2-Clause-Patent

**/
#include <PiPei.h>
#include <Ppi/EmuThunk.h>
#include <Protocol/EmuThunk.h>

#include <Library/UefiImageLib.h>
#include <Library/PeiServicesLib.h>
#include <Library/DebugLib.h>
#include <Library/BaseLib.h>
#include <Library/UefiImageExtraActionLib.h>
#include <Library/EmuMagicPageLib.h>

//
// Cache of UnixThunk protocol
//
EMU_THUNK_PROTOCOL  *mThunk = NULL;

/**
  The function caches the pointer of the Unix thunk functions
  It will ASSERT() if Unix thunk ppi is not installed.

  @retval EFI_SUCCESS   WinNT thunk protocol is found and cached.

**/
EFI_STATUS
EFIAPI
EmuUefiImageGetThunkStucture (
  )
{
  EMU_THUNK_PPI  *ThunkPpi;
  EFI_STATUS     Status;

  //
  // Locate Unix ThunkPpi for retrieving standard output handle
  //
  Status = PeiServicesLocatePpi (
             &gEmuThunkPpiGuid,
             0,
             NULL,
             (VOID **)&ThunkPpi
             );
  ASSERT_EFI_ERROR (Status);

  EMU_MAGIC_PAGE ()->Thunk = (EMU_THUNK_PROTOCOL *)ThunkPpi->Thunk ();

  return EFI_SUCCESS;
}

/**
  Performs additional actions after a PE/COFF image has been loaded and relocated.

  If ImageContext is NULL, then ASSERT().

  @param  ImageContext  Pointer to the image context structure that describes the
                        PE/COFF image that has already been loaded and relocated.

**/
VOID
EFIAPI
UefiImageLoaderRelocateImageExtraAction (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *ImageContext
  )
{
  if (EMU_MAGIC_PAGE ()->Thunk == NULL) {
    EmuUefiImageGetThunkStucture ();
  }

  EMU_MAGIC_PAGE ()->Thunk->UefiImageRelocateImageExtraAction (ImageContext);
}

/**
  Performs additional actions just before a PE/COFF image is unloaded.  Any resources
  that were allocated by UefiImageLoaderRelocateImageExtraAction() must be freed.

  If ImageContext is NULL, then ASSERT().

  @param  ImageContext  Pointer to the image context structure that describes the
                        PE/COFF image that is being unloaded.

**/
VOID
EFIAPI
UefiImageLoaderUnloadImageExtraAction (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *ImageContext
  )
{
  if (EMU_MAGIC_PAGE ()->Thunk == NULL) {
    EmuUefiImageGetThunkStucture ();
  }

  EMU_MAGIC_PAGE ()->Thunk->UefiImageUnloadImageExtraAction (ImageContext);
}
