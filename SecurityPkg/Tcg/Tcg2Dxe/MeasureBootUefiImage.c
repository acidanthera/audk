/** @file
  This module implements measuring UEFI Image for Tcg2 Protocol.

  Caution: This file requires additional review when modified.
  This driver will have external input - PE/COFF image.
  This external input must be validated carefully to avoid security issue like
  buffer overflow, integer overflow.

Copyright (c) 2015 - 2018, Intel Corporation. All rights reserved.<BR>
SPDX-License-Identifier: BSD-2-Clause-Patent

**/

#include <PiDxe.h>

#include <Library/BaseLib.h>
#include <Library/DebugLib.h>
#include <Library/BaseMemoryLib.h>
#include <Library/MemoryAllocationLib.h>
#include <Library/DevicePathLib.h>
#include <Library/UefiBootServicesTableLib.h>
#include <Library/UefiImageLib.h>
#include <Library/Tpm2CommandLib.h>
#include <Library/HashLib.h>

STATIC
EFI_STATUS
EFIAPI
UifiImageHashUpdate (
  IN UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *ImageContext,
  IN HASH_HANDLE                      HashHandle
  )
{
  return UefiImageHashImageDefault (
           ImageContext,
           (VOID *)HashHandle,
           (UEFI_IMAGE_LOADER_HASH_UPDATE)HashUpdate
           ) ? EFI_SUCCESS : EFI_ABORTED;
}

/**
  Measure UEFI image into TPM log based on its default image hashing.

  Caution: This function may receive untrusted input.
  UEFI image is external input, so this function will validate its data structure
  within this image buffer before use.

  Notes: UEFI image is checked by UefiImageLibLib UefiImageInitializeContext().

  @param[in]  PCRIndex       TPM PCR index
  @param[in]  ImageAddress   Start address of image buffer.
  @param[in]  ImageSize      Image size
  @param[out] DigestList     Digest list of this image.

  @retval EFI_SUCCESS            Successfully measure image.
  @retval EFI_OUT_OF_RESOURCES   No enough resource to measure image.
  @retval other error value
**/
EFI_STATUS
MeasureUefiImageAndExtend (
  IN  UINT32                PCRIndex,
  IN  EFI_PHYSICAL_ADDRESS  ImageAddress,
  IN  UINTN                 ImageSize,
  OUT TPML_DIGEST_VALUES    *DigestList
  )
{
  EFI_STATUS                       Status;
  HASH_HANDLE                      HashHandle;
  UEFI_IMAGE_LOADER_IMAGE_CONTEXT  ImageContext;

  Status = EFI_UNSUPPORTED;

  // FIXME: Can this somehow be abstracted away?
  //
  // Get information about the image being loaded
  //
  Status = UefiImageInitializeContextPreHash (
             &ImageContext,
             (VOID *) (UINTN) ImageAddress,
             (UINT32) ImageSize,
             UEFI_IMAGE_SOURCE_ALL,
             UefiImageOriginFv
             );
  if (EFI_ERROR (Status)) {
    //
    // The information can't be got from the invalid PeImage
    //
    DEBUG ((DEBUG_INFO, "Tcg2Dxe: PeImage invalid. Cannot retrieve image information.\n"));
    return Status;
  }

  //
  // UEFI Image Measurement
  //

  // Initialize a SHA hash context.

  Status = HashStart (&HashHandle);
  if (EFI_ERROR (Status)) {
    return Status;
  }

  // FIXME: This is just an ugly wrapper, the types should match (UINTN <-> VOID *), fix the libs
  Status = UifiImageHashUpdate (&ImageContext, HashHandle);
  if (EFI_ERROR (Status)) {
    return Status;
  }

  //
  // 17.  Finalize the SHA hash.
  //
  return HashCompleteAndExtend (HashHandle, PCRIndex, NULL, 0, DigestList);
}
