/** @file
  UEFI Image Loader library implementation for PE/COFF and TE Images.

  Copyright (c) 2021, Marvin Häuser. All rights reserved.<BR>

  SPDX-License-Identifier: BSD-3-Clause
**/

#ifndef PE_COFF_SUPPORT_H_
#define PE_COFF_SUPPORT_H_

#include <Library/PeCoffLib2.h>
#include <Library/UefiImageLib.h>

UEFI_IMAGE_RECORD *
UefiImageLoaderGetImageRecordPeCoff (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  );

RETURN_STATUS
UefiImageDebugLocateImagePeCoff (
  OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  IN  UINTN                         Address
  );

RETURN_STATUS
UefiImageGetFixedAddressPeCoff (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  OUT    UINT64                        *Address
  );

VOID
UefiImageDebugPrintSegmentsPeCoff (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  );

#endif // PE_COFF_SUPPORT_H_
