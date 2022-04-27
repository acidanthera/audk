/** @file
  Implements APIs to load PE/COFF Images for subsequent execution.

  Copyright (c) 2020 - 2021, Marvin Häuser. All rights reserved.<BR>
  Copyright (c) 2020, Vitaly Cheptsov. All rights reserved.<BR>
  Copyright (c) 2020, ISP RAS. All rights reserved.<BR>

  SPDX-License-Identifier: BSD-3-Clause
**/

#include <Base.h>

#include <Library/DebugLib.h>
#include <Library/CacheMaintenanceLib.h>
#include <Library/PcdLib.h>
#include <Library/PeCoffLib2.h>

#include "BasePeCoffLib2Internals.h"

RETURN_STATUS
PeCoffRelocateImageInplaceForExecution (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  )
{
  RETURN_STATUS Status;
  UINT64        ImageBase;
  UINTN         NewBase;
  UINTN         SizeOfImage;

  Status = PeCoffLoadImageInplaceNoBase (Context);
  if (RETURN_ERROR (Status)) {
    DEBUG_RAISE ();
    return Status;
  }

  ImageBase = PeCoffGetImageBase (Context);
  NewBase   = PeCoffLoaderGetImageAddress (Context);

  // FIXME: Generally push this check to the callers?
  if (ImageBase != NewBase) {
    Status = PeCoffRelocateImage (Context, NewBase, NULL, 0);
    if (RETURN_ERROR (Status)) {
      DEBUG_RAISE ();
      return Status;
    }

    SizeOfImage = PeCoffGetSizeOfImageInplace (Context);
    //
    // Flush the instruction cache so the image data is written before
    // execution.
    //
    InvalidateInstructionCacheRange (
      (VOID *) Context->ImageBuffer,
      SizeOfImage
      );
  }

  return RETURN_SUCCESS;
}
