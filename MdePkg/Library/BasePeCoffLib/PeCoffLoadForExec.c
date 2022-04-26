/** @file
  Implements APIs to load PE/COFF Images for subsequent execution.

  Copyright (c) 2020 - 2021, Marvin Häuser. All rights reserved.<BR>
  Copyright (c) 2020, Vitaly Cheptsov. All rights reserved.<BR>
  Copyright (c) 2020, ISP RAS. All rights reserved.<BR>

  SPDX-License-Identifier: BSD-3-Clause
**/

#include <Base.h>

#include <Library/PeCoffLib.h>
#include <Library/CacheMaintenanceLib.h>

#include "BasePeCoffLibInternals.h"

// FIXME: Check Machine / Subsystem here?
RETURN_STATUS
PeCoffLoadImageForExecution (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT    *Context,
  OUT    VOID                            *Destination,
  IN     UINT32                          DestinationSize,
  OUT    PE_COFF_LOADER_RUNTIME_CONTEXT  *RuntimeContext OPTIONAL,
  IN     UINT32                          RuntimeContextSize
  )
{
  RETURN_STATUS Status;
  UINTN         BaseAddress;
  UINTN         SizeOfImage;
  //
  // Load the Image into the memory space.
  //
  Status = PeCoffLoadImage (Context, Destination, DestinationSize);
  if (RETURN_ERROR (Status)) {
    return Status;
  }
  //
  // Relocate the Image to the address it has been loaded to.
  //
  BaseAddress = PeCoffLoaderGetImageAddress (Context);
  Status = PeCoffRelocateImage (
             Context,
             BaseAddress,
             RuntimeContext,
             RuntimeContextSize
             );
  if (RETURN_ERROR (Status)) {
    return Status;
  }

  SizeOfImage = PeCoffGetSizeOfImage (Context);
  //
  // Flush the instruction cache so the image data is written before execution.
  //
  InvalidateInstructionCacheRange ((VOID *) BaseAddress, SizeOfImage);

  return RETURN_SUCCESS;
}

RETURN_STATUS
PeCoffRelocateImageInplaceForExecution (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  IN     UINT64                        BaseAddress
  )
{
  RETURN_STATUS Status;
  UINT64        ImageBase;
  UINTN         SizeOfImage;

  Status = PeCoffLoadImageInplaceNoBase (Context);
  if (RETURN_ERROR (Status)) {
    return Status;
  }

  ImageBase = PeCoffGetImageBase (Context);

  // FIXME: Generally push this check to the callers?
  if (ImageBase != BaseAddress) {
    Status = PeCoffRelocateImage (Context, BaseAddress, NULL, 0);
    if (RETURN_ERROR (Status)) {
      return Status;
    }

    SizeOfImage = PeCoffGetSizeOfImage (Context);
    //
    // Flush the instruction cache so the image data is written before
    // execution.
    //
    InvalidateInstructionCacheRange ((VOID *) BaseAddress, SizeOfImage);
  }

  return RETURN_SUCCESS;
}

RETURN_STATUS
PeCoffRelocateImageForRuntimeExecution (
  IN OUT VOID                                  *Image,
  IN     UINT32                                ImageSize,
  IN     UINT64                                BaseAddress,
  IN     CONST PE_COFF_LOADER_RUNTIME_CONTEXT  *RuntimeContext
  )
{
  RETURN_STATUS Status;
  //
  // Relocate the Image to the new address.
  //
  Status = PeCoffRelocateImageForRuntime (
             Image,
             ImageSize,
             BaseAddress,
             RuntimeContext
             );
  if (RETURN_ERROR (Status)) {
    return Status;
  }
  //
  // Flush the instruction cache so the image data is written before execution.
  //
  InvalidateInstructionCacheRange (Image, ImageSize);

  return RETURN_SUCCESS;
}
