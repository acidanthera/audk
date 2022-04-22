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

RETURN_STATUS
PeCoffLoadImageForExecution (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  OUT    VOID                          *Destination,
  IN     UINT32                        DestinationSize,
  OUT PE_COFF_LOADER_RUNTIME_CONTEXT   *RuntimeContext OPTIONAL,
  IN  UINT32                           RuntimeContextSize
  )
{
  RETURN_STATUS Status;
  UINTN         BaseAddress;
  UINTN         SizeOfImage;

  Status = PeCoffLoadImage (Context, Destination, DestinationSize);
  if (RETURN_ERROR (Status)) {
    return Status;
  }

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
  // Flush the instruction cache so the image data is written before we execute
  // it.
  //
  InvalidateInstructionCacheRange ((VOID *) BaseAddress, SizeOfImage);

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
  // Flush the instruction cache so the image data is written before we execute
  // it.
  //
  InvalidateInstructionCacheRange (Image, ImageSize);

  return RETURN_SUCCESS;
}
