/** @file
  UEFI Image Loader library implementation for UE Images.

  Copyright (c) 2021, Marvin Häuser. All rights reserved.<BR>

  SPDX-License-Identifier: BSD-3-Clause
**/

#define UEFI_IMAGE_LOADER_IMAGE_CONTEXT    UE_LOADER_IMAGE_CONTEXT
#define UEFI_IMAGE_LOADER_RUNTIME_CONTEXT  UE_LOADER_RUNTIME_CONTEXT

#include <Base.h>
#include <Uefi/UefiBaseType.h>
#include <Uefi/UefiSpec.h>

#include <Library/BaseLib.h>
#include <Library/BaseMemoryLib.h>
#include <Library/CacheMaintenanceLib.h>
#include <Library/DebugLib.h>
#include <Library/MemoryAllocationLib.h>
#include <Library/UeImageLib.h>
#include <Library/PcdLib.h>
#include <Library/UefiImageLib.h>

#include "../BasePeCoffLib2/BaseOverflow.h"

#include "UeSupport.h"

RETURN_STATUS
UefiImageInitializeContextPreHash (
  OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context,
  IN  CONST VOID                       *FileBuffer,
  IN  UINT32                           FileSize
  )
{
  return UeInitializeContextPreHash (Context, FileBuffer, FileSize);
}

RETURN_STATUS
UefiImageInitializeContextPostHash (
  OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  return UeInitializeContextPostHash (Context);
}

BOOLEAN
UefiImageHashImageDefault (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context,
  IN OUT VOID                             *HashContext,
  IN     UEFI_IMAGE_LOADER_HASH_UPDATE    HashUpdate
  )
{
  return UeHashImageDefault (Context, HashContext, HashUpdate);
}

RETURN_STATUS
UefiImageLoadImage (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context,
  OUT    VOID                             *Destination,
  IN     UINT32                           DestinationSize
  )
{
  return UeLoadImage (Context, Destination, DestinationSize);
}

BOOLEAN
UefiImageImageIsInplace (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  ASSERT (Context != NULL);
  //
  // FIXME: Implement
  //
  return FALSE;
}

RETURN_STATUS
UefiImageLoadImageInplace (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  return UeLoadImageInplace (Context);
}

RETURN_STATUS
UefiImageLoaderGetRuntimeContextSize (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context,
  OUT    UINT32                           *Size
  )
{
  return UeLoaderGetRuntimeContextSize (Context, Size);
}

RETURN_STATUS
UefiImageRelocateImage (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT    *Context,
  IN     UINT64                             BaseAddress,
  OUT    UEFI_IMAGE_LOADER_RUNTIME_CONTEXT  *RuntimeContext OPTIONAL,
  IN     UINT32                             RuntimeContextSize
  )
{
  return UeRelocateImage (
           Context,
           BaseAddress
           );
}

RETURN_STATUS
UefiImageRuntimeRelocateImage (
  IN OUT VOID                                     *Image,
  IN     UINT32                                   ImageSize,
  IN     UINT64                                   BaseAddress,
  IN     CONST UEFI_IMAGE_LOADER_RUNTIME_CONTEXT  *RuntimeContext
  )
{
  return UeRelocateImageForRuntime (
           Image,
           ImageSize,
           BaseAddress,
           RuntimeContext
           );
}

VOID
UefiImageDiscardSegments (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  ASSERT (Context != NULL);
  //
  // Anything discardable is not loaded in the first place.
  //
}

RETURN_STATUS
UefiImageGetSymbolsPath (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context,
  OUT    CONST CHAR8                      **SymbolsPath,
  OUT    UINT32                           *SymbolsPathSize
  )
{
  return UeGetSymbolsPath (Context, SymbolsPath, SymbolsPathSize);
}

RETURN_STATUS
UefiImageGetFirstCertificate (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context,
  OUT    CONST WIN_CERTIFICATE            **Certificate
  )
{
  return UeGetFirstCertificate (Context, Certificate);
}

RETURN_STATUS
UefiImageGetNextCertificate (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context,
  IN OUT CONST WIN_CERTIFICATE            **Certificate
  )
{
  return UeGetNextCertificate (Context, Certificate);
}

RETURN_STATUS
UefiImageGetHiiDataRva (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context,
  OUT    UINT32                           *HiiRva,
  OUT    UINT32                           *HiiSize
  )
{
  return UeGetHiiDataRva (Context, HiiRva, HiiSize);
}

UINT32
UefiImageGetEntryPointAddress (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  return UeGetAddressOfEntryPoint (Context);
}

UINT16
UefiImageGetMachine (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  return UeGetMachine (Context);
}

UINT16
UefiImageGetSubsystem (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  return UeGetSubsystem (Context);
}

UINT32
UefiImageGetSegmentAlignment (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  return UeGetSegmentAlignment (Context);
}

UINT32
UefiImageGetImageSize (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  return UeGetImageSize (Context);
}

UINT32
UefiImageGetImageSizeInplace (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  return UeGetImageSizeInplace (Context);
}

UINT64
UefiImageGetPreferredAddress (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  return UeGetPreferredAddress (Context);
}

BOOLEAN
UefiImageGetRelocsStripped (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  return UeGetRelocsStripped (Context);
}

UINTN
UefiImageLoaderGetImageAddress (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  return UeLoaderGetImageAddress (Context);
}

UEFI_IMAGE_RECORD *
UefiImageLoaderGetImageRecord (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  return UefiImageLoaderGetImageRecordUe (Context);
}

RETURN_STATUS
UefiImageDebugLocateImage (
  OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context,
  IN  UINTN                            Address
  )
{
  return UefiImageDebugLocateImageUe (Context, Address);
}

RETURN_STATUS
UefiImageGetFixedAddress (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context,
  OUT    UINT64                           *Address
  )
{
  return UefiImageGetFixedAddressUe (
           Context,
           Address
           );
}

VOID
UefiImageDebugPrintSegments (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  UefiImageDebugPrintSegmentsUe (Context);
}
