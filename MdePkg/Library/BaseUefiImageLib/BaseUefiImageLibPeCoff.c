/** @file
  UEFI Image Loader library implementation for PE/COFF and TE Images.

  Copyright (c) 2021, Marvin Häuser. All rights reserved.<BR>

  SPDX-License-Identifier: BSD-3-Clause
**/

#include <Base.h>

#include <Library/PeCoffLib2.h>
#include <Library/UefiImageLib.h>

RETURN_STATUS
UefiImageInitializeContext (
  OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context,
  IN  CONST VOID                       *FileBuffer,
  IN  UINT32                           FileSize
  )
{
  return PeCoffInitializeContext (Context, FileBuffer, FileSize);
}

BOOLEAN
UefiImageHashImageDefault (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context,
  IN OUT VOID                             *HashContext,
  IN     UEFI_IMAGE_LOADER_HASH_UPDATE    HashUpdate
  )
{
  return PeCoffHashImageAuthenticode (Context, HashContext, HashUpdate);
}

RETURN_STATUS
UefiImageLoaderGetDestinationSize (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context,
  OUT    UINT32                           *Size
  )
{
  return PeCoffLoaderGetDestinationSize (Context, Size);
}

RETURN_STATUS
UefiImageLoadImage (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context,
  OUT    VOID                          *Destination,
  IN     UINT32                        DestinationSize
  )
{
  return PeCoffLoadImage (Context, Destination, DestinationSize);
}

RETURN_STATUS
UefiImageLoadImageInplace (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  return PeCoffLoadImageInplace (Context);
}

RETURN_STATUS
UefiImageRelocateImageInplaceForExecution (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  return PeCoffRelocateImageInplaceForExecution (Context);
}

RETURN_STATUS
UefiImageLoaderGetRuntimeContextSize (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context,
  OUT    UINT32                           *Size
  )
{
  return PeCoffLoaderGetRuntimeContextSize (Context, Size);
}

RETURN_STATUS
UefiImageRelocateImage (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT    *Context,
  IN     UINT64                             BaseAddress,
  OUT    UEFI_IMAGE_LOADER_RUNTIME_CONTEXT  *RuntimeContext OPTIONAL,
  IN     UINT32                             RuntimeContextSize
  )
{
  return PeCoffRelocateImage (
           Context,
           BaseAddress,
           RuntimeContext,
           RuntimeContextSize
           );
}

RETURN_STATUS
UefiImageLoadImageForExecution (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT    *Context,
  OUT    VOID                               *Destination,
  IN     UINT32                             DestinationSize,
  OUT    UEFI_IMAGE_LOADER_RUNTIME_CONTEXT  *RuntimeContext OPTIONAL,
  IN     UINT32                             RuntimeContextSize
  )
{
  return PeCoffLoadImageForExecution (
           Context,
           Destination,
           DestinationSize,
           RuntimeContext,
           RuntimeContextSize
           );
}

RETURN_STATUS
UefiImageRelocateImageForRuntime (
  IN OUT VOID                                     *Image,
  IN     UINT32                                   ImageSize,
  IN     UINT64                                   BaseAddress,
  IN     CONST UEFI_IMAGE_LOADER_RUNTIME_CONTEXT  *RuntimeContext
  )
{
  return PeCoffRelocateImageForRuntime (
           Image,
           ImageSize,
           BaseAddress,
           RuntimeContext
           );
}

RETURN_STATUS
UefiImageRelocateImageForRuntimeExecution (
  IN OUT VOID                                     *Image,
  IN     UINT32                                   ImageSize,
  IN     UINT64                                   BaseAddress,
  IN     CONST UEFI_IMAGE_LOADER_RUNTIME_CONTEXT  *RuntimeContext
  )
{
  return PeCoffRelocateImageForRuntimeExecution (
           Image,
           ImageSize,
           BaseAddress,
           RuntimeContext
           );
}

VOID
UefiImageDiscardSections (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  PeCoffDiscardSections (Context);
}

RETURN_STATUS
UefiImageGetSymbolsPath (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context,
  OUT    CONST CHAR8                      **SymbolsPath,
  OUT    UINT32                           *SymbolsPathSize
  )
{
  return PeCoffGetPdbPath (Context, SymbolsPath, SymbolsPathSize);
}

RETURN_STATUS
UefiImageGetModuleNameFromSymbolsPath (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context,
  OUT    CHAR8                            *ModuleName,
  IN     UINT32                           ModuleNameSize
  )
{
  return PeCoffGetModuleNameFromPdb (Context, ModuleName, ModuleNameSize);
}

RETURN_STATUS
UefiImageGetFirstCertificate (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context,
  OUT    CONST WIN_CERTIFICATE            **Certificate
  )
{
  return PeCoffGetFirstCertificate (Context, Certificate);
}

RETURN_STATUS
UefiImageGetNextCertificate (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context,
  IN OUT CONST WIN_CERTIFICATE            **Certificate
  )
{
  return PeCoffGetNextCertificate (Context, Certificate);
}

RETURN_STATUS
UefiImageGetHiiDataRva (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context,
  OUT    UINT32                           *HiiRva,
  OUT    UINT32                           *HiiSize
  )
{
  return PeCoffGetHiiDataRva (Context, HiiRva, HiiSize);
}

UINT32
UefiImageGetAddressOfEntryPoint (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  return PeCoffGetAddressOfEntryPoint (Context);
}

UINT16
UefiImageGetMachine (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  return PeCoffGetMachine (Context);
}

UINT16
UefiImageGetSubsystem (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  return PeCoffGetSubsystem (Context);
}

UINT32
UefiImageGetSectionAlignment (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  return PeCoffGetSectionAlignment (Context);
}

UINT32
UefiImageGetSizeOfImage (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  return PeCoffGetSizeOfImage (Context);
}

UINT64
UefiImageGetImageBase (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  return PeCoffGetImageBase (Context);
}

BOOLEAN
UefiImageGetRelocsStripped (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  return PeCoffGetRelocsStripped (Context);
}

UINTN
UefiImageLoaderGetImageAddress (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  return PeCoffLoaderGetImageAddress (Context);
}

UINTN
UefiImageLoaderGetRvctSymbolsBaseAddress (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  return PeCoffLoaderGetRvctSymbolsBaseAddress (Context);
}

UINTN
UefiImageLoaderGetImageEntryPoint (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  return PeCoffLoaderGetImageEntryPoint (Context);
}

UEFI_IMAGE_IMAGE_RECORD *
UefiImageLoaderGetImageRecord (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  return PeCoffLoaderGetImageRecord (Context);
}

RETURN_STATUS
UefiImageDebugLocateImage (
  OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context,
  IN  UINTN                            Address
  )
{
  return PeCoffDebugLocateImage (Context, Address);
}

RETURN_STATUS
UefiImageGetAssignedAddress (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context,
  OUT    UINT64                           *Address
  )
{
  return PeCoffGetAssignedAddress (Context, Address);
}

VOID
UefiImageDebugPrintSegments (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  PeCoffDebugPrintSectionTable (Context);
}
