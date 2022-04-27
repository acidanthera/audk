/** @file
  UEFI Image Loader library implementation for PE/COFF and TE Images.

  Copyright (c) 2021, Marvin Häuser. All rights reserved.<BR>

  SPDX-License-Identifier: BSD-3-Clause
**/

#include <Base.h>

#include <Library/CacheMaintenanceLib.h>
#include <Library/DebugLib.h>
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

BOOLEAN
UefiImageImageIsInplace (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  )
{
  return PeCoffImageIsInplace (Context);
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
  RETURN_STATUS Status;
  UINTN         SizeOfImage;

  Status = PeCoffRelocateImageInplace (Context);
  if (RETURN_ERROR (Status)) {
    DEBUG_RAISE ();
    return Status;
  }

  SizeOfImage = PeCoffGetSizeOfImageInplace (Context);
  //
  // Flush the instruction cache so the image data is written before
  // execution.
  // FIXME: TE XIP
  //
  InvalidateInstructionCacheRange (
    (VOID *) Context->ImageBuffer,
    SizeOfImage
    );

  return RETURN_SUCCESS;
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

// FIXME: Check Subsystem here
RETURN_STATUS
UefiImageLoadImageForExecution (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT    *Context,
  OUT    VOID                               *Destination,
  IN     UINT32                             DestinationSize,
  OUT    UEFI_IMAGE_LOADER_RUNTIME_CONTEXT  *RuntimeContext OPTIONAL,
  IN     UINT32                             RuntimeContextSize
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
UefiImageRuntimeRelocateImage (
  IN OUT VOID                                     *Image,
  IN     UINT32                                   ImageSize,
  IN     UINT64                                   BaseAddress,
  IN     CONST UEFI_IMAGE_LOADER_RUNTIME_CONTEXT  *RuntimeContext
  )
{
  return PeCoffRuntimeRelocateImage (
           Image,
           ImageSize,
           BaseAddress,
           RuntimeContext
           );
}

RETURN_STATUS
UefiImageRuntimeRelocateImageForExecution (
  IN OUT VOID                                     *Image,
  IN     UINT32                                   ImageSize,
  IN     UINT64                                   BaseAddress,
  IN     CONST UEFI_IMAGE_LOADER_RUNTIME_CONTEXT  *RuntimeContext
  )
{
  RETURN_STATUS Status;
  //
  // Relocate the Image to the new address.
  //
  Status = PeCoffRuntimeRelocateImage (
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

VOID
UefiImageDiscardSegments (
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

// FIXME: Some image prints use this and some don't. Is this really needed?
RETURN_STATUS
UefiImageGetModuleNameFromSymbolsPath (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context,
  OUT    CHAR8                            *ModuleName,
  IN     UINT32                           ModuleNameSize
  )
{
  RETURN_STATUS Status;
  CONST CHAR8   *PdbPath;
  UINT32        PdbSize;
  UINTN         Index;
  UINTN         StartIndex;

  ASSERT (Context != NULL);
  ASSERT (ModuleName != NULL);
  ASSERT (ModuleNameSize >= 4);
  //
  // Retrieve the PDB path.
  //
  Status = PeCoffGetPdbPath (Context, &PdbPath, &PdbSize);
  if (RETURN_ERROR (Status)) {
    return Status;
  }
  //
  // Find the last component of the PDB path, which is the file containing the
  // debug symbols for the Image.
  //
  StartIndex = 0;
  for (Index = 0; PdbPath[Index] != '\0'; Index++) {
    if (PdbPath[Index] == '\\' || PdbPath[Index] == '/') {
      StartIndex = Index + 1;
    }
  }
  //
  // Extract the module name from the debug symbols file and ensure the correct
  // file extensions.
  //
  for (Index = 0; Index < ModuleNameSize - 4; Index++) {
    ModuleName[Index] = PdbPath[Index + StartIndex];
    if (ModuleName[Index] == '\0') {
      ModuleName[Index] = '.';
    }
    if (ModuleName[Index] == '.') {
      ModuleName[Index + 1] = 'e';
      ModuleName[Index + 2] = 'f';
      ModuleName[Index + 3] = 'i';
      Index += 4;
      break;
    }
  }
  //
  // Terminate the newly created module name string.
  //
  ModuleName[Index] = '\0';

  return RETURN_SUCCESS;
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
UefiImageGetEntryPointAddress (
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
UefiImageGetSegmentAlignment (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  return PeCoffGetSectionAlignment (Context);
}

UINT32
UefiImageGetImageSize (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  return PeCoffGetSizeOfImage (Context);
}

UINT32
UefiImageGetImageSizeInplace (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  return PeCoffGetSizeOfImageInplace (Context);
}

UINT64
UefiImageGetPreferredAddress (
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
UefiImageGetFixedAddress (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context,
  OUT    UINT64                           *Address
  )
{
  return PeCoffGetFixedAddress (Context, Address);
}

VOID
UefiImageDebugPrintSegments (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  PeCoffDebugPrintSectionTable (Context);
}
