/** @file
  Support for functions common to all Image formats.

  Copyright (c) 2021, Marvin Häuser. All rights reserved.<BR>

  SPDX-License-Identifier: BSD-3-Clause
**/

#include <Base.h>
#include <Uefi/UefiBaseType.h>
#include <Uefi/UefiSpec.h>

#include <Library/CacheMaintenanceLib.h>
#include <Library/DebugLib.h>
#include <Library/UefiImageLib.h>

#include "../BasePeCoffLib2/BaseOverflow.h"

RETURN_STATUS
UefiImageLoaderGetDestinationSize (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context,
  OUT    UINT32                           *Size
  )
{
  BOOLEAN Overflow;
  UINT32  AlignedSize;
  UINT32  SectionAlignment;

  ASSERT (Context != NULL);
  ASSERT (Size != NULL);

  AlignedSize      = UefiImageGetImageSize (Context);
  SectionAlignment = UefiImageGetSegmentAlignment (Context);
  //
  // If the Image section alignment is larger than the UEFI page size,
  // sufficient alignment cannot be guaranteed by the allocater. Allodate an
  // additional Image page to be able to manually align within the buffer.
  //
  if (SectionAlignment > EFI_PAGE_SIZE) {
    Overflow = BaseOverflowAddU32 (
                 AlignedSize,
                 SectionAlignment - EFI_PAGE_SIZE,
                 &AlignedSize
                 );
    if (Overflow) {
      return RETURN_UNSUPPORTED;
    }
  }

  *Size = AlignedSize;

  return RETURN_SUCCESS;
}

UINTN
UefiImageLoaderGetImageEntryPoint (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  UINTN  ImageAddress;
  UINT32 EntryPointAddress;

  ASSERT (Context != NULL);
  ASSERT (Context->ImageBuffer != NULL);

  ImageAddress      = UefiImageLoaderGetImageAddress (Context);
  EntryPointAddress = UefiImageGetEntryPointAddress (Context);

  return ImageAddress + EntryPointAddress;
}

RETURN_STATUS
UefiImageRelocateImageInplaceForExecution (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  RETURN_STATUS Status;
  UINTN         ImageAddress;
  UINTN         ImageSize;

  Status = UefiImageRelocateImageInplace (Context);
  if (RETURN_ERROR (Status)) {
    DEBUG_RAISE ();
    return Status;
  }

  ImageAddress = UefiImageLoaderGetImageAddress (Context);
  ImageSize    = UefiImageGetImageSizeInplace (Context);
  //
  // Flush the instruction cache so the image data is written before
  // execution.
  // FIXME: TE XIP
  //
  InvalidateInstructionCacheRange ((VOID *) ImageAddress, ImageSize);

  return RETURN_SUCCESS;
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
  Status = UefiImageLoadImage (Context, Destination, DestinationSize);
  if (RETURN_ERROR (Status)) {
    return Status;
  }
  //
  // Relocate the Image to the address it has been loaded to.
  //
  BaseAddress = UefiImageLoaderGetImageAddress (Context);
  Status = UefiImageRelocateImage (
             Context,
             BaseAddress,
             RuntimeContext,
             RuntimeContextSize
             );
  if (RETURN_ERROR (Status)) {
    return Status;
  }

  SizeOfImage = UefiImageGetImageSize (Context);
  //
  // Flush the instruction cache so the image data is written before execution.
  //
  InvalidateInstructionCacheRange ((VOID *) BaseAddress, SizeOfImage);

  return RETURN_SUCCESS;
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
  Status = UefiImageRuntimeRelocateImage (
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

// FIXME: Some image prints use this and some don't. Is this really needed?
RETURN_STATUS
UefiImageGetModuleNameFromSymbolsPath (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context,
  OUT    CHAR8                            *ModuleName,
  IN     UINT32                           ModuleNameSize
  )
{
  RETURN_STATUS Status;
  CONST CHAR8   *SymbolsPath;
  UINT32        SymbolsPathSize;
  UINTN         Index;
  UINTN         StartIndex;

  ASSERT (Context != NULL);
  ASSERT (ModuleName != NULL);
  ASSERT (3 <= ModuleNameSize);

  Status = UefiImageGetSymbolsPath (
             Context,
             &SymbolsPath,
             &SymbolsPathSize
             );
  if (RETURN_ERROR (Status)) {
    return Status;
  }
  //
  // Find the last component of the symbols path, which is the file containing
  // the debug symbols for the Image.
  //
  StartIndex = 0;
  for (
    Index = 0;
    Index < SymbolsPathSize && SymbolsPath[Index] != '\0';
    ++Index
    ) {
    if (SymbolsPath[Index] == '\\' || SymbolsPath[Index] == '/') {
      StartIndex = Index + 1;
    }
  }
  //
  // Extract the module name from the debug symbols file and ensure the correct
  // file extensions.
  //
  for (
    Index = 0;
    Index < MIN (ModuleNameSize, SymbolsPathSize);
    ++Index
    ) {
    ModuleName[Index] = SymbolsPath[Index + StartIndex];
    if (ModuleName[Index] == '\0') {
      ModuleName[Index] = '.';
    }
    if (ModuleName[Index] == '.') {
      if (Index > ModuleNameSize - 3) {
        break;
      }

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
