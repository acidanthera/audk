/** @file

Copyright (c) 2015 - 2017, Intel Corporation. All rights reserved.<BR>

SPDX-License-Identifier: BSD-2-Clause-Patent

**/

#include <Uefi.h>
#include <Library/BaseLib.h>
#include <Library/UefiDriverEntryPoint.h>
#include <Library/BaseMemoryLib.h>
#include <Library/DebugLib.h>
#include <Library/UefiImageLib.h>
#include <Library/UefiBootServicesTableLib.h>
#include <Library/DxeServicesLib.h>
#include <Library/CacheMaintenanceLib.h>
#include <Library/UefiLib.h>
#include <Library/MemoryAllocationLib.h>
#include <Library/MemoryAllocationLibEx.h>

/**
  Relocate this image under 4G memory.

  @param  ImageHandle  Handle of driver image.
  @param  SystemTable  Pointer to system table.

  @retval EFI_SUCCESS  Image successfully relocated.
  @retval EFI_ABORTED  Failed to relocate image.

**/
EFI_STATUS
RelocateImageUnder4GIfNeeded (
  IN EFI_HANDLE        ImageHandle,
  IN EFI_SYSTEM_TABLE  *SystemTable
  )
{
  EFI_STATUS                    Status;
  UINT8                         *Buffer;
  UINTN                         BufferSize;
  EFI_HANDLE                    NewImageHandle;
  UINT32                        ImageSize;
  UINT32                        ImageAlignment;
  UINTN                         Pages;
  EFI_PHYSICAL_ADDRESS          FfsBuffer;
  UEFI_IMAGE_LOADER_IMAGE_CONTEXT ImageContext;
  VOID                          *Interface;

  //
  // If it is already <4G, no need do relocate
  //
  if ((UINTN)RelocateImageUnder4GIfNeeded < 0xFFFFFFFF) {
    return EFI_SUCCESS;
  }

  //
  // If locate gEfiCallerIdGuid success, it means 2nd entry.
  //
  Status = gBS->LocateProtocol (&gEfiCallerIdGuid, NULL, &Interface);
  if (!EFI_ERROR (Status)) {
    DEBUG ((DEBUG_INFO, "FspNotifyDxe - 2nd entry\n"));
    return EFI_SUCCESS;
  }

  DEBUG ((DEBUG_INFO, "FspNotifyDxe - 1st entry\n"));

  //
  // Here we install a dummy handle
  //
  NewImageHandle = NULL;
  Status         = gBS->InstallProtocolInterface (
                          &NewImageHandle,
                          &gEfiCallerIdGuid,
                          EFI_NATIVE_INTERFACE,
                          NULL
                          );
  ASSERT_EFI_ERROR (Status);

  //
  // Reload image itself to <4G mem
  //
  Status = GetSectionFromAnyFv (
             &gEfiCallerIdGuid,
             EFI_SECTION_PE32,
             0,
             (VOID **)&Buffer,
             &BufferSize
             );
  ASSERT_EFI_ERROR (Status);
  //
  // Get information about the image being loaded
  //
  Status = UefiImageInitializeContext (
             &ImageContext,
             Buffer,
             (UINT32) BufferSize,
             UEFI_IMAGE_SOURCE_FV
             );
  ASSERT_EFI_ERROR (Status);
  ImageSize      = UefiImageGetImageSize (&ImageContext);
  ImageAlignment = UefiImageGetSegmentAlignment (&ImageContext);
  Pages = EFI_SIZE_TO_PAGES (ImageSize);

  FfsBuffer = 0xFFFFFFFF;
  Status    = AllocateAlignedPagesEx (
                AllocateMaxAddress,
                EfiBootServicesCode,
                Pages,
                ImageAlignment,
                &FfsBuffer
                );
  ASSERT_EFI_ERROR (Status);
  //
  // Load and relocate the image to our new buffer
  //
  Status = UefiImageLoadImageForExecution (
             &ImageContext,
             (VOID *) (UINTN) FfsBuffer,
             ImageSize,
             NULL,
             0
             );
  ASSERT_EFI_ERROR (Status);

  //
  // Free the buffer allocated by ReadSection since the image has been relocated in the new buffer
  //
  gBS->FreePool (Buffer);

  DEBUG ((DEBUG_INFO, "Loading driver at 0x%08llx EntryPoint=0x%08x\n", FfsBuffer, UefiImageLoaderGetImageEntryPoint (&ImageContext)));
  Status = ((EFI_IMAGE_ENTRY_POINT)(UefiImageLoaderGetImageEntryPoint (&ImageContext)))(NewImageHandle, gST);
  if (EFI_ERROR (Status)) {
    DEBUG ((DEBUG_ERROR, "Error: Image at 0x%08llx start failed: %r\n", FfsBuffer, Status));
    FreeAlignedPages ((VOID *)(UINTN)FfsBuffer, Pages);
  }

  //
  // return error to unload >4G copy, if we already relocate itself to <4G.
  //
  return EFI_ALREADY_STARTED;
}
