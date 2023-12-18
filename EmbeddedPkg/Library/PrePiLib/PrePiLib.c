/** @file

  Copyright (c) 2008 - 2009, Apple Inc. All rights reserved.<BR>

  SPDX-License-Identifier: BSD-2-Clause-Patent

**/

#include <PrePi.h>

//
// Hack to work in NT32
//
EFI_STATUS

EFIAPI

SecWinNtPeiLoadFile (
  IN  VOID                  *Pe32Data,
  IN  EFI_PHYSICAL_ADDRESS  *ImageAddress,
  IN  UINT64                *ImageSize,
  IN  EFI_PHYSICAL_ADDRESS  *EntryPoint
  );

EFI_STATUS
EFIAPI
LoadUefiImage (
  IN  VOID                  *UefiImage,
  IN  UINT32                UefiImageSize,
  OUT EFI_PHYSICAL_ADDRESS  *ImageAddress,
  OUT UINT32                *DestinationSize,
  OUT EFI_PHYSICAL_ADDRESS  *EntryPoint
  )
{
  RETURN_STATUS                   Status;
  UEFI_IMAGE_LOADER_IMAGE_CONTEXT ImageContext;
  UINT32                          ImageSize;
  VOID                            *Buffer;
  UINT32                          BufferSize;
  UINT32                          BufferPages;
  UINT32                          BufferAlignment;

  Status = UefiImageInitializeContext (
             &ImageContext,
             UefiImage,
             UefiImageSize,
             UEFI_IMAGE_SOURCE_FV
             );
  ASSERT_EFI_ERROR (Status);

  ImageSize       = UefiImageGetImageSize (&ImageContext);
  BufferPages     = EFI_SIZE_TO_PAGES (ImageSize);
  BufferSize      = EFI_PAGES_TO_SIZE (BufferPages);
  BufferAlignment = UefiImageGetSegmentAlignment (&ImageContext);

  //
  // Allocate Memory for the image
  //
  Buffer = AllocateAlignedCodePages (BufferPages, BufferAlignment);
  ASSERT (Buffer != 0);

  //
  // Load and relocate the image to our new buffer
  //
  Status = UefiImageLoadImageForExecution (&ImageContext, Buffer, BufferSize, NULL, 0);
  ASSERT_EFI_ERROR (Status);

  *ImageAddress    = (UINTN) Buffer;
  *DestinationSize = BufferSize;
  *EntryPoint      = (UINTN) UefiImageLoaderGetImageEntryPoint (&ImageContext);

  return Status;
}

typedef
VOID
(EFIAPI *DXE_CORE_ENTRY_POINT)(
  IN  VOID *HobStart
  );

EFI_STATUS
EFIAPI
LoadDxeCoreFromFfsFile (
  IN EFI_PEI_FILE_HANDLE  FileHandle,
  IN UINTN                StackSize
  )
{
  EFI_STATUS            Status;
  VOID                  *UefiImage;
  UINT32                UefiImageSize;
  EFI_PHYSICAL_ADDRESS  ImageAddress;
  UINT32                DestinationSize;
  EFI_PHYSICAL_ADDRESS  EntryPoint;
  VOID                  *BaseOfStack;
  VOID                  *TopOfStack;
  VOID                  *Hob;
  EFI_FV_FILE_INFO      FvFileInfo;

  Status = FfsFindSectionDataWithHook (EFI_SECTION_PE32, NULL, FileHandle, &UefiImage, &UefiImageSize);
  if (EFI_ERROR (Status)) {
    return Status;
  }

  Status = LoadUefiImage (UefiImage, UefiImageSize, &ImageAddress, &DestinationSize, &EntryPoint);
  // For NT32 Debug  Status = SecWinNtPeiLoadFile (UefiImage, &ImageAddress, &ImageSize, &EntryPoint);
  ASSERT_EFI_ERROR (Status);

  //
  // Extract the DxeCore GUID file name.
  //
  Status = FfsGetFileInfo (FileHandle, &FvFileInfo);
  ASSERT_EFI_ERROR (Status);

  BuildModuleHob (&FvFileInfo.FileName, (EFI_PHYSICAL_ADDRESS)(UINTN)ImageAddress, DestinationSize, EntryPoint);

  DEBUG ((DEBUG_INFO | DEBUG_LOAD, "Loading DxeCore at 0x%10p EntryPoint=0x%10p\n", (VOID *)(UINTN)ImageAddress, (VOID *)(UINTN)EntryPoint));

  Hob = GetHobList ();
  if (StackSize == 0) {
    // User the current stack

    ((DXE_CORE_ENTRY_POINT)(UINTN)EntryPoint)(Hob);
  } else {
    //
    // Allocate 128KB for the Stack
    //
    BaseOfStack = AllocatePages (EFI_SIZE_TO_PAGES (StackSize));
    ASSERT (BaseOfStack != NULL);

    //
    // Compute the top of the stack we were allocated. Pre-allocate a UINTN
    // for safety.
    //
    TopOfStack = (VOID *)((UINTN)BaseOfStack + EFI_SIZE_TO_PAGES (StackSize) * EFI_PAGE_SIZE - CPU_STACK_ALIGNMENT);
    TopOfStack = ALIGN_POINTER (TopOfStack, CPU_STACK_ALIGNMENT);

    //
    // Update the contents of BSP stack HOB to reflect the real stack info passed to DxeCore.
    //
    UpdateStackHob ((EFI_PHYSICAL_ADDRESS)(UINTN)BaseOfStack, StackSize);

    SwitchStack (
      (SWITCH_STACK_ENTRY_POINT)(UINTN)EntryPoint,
      Hob,
      NULL,
      TopOfStack
      );
  }

  // Should never get here as DXE Core does not return
  DEBUG ((DEBUG_ERROR, "DxeCore returned\n"));
  ASSERT (FALSE);

  return EFI_DEVICE_ERROR;
}

EFI_STATUS
EFIAPI
LoadDxeCoreFromFv (
  IN UINTN  *FvInstance    OPTIONAL,
  IN UINTN  StackSize
  )
{
  EFI_STATUS           Status;
  EFI_PEI_FV_HANDLE    VolumeHandle;
  EFI_PEI_FILE_HANDLE  FileHandle = NULL;

  if (FvInstance != NULL) {
    //
    // Caller passed in a specific FV to try, so only try that one
    //
    Status = FfsFindNextVolume (*FvInstance, &VolumeHandle);
    if (!EFI_ERROR (Status)) {
      Status = FfsFindNextFile (EFI_FV_FILETYPE_DXE_CORE, VolumeHandle, &FileHandle);
    }
  } else {
    Status = FfsAnyFvFindFirstFile (EFI_FV_FILETYPE_DXE_CORE, &VolumeHandle, &FileHandle);
  }

  if (!EFI_ERROR (Status)) {
    return LoadDxeCoreFromFfsFile (FileHandle, StackSize);
  }

  return Status;
}

EFI_STATUS
EFIAPI
DecompressFirstFv (
  VOID
  )
{
  EFI_STATUS           Status;
  EFI_PEI_FV_HANDLE    VolumeHandle;
  EFI_PEI_FILE_HANDLE  FileHandle;

  Status = FfsAnyFvFindFirstFile (EFI_FV_FILETYPE_FIRMWARE_VOLUME_IMAGE, &VolumeHandle, &FileHandle);
  if (!EFI_ERROR (Status)) {
    Status = FfsProcessFvFile (FileHandle);
  }

  return Status;
}
