/** @file

  Copyright (c) 2020, Intel Corporation. All rights reserved.<BR>

  SPDX-License-Identifier: BSD-2-Clause-Patent

**/

#include "UefiPayloadEntry.h"

/**
    Loads and relocates a PE/COFF image

  @param[in]   UefiImage      Point to a Pe/Coff image.
  @param[out]  ImageAddress   The image memory address after relocation.
  @param[out]  ImageSize      The image size.
  @param[out]  EntryPoint     The image entry point.

  @return EFI_SUCCESS    If the image is loaded and relocated successfully.
  @return Others         If the image failed to load or relocate.
**/
EFI_STATUS
LoadUefiImage (
  IN  VOID                  *UefiImage,
  IN  UINT32                UefiImageSize,
  OUT EFI_PHYSICAL_ADDRESS  *ImageAddress,
  OUT UINT32                *DestinationSize,
  OUT EFI_PHYSICAL_ADDRESS  *EntryPoint
  )
{
  RETURN_STATUS                 Status;
  UEFI_IMAGE_LOADER_IMAGE_CONTEXT   ImageContext;
  UINT32                            ImageSize;
  UINT32                            ImageAlignment;
  UINT32                        BufferPages;
  UINT32                        BufferSize;
  VOID                          *Buffer;

  Status = UefiImageInitializeContext (
             &ImageContext,
             UefiImage,
             UefiImageSize,
             UEFI_IMAGE_SOURCE_FV
             );
  if (EFI_ERROR (Status)) {
    ASSERT_EFI_ERROR (Status);
    return Status;
  }

  ImageSize      = UefiImageGetImageSize (&ImageContext);
  BufferPages    = EFI_SIZE_TO_PAGES (ImageSize);
  BufferSize     = EFI_PAGES_TO_SIZE (BufferPages);
  ImageAlignment = UefiImageGetSegmentAlignment (&ImageContext);

  //
  // Allocate Memory for the image
  //
  Buffer = AllocateAlignedCodePages (BufferPages, ImageAlignment);
  if (Buffer == NULL) {
    return EFI_OUT_OF_RESOURCES;
  }

  //
  // Load and relocate the image to our new buffer
  //
  Status = UefiImageLoadImageForExecution (
             &ImageContext,
             Buffer,
             BufferSize,
             NULL,
             0
             );
  if (EFI_ERROR (Status)) {
    ASSERT_EFI_ERROR (Status);
    return Status;
  }

  *ImageAddress    = (UINTN)Buffer;
  *DestinationSize = BufferSize;
  *EntryPoint      = UefiImageLoaderGetImageEntryPoint (&ImageContext);

  return EFI_SUCCESS;
}

/**
  This function searchs a given file type with a given Guid within a valid FV.
  If input Guid is NULL, will locate the first section having the given file type

  @param FvHeader        A pointer to firmware volume header that contains the set of files
                         to be searched.
  @param FileType        File type to be searched.
  @param Guid            Will ignore if it is NULL.
  @param FileHeader      A pointer to the discovered file, if successful.

  @retval EFI_SUCCESS    Successfully found FileType
  @retval EFI_NOT_FOUND  File type can't be found.
**/
EFI_STATUS
FvFindFileByTypeGuid (
  IN  EFI_FIRMWARE_VOLUME_HEADER  *FvHeader,
  IN  EFI_FV_FILETYPE             FileType,
  IN  EFI_GUID                    *Guid           OPTIONAL,
  OUT EFI_FFS_FILE_HEADER         **FileHeader
  )
{
  EFI_PHYSICAL_ADDRESS  CurrentAddress;
  EFI_PHYSICAL_ADDRESS  EndOfFirmwareVolume;
  EFI_FFS_FILE_HEADER   *File;
  UINT32                Size;
  EFI_PHYSICAL_ADDRESS  EndOfFile;

  CurrentAddress      = (EFI_PHYSICAL_ADDRESS)(UINTN)FvHeader;
  EndOfFirmwareVolume = CurrentAddress + FvHeader->FvLength;

  //
  // Loop through the FFS files
  //
  for (EndOfFile = CurrentAddress + FvHeader->HeaderLength; ; ) {
    CurrentAddress = (EndOfFile + 7) & 0xfffffffffffffff8ULL;
    if (CurrentAddress > EndOfFirmwareVolume) {
      break;
    }

    File = (EFI_FFS_FILE_HEADER *)(UINTN)CurrentAddress;
    if (IS_FFS_FILE2 (File)) {
      Size = FFS_FILE2_SIZE (File);
      if (Size <= 0x00FFFFFF) {
        break;
      }
    } else {
      Size = FFS_FILE_SIZE (File);
      if (Size < sizeof (EFI_FFS_FILE_HEADER)) {
        break;
      }
    }

    EndOfFile = CurrentAddress + Size;
    if (EndOfFile > EndOfFirmwareVolume) {
      break;
    }

    //
    // Look for file type
    //
    if (File->Type == FileType) {
      if ((Guid == NULL) || CompareGuid (&File->Name, Guid)) {
        *FileHeader = File;
        return EFI_SUCCESS;
      }
    }
  }

  return EFI_NOT_FOUND;
}

/**
  This function searchs a given section type within a valid FFS file.

  @param  FileHeader            A pointer to the file header that contains the set of sections to
                                be searched.
  @param  SectionType            The value of the section type to search.
  @param  SectionData           A pointer to the discovered section, if successful.

  @retval EFI_SUCCESS           The section was found.
  @retval EFI_NOT_FOUND         The section was not found.

**/
EFI_STATUS
FileFindSection (
  IN EFI_FFS_FILE_HEADER  *FileHeader,
  IN EFI_SECTION_TYPE     SectionType,
  OUT VOID                      **SectionData,
  OUT UINT32                    *SectionSize
  )
{
  UINT32                     FileSize;
  EFI_COMMON_SECTION_HEADER  *Section;
  UINT32                        CurSectionSize;
  UINT32                     Index;

  if (IS_FFS_FILE2 (FileHeader)) {
    FileSize = FFS_FILE2_SIZE (FileHeader);
  } else {
    FileSize = FFS_FILE_SIZE (FileHeader);
  }

  FileSize -= sizeof (EFI_FFS_FILE_HEADER);

  Section = (EFI_COMMON_SECTION_HEADER *)(FileHeader + 1);
  Index   = 0;
  while (Index < FileSize) {
    if (Section->Type == SectionType) {
      // FIXME: Use general API (MdePkg?) with proper size checks
      if (IS_SECTION2 (Section)) {
        *SectionData = (VOID *)((UINT8 *)Section + sizeof (EFI_COMMON_SECTION_HEADER2));
        *SectionSize = CurSectionSize - sizeof (EFI_COMMON_SECTION_HEADER2);
      } else {
        *SectionData = (VOID *)((UINT8 *)Section + sizeof (EFI_COMMON_SECTION_HEADER));
        *SectionSize = CurSectionSize - sizeof (EFI_COMMON_SECTION_HEADER);
      }

      return EFI_SUCCESS;
    }

    if (IS_SECTION2 (Section)) {
      CurSectionSize = SECTION2_SIZE (Section);
    } else {
      CurSectionSize = SECTION_SIZE (Section);
    }

    CurSectionSize = GET_OCCUPIED_SIZE (CurSectionSize, 4);
    ASSERT (CurSectionSize != 0);
    Index += CurSectionSize;

    Section = (EFI_COMMON_SECTION_HEADER *)((UINT8 *)Section + CurSectionSize);
  }

  return EFI_NOT_FOUND;
}

/**
  Find DXE core from FV and build DXE core HOBs.

  @param[out]  DxeCoreEntryPoint     DXE core entry point

  @retval EFI_SUCCESS        If it completed successfully.
  @retval EFI_NOT_FOUND      If it failed to load DXE FV.
**/
EFI_STATUS
LoadDxeCore (
  OUT PHYSICAL_ADDRESS  *DxeCoreEntryPoint
  )
{
  EFI_STATUS                  Status;
  EFI_FIRMWARE_VOLUME_HEADER  *PayloadFv;
  EFI_FIRMWARE_VOLUME_HEADER  *DxeCoreFv;
  UINT32                      DxeCoreFvSize;
  EFI_FFS_FILE_HEADER         *FileHeader;
  VOID                        *UefiImage;
  UINT32                      UefiImageSize;
  EFI_PHYSICAL_ADDRESS        ImageAddress;
  UINT32                      DestinationSize;

  PayloadFv = (EFI_FIRMWARE_VOLUME_HEADER *)(UINTN)PcdGet32 (PcdPayloadFdMemBase);

  //
  // DXE FV is inside Payload FV. Here find DXE FV from Payload FV
  //
  Status = FvFindFileByTypeGuid (PayloadFv, EFI_FV_FILETYPE_FIRMWARE_VOLUME_IMAGE, NULL, &FileHeader);
  if (EFI_ERROR (Status)) {
    return Status;
  }

  Status = FileFindSection (FileHeader, EFI_SECTION_FIRMWARE_VOLUME_IMAGE, (VOID **)&DxeCoreFv, &DxeCoreFvSize);
  if (EFI_ERROR (Status)) {
    return Status;
  }

  //
  // Report DXE FV to DXE core
  //
  BuildFvHob ((EFI_PHYSICAL_ADDRESS)(UINTN)DxeCoreFv, DxeCoreFv->FvLength);

  //
  // Find DXE core file from DXE FV
  //
  Status = FvFindFileByTypeGuid (DxeCoreFv, EFI_FV_FILETYPE_DXE_CORE, NULL, &FileHeader);
  if (EFI_ERROR (Status)) {
    return Status;
  }

  Status = FileFindSection (FileHeader, EFI_SECTION_PE32, (VOID **)&UefiImage, &UefiImageSize);
  if (EFI_ERROR (Status)) {
    return Status;
  }

  //
  // Get DXE core info
  //
  Status = LoadUefiImage (UefiImage, UefiImageSize, &ImageAddress, &DestinationSize, DxeCoreEntryPoint);
  if (EFI_ERROR (Status)) {
    return Status;
  }

  BuildModuleHob (&FileHeader->Name, ImageAddress, DestinationSize, *DxeCoreEntryPoint);

  return EFI_SUCCESS;
}

/**
  Find DXE core from FV and build DXE core HOBs.

  @param[in]   DxeFv                 The FV where to find the DXE core.
  @param[out]  DxeCoreEntryPoint     DXE core entry point

  @retval EFI_SUCCESS        If it completed successfully.
  @retval EFI_NOT_FOUND      If it failed to load DXE FV.
**/
EFI_STATUS
UniversalLoadDxeCore (
  IN  EFI_FIRMWARE_VOLUME_HEADER  *DxeFv,
  OUT PHYSICAL_ADDRESS            *DxeCoreEntryPoint
  )
{
  EFI_STATUS            Status;
  EFI_FFS_FILE_HEADER   *FileHeader;
  VOID                  *UefiImage;
  UINT32                UefiImageSize;
  EFI_PHYSICAL_ADDRESS  ImageAddress;
  UINT32                DestinationSize;

  //
  // Find DXE core file from DXE FV
  //
  Status = FvFindFileByTypeGuid (DxeFv, EFI_FV_FILETYPE_DXE_CORE, NULL, &FileHeader);
  if (EFI_ERROR (Status)) {
    return Status;
  }

  Status = FileFindSection (FileHeader, EFI_SECTION_PE32, (VOID **)&UefiImage, &UefiImageSize);
  if (EFI_ERROR (Status)) {
    return Status;
  }

  //
  // Get DXE core info
  //
  Status = LoadUefiImage (UefiImage, UefiImageSize, &ImageAddress, &DestinationSize, DxeCoreEntryPoint);
  if (EFI_ERROR (Status)) {
    return Status;
  }

  BuildModuleHob (&FileHeader->Name, ImageAddress, DestinationSize, *DxeCoreEntryPoint);

  return EFI_SUCCESS;
}
