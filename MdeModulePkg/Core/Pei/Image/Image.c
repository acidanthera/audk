/** @file
  Pei Core Load Image Support

Copyright (c) 2006 - 2021, Intel Corporation. All rights reserved.<BR>
SPDX-License-Identifier: BSD-2-Clause-Patent

**/

#include "PeiMain.h"

EFI_PEI_LOAD_FILE_PPI  mPeiLoadImagePpi = {
  PeiLoadImageLoadImageWrapper
};

EFI_PEI_PPI_DESCRIPTOR  gPpiLoadFilePpiList = {
  (EFI_PEI_PPI_DESCRIPTOR_PPI | EFI_PEI_PPI_DESCRIPTOR_TERMINATE_LIST),
  &gEfiPeiLoadFilePpiGuid,
  &mPeiLoadImagePpi
};

/**
  To check memory usage bit map array to figure out if the memory range the image will be loaded in is available or not. If
  memory range is available, the function will mark the corresponding bits to 1 which indicates the memory range is used.
  The function is only invoked when load modules at fixed address feature is enabled.

  @param  Private                  Pointer to the private data passed in from caller
  @param  ImageBase                The base address the image will be loaded at.
  @param  ImageSize                The size of the image

  @retval EFI_SUCCESS              The memory range the image will be loaded in is available
  @retval EFI_NOT_FOUND            The memory range the image will be loaded in is not available
**/
EFI_STATUS
CheckAndMarkFixLoadingMemoryUsageBitMap (
  IN  PEI_CORE_INSTANCE     *Private,
  IN  EFI_PHYSICAL_ADDRESS  ImageBase,
  IN  UINT32                ImageSize
  )
{
  UINT32                DxeCodePageNumber;
  UINT64                ReservedCodeSize;
  EFI_PHYSICAL_ADDRESS  PeiCodeBase;
  UINT32                BaseOffsetPageNumber;
  UINT32                TopOffsetPageNumber;
  UINT32                Index;
  UINT64                *MemoryUsageBitMap;

  //
  // The reserved code range includes RuntimeCodePage range, Boot time code range and PEI code range.
  //
  DxeCodePageNumber  = PcdGet32 (PcdLoadFixAddressBootTimeCodePageNumber);
  DxeCodePageNumber += PcdGet32 (PcdLoadFixAddressRuntimeCodePageNumber);
  ReservedCodeSize   = EFI_PAGES_TO_SIZE (DxeCodePageNumber + PcdGet32 (PcdLoadFixAddressPeiCodePageNumber));
  PeiCodeBase        = Private->LoadModuleAtFixAddressTopAddress - ReservedCodeSize;

  //
  // Test the memory range for loading the image in the PEI code range.
  //
  if (((Private->LoadModuleAtFixAddressTopAddress - EFI_PAGES_TO_SIZE (DxeCodePageNumber)) < (ImageBase + ImageSize)) ||
      (PeiCodeBase > ImageBase))
  {
    return EFI_NOT_FOUND;
  }

  //
  // Test if the memory is available or not.
  //
  MemoryUsageBitMap    = Private->PeiCodeMemoryRangeUsageBitMap;
  BaseOffsetPageNumber = EFI_SIZE_TO_PAGES ((UINT32)(ImageBase - PeiCodeBase));
  TopOffsetPageNumber  = EFI_SIZE_TO_PAGES ((UINT32)(ImageBase + ImageSize - PeiCodeBase));
  for (Index = BaseOffsetPageNumber; Index < TopOffsetPageNumber; Index++) {
    if ((MemoryUsageBitMap[Index / 64] & LShiftU64 (1, (Index % 64))) != 0) {
      //
      // This page is already used.
      //
      return EFI_NOT_FOUND;
    }
  }

  //
  // Being here means the memory range is available.  So mark the bits for the memory range
  //
  for (Index = BaseOffsetPageNumber; Index < TopOffsetPageNumber; Index++) {
    MemoryUsageBitMap[Index / 64] |= LShiftU64 (1, (Index % 64));
  }

  return EFI_SUCCESS;
}

/**

  Get the fixed loading address from image header assigned by build tool. This function only be called
  when Loading module at Fixed address feature enabled.

  @param ImageContext              Pointer to the image context structure that describes the PE/COFF
                                    image that needs to be examined by this function.
  @param Private                    Pointer to the private data passed in from caller

  @retval EFI_SUCCESS               An fixed loading address is assigned to this image by build tools .
  @retval EFI_NOT_FOUND             The image has no assigned fixed loading address.

**/
EFI_STATUS
GetUefiImageFixLoadingAssignedAddress (
  OUT EFI_PHYSICAL_ADDRESS  *LoadAddress,
  IN  UINT64                ValueInSectionHeader,
  IN  UINT32                ImageDestSize,
  IN  PEI_CORE_INSTANCE     *Private
  )
{
   EFI_STATUS           Status;
   EFI_PHYSICAL_ADDRESS FixLoadingAddress;

  if ((INT64)PcdGet64(PcdLoadModuleAtFixAddressEnable) > 0) {
    //
    // When LMFA feature is configured as Load Module at Fixed Absolute Address mode, PointerToRelocations & PointerToLineNumbers field
    // hold the absolute address of image base running in memory
    //
    FixLoadingAddress = ValueInSectionHeader;
  } else {
    //
    // When LMFA feature is configured as Load Module at Fixed offset mode, PointerToRelocations & PointerToLineNumbers field
    // hold the offset relative to a platform-specific top address.
    //
    FixLoadingAddress = (EFI_PHYSICAL_ADDRESS)(Private->LoadModuleAtFixAddressTopAddress + ValueInSectionHeader);
  }
  //
  // Check if the memory range is available.
  //
  Status = CheckAndMarkFixLoadingMemoryUsageBitMap (Private, FixLoadingAddress, ImageDestSize);
  *LoadAddress = FixLoadingAddress;

  DEBUG ((EFI_D_INFO|EFI_D_LOAD, "LOADING MODULE FIXED INFO: Loading module at fixed address 0x%11p. Status= %r \n", (VOID *)(UINTN)FixLoadingAddress, Status));
  return Status;
}

/**

  Loads and relocates a PE/COFF image into memory.
  If the image is not relocatable, it will not be loaded into memory and be loaded as XIP image.

  @param FileHandle      - Pointer to the FFS file header of the image.
  @param Pe32Data        - The base address of the PE/COFF file that is to be loaded and relocated
  @param ImageAddress    - The base address of the relocated PE/COFF image
  @param ImageSize       - The size of the relocated PE/COFF image
  @param EntryPoint      - The entry point of the relocated PE/COFF image

  @retval EFI_SUCCESS           The file was loaded and relocated
  @retval EFI_OUT_OF_RESOURCES  There was not enough memory to load and relocate the PE/COFF file
  @retval EFI_WARN_BUFFER_TOO_SMALL
                                There is not enough heap to allocate the requested size.
                                This will not prevent the XIP image from being invoked.

**/
EFI_STATUS
LoadAndRelocateUefiImage (
  IN  EFI_PEI_FILE_HANDLE   FileHandle,
  IN  VOID                  *Pe32Data,
  IN  UINT32                                    Pe32DataSize,
  OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT           *ImageContext,
  OUT EFI_PHYSICAL_ADDRESS                      *ImageAddress,
  OUT UINTN                                     *DebugBase
  )
{
  EFI_STATUS                    Status;
  BOOLEAN                       Success;
  PEI_CORE_INSTANCE             *Private;
  UINT32                                ImageSize;
  UINT32                                ImageAlignment;
  UINT64                                ValueInSectionHeader;
  BOOLEAN                       IsXipImage;
  EFI_STATUS                    ReturnStatus;
  BOOLEAN                       IsS3Boot;
  BOOLEAN                       IsPeiModule;
  BOOLEAN                       IsRegisterForShadow;
  EFI_FV_FILE_INFO              FileInfo;
  UINT32                                DestinationPages;
  UINT32                                DestinationSize;
  EFI_PHYSICAL_ADDRESS                  Destination;
  UINT16                                Machine;
  BOOLEAN                               LoadDynamically;

  Private = PEI_CORE_INSTANCE_FROM_PS_THIS (GetPeiServicesTablePointer ());

  ReturnStatus = EFI_SUCCESS;

  Status = UefiImageInitializeContext (
             ImageContext,
             Pe32Data,
             Pe32DataSize,
             UEFI_IMAGE_SOURCE_FV
             );
  if (EFI_ERROR (Status)) {
    return Status;
  }

  Machine = UefiImageGetMachine (ImageContext);

  if (!EFI_IMAGE_MACHINE_TYPE_SUPPORTED (Machine)) {
    if (!EFI_IMAGE_MACHINE_CROSS_TYPE_SUPPORTED (Machine)) {
      return EFI_UNSUPPORTED;
    }
  }

  //
  // Initialize local IsS3Boot and IsRegisterForShadow variable
  //
  IsS3Boot = FALSE;
  if (Private->HobList.HandoffInformationTable->BootMode == BOOT_ON_S3_RESUME) {
    IsS3Boot = TRUE;
  }

  IsRegisterForShadow = FALSE;
  if (  (Private->CurrentFileHandle == FileHandle)
     && (Private->Fv[Private->CurrentPeimFvCount].PeimState[Private->CurrentPeimCount] == PEIM_STATE_REGISTER_FOR_SHADOW))
  {
    IsRegisterForShadow = TRUE;
  }

  //
  // XIP image that ImageAddress is same to Image handle.
  //
  IsXipImage = UefiImageImageIsInplace (ImageContext);

  //
  // Get file type first
  //
  Status = PeiServicesFfsGetFileInfo (FileHandle, &FileInfo);
  ASSERT_EFI_ERROR (Status);

  //
  // Check whether the file type is PEI module.
  //
  IsPeiModule = FALSE;
  if ((FileInfo.FileType == EFI_FV_FILETYPE_PEI_CORE) ||
      (FileInfo.FileType == EFI_FV_FILETYPE_PEIM) ||
      (FileInfo.FileType == EFI_FV_FILETYPE_COMBINED_PEIM_DRIVER))
  {
    IsPeiModule = TRUE;
  }

  //
  // When Image has no reloc section, it can't be relocated into memory.
  //
  if (UefiImageGetRelocsStripped (ImageContext) && (Private->PeiMemoryInstalled) &&
      ((!IsPeiModule) || PcdGetBool (PcdMigrateTemporaryRamFirmwareVolumes) ||
       (!IsS3Boot && (PcdGetBool (PcdShadowPeimOnBoot) || IsRegisterForShadow)) ||
       (IsS3Boot && PcdGetBool (PcdShadowPeimOnS3Boot)))
      )
  {
    DEBUG ((DEBUG_INFO|DEBUG_LOAD, "The image at 0x%08x without reloc section can't be loaded into memory\n", (UINTN)Pe32Data));
  }

  LoadDynamically  = FALSE;
  ImageSize        = UefiImageGetImageSize (ImageContext);
  DestinationPages = EFI_SIZE_TO_PAGES (ImageSize);
  DestinationSize  = EFI_PAGES_TO_SIZE (DestinationPages);

  //
  // Allocate Memory for the image when memory is ready, and image is relocatable.
  // On normal boot, PcdShadowPeimOnBoot decides whether load PEIM or PeiCore into memory.
  // On S3 boot, PcdShadowPeimOnS3Boot decides whether load PEIM or PeiCore into memory.
  //
  if ((!UefiImageGetRelocsStripped (ImageContext)) && (Private->PeiMemoryInstalled) &&
      ((!IsPeiModule) || PcdGetBool (PcdMigrateTemporaryRamFirmwareVolumes) ||
       (!IsS3Boot && (PcdGetBool (PcdShadowPeimOnBoot) || IsRegisterForShadow)) ||
       (IsS3Boot && PcdGetBool (PcdShadowPeimOnS3Boot)))
      )
  {
    Success = FALSE;

    if (PcdGet64(PcdLoadModuleAtFixAddressEnable) != 0 && (Private->HobList.HandoffInformationTable->BootMode != BOOT_ON_S3_RESUME)) {
      Status = UefiImageGetFixedAddress (ImageContext, &ValueInSectionHeader);
      if (!RETURN_ERROR (Status)) {
        Status = GetUefiImageFixLoadingAssignedAddress(&Destination, ValueInSectionHeader, DestinationSize, Private);
      }

      if (!EFI_ERROR (Status)){
        Success = Destination == UefiImageGetPreferredAddress (ImageContext);

        if (!Success) {
          DEBUG ((DEBUG_INFO|DEBUG_LOAD, "LOADING MODULE FIXED ERROR: Loading module at fixed address failed since relocs have been stripped.\n"));
        }
      } else {
        DEBUG ((EFI_D_INFO|EFI_D_LOAD, "LOADING MODULE FIXED ERROR: Failed to load module at fixed address. \n"));
      }
    }

    if (!Success) {
      //
      // Allocate more buffer to avoid buffer overflow.
      //
      ImageAlignment = UefiImageGetSegmentAlignment (ImageContext);

      Destination = (UINTN)AllocateAlignedCodePages (
                             DestinationPages,
                             ImageAlignment
                             );
      Success = Destination != 0;
    }

    if (Success) {
      LoadDynamically = TRUE;
      //
      // Load the image to our new buffer
      //
      Status = UefiImageLoadImageForExecution (
                ImageContext,
                (VOID *) (UINTN)Destination,
                DestinationSize,
                NULL,
                0
                );
      if (EFI_ERROR (Status)) {
        return              Status;
      }
    } else {
      //
      // No enough memory resource.
      //
      if (!IsXipImage) {
        //
        // Non XIP image can't be loaded because no enough memory is allocated.
        //
        ASSERT (FALSE);
        return EFI_OUT_OF_RESOURCES;
      }
      //
      // XIP image can still be invoked.
      //
      ReturnStatus = EFI_WARN_BUFFER_TOO_SMALL;
    }
  }

  if (!LoadDynamically) {
    Status = UefiImageLoadImageInplace (ImageContext);
    if (EFI_ERROR (Status)) {
      return Status;
    }
  }

  *ImageAddress = UefiImageLoaderGetImageAddress (ImageContext);
  *DebugBase    = UefiImageLoaderGetDebugAddress (ImageContext);

  return ReturnStatus;
}

/**
  Loads and relocates a PE/COFF image in place.

  @param Pe32Data         The base address of the PE/COFF file that is to be loaded and relocated
  @param ImageAddress     The base address of the relocated PE/COFF image

  @retval EFI_SUCCESS     The file was loaded and relocated.
  @retval Others          The file not be loaded and error occurred.

**/
EFI_STATUS
LoadAndRelocateUefiImageInPlace (
  IN  VOID  *Pe32Data,
  IN  VOID    *ImageAddress,
  IN  UINT32  ImageSize
  )
{
  EFI_STATUS                    Status;
  UEFI_IMAGE_LOADER_IMAGE_CONTEXT ImageContext;

  ASSERT (Pe32Data != ImageAddress);

  CopyMem (ImageAddress, Pe32Data, ImageSize);

  Status = UefiImageInitializeContext (
             &ImageContext,
             ImageAddress,
             ImageSize,
             UEFI_IMAGE_SOURCE_FV
             );
  if (EFI_ERROR (Status)) {
    ASSERT_EFI_ERROR (Status);
    return Status;
  }

  //
  // Load the image in place
  //
  Status = UefiImageRelocateImageInplaceForExecution (&ImageContext);
  ASSERT_EFI_ERROR (Status);

  return Status;
}

/**
  Find the PE32 Data for an FFS file.

  @param FileHandle       Pointer to the FFS file header of the image.
  @param Pe32Data         Pointer to a (VOID *) PE32 Data pointer.

  @retval EFI_SUCCESS      Image is successfully loaded.
  @retval EFI_NOT_FOUND    Fail to locate PE32 Data.

**/
EFI_STATUS
PeiGetPe32Data (
  IN     EFI_PEI_FILE_HANDLE  FileHandle,
  OUT    VOID                 **Pe32Data,
  OUT    UINT32               *Pe32DataSize
  )
{
  EFI_STATUS  Status;
  UINT32      AuthenticationState;

  *Pe32Data = NULL;

  //
  // Try to find the exe section.
  //
  Status = PeiServicesFfsFindSectionData4 (
             EFI_SECTION_PE32,
             0,
             FileHandle,
             Pe32Data,
             Pe32DataSize,
             &AuthenticationState
             );
  return Status;
}

/**
  Loads a PEIM into memory for subsequent execution. If there are compressed
  images or images that need to be relocated into memory for performance reasons,
  this service performs that transformation.

  @param PeiServices      An indirect pointer to the EFI_PEI_SERVICES table published by the PEI Foundation
  @param FileHandle       Pointer to the FFS file header of the image.
  @param ImageAddressArg  Pointer to PE/TE image.
  @param ImageSizeArg     Size of PE/TE image.
  @param EntryPoint       Pointer to entry point of specified image file for output.
  @param AuthenticationState - Pointer to attestation authentication state of image.

  @retval EFI_SUCCESS      Image is successfully loaded.
  @retval EFI_NOT_FOUND    Fail to locate necessary PPI.
  @retval EFI_UNSUPPORTED  Image Machine Type is not supported.
  @retval EFI_WARN_BUFFER_TOO_SMALL
                           There is not enough heap to allocate the requested size.
                           This will not prevent the XIP image from being invoked.

**/
EFI_STATUS
PeiLoadImageLoadImage (
  IN     CONST EFI_PEI_SERVICES  **PeiServices,
  IN     EFI_PEI_FILE_HANDLE     FileHandle,
  OUT    EFI_PHYSICAL_ADDRESS    *ImageAddressArg   OPTIONAL,
  OUT    UINT64                  *ImageSizeArg      OPTIONAL,
  OUT    EFI_PHYSICAL_ADDRESS    *EntryPoint,
  OUT    UINT32                  *AuthenticationState
  )
{
  EFI_STATUS            Status;
  VOID                  *Pe32Data;
  UINT32                      Pe32DataSize;
  EFI_PHYSICAL_ADDRESS  ImageAddress;
  UINTN                 DebugBase;
  UEFI_IMAGE_LOADER_IMAGE_CONTEXT ImageContext;

  *EntryPoint          = 0;
  *AuthenticationState = 0;

  //
  // Try to find the exe section.
  //
  Status = PeiServicesFfsFindSectionData4 (
             EFI_SECTION_PE32,
             0,
             FileHandle,
             &Pe32Data,
             &Pe32DataSize,
             AuthenticationState
             );
  if (EFI_ERROR (Status)) {
    //
    // PEI core only carry the loader function for PE32 executables
    // If this two section does not exist, just return.
    //
    return Status;
  }

  DEBUG ((DEBUG_INFO, "Loading PEIM %g\n", FileHandle));

  //
  // If memory is installed, perform the shadow operations
  //
  Status = LoadAndRelocateUefiImage (
             FileHandle,
             Pe32Data,
    Pe32DataSize,
    &ImageContext,
    &ImageAddress,
    &DebugBase
             );

  if (EFI_ERROR (Status)) {
    return Status;
  }

  //
  // Got the entry point from the loaded Pe32Data
  //
  *EntryPoint = UefiImageLoaderGetImageEntryPoint (&ImageContext);

  if (ImageAddressArg != NULL) {
    *ImageAddressArg = ImageAddress;
  }

  if (ImageSizeArg != NULL) {
    *ImageSizeArg =UefiImageGetImageSize (&ImageContext);
  }

  DEBUG_CODE_BEGIN ();
    CHAR8  EfiFileName[512];
    UINT16 Machine;

    Machine = UefiImageGetMachine (&ImageContext);

    //
    // Print debug message: Loading PEIM at 0x12345678 EntryPoint=0x12345688 Driver.efi
    //
    if (Machine != EFI_IMAGE_MACHINE_IA64) {
      DEBUG ((DEBUG_INFO | DEBUG_LOAD, "Loading PEIM at 0x%11p DebugBase=0x%11p EntryPoint=0x%11p ", (VOID *)(UINTN)ImageAddress, (VOID *)(UINTN)DebugBase, (VOID *)(UINTN)*EntryPoint));
    } else {
      //
      // For IPF Image, the real entry point should be print.
      //
      DEBUG ((DEBUG_INFO | DEBUG_LOAD, "Loading PEIM at 0x%11p DebugBase=0x%11p EntryPoint=0x%11p ", (VOID *)(UINTN)ImageAddress, (VOID *)(UINTN)DebugBase, (VOID *)(UINTN)(*(UINT64 *)(UINTN)*EntryPoint)));
    }

    //
    // Print Module Name by PeImage PDB file name.
    //
    Status = UefiImageGetModuleNameFromSymbolsPath (
               &ImageContext,
               EfiFileName,
               sizeof (EfiFileName)
               );

    if (!RETURN_ERROR (Status)) {
      DEBUG ((DEBUG_INFO | DEBUG_LOAD, "%a", EfiFileName));
    }

  DEBUG_CODE_END ();

  DEBUG ((DEBUG_INFO | DEBUG_LOAD, "\n"));

  return EFI_SUCCESS;
}

/**
  The wrapper function of PeiLoadImageLoadImage().

  @param This            - Pointer to EFI_PEI_LOAD_FILE_PPI.
  @param FileHandle      - Pointer to the FFS file header of the image.
  @param ImageAddressArg - Pointer to PE/TE image.
  @param ImageSizeArg    - Size of PE/TE image.
  @param EntryPoint      - Pointer to entry point of specified image file for output.
  @param AuthenticationState - Pointer to attestation authentication state of image.

  @return Status of PeiLoadImageLoadImage().

**/
EFI_STATUS
EFIAPI
PeiLoadImageLoadImageWrapper (
  IN     CONST EFI_PEI_LOAD_FILE_PPI  *This,
  IN     EFI_PEI_FILE_HANDLE          FileHandle,
  OUT    EFI_PHYSICAL_ADDRESS         *ImageAddressArg   OPTIONAL,
  OUT    UINT64                       *ImageSizeArg      OPTIONAL,
  OUT    EFI_PHYSICAL_ADDRESS         *EntryPoint,
  OUT    UINT32                       *AuthenticationState
  )
{
  return PeiLoadImageLoadImage (
           GetPeiServicesTablePointer (),
           FileHandle,
           ImageAddressArg,
           ImageSizeArg,
           EntryPoint,
           AuthenticationState
           );
}

/**
  Check whether the input image has the relocation.

  @param  Pe32Data   Pointer to the PE/COFF image.

  @retval TRUE       Relocation is stripped.
  @retval FALSE      Relocation is not stripped.

**/
/*BOOLEAN
RelocationIsStrip (
  IN VOID  *Pe32Data
  )
{
  EFI_IMAGE_OPTIONAL_HEADER_PTR_UNION  Hdr;
  EFI_IMAGE_DOS_HEADER                 *DosHdr;

  ASSERT (Pe32Data != NULL);

  DosHdr = (EFI_IMAGE_DOS_HEADER *)Pe32Data;
  if (DosHdr->e_magic == EFI_IMAGE_DOS_SIGNATURE) {
    //
    // DOS image header is present, so read the PE header after the DOS image header.
    //
    Hdr.Pe32 = (EFI_IMAGE_NT_HEADERS32 *)((UINTN)Pe32Data + (UINTN)((DosHdr->e_lfanew) & 0x0ffff));
  } else {
    //
    // DOS image header is not present, so PE header is at the image base.
    //
    Hdr.Pe32 = (EFI_IMAGE_NT_HEADERS32 *)Pe32Data;
  }

  //
  // Three cases with regards to relocations:
  // - Image has base relocs, RELOCS_STRIPPED==0    => image is relocatable
  // - Image has no base relocs, RELOCS_STRIPPED==1 => Image is not relocatable
  // - Image has no base relocs, RELOCS_STRIPPED==0 => Image is relocatable but
  //   has no base relocs to apply
  // Obviously having base relocations with RELOCS_STRIPPED==1 is invalid.
  //
  // Look at the file header to determine if relocations have been stripped, and
  // save this info in the image context for later use.
  //
  if (Hdr.Pe32->Signature == EFI_IMAGE_NT_SIGNATURE) {
    if ((Hdr.Pe32->FileHeader.Characteristics & EFI_IMAGE_FILE_RELOCS_STRIPPED) != 0) {
      return TRUE;
    } else {
      return FALSE;
    }
  }

  return FALSE;
}*/

/**
  Routine to load image file for subsequent execution by LoadFile Ppi.
  If any LoadFile Ppi is not found, the build-in support function for the PE32+/TE
  XIP image format is used.

  @param PeiServices     - An indirect pointer to the EFI_PEI_SERVICES table published by the PEI Foundation
  @param FileHandle      - Pointer to the FFS file header of the image.
  @param PeimState       - The dispatch state of the input PEIM handle.
  @param EntryPoint      - Pointer to entry point of specified image file for output.
  @param AuthenticationState - Pointer to attestation authentication state of image.

  @retval EFI_SUCCESS    - Image is successfully loaded.
  @retval EFI_NOT_FOUND  - Fail to locate necessary PPI
  @retval Others         - Fail to load file.

**/
EFI_STATUS
PeiLoadImage (
  IN     CONST EFI_PEI_SERVICES  **PeiServices,
  IN     EFI_PEI_FILE_HANDLE     FileHandle,
  IN     UINT8                   PeimState,
  OUT    EFI_PHYSICAL_ADDRESS    *EntryPoint,
  OUT    UINT32                  *AuthenticationState
  )
{
  EFI_STATUS             PpiStatus;
  EFI_STATUS             Status;
  UINTN                  Index;
  EFI_PEI_LOAD_FILE_PPI  *LoadFile;
  EFI_PHYSICAL_ADDRESS   ImageAddress;
  UINT64                 ImageSize;
  //BOOLEAN                 IsStrip;

  //IsStrip = FALSE;
  //
  // If any instances of PEI_LOAD_FILE_PPI are installed, they are called.
  // one at a time, until one reports EFI_SUCCESS.
  //
  Index = 0;
  do {
    PpiStatus = PeiServicesLocatePpi (
                  &gEfiPeiLoadFilePpiGuid,
                  Index,
                  NULL,
                  (VOID **)&LoadFile
                  );
    if (!EFI_ERROR (PpiStatus)) {
      Status = LoadFile->LoadFile (
                           LoadFile,
                           FileHandle,
                           &ImageAddress,
                           &ImageSize,
                           EntryPoint,
                           AuthenticationState
                           );
      if (!EFI_ERROR (Status) || (Status == EFI_WARN_BUFFER_TOO_SMALL)) {
        //
        // The shadowed PEIM must be relocatable.
        //
        // FIXME:
        /*if (PeimState == PEIM_STATE_REGISTER_FOR_SHADOW) {
          // FIXME: Assumes headers were loaded into the image memory
          IsStrip = RelocationIsStrip ((VOID *)(UINTN)ImageAddress);
          ASSERT (!IsStrip);
          if (IsStrip) {
            return EFI_UNSUPPORTED;
          }
        }

        //
        // The image to be started must have the machine type supported by PeiCore.
        //
        ASSERT (EFI_IMAGE_MACHINE_TYPE_SUPPORTED (UefiImageLoaderGetMachineType ((VOID *)(UINTN)ImageAddress)));
        if (!EFI_IMAGE_MACHINE_TYPE_SUPPORTED (UefiImageLoaderGetMachineType ((VOID *)(UINTN)ImageAddress))) {
          return EFI_UNSUPPORTED;
        }*/

        return EFI_SUCCESS;
      }
    }

    Index++;
  } while (!EFI_ERROR (PpiStatus));

  return PpiStatus;
}

/**

  Install Pei Load File PPI.


  @param PrivateData     - Pointer to PEI_CORE_INSTANCE.
  @param OldCoreData     - Pointer to PEI_CORE_INSTANCE.

**/
VOID
InitializeImageServices (
  IN  PEI_CORE_INSTANCE  *PrivateData,
  IN  PEI_CORE_INSTANCE  *OldCoreData
  )
{
  if (OldCoreData == NULL) {
    //
    // The first time we are XIP (running from FLASH). We need to remember the
    // FLASH address so we can reinstall the memory version that runs faster
    //
    PrivateData->XipLoadFile = &gPpiLoadFilePpiList;
    PeiServicesInstallPpi (PrivateData->XipLoadFile);
  } else {
    //
    // 2nd time we are running from memory so replace the XIP version with the
    // new memory version.
    //
    PeiServicesReInstallPpi (PrivateData->XipLoadFile, &gPpiLoadFilePpiList);
  }
}
