/** @file
*  Main file supporting the SEC Phase for Versatile Express
*
*  Copyright (c) 2011-2014, ARM Limited. All rights reserved.
*
*  SPDX-License-Identifier: BSD-2-Clause-Patent
*
**/

#include <Uefi.h>
#include <Library/BaseLib.h>
#include <Library/BaseMemoryLib.h>
#include <Library/DebugLib.h>
#include <Library/DebugAgentLib.h>
#include <Library/PcdLib.h>
#include <Library/UefiImageExtraActionLib.h>
#include <Library/UefiImageLib.h>

#include <Pi/PiFirmwareFile.h>
#include <Pi/PiFirmwareVolume.h>

#define GET_OCCUPIED_SIZE(ActualSize, Alignment) \
  (ActualSize) + (((Alignment) - ((ActualSize) & ((Alignment) - 1))) & ((Alignment) - 1))

// Vector Table for Sec Phase
VOID
DebugAgentVectorTable (
  VOID
  );

/**
  Returns the highest bit set of the State field

  @param ErasePolarity   Erase Polarity  as defined by EFI_FVB2_ERASE_POLARITY
                         in the Attributes field.
  @param FfsHeader       Pointer to FFS File Header


  @retval the highest bit in the State field

**/
STATIC
EFI_FFS_FILE_STATE
GetFileState (
  IN UINT8                ErasePolarity,
  IN EFI_FFS_FILE_HEADER  *FfsHeader
  )
{
  EFI_FFS_FILE_STATE  FileState;
  EFI_FFS_FILE_STATE  HighestBit;

  FileState = FfsHeader->State;

  if (ErasePolarity != 0) {
    FileState = (EFI_FFS_FILE_STATE) ~FileState;
  }

  HighestBit = 0x80;
  while (HighestBit != 0 && (HighestBit & FileState) == 0) {
    HighestBit >>= 1;
  }

  return HighestBit;
}

/**
  Calculates the checksum of the header of a file.
  The header is a zero byte checksum, so zero means header is good

  @param FfsHeader       Pointer to FFS File Header

  @retval Checksum of the header

**/
STATIC
UINT8
CalculateHeaderChecksum (
  IN EFI_FFS_FILE_HEADER  *FileHeader
  )
{
  UINT8  Sum;

  // Calculate the sum of the header
  Sum = CalculateSum8 ((CONST VOID *)FileHeader, sizeof (EFI_FFS_FILE_HEADER));

  // State field (since this indicates the different state of file).
  Sum = (UINT8)(Sum - FileHeader->State);

  // Checksum field of the file is not part of the header checksum.
  Sum = (UINT8)(Sum - FileHeader->IntegrityCheck.Checksum.File);

  return Sum;
}

EFI_STATUS
GetFfsFile (
  IN  EFI_FIRMWARE_VOLUME_HEADER  *FwVolHeader,
  IN  EFI_FV_FILETYPE             FileType,
  OUT EFI_FFS_FILE_HEADER         **FileHeader
  )
{
  UINT64               FvLength;
  UINTN                FileOffset;
  EFI_FFS_FILE_HEADER  *FfsFileHeader;
  UINT8                ErasePolarity;
  UINT8                FileState;
  UINT32               FileLength;
  UINT32               FileOccupiedSize;

  ASSERT (FwVolHeader->Signature == EFI_FVH_SIGNATURE);

  FvLength      = FwVolHeader->FvLength;
  FfsFileHeader = (EFI_FFS_FILE_HEADER *)((UINT8 *)FwVolHeader + FwVolHeader->HeaderLength);
  FileOffset    = FwVolHeader->HeaderLength;

  if (FwVolHeader->Attributes & EFI_FVB2_ERASE_POLARITY) {
    ErasePolarity = 1;
  } else {
    ErasePolarity = 0;
  }

  while (FileOffset < (FvLength - sizeof (EFI_FFS_FILE_HEADER))) {
    // Get FileState which is the highest bit of the State
    FileState = GetFileState (ErasePolarity, FfsFileHeader);

    switch (FileState) {
      case EFI_FILE_HEADER_INVALID:
        FileOffset   += sizeof (EFI_FFS_FILE_HEADER);
        FfsFileHeader = (EFI_FFS_FILE_HEADER *)((UINT8 *)FfsFileHeader + sizeof (EFI_FFS_FILE_HEADER));
        break;

      case EFI_FILE_DATA_VALID:
      case EFI_FILE_MARKED_FOR_UPDATE:
        if (CalculateHeaderChecksum (FfsFileHeader) != 0) {
          ASSERT (FALSE);
          return EFI_NOT_FOUND;
        }

        if (FfsFileHeader->Type == FileType) {
          *FileHeader = FfsFileHeader;
          return EFI_SUCCESS;
        }

        FileLength       = *(UINT32 *)(FfsFileHeader->Size) & 0x00FFFFFF;
        FileOccupiedSize = GET_OCCUPIED_SIZE (FileLength, 8);

        FileOffset   += FileOccupiedSize;
        FfsFileHeader = (EFI_FFS_FILE_HEADER *)((UINT8 *)FfsFileHeader + FileOccupiedSize);
        break;

      case EFI_FILE_DELETED:
        FileLength       = *(UINT32 *)(FfsFileHeader->Size) & 0x00FFFFFF;
        FileOccupiedSize = GET_OCCUPIED_SIZE (FileLength, 8);
        FileOffset      += FileOccupiedSize;
        FfsFileHeader    = (EFI_FFS_FILE_HEADER *)((UINT8 *)FfsFileHeader + FileOccupiedSize);
        break;

      default:
        return EFI_NOT_FOUND;
    }
  }

  return EFI_NOT_FOUND;
}

EFI_STATUS
GetImageContext (
  IN  EFI_FFS_FILE_HEADER              *FfsHeader,
  OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *ImageContext
  )
{
  EFI_STATUS                              Status;
  UINTN                                   ParsedLength;
  UINT32                                  SectionSize;
  UINT32                                  SectionLength;
  EFI_COMMON_SECTION_HEADER               *Section;
  VOID                                    *EfiImage;

  Section      = (EFI_COMMON_SECTION_HEADER *)(FfsHeader + 1);
  SectionLength = 0;
  SectionSize  = *(UINT32 *)(FfsHeader->Size) & 0x00FFFFFF;
  SectionSize -= sizeof (EFI_FFS_FILE_HEADER);
  ParsedLength = 0;
  EfiImage     = NULL;

  while (ParsedLength < SectionSize) {
    //
    // Size is 24 bits wide so mask upper 8 bits.
    //
    SectionLength = *(UINT32 *)Section->Size & 0x00FFFFFF;
    if (SectionLength < sizeof (*Section)) {
      return EFI_VOLUME_CORRUPTED;
    }

    if (Section->Type == EFI_SECTION_PE32) {
      EfiImage = (Section + 1);
      break;
    }

    //
    // SectionLength is adjusted it is 4 byte aligned.
    // Go to the next section
    //
    SectionLength = *(UINT32 *)Section->Size & 0x00FFFFFF;
    SectionLength = GET_OCCUPIED_SIZE (SectionLength, 4);
    ASSERT (SectionLength != 0);
    ParsedLength += SectionLength;
    Section       = (EFI_COMMON_SECTION_HEADER *)((UINT8 *)Section + SectionLength);
  }

  if (EfiImage == NULL) {
    return EFI_NOT_FOUND;
  }

  // Initialize the Image Context
  // FIXME: Common FFS API with size checks
  Status = UefiImageInitializeContext (
             ImageContext,
             EfiImage,
             SectionLength - sizeof (*Section),
             UEFI_IMAGE_SOURCE_FV
             );
  if (!EFI_ERROR(Status)) {
    Status = UefiImageLoadImageInplace( ImageContext);
  }

  return Status;
}

/**
  Initialize debug agent.

  This function is used to set up debug environment to support source level debugging.
  If certain Debug Agent Library instance has to save some private data in the stack,
  this function must work on the mode that doesn't return to the caller, then
  the caller needs to wrap up all rest of logic after InitializeDebugAgent() into one
  function and pass it into InitializeDebugAgent(). InitializeDebugAgent() is
  responsible to invoke the passing-in function at the end of InitializeDebugAgent().

  If the parameter Function is not NULL, Debug Agent Library instance will invoke it by
  passing in the Context to be its parameter.

  If Function() is NULL, Debug Agent Library instance will return after setup debug
  environment.

  @param[in] InitFlag     Init flag is used to decide the initialize process.
  @param[in] Context      Context needed according to InitFlag; it was optional.
  @param[in] Function     Continue function called by debug agent library; it was
                          optional.

**/
VOID
EFIAPI
InitializeDebugAgent (
  IN UINT32                InitFlag,
  IN VOID                  *Context  OPTIONAL,
  IN DEBUG_AGENT_CONTINUE  Function  OPTIONAL
  )
{
  EFI_STATUS                      Status;
  EFI_FFS_FILE_HEADER             *FfsHeader;
  UEFI_IMAGE_LOADER_IMAGE_CONTEXT ImageContext;

  // We use InitFlag to know if DebugAgent has been initialized from
  // Sec (DEBUG_AGENT_INIT_PREMEM_SEC) or PrePi (DEBUG_AGENT_INIT_POSTMEM_SEC)
  // modules
  if (InitFlag == DEBUG_AGENT_INIT_PREMEM_SEC) {
    //
    // Get the Sec or PrePeiCore module (defined as SEC type module)
    //
    Status = GetFfsFile ((EFI_FIRMWARE_VOLUME_HEADER *)(UINTN)PcdGet64 (PcdSecureFvBaseAddress), EFI_FV_FILETYPE_SECURITY_CORE, &FfsHeader);
    if (!EFI_ERROR (Status)) {
      Status = GetImageContext (FfsHeader, &ImageContext);
      if (!EFI_ERROR (Status)) {
        UefiImageLoaderRelocateImageExtraAction (&ImageContext);
      }
    }
  } else if (InitFlag == DEBUG_AGENT_INIT_POSTMEM_SEC) {
    //
    // Get the PrePi or PrePeiCore module (defined as SEC type module)
    //
    Status = GetFfsFile ((EFI_FIRMWARE_VOLUME_HEADER *)(UINTN)PcdGet64 (PcdFvBaseAddress), EFI_FV_FILETYPE_SECURITY_CORE, &FfsHeader);
    if (!EFI_ERROR (Status)) {
      Status = GetImageContext (FfsHeader, &ImageContext);
      if (!EFI_ERROR (Status)) {
        UefiImageLoaderRelocateImageExtraAction (&ImageContext);
      }
    }

    //
    // Get the PeiCore module (defined as PEI_CORE type module)
    //
    Status = GetFfsFile ((EFI_FIRMWARE_VOLUME_HEADER *)(UINTN)PcdGet64 (PcdFvBaseAddress), EFI_FV_FILETYPE_PEI_CORE, &FfsHeader);
    if (!EFI_ERROR (Status)) {
      Status = GetImageContext (FfsHeader, &ImageContext);
      if (!EFI_ERROR (Status)) {
        UefiImageLoaderRelocateImageExtraAction (&ImageContext);
      }
    }
  }
}

/**
  Enable/Disable the interrupt of debug timer and return the interrupt state
  prior to the operation.

  If EnableStatus is TRUE, enable the interrupt of debug timer.
  If EnableStatus is FALSE, disable the interrupt of debug timer.

  @param[in] EnableStatus    Enable/Disable.

  @return FALSE always.

**/
BOOLEAN
EFIAPI
SaveAndSetDebugTimerInterrupt (
  IN BOOLEAN  EnableStatus
  )
{
  return FALSE;
}
