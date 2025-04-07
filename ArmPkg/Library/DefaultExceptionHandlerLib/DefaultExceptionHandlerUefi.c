/** @file

  Copyright (c) 2008 - 2009, Apple Inc. All rights reserved.<BR>

  SPDX-License-Identifier: BSD-2-Clause-Patent

**/

#include <Uefi.h>
#include <Library/UefiLib.h>

#include <Guid/DebugImageInfoTable.h>

/**
  Use the EFI Debug Image Table to lookup the FaultAddress and find which PE/COFF image
  it came from. As long as the PE/COFF image contains a debug directory entry a
  string can be returned. For ELF and Mach-O images the string points to the Mach-O or ELF
  image. Microsoft tools contain a pointer to the PDB file that contains the debug information.

  @param  FaultAddress         Address to find PE/COFF image for.
  @param  ImageBase            Return load address of found image
  @param  ImageBase            Return debug address of found image

  @retval NULL                 FaultAddress not in a loaded PE/COFF image.
  @retval                      Path and file name of PE/COFF image.

**/
CONST CHAR8 *
GetImageName (
  IN  UINTN  FaultAddress,
  OUT UINTN  *ImageBase,
  OUT UINTN  *DebugBase
  )
{
  EFI_STATUS                         Status;
  EFI_DEBUG_IMAGE_INFO_TABLE_HEADER  *DebugTableHeader;
  EFI_DEBUG_IMAGE_INFO               *DebugTable;
  UINTN                              Entry;
  CHAR8                              *Address;

  Status = EfiGetSystemConfigurationTable (&gEfiDebugImageInfoTableGuid, (VOID **)&DebugTableHeader);
  if (EFI_ERROR (Status)) {
    return NULL;
  }

  DebugTable = DebugTableHeader->EfiDebugImageInfoTable;
  if (DebugTable == NULL) {
    return NULL;
  }

  Address = (CHAR8 *)(UINTN)FaultAddress;
  for (Entry = 0; Entry < DebugTableHeader->TableSize; Entry++, DebugTable++) {
    if (DebugTable->NormalImage2 != NULL) {
      if ((DebugTable->NormalImage2->ImageInfoType == EFI_DEBUG_IMAGE_INFO_TYPE_NORMAL2) &&
          (DebugTable->NormalImage2->LoadedImageProtocolInstance != NULL))
      {
        if ((Address >= (CHAR8 *)DebugTable->NormalImage2->LoadedImageProtocolInstance->ImageBase) &&
            (Address <= ((CHAR8 *)DebugTable->NormalImage2->LoadedImageProtocolInstance->ImageBase + DebugTable->NormalImage2->LoadedImageProtocolInstance->ImageSize)))
        {
          *ImageBase           = (UINTN)DebugTable->NormalImage2->LoadedImageProtocolInstance->ImageBase;
          *DebugBase           = (UINTN)DebugTable->NormalImage2->DebugBase;
          return DebugTable->NormalImage2->PdbPath;
        }
      }
    }
  }

  return NULL;
}
