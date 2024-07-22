/** @file
  Locate, get and update PE/COFF permissions during Standalone MM
  Foundation Entry point on ARM platforms.

Copyright (c) 2017 - 2021, Arm Ltd. All rights reserved.<BR>
SPDX-License-Identifier: BSD-2-Clause-Patent

**/

#include <PiMm.h>

#include <PiPei.h>
#include <Guid/MmramMemoryReserve.h>
#include <Guid/MpInformation.h>

#include <Library/ArmStandaloneMmCoreEntryPoint.h>
#include <Library/ArmMmuLib.h>
#include <Library/ArmSvcLib.h>
#include <Library/DebugLib.h>
#include <Library/HobLib.h>
#include <Library/BaseLib.h>
#include <Library/BaseMemoryLib.h>
#include <Library/SerialPortLib.h>

#include <IndustryStandard/ArmStdSmc.h>

/**
  Privileged firmware assigns RO & Executable attributes to all memory occupied
  by the Boot Firmware Volume. This function locates the Standalone MM Core
  module PE/COFF image in the BFV and returns this information.

  @param  [in]      BfvAddress        Base Address of Boot Firmware Volume
  @param  [in, out] UefiImage         Pointer to address for allocating memory
                                      for PE/COFF image data
  @param  [in, out] UefiImageSize     Pointer to size of PE/COFF image data

**/
EFI_STATUS
EFIAPI
LocateStandaloneMmCoreUefiImage (
  IN        EFI_FIRMWARE_VOLUME_HEADER  *BfvAddress,
  IN  OUT   VOID                        **UefiImage,
  IN  OUT   UINT32                      *UefiImageSize
  )
{
  EFI_FFS_FILE_HEADER  *FileHeader;
  EFI_STATUS           Status;

  FileHeader = NULL;
  Status     = FfsFindNextFile (
                 EFI_FV_FILETYPE_SECURITY_CORE,
                 BfvAddress,
                 &FileHeader
                 );

  if (EFI_ERROR (Status)) {
    DEBUG ((
      DEBUG_ERROR,
      "Unable to locate Standalone MM FFS file - 0x%x\n",
      Status
      ));
    return Status;
  }

  Status = FfsFindSectionData (
             EFI_SECTION_PE32,
             FileHeader,
             UefiImage,
             (UINTN *)UefiImageSize
             );
  if (EFI_ERROR (Status)) {
    DEBUG ((
      DEBUG_ERROR,
      "Unable to locate Standalone MM Section data - %r\n",
      Status
      ));
    return Status;
  }

  DEBUG ((DEBUG_INFO, "Found Standalone MM PE data - 0x%x\n", *UefiImage));
  return Status;
}
