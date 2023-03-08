/** @file
  The firmware file related definitions in PI.

  @par Revision Reference:
  Version 1.4.

  Copyright (c) 2006 - 2018, Intel Corporation. All rights reserved.<BR>

  SPDX-License-Identifier: BSD-2-Clause-Patent

**/

#ifndef __BT_PI_FIRMWARE_FILE_H__
#define __BT_PI_FIRMWARE_FILE_H__

#include <Uefi/UefiMultiPhase.h>
#include <Pi/PiMultiPhase.h>

#define MAX_FFS_SIZE        0x1000000
#define MAX_SECTION_SIZE    0x1000000

//
// FFS File Attributes.
//
#define FFS_ATTRIB_DATA_ALIGNMENT2    FFS_ATTRIB_DATA_ALIGNMENT_2

//
// CompressionType of EFI_COMPRESSION_SECTION.
//
#define TIANO_COMPRESS            0x02

typedef union {
  EFI_COMMON_SECTION_HEADER         *CommonHeader;
  EFI_COMPRESSION_SECTION           *CompressionSection;
  EFI_GUID_DEFINED_SECTION          *GuidDefinedSection;
  EFI_PE32_SECTION                  *Pe32Section;
  EFI_PIC_SECTION                   *PicSection;
  EFI_TE_SECTION                    *TeSection;
  EFI_PEI_DEPEX_SECTION             *PeimHeaderSection;
  EFI_DXE_DEPEX_SECTION             *DependencySection;
  EFI_VERSION_SECTION               *VersionSection;
  EFI_USER_INTERFACE_SECTION        *UISection;
  EFI_COMPATIBILITY16_SECTION       *Code16Section;
  EFI_FIRMWARE_VOLUME_IMAGE_SECTION *FVImageSection;
  EFI_FREEFORM_SUBTYPE_GUID_SECTION *FreeformSubtypeSection;
  EFI_RAW_SECTION                   *RawSection;
  //
  // For section whose size is equal or greater than 0x1000000
  //
  EFI_COMMON_SECTION_HEADER2         *CommonHeader2;
  EFI_COMPRESSION_SECTION2           *CompressionSection2;
  EFI_GUID_DEFINED_SECTION2          *GuidDefinedSection2;
  EFI_PE32_SECTION2                  *Pe32Section2;
  EFI_PIC_SECTION2                   *PicSection2;
  EFI_TE_SECTION2                    *TeSection2;
  EFI_PEI_DEPEX_SECTION2             *PeimHeaderSection2;
  EFI_DXE_DEPEX_SECTION2             *DependencySection2;
  EFI_VERSION_SECTION2               *VersionSection2;
  EFI_USER_INTERFACE_SECTION2        *UISection2;
  EFI_COMPATIBILITY16_SECTION2       *Code16Section2;
  EFI_FIRMWARE_VOLUME_IMAGE_SECTION2 *FVImageSection2;
  EFI_FREEFORM_SUBTYPE_GUID_SECTION2 *FreeformSubtypeSection2;
  EFI_RAW_SECTION2                   *RawSection2;
} EFI_FILE_SECTION_POINTER;

#endif

