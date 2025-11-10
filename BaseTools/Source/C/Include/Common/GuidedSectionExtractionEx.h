/** @file
  This file declares GUIDed section extraction protocol.

  This interface provides a means of decoding a GUID defined encapsulation
  section. There may be multiple different GUIDs associated with the GUIDed
  section extraction protocol. That is, all instances of the GUIDed section
  extraction protocol must have the same interface structure.

  @par Revision Reference: PI
  Version 1.00.

  Copyright (c) 2006 - 2018, Intel Corporation. All rights reserved.<BR>

  SPDX-License-Identifier: BSD-2-Clause-Patent

**/

#ifndef __BT_EFI_GUIDED_SECTION_EXTRACTION_PROTOCOL_H__
#define __BT_EFI_GUIDED_SECTION_EXTRACTION_PROTOCOL_H__

#include <Protocol/GuidedSectionExtraction.h>
#include <Guid/Crc32GuidedSectionExtraction.h>

//
// Protocol GUID definition. Each GUIDed section extraction protocol has the
// same interface but with different GUID. All the GUIDs is defined here.
// May add multiple GUIDs here.
//
#define EFI_CRC32_GUIDED_SECTION_EXTRACTION_PROTOCOL_GUID  EFI_CRC32_GUIDED_SECTION_EXTRACTION_GUID

//
// may add other GUID here
//
#define gEfiCrc32GuidedSectionExtractionProtocolGuid  gEfiCrc32GuidedSectionExtractionGuid

#endif