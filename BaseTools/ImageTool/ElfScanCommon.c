/** @file
  Copyright (c) 2023, Marvin Häuser. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause
**/

#include "ElfScanCommon.h"

RETURN_STATUS
ScanElf (
  OUT image_tool_image_info_t  *ImageInfo,
  IN  const void               *File,
  IN  uint32_t                 FileSize,
  IN  const char               *SymbolsPath OPTIONAL
  )
{
  RETURN_STATUS  Status;

  Status = ScanElf64 (ImageInfo, File, FileSize, SymbolsPath);
  if (Status == RETURN_UNSUPPORTED) {
    Status = ScanElf32 (ImageInfo, File, FileSize, SymbolsPath);
  }

  return Status;
}
