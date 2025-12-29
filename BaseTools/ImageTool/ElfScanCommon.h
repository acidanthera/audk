/** @file
  Copyright (c) 2023, Marvin Häuser. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause
**/

#ifndef ELF_SCAN_COMMON_H
#define ELF_SCAN_COMMON_H

#include <stdint.h>

#include "ImageTool.h"

RETURN_STATUS
ScanElf32 (
  OUT image_tool_image_info_t  *ImageInfo,
  IN  const void               *File,
  IN  uint32_t                 FileSize,
  IN  const char               *SymbolsPath OPTIONAL
  );

RETURN_STATUS
ScanElf64 (
  OUT image_tool_image_info_t  *ImageInfo,
  IN  const void               *File,
  IN  uint32_t                 FileSize,
  IN  const char               *SymbolsPath OPTIONAL
  );

#endif // ELF_SCAN_COMMON_H
