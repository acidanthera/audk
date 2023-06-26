/** @file
  Copyright (c) 2023, Marvin Häuser. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause
**/

#ifndef PE_SCAN_H
#define PE_SCAN_H

#include "ImageTool.h"

bool
ScanPeGetRelocInfo (
  OUT image_tool_reloc_info_t       *RelocInfo,
  IN  PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  );

bool
ScanPeGetSegmentInfo (
  OUT image_tool_segment_info_t    *SegmentInfo,
  IN  PE_COFF_LOADER_IMAGE_CONTEXT *Context
  );

#endif // PE_SCAN_H
