/** @file
  Copyright (c) 2023, Marvin Häuser. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause
**/

#ifndef PE_EMIT_COMMON_H
#define PE_EMIT_COMMON_H

#include <stdint.h>

#include "ImageTool.h"

void *
ToolImageEmitPe32 (
  const image_tool_image_info_t  *Image,
  uint32_t                       *FileSize,
  bool                           Xip
  );

void *
ToolImageEmitPe64 (
  const image_tool_image_info_t  *Image,
  uint32_t                       *FileSize,
  bool                           Xip
  );

#endif // PE_EMIT_COMMON_H
