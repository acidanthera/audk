/** @file
  Copyright (c) 2023, Marvin Häuser. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause
**/

#include "PeEmitCommon.h"

void *
ToolImageEmitPe (
  image_tool_image_info_t  *Image,
  uint32_t                 *FileSize,
  bool                     Xip,
  bool                     Strip
  )
{
  if (Strip) {
    ToolImageStripRelocs (Image);
  }

  switch (Image->HeaderInfo.Machine) {
    case IMAGE_FILE_MACHINE_I386:
    case IMAGE_FILE_MACHINE_ARMTHUMB_MIXED:
    {
      return ToolImageEmitPe32 (Image, FileSize, Xip);
    }

    case IMAGE_FILE_MACHINE_X64:
    case IMAGE_FILE_MACHINE_ARM64:
    {
      return ToolImageEmitPe64 (Image, FileSize, Xip);
    }

    default:
    {
      assert (false);
    }
  }

  return NULL;
}
