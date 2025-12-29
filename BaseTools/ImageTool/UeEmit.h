#ifndef UE_EMIT_H
#define UE_EMIT_H

#include <stdint.h>

#include "ImageTool.h"

void *
ToolImageEmitUe (
  image_tool_image_info_t  *Image,
  uint32_t                 *FileSize
  );

#endif // UE_EMIT_H
