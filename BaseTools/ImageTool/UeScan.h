#ifndef UE_SCAN_H
#define UE_SCAN_H

#include "ImageTool.h"

RETURN_STATUS
ScanUeGetRelocInfo (
  OUT image_tool_reloc_info_t          *RelocInfo,
  IN  const image_tool_segment_info_t  *SegmentInfo,
  IN  UE_LOADER_IMAGE_CONTEXT          *Context
  );

RETURN_STATUS
ScanUeGetSegmentInfo (
  OUT image_tool_segment_info_t  *SegmentInfo,
  IN  UE_LOADER_IMAGE_CONTEXT    *Context
  );

#endif // UE_SCAN_H
