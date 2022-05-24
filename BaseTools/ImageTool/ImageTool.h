#ifndef IMAGE_TOOL_H
#define IMAGE_TOOL_H

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

#define raise() assert(false)

typedef struct {
  uint64_t PreferredAddress;
  uint32_t EntryPointAddress;
  uint8_t  Machine;
  uint8_t  Subsystem;
  bool     IsXip;
} image_tool_header_info_t;

typedef enum {
  ToolImageSectionTypeCode,
  ToolImageSectionTypeInitialisedData,
  ToolImageSectionTypeUninitialisedData
} image_tool_type_t;

typedef struct {
  char     *Name;
  uint8_t  *Data;
  uint32_t DataSize;
  uint64_t ImageAddress;
  uint32_t ImageSize;
  bool     Read;
  bool     Write;
  bool     Execute;
  image_tool_type_t Type;
} image_tool_segment_t;

typedef struct {
  uint32_t             SegmentAlignment;
  uint64_t             NumSegments;
  image_tool_segment_t *Segments;
} image_tool_segment_info_t;

typedef struct {
  uint8_t  Type;
  uint32_t Target;
} image_tool_reloc_t;

typedef struct {
  uint32_t           NumRelocs;
  bool               RelocsStripped;
  image_tool_reloc_t *Relocs;
} image_tool_reloc_info_t;

typedef struct {
  char   *SymbolsPath;
  size_t SymbolsPathLen;
} image_tool_debug_info_t;

typedef struct {
  uint32_t DebugDirAddress;
  uint32_t DebugDirSize;
} image_tool_pe_datadir_info_t;

typedef struct {
  void     *Data;
  uint32_t DataSize;
} image_tool_hii_info_t;

typedef struct {
  image_tool_header_info_t  HeaderInfo;
  image_tool_segment_info_t SegmentInfo;
  image_tool_reloc_info_t   RelocInfo;
  image_tool_hii_info_t     HiiInfo;
  image_tool_debug_info_t   DebugInfo;
} image_tool_image_info_t;

void ToolImageDestruct(image_tool_image_info_t *Image);
bool ImageConvertToXip(image_tool_image_info_t *Image);

#endif // IMAGE_TOOL_H
