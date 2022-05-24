#ifndef IMAGE_TOOL_H
#define IMAGE_TOOL_H

typedef struct {
  uint64_t PreferredAddress;
  uint64_t EntryPointAddress;
  uint8_t  Machine;
  uint8_t  Subsystem;
} image_tool_header_info_t;

typedef struct {
  char     *Name;
  uint8_t  *Data;
  uint64_t DataSize;
  uint64_t ImageAddress;
  uint64_t ImageSize;
  bool     Read;
  bool     Write;
  bool     Execute;
} image_tool_segment_t;

typedef struct {
  uint64_t             SegmentAlignment;
  uint64_t             NumSegments;
  image_tool_segment_t *Segments;
} image_tool_segment_info_t;

typedef struct {
  uint8_t  Type;
  uint64_t Target;
} image_tool_reloc_t;

typedef struct {
  uint64_t           NumRelocs;
  bool               RelocsStripped;
  image_tool_reloc_t *Relocs;
} image_tool_reloc_info_t;

typedef struct {
  char *SymbolsPath;
} image_tool_debug_info_t;

typedef struct {
  void     *Data;
  uint64_t DataSize;
} image_tool_hii_info_t;

typedef struct {
  image_tool_header_info_t  HeaderInfo;
  image_tool_segment_info_t SegmentInfo;
  image_tool_reloc_info_t   RelocInfo;
  image_tool_hii_info_t     HiiInfo;
  image_tool_debug_info_t   DebugInfo;
} image_tool_image_info_t;

#endif // IMAGE_TOOL_H
