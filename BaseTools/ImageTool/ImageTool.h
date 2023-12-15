/** @file
  Copyright (c) 2021, Marvin Häuser. All rights reserved.
  Copyright (c) 2022, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause
**/

#ifndef IMAGE_TOOL_H
#define IMAGE_TOOL_H

#include <Base.h>

#include <stdbool.h>
#include <errno.h>
#include <assert.h>

#include <IndustryStandard/PeImage2.h>
#include <Library/PeCoffLib2.h>
#include <Library/BaseLib.h>
#include <Library/BaseMemoryLib.h>
#include <Library/BaseOverflowLib.h>
#include <Library/DebugLib.h>
#include <Library/MemoryAllocationLib.h>
#include <UserFile.h>

#define MAX_PE_ALIGNMENT     0x10000

#define PAGE(x)     ((x) & ~4095U)
#define PAGE_OFF(x) ((x) & 4095U)

typedef struct {
  uint64_t BaseAddress;
  uint32_t EntryPointAddress;
  uint16_t Machine;
  uint16_t Subsystem;
  uint8_t  FixedAddress;
  uint8_t  Reserved[7];
} image_tool_header_info_t;

typedef struct {
  uint32_t ImageAddress;
  uint32_t ImageSize;
  uint8_t  Read;
  uint8_t  Write;
  uint8_t  Execute;
  uint8_t  Reserved[1];

  char     *Name;
  uint8_t  *Data;

  uint32_t UnpaddedSize;
} image_tool_segment_t;

typedef struct {
  uint32_t             SegmentAlignment;
  uint16_t             NumSegments;
  uint8_t              Reserved[2];

  image_tool_segment_t *Segments;
} image_tool_segment_info_t;

typedef struct {
  uint8_t  Type;
  uint8_t  Reserved[3];
  uint32_t Target;
} image_tool_reloc_t;

typedef struct {
  uint32_t           NumRelocs;
  uint8_t            RelocsStripped;
  uint8_t            Reserved[3];

  image_tool_reloc_t *Relocs;
} image_tool_reloc_info_t;

typedef struct {
  uint32_t SymbolsPathLen;

  char     *SymbolsPath;
} image_tool_debug_info_t;

typedef struct {
  uint32_t DebugDirAddress;
  uint32_t DebugDirSize;
} image_tool_pe_datadir_info_t;

typedef struct {
  uint32_t DataSize;

  void     *Data;
} image_tool_hii_info_t;

typedef struct {
  image_tool_header_info_t  HeaderInfo;
  image_tool_segment_info_t SegmentInfo;
  image_tool_reloc_info_t   RelocInfo;
  image_tool_hii_info_t     HiiInfo;
  image_tool_debug_info_t   DebugInfo;
} image_tool_image_info_t;

void
ToolImageDestruct (
  image_tool_image_info_t *Image
  );

void
ImageInitUnpaddedSize (
  const image_tool_image_info_t *Image
  );

bool
ToolImageRelocate (
  image_tool_image_info_t *Image,
  uint64_t                BaseAddress,
  uint32_t                IgnorePrefix
  );

void
ToolImageSortRelocs (
  image_tool_image_info_t  *Image
  );

bool
ToolImageCompare (
  const image_tool_image_info_t  *Image1,
  const image_tool_image_info_t  *Image2
  );

void
ToolImageStripRelocs (
  image_tool_image_info_t  *Image
  );

uint8_t
ToolImageGetRelocSize (
  uint8_t  Type
  );

RETURN_STATUS
ToolContextConstructUefiImage (
  OUT image_tool_image_info_t *Image,
  OUT INT8                    *Format,
  IN  const void              *File,
  IN  size_t                  FileSize
  );

bool
CheckToolImage (
  const image_tool_image_info_t *Image
  );

void *
ToolImageEmitPe (
  image_tool_image_info_t *Image,
  uint32_t                *FileSize,
  bool                    Xip,
  bool                    Strip
  );

RETURN_STATUS
ScanElf (
  OUT image_tool_image_info_t  *ImageInfo,
  IN  const void               *File,
  IN  uint32_t                 FileSize,
  IN  const char               *SymbolsPath OPTIONAL
  );

extern CONST UINT8 mHiiResourceSectionHeaderSize;

VOID
InitializeHiiResouceSectionHeader (
  OUT UINT8   *HiiSectionHeader,
  IN  UINT32  HiiDataAddress,
  IN  UINT32  HiiDataSize
  );

RETURN_STATUS
ConstructHii (
  IN  const char *FileNames[],
  IN  UINT32     NumOfFiles,
  IN  GUID       *HiiGuid,
  OUT void       **Hii,
  OUT UINT32     *HiiSize
  );

const image_tool_segment_t *
ImageGetSegmentByAddress (
  uint32_t                        *Address,
  uint32_t                        *RemainingSize,
  const image_tool_segment_info_t *SegmentInfo
  );

#endif // IMAGE_TOOL_H
