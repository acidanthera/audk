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
#include <Library/MemoryAllocationLib.h>
#include <UserFile.h>

#define MAX_PE_ALIGNMENT     0x10000

#define raise() assert(false)

typedef struct {
  EFI_IMAGE_DEBUG_DIRECTORY_ENTRY     Dir;
  EFI_IMAGE_DEBUG_CODEVIEW_NB10_ENTRY Nb10;
  char                                Name[];
} DebugData;

#define PAGE(x)     ((x) & ~4095U)
#define PAGE_OFF(x) ((x) & 4095U)

typedef struct {
  uint64_t BaseAddress;
  uint32_t EntryPointAddress;
  uint16_t Machine;
  uint16_t Subsystem;
  bool     IsXip;
} image_tool_header_info_t;

typedef struct {
  char     *Name;
  uint8_t  *Data;
  uint32_t DataSize;
  uint64_t ImageAddress;
  uint32_t ImageSize;
  bool     Read;
  bool     Write;
  bool     Execute;
} image_tool_segment_t;

typedef struct {
  uint32_t             SegmentAlignment;
  uint32_t             NumSegments;
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
  char     *SymbolsPath;
  uint32_t SymbolsPathLen;
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

void
ToolImageDestruct (
  image_tool_image_info_t *Image
  );

void
ImageShrinkSegmentData (
  const image_tool_image_info_t *Image
  );

bool
ImageConvertToXip (
  image_tool_image_info_t *Image
  );

RETURN_STATUS
ToolContextConstructPe (
  OUT image_tool_image_info_t *Image,
  IN  const void              *File,
  IN  size_t                  FileSize
  );

bool
CheckToolImage (
  image_tool_image_info_t *Image
  );

void *
ToolImageEmitPe (
  const image_tool_image_info_t *Image,
  uint32_t                      *FileSize
  );

RETURN_STATUS
ScanElf (
  OUT image_tool_image_info_t  *ImageInfo,
  IN  const void               *File,
  IN  uint32_t                 FileSize,
  IN  const char               *SymbolsPath
  );

RETURN_STATUS
ConstructHii (
  IN  const char *FileNames[],
  IN  UINT32     NumOfFiles,
  IN  GUID       *HiiGuid,
  OUT void       **Hii,
  OUT UINT32     *HiiSize,
  IN  BOOLEAN    IsElf
  );

#endif // IMAGE_TOOL_H
