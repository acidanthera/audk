/** @file
  Copyright (c) 2023, Marvin Häuser. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause
**/

#include "ImageTool.h"

#include <Uefi/UefiBaseType.h>

#include <Library/UefiImageLib.h>

#include <stdlib.h>

#include "ImageToolEmit.h"

static
RETURN_STATUS
ToolContextConstruct (
  OUT image_tool_image_info_t  *ImageInfo,
  OUT int8_t                   *Format,
  IN  const void               *File,
  IN  uint32_t                 FileSize,
  IN  const char               *SymbolsPath OPTIONAL
  )
{
  RETURN_STATUS  Status;

  *Format = -1;

  Status = ToolContextConstructUefiImage (
             ImageInfo,
             Format,
             File,
             FileSize
             );
 #ifndef IMAGE_TOOL_DISABLE_ELF
  if (Status == RETURN_UNSUPPORTED) {
    Status = ScanElf (ImageInfo, File, FileSize, SymbolsPath);
  }

 #endif

  return Status;
}

static
RETURN_STATUS
ValidateOutputFile (
  void                           *OutputFile,
  uint32_t                       OutputFileSize,
  const image_tool_image_info_t  *ImageInfo
  )
{
  RETURN_STATUS            Status;
  bool                     Result;
  image_tool_image_info_t  OutputImageInfo;
  int8_t                   Format;

  Status = ToolContextConstruct (
             &OutputImageInfo,
             &Format,
             OutputFile,
             OutputFileSize,
             NULL
             );
  if (EFI_ERROR (Status)) {
    assert (Status == RETURN_OUT_OF_RESOURCES);
    return Status;
  }

  Result = CheckToolImage (&OutputImageInfo);
  if (!Result) {
    assert (false);
    ToolImageDestruct (&OutputImageInfo);
    return RETURN_UNSUPPORTED;
  }

  Result = ToolImageCompare (&OutputImageInfo, ImageInfo);

  ToolImageDestruct (&OutputImageInfo);

  if (!Result) {
    assert (false);
    return RETURN_VOLUME_CORRUPTED;
  }

  return RETURN_SUCCESS;
}

void *
ToolImageEmit (
  OUT uint32_t    *OutputFileSize,
  IN  const void  *Buffer,
  IN  uint32_t    BufferSize,
  IN  int8_t      Format,
  IN  int32_t     Type,
  IN  bool        Relocate,
  IN  uint64_t    BaseAddress,
  IN  const char  *SymbolsPath OPTIONAL,
  IN  bool        Xip,
  IN  bool        Strip,
  IN  bool        FixedAddress
  )
{
  RETURN_STATUS            Status;
  bool                     Success;
  image_tool_image_info_t  ImageInfo;
  int8_t                   SourceFormat;
  void                     *OutputFile;

  Status = ToolContextConstruct (
             &ImageInfo,
             &SourceFormat,
             Buffer,
             BufferSize,
             SymbolsPath
             );

  if (SymbolsPath == NULL) {
    SymbolsPath = "<unknown>";
  }

  if (RETURN_ERROR (Status)) {
    fprintf (stderr, "ImageTool: Could not parse input file %s - %llx\n", SymbolsPath, (unsigned long long)Status);
    return NULL;
  }

  if (Format == -1) {
    Format = SourceFormat;
    if (Format == -1) {
      fprintf (stderr, "ImageTool: Unknown output format of file %s\n", SymbolsPath);
      ToolImageDestruct (&ImageInfo);
      return NULL;
    }
  }

  if (Type != -1) {
    ImageInfo.HeaderInfo.Subsystem = (uint16_t)Type;
  }

  ToolImageSortRelocs (&ImageInfo);

  Success = CheckToolImage (&ImageInfo);
  if (!Success) {
    DEBUG_RAISE ();
    ToolImageDestruct (&ImageInfo);
    return NULL;
  }

  if (Relocate) {
    Success = ToolImageRelocate (&ImageInfo, BaseAddress, 0);
    if (!Success) {
      fprintf (stderr, "ImageTool: Failed to relocate input file %s\n", SymbolsPath);
      ToolImageDestruct (&ImageInfo);
      return NULL;
    }
  }

  if (FixedAddress) {
    ImageInfo.HeaderInfo.FixedAddress = true;
  }

  OutputFile = NULL;
  if (Format == UefiImageFormatPe) {
    OutputFile = ToolImageEmitPe (&ImageInfo, OutputFileSize, Xip, Strip);
  } else {
    assert (false);
  }

  if (OutputFile == NULL) {
    DEBUG_RAISE ();
    ToolImageDestruct (&ImageInfo);
    return NULL;
  }

  Status = ValidateOutputFile (OutputFile, *OutputFileSize, &ImageInfo);

  ToolImageDestruct (&ImageInfo);

  if (EFI_ERROR (Status)) {
    assert (Status == RETURN_OUT_OF_RESOURCES);
    FreePool (OutputFile);
    return NULL;
  }

  return OutputFile;
}
