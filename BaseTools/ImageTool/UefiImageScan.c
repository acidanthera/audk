/** @file
  Copyright (c) 2023, Marvin Häuser. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause
**/

#include "ImageTool.h"

#include <Uefi/UefiBaseType.h>

#include <Library/UefiImageLib.h>

#include "PeScan.h"
#include "UeScan.h"

static
bool
ScanUefiImageGetHeaderInfo (
  OUT image_tool_header_info_t         *HeaderInfo,
  IN  UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  RETURN_STATUS  Status;
  UINT64         Address;

  HeaderInfo->BaseAddress       = UefiImageGetBaseAddress (Context);
  HeaderInfo->EntryPointAddress = UefiImageGetEntryPointAddress (Context);
  HeaderInfo->Machine           = UefiImageGetMachine (Context);
  if (HeaderInfo->Machine == 0xFFFF) {
    DEBUG_RAISE ();
    return false;
  }

  HeaderInfo->Subsystem = UefiImageGetSubsystem (Context);

  Status = UefiImageGetFixedAddress (Context, &Address);
  if (!RETURN_ERROR (Status)) {
    if (Address != HeaderInfo->BaseAddress) {
      fprintf (
        stderr,
        "ImageTool: Images with a fixed address different from their base address are not supported.\n"
        );
      return false;
    }

    HeaderInfo->FixedAddress = true;
  } else if (Status != RETURN_NOT_FOUND) {
    return false;
  }

  return true;
}

static
RETURN_STATUS
ScanUefiImageGetRelocInfo (
  OUT image_tool_reloc_info_t          *RelocInfo,
  IN  const image_tool_segment_info_t  *SegmentInfo,
  IN  UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  UINT8  FormatIndex;

  FormatIndex = UefiImageGetFormat (Context);

  RelocInfo->RelocsStripped = UefiImageGetRelocsStripped (Context);

  if (FormatIndex == UefiImageFormatPe) {
    return ScanPeGetRelocInfo (RelocInfo, &Context->Ctx.Pe);
  }

  // LCOV_EXCL_START
  if (FormatIndex == UefiImageFormatUe) {
    // LCOV_EXCL_STOP
    return ScanUeGetRelocInfo (RelocInfo, SegmentInfo, &Context->Ctx.Ue);
  }

  // LCOV_EXCL_START
  fprintf (
    stderr,
    "ImageTool: Unsupported UefiImage format %u\n",
    FormatIndex
    );
  assert (false);
  return RETURN_UNSUPPORTED;
  // LCOV_EXCL_STOP
}

static
RETURN_STATUS
ScanUefiImageGetSegmentInfo (
  OUT image_tool_segment_info_t        *SegmentInfo,
  IN  UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  UINT8  FormatIndex;

  FormatIndex = UefiImageGetFormat (Context);

  SegmentInfo->SegmentAlignment = UefiImageGetSegmentAlignment (Context);

  if (FormatIndex == UefiImageFormatPe) {
    return ScanPeGetSegmentInfo (SegmentInfo, &Context->Ctx.Pe);
  }

  // LCOV_EXCL_START
  if (FormatIndex == UefiImageFormatUe) {
    // LCOV_EXCL_STOP
    return ScanUeGetSegmentInfo (SegmentInfo, &Context->Ctx.Ue);
  }

  // LCOV_EXCL_START
  fprintf (
    stderr,
    "ImageTool: Unsupported UefiImage format %u\n",
    FormatIndex
    );
  assert (false);
  return RETURN_UNSUPPORTED;
  // LCOV_EXCL_STOP
}

RETURN_STATUS
ScanUefiImageGetDebugInfo (
  OUT image_tool_debug_info_t          *DebugInfo,
  IN  UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  RETURN_STATUS  Status;
  const CHAR8    *SymbolsPath;
  UINT32         SymbolsPathSize;

  Status = UefiImageGetSymbolsPath (Context, &SymbolsPath, &SymbolsPathSize);
  if ((Status == RETURN_NOT_FOUND) || (Status == RETURN_UNSUPPORTED)) {
    return RETURN_SUCCESS;
  }

  if (RETURN_ERROR (Status)) {
    fprintf (stderr, "ImageTool: Could not get SymbolsPath\n");
    return Status;
  }

  assert (SymbolsPathSize >= 1);

  DebugInfo->SymbolsPath = AllocateCopyPool (SymbolsPathSize, SymbolsPath);
  if (DebugInfo->SymbolsPath == NULL) {
    fprintf (stderr, "ImageTool: Could not allocate memory for SymbolsPath\n");
    return RETURN_OUT_OF_RESOURCES;
  }

  assert (DebugInfo->SymbolsPath[SymbolsPathSize - 1] == '\0');

  DebugInfo->SymbolsPathLen = SymbolsPathSize - 1;

  return RETURN_SUCCESS;
}

RETURN_STATUS
ScanUefiImageGetHiiInfo (
  OUT image_tool_hii_info_t            *HiiInfo,
  IN  UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  RETURN_STATUS  Status;
  UINT32         HiiRva;
  UINT32         HiiSize;
  const char     *ImageBuffer;

  Status = UefiImageGetHiiDataRva (Context, &HiiRva, &HiiSize);
  if (Status == RETURN_NOT_FOUND) {
    return RETURN_SUCCESS;
  }

  if (RETURN_ERROR (Status)) {
    fprintf (stderr, "ImageTool: Malformed HII data\n");
    return Status;
  }

  ImageBuffer = (char *)UefiImageLoaderGetImageAddress (Context);

  HiiInfo->Data = AllocateCopyPool (HiiSize, ImageBuffer + HiiRva);
  if (HiiInfo->Data == NULL) {
    fprintf (stderr, "ImageTool: Could not allocate memory for HiiInfo Data\n");
    return RETURN_OUT_OF_RESOURCES;
  }

  HiiInfo->DataSize = HiiSize;

  return RETURN_SUCCESS;
}

RETURN_STATUS
ToolContextConstructUefiImage (
  OUT image_tool_image_info_t  *Image,
  OUT int8_t                   *Format,
  IN  const void               *File,
  IN  uint32_t                 FileSize
  )
{
  RETURN_STATUS                    Status;
  UEFI_IMAGE_LOADER_IMAGE_CONTEXT  Context;
  UINT32                           ImageSize;
  UINT32                           ImageAlignment;
  UINT32                           DestinationPages;
  UINT32                           DestinationSize;
  void                             *Destination;
  bool                             Success;

  assert (File != NULL || FileSize == 0);

  Status = UefiImageInitializeContext (
             &Context,
             File,
             (UINT32)FileSize,
             UEFI_IMAGE_SOURCE_FV
             );
  if (RETURN_ERROR (Status)) {
    return Status;
  }

  *Format = (int8_t)UefiImageGetFormat (&Context);

  ImageSize        = UefiImageGetImageSize (&Context);
  DestinationPages = EFI_SIZE_TO_PAGES (ImageSize);
  DestinationSize  = EFI_PAGES_TO_SIZE (DestinationPages);
  ImageAlignment   = UefiImageGetSegmentAlignment (&Context);

  Destination = AllocateAlignedCodePages (DestinationPages, ImageAlignment);
  if (Destination == NULL) {
    fprintf (stderr, "ImageTool: Could not allocate Destination buffer\n");
    return RETURN_OUT_OF_RESOURCES;
  }

  Status = UefiImageLoadImage (&Context, Destination, DestinationSize);
  // LCOV_EXCL_START
  if (RETURN_ERROR (Status)) {
    fprintf (stderr, "ImageTool: Could not Load Image\n");
    FreeAlignedPages (Destination, DestinationPages);
    return Status;
  }

  // LCOV_EXCL_STOP

  memset (Image, 0, sizeof (*Image));

  Success = ScanUefiImageGetHeaderInfo (&Image->HeaderInfo, &Context);
  if (!Success) {
    fprintf (stderr, "ImageTool: Could not retrieve header info\n");
    ToolImageDestruct (Image);
    FreeAlignedPages (Destination, DestinationPages);
    return RETURN_VOLUME_CORRUPTED;
  }

  Status = ScanUefiImageGetSegmentInfo (&Image->SegmentInfo, &Context);
  if (RETURN_ERROR (Status)) {
    fprintf (stderr, "ImageTool: Could not retrieve segment info\n");
    ToolImageDestruct (Image);
    FreeAlignedPages (Destination, DestinationPages);
    return Status;
  }

  Status = ScanUefiImageGetRelocInfo (
             &Image->RelocInfo,
             &Image->SegmentInfo,
             &Context
             );
  if (RETURN_ERROR (Status)) {
    fprintf (stderr, "ImageTool: Could not retrieve reloc info\n");
    ToolImageDestruct (Image);
    FreeAlignedPages (Destination, DestinationPages);
    return Status;
  }

  Status = ScanUefiImageGetHiiInfo (&Image->HiiInfo, &Context);
  if (RETURN_ERROR (Status)) {
    fprintf (stderr, "ImageTool: Could not retrieve HII info\n");
    ToolImageDestruct (Image);
    FreeAlignedPages (Destination, DestinationPages);
    return Status;
  }

  Status = ScanUefiImageGetDebugInfo (&Image->DebugInfo, &Context);
  if (RETURN_ERROR (Status)) {
    fprintf (stderr, "ImageTool: Could not retrieve debug info\n");
    ToolImageDestruct (Image);
    FreeAlignedPages (Destination, DestinationPages);
    return Status;
  }

  FreeAlignedPages (Destination, DestinationPages);

  return RETURN_SUCCESS;
}
