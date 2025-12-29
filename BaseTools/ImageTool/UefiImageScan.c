/** @file
  Copyright (c) 2023, Marvin Häuser. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause
**/

#include "ImageTool.h"

#include <Uefi/UefiBaseType.h>

#include <Library/UefiImageLib.h>

#include "PeScan.h"

static
bool
ScanUefiImageGetHeaderInfo (
  OUT image_tool_header_info_t         *HeaderInfo,
  IN  UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  RETURN_STATUS  Status;
  UINT64         Address;

  assert (HeaderInfo != NULL);
  assert (Context    != NULL);

  HeaderInfo->BaseAddress       = UefiImageGetPreferredAddress (Context);
  HeaderInfo->EntryPointAddress = UefiImageGetEntryPointAddress (Context);
  HeaderInfo->Machine           = UefiImageGetMachine (Context);
  HeaderInfo->Subsystem         = UefiImageGetSubsystem (Context);
  // FIXME:
  HeaderInfo->IsXip = true;

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
bool
ScanUefiImageGetRelocInfo (
  OUT image_tool_reloc_info_t          *RelocInfo,
  IN  UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  UINT8  FormatIndex;

  assert (RelocInfo != NULL);
  assert (Context != NULL);

  FormatIndex = UefiImageGetFormat (Context);

  RelocInfo->RelocsStripped = UefiImageGetRelocsStripped (Context);

  if (FormatIndex == UefiImageFormatPe) {
    return ScanPeGetRelocInfo (
             RelocInfo,
             (PE_COFF_LOADER_IMAGE_CONTEXT *)Context
             );
  }

  fprintf (
    stderr,
    "ImageTool: Unsupported UefiImage format %u\n",
    FormatIndex
    );
  return false;
}

static
bool
ScanUefiImageGetSegmentInfo (
  OUT image_tool_segment_info_t        *SegmentInfo,
  IN  UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  UINT8  FormatIndex;

  assert (SegmentInfo != NULL);
  assert (Context != NULL);

  FormatIndex = UefiImageGetFormat (Context);

  SegmentInfo->SegmentAlignment = UefiImageGetSegmentAlignment (Context);

  if (FormatIndex == UefiImageFormatPe) {
    return ScanPeGetSegmentInfo (
             SegmentInfo,
             (PE_COFF_LOADER_IMAGE_CONTEXT *)Context
             );
  }

  fprintf (
    stderr,
    "ImageTool: Unsupported UefiImage format %u\n",
    FormatIndex
    );
  return false;
}

bool
ScanUefiImageGetDebugInfo (
  OUT image_tool_debug_info_t          *DebugInfo,
  IN  UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  RETURN_STATUS  Status;
  const CHAR8    *SymbolsPath;
  UINT32         SymbolsPathSize;

  assert (DebugInfo != NULL);
  assert (Context   != NULL);

  Status = UefiImageGetSymbolsPath (Context, &SymbolsPath, &SymbolsPathSize);
  if (Status == RETURN_NOT_FOUND) {
    return true;
  }

  if (RETURN_ERROR (Status)) {
    fprintf (stderr, "ImageTool: Could not get SymbolsPath\n");
    return false;
  }

  assert (SymbolsPathSize >= 1);

  DebugInfo->SymbolsPath = malloc (SymbolsPathSize + 1);
  if (DebugInfo->SymbolsPath == NULL) {
    fprintf (stderr, "ImageTool: Could not allocate memory for SymbolsPath\n");
    return false;
  }

  memmove (DebugInfo->SymbolsPath, SymbolsPath, SymbolsPathSize);
  assert (DebugInfo->SymbolsPath[SymbolsPathSize - 1] == '\0');

  DebugInfo->SymbolsPathLen = SymbolsPathSize - 1;

  return true;
}

bool
ScanUefiImageGetHiiInfo (
  OUT image_tool_hii_info_t            *HiiInfo,
  IN  UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  RETURN_STATUS  Status;
  UINT32         HiiRva;
  UINT32         HiiSize;
  const char     *ImageBuffer;

  assert (HiiInfo != NULL);
  assert (Context != NULL);

  Status = UefiImageGetHiiDataRva (Context, &HiiRva, &HiiSize);
  if (Status == RETURN_NOT_FOUND) {
    return true;
  }

  if (RETURN_ERROR (Status)) {
    fprintf (stderr, "ImageTool: Malformed HII data\n");
    return false;
  }

  HiiInfo->Data = malloc (HiiSize);
  if (HiiInfo->Data == NULL) {
    fprintf (stderr, "ImageTool: Could not allocate memory for HiiInfo Data\n");
    return false;
  }

  ImageBuffer = (char *)UefiImageLoaderGetImageAddress (Context);

  memmove (HiiInfo->Data, ImageBuffer + HiiRva, HiiSize);
  HiiInfo->DataSize = HiiSize;

  return true;
}

RETURN_STATUS
ToolContextConstructUefiImage (
  OUT image_tool_image_info_t  *Image,
  OUT int8_t                   *Format,
  IN  const void               *File,
  IN  size_t                   FileSize
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

  assert (Image != NULL);
  assert (File != NULL || FileSize == 0);

  if (FileSize > MAX_UINT32) {
    fprintf (stderr, "ImageTool: FileSize is too huge\n");
    return RETURN_UNSUPPORTED;
  }

  Status = UefiImageInitializeContext (&Context, File, (UINT32)FileSize);
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
  if (RETURN_ERROR (Status)) {
    fprintf (stderr, "ImageTool: Could not Load Image\n");
    FreeAlignedPages (Destination, DestinationPages);
    return RETURN_VOLUME_CORRUPTED;
  }

  memset (Image, 0, sizeof (*Image));

  Success = ScanUefiImageGetHeaderInfo (&Image->HeaderInfo, &Context);
  if (!Success) {
    fprintf (stderr, "ImageTool: Could not retrieve header info\n");
    FreeAlignedPages (Destination, DestinationPages);
    return RETURN_VOLUME_CORRUPTED;
  }

  Success = ScanUefiImageGetSegmentInfo (&Image->SegmentInfo, &Context);
  if (!Success) {
    fprintf (stderr, "ImageTool: Could not retrieve segment info\n");
    FreeAlignedPages (Destination, DestinationPages);
    return RETURN_VOLUME_CORRUPTED;
  }

  Success = ScanUefiImageGetRelocInfo (&Image->RelocInfo, &Context);
  if (!Success) {
    fprintf (stderr, "ImageTool: Could not retrieve reloc info\n");
    FreeAlignedPages (Destination, DestinationPages);
    return RETURN_VOLUME_CORRUPTED;
  }

  Success = ScanUefiImageGetHiiInfo (&Image->HiiInfo, &Context);
  if (!Success) {
    fprintf (stderr, "ImageTool: Could not retrieve HII info\n");
    FreeAlignedPages (Destination, DestinationPages);
    return RETURN_VOLUME_CORRUPTED;
  }

  Success = ScanUefiImageGetDebugInfo (&Image->DebugInfo, &Context);
  if (!Success) {
    fprintf (stderr, "ImageTool: Could not retrieve debug info\n");
    FreeAlignedPages (Destination, DestinationPages);
    return RETURN_VOLUME_CORRUPTED;
  }

  FreeAlignedPages (Destination, DestinationPages);

  return RETURN_SUCCESS;
}
