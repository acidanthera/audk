/** @file
  Support functions for managing debug image info table when loading and unloading
  images.

Copyright (c) 2006 - 2018, Intel Corporation. All rights reserved.<BR>
SPDX-License-Identifier: BSD-2-Clause-Patent

**/

#include "PiSmmCore.h"

// FIXME: Unify with DXE

EFI_DEBUG_IMAGE_INFO_TABLE_HEADER  mDebugInfoTableHeader = {
  0,          // volatile UINT32                 UpdateStatus;
  0,          // UINT32                          TableSize;
  NULL        // EFI_DEBUG_IMAGE_INFO            *EfiDebugImageInfoTable;
};

UINTN mMaxTableEntries = 0;

#define EFI_DEBUG_TABLE_ENTRY_SIZE       (sizeof (VOID *))

/**
  Creates and initializes the DebugImageInfo Table.  Also creates the configuration
  table and registers it into the system table.

**/
VOID
SmmInitializeDebugImageInfoTable (
  VOID
  )
{
  EFI_STATUS Status;

  //
  // Install the EFI_SYSTEM_TABLE_POINTER structure in the EFI System
  // Configuration Table
  //
  Status = SmmInstallConfigurationTable (
             gSmst,
             &gEfiDebugImageInfoTableGuid,
             &mDebugInfoTableHeader,
             sizeof (mDebugInfoTableHeader)
             );
  ASSERT_EFI_ERROR (Status);
}


/**
  Adds a new DebugImageInfo structure to the DebugImageInfo Table.  Re-Allocates
  the table if it's not large enough to accommodate another entry.

  @param  LoadedImage    pointer to the loaded image protocol for the image being
                         loaded
  @param  ImageHandle    image handle for the image being loaded
  @param  ImageContext   image context for the image being loaded

**/
VOID
SmmNewDebugImageInfoEntry (
  IN       EFI_LOADED_IMAGE_PROTOCOL        *LoadedImage,
  IN       EFI_HANDLE                       ImageHandle,
  IN CONST UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *ImageContext
  )
{
  EFI_DEBUG_IMAGE_INFO          *Table;
  EFI_DEBUG_IMAGE_INFO          *NewTable;
  UINTN                         Index;
  UINTN                         TableSize;
  EFI_DEBUG_IMAGE_INFO_NORMAL2  *NormalImage2;
  RETURN_STATUS                 Status;
  CONST CHAR8                   *PdbPath;
  UINT32                        PdbPathSize;

  //
  // Set the flag indicating that we're in the process of updating the table.
  //
  mDebugInfoTableHeader.UpdateStatus |= EFI_DEBUG_IMAGE_INFO_UPDATE_IN_PROGRESS;

  Table = mDebugInfoTableHeader.EfiDebugImageInfoTable;

  if (mDebugInfoTableHeader.TableSize < mMaxTableEntries) {
    //
    // We still have empty entires in the Table, find the first empty entry.
    //
    Index = 0;
    while (Table[Index].NormalImage2 != NULL) {
      Index++;
    }
    //
    // There must be an empty entry in the in the table.
    //
    ASSERT (Index < mMaxTableEntries);
  } else {
    //
    //  Table is full, so re-allocate another page for a larger table...
    //
    TableSize = mMaxTableEntries * EFI_DEBUG_TABLE_ENTRY_SIZE;
    NewTable = AllocateZeroPool (TableSize + EFI_PAGE_SIZE);
    if (NewTable == NULL) {
      mDebugInfoTableHeader.UpdateStatus &= ~EFI_DEBUG_IMAGE_INFO_UPDATE_IN_PROGRESS;
      return;
    }
    //
    // Copy the old table into the new one
    //
    CopyMem (NewTable, Table, TableSize);
    mDebugInfoTableHeader.EfiDebugImageInfoTable = NewTable;
    //
    // Enlarge the max table entries.
    //
    mMaxTableEntries += EFI_PAGE_SIZE / EFI_DEBUG_TABLE_ENTRY_SIZE;
    //
    // Free the old table
    //
    SmmFreePool (Table);
    //
    // Update the table header
    //
    Table = NewTable;
    //
    // Set the first empty entry index to be the original max table entries.
    //
    Index             = mMaxTableEntries;
  }

  //
  // Allocate data for new entry
  //
  NormalImage2 = AllocateZeroPool (sizeof (EFI_DEBUG_IMAGE_INFO_NORMAL2));
  if (NormalImage2 != NULL) {
    //
    // Update the entry
    //
    NormalImage2->ImageInfoType               = EFI_DEBUG_IMAGE_INFO_TYPE_NORMAL2;
    NormalImage2->LoadedImageProtocolInstance = LoadedImage;
    NormalImage2->ImageHandle                 = ImageHandle;

    Status = UefiImageGetSymbolsPath (ImageContext, &PdbPath, &PdbPathSize);
    if (!RETURN_ERROR (Status)) {
      NormalImage2->PdbPath = AllocateCopyPool (PdbPathSize, PdbPath);
    }

    NormalImage2->DebugBase = UefiImageLoaderGetDebugAddress (ImageContext);
    //
    // Increase the number of EFI_DEBUG_IMAGE_INFO elements and set the mDebugInfoTable in modified status.
    //
    mDebugInfoTableHeader.UpdateStatus |= EFI_DEBUG_IMAGE_INFO_TABLE_MODIFIED;
    Table[Index].NormalImage2 = NormalImage2;
    mDebugInfoTableHeader.TableSize++;
  }
  mDebugInfoTableHeader.UpdateStatus &= ~EFI_DEBUG_IMAGE_INFO_UPDATE_IN_PROGRESS;
}
