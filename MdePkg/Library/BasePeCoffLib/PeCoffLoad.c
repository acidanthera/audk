/** @file
  Implements APIs to load PE/COFF Images.

  Portions copyright (c) 2006 - 2019, Intel Corporation. All rights reserved.<BR>
  Portions copyright (c) 2008 - 2010, Apple Inc. All rights reserved.<BR>
  Portions Copyright (c) 2020, Hewlett Packard Enterprise Development LP. All rights reserved.<BR>
  Copyright (c) 2020 - 2021, Marvin Häuser. All rights reserved.<BR>
  Copyright (c) 2020, Vitaly Cheptsov. All rights reserved.<BR>
  Copyright (c) 2020, ISP RAS. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-3-Clause
**/

#include <Base.h>
#include <Uefi/UefiBaseType.h>

#include <IndustryStandard/PeImage.h>

#include <Library/BaseMemoryLib.h>
#include <Library/DebugLib.h>
#include <Library/PcdLib.h>
#include <Library/PeCoffLib.h>

#include "BasePeCoffLibInternals.h"

/**
  Loads the Image Sections into the memory space and initialises any padding
  with zeros.

  @param[in]  Context           The context describing the Image. Must have been
                                initialised by PeCoffInitializeContext().
  @param[in]  LoadedHeaderSize  The size, in Bytes, of the loaded Image Headers.
  @param[out] Destination       The Image destination memory.
  @param[in]  DestinationSize   The size, in Bytes, of Destination.
                                Must be at least
                                Context->SizeOfImage +
                                Context->SizeOfImageDebugAdd. If the Section
                                Alignment exceeds 4 KB, must be at least
                                Context->SizeOfImage +
                                Context->SizeOfImageDebugAdd
                                Context->SectionAlignment.
**/
STATIC
VOID
InternalLoadSections (
  IN  CONST PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  IN  UINT32                              LoadedHeaderSize,
  OUT VOID                                *Destination,
  IN  UINT32                              DestinationSize
  )
{
  CONST EFI_IMAGE_SECTION_HEADER *Sections;
  UINT16                         Index;
  UINT32                         DataSize;
  UINT32                         PreviousTopRva;

  Sections = (CONST EFI_IMAGE_SECTION_HEADER *) (CONST VOID *) (
               (CONST CHAR8 *) Context->FileBuffer + Context->SectionsOffset
               );
  //
  // As the loop zero's the data from the end of the previous section, start
  // with the size of the loaded Image Headers to zero their trailing data.
  //
  PreviousTopRva = LoadedHeaderSize;

  for (Index = 0; Index < Context->NumberOfSections; ++Index) {
    if (Sections[Index].VirtualSize < Sections[Index].SizeOfRawData) {
      DataSize = Sections[Index].VirtualSize;
    } else {
      DataSize = Sections[Index].SizeOfRawData;
    }
    //
    // Zero from the end of the previous Section to the start of this Section.
    //
    ZeroMem ((CHAR8 *) Destination + PreviousTopRva, Sections[Index].VirtualAddress - PreviousTopRva);
    //
    // Load the current Section into memory.
    //
    CopyMem (
      (CHAR8 *) Destination + Sections[Index].VirtualAddress,
      (CONST CHAR8 *) Context->FileBuffer + (Sections[Index].PointerToRawData - Context->TeStrippedOffset),
      DataSize
      );

    PreviousTopRva = Sections[Index].VirtualAddress + DataSize;
  }
  //
  // Zero the trailer after the last Image Section.
  //
  ZeroMem (
    (CHAR8 *) Destination + PreviousTopRva,
    DestinationSize - PreviousTopRva
    );
}

RETURN_STATUS
PeCoffLoadImage (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  OUT    VOID                          *Destination,
  IN     UINT32                        DestinationSize
  )
{
  CHAR8                          *AlignedDest;
  UINT32                         AlignOffset;
  UINT32                         AlignedSize;
  UINT32                         LoadedHeaderSize;
  CONST EFI_IMAGE_SECTION_HEADER *Sections;
  UINTN                          Address;
  UINTN                          AlignedAddress;

  ASSERT (Context != NULL);
  ASSERT (Destination != NULL);
  ASSERT (Context->SectionAlignment <= DestinationSize);
  //
  // Sufficiently align the Image data in memory.
  //
  if (Context->SectionAlignment <= EFI_PAGE_SIZE) {
    //
    // The caller is required to allocate page memory, hence we have at least
    // 4 KB alignment guaranteed.
    //
    AlignedDest = Destination;
    AlignedSize = DestinationSize;
    AlignOffset = 0;
  } else {
    Address        = (UINTN) Destination;
    AlignedAddress = ALIGN_VALUE (Address, (UINTN) Context->SectionAlignment);
    AlignOffset    = (UINT32) (AlignedAddress - Address);
    AlignedDest    = (CHAR8 *) Destination + AlignOffset;
    AlignedSize    = DestinationSize - AlignOffset;

    ASSERT (Context->SizeOfImage <= AlignedSize);

    ZeroMem (Destination, AlignOffset);
  }

  ASSERT (AlignedSize >= Context->SizeOfImage);
  //
  // Load the Image Headers into the memory space, if the policy demands it.
  //
  Sections = (CONST EFI_IMAGE_SECTION_HEADER *) (CONST VOID *) (
               (CONST CHAR8 *) Context->FileBuffer + Context->SectionsOffset
               );
  if (PcdGetBool (PcdImageLoaderLoadHeader) && Sections[0].VirtualAddress != 0) {
    LoadedHeaderSize = (Context->SizeOfHeaders - Context->TeStrippedOffset);
    CopyMem (AlignedDest, Context->FileBuffer, LoadedHeaderSize);
  } else {
    LoadedHeaderSize = 0;
  }
  //
  // Load all Image Sections into the memory space.
  //
  InternalLoadSections (
    Context,
    LoadedHeaderSize,
    AlignedDest,
    AlignedSize
    );

  Context->ImageBuffer = AlignedDest;
  //
  // Force-load its contents into the memory space, if the policy demands it.
  //
  if (PcdGet32 (PcdImageLoaderDebugSupport) >= PCD_DEBUG_SUPPORT_FORCE_LOAD) {
    PeCoffLoaderLoadCodeView (Context);
  }

  return RETURN_SUCCESS;
}

RETURN_STATUS
PeCoffLoadImageInplace (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  )
{
  CONST EFI_IMAGE_SECTION_HEADER *Sections;
  UINT32                         AlignedSize;
  UINT16                         Index;

  ASSERT (Context != NULL);
  //
  // Verify the Image is located at its preferred load address.
  //
  if ((UINTN) Context->FileBuffer != Context->ImageBase) {
    return RETURN_UNSUPPORTED;
  }

  Sections = (CONST EFI_IMAGE_SECTION_HEADER *) (CONST VOID *) (
               (CONST CHAR8 *) Context->FileBuffer + Context->SectionsOffset
               );
  //
  // Verify all RVAs and raw file offsets are identical for XIP Images.
  //
  for (Index = 0; Index < Context->NumberOfSections; ++Index) {
    AlignedSize = ALIGN_VALUE (Sections[Index].VirtualSize, Context->SectionAlignment);
    if (Sections[Index].PointerToRawData != Sections[Index].VirtualAddress
     || Sections[Index].SizeOfRawData != AlignedSize) {
      DEBUG_RAISE ();
      return RETURN_UNSUPPORTED;
    }
  }

  Context->ImageBuffer = (VOID *) Context->FileBuffer;
  //
  // Force-load its contents into the memory space, if the policy demands it.
  //
  if (PcdGet32 (PcdImageLoaderDebugSupport) >= PCD_DEBUG_SUPPORT_FORCE_LOAD) {
    PeCoffLoaderLoadCodeViewInplace (Context);
  }

  return RETURN_SUCCESS;
}

//
// FIXME: Provide a Runtime version of this API as well.
//
VOID
PeCoffDiscardSections (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  )
{
  CONST EFI_IMAGE_SECTION_HEADER *Sections;
  UINT32                         SectIndex;

  ASSERT (Context != NULL);
  //
  // By the PE/COFF specification, the .reloc section is supposed to be
  // discardable, so we must assume it is no longer valid.
  //
  Context->RelocDirRva  = 0;
  Context->RelocDirSize = 0;

  Sections = (CONST EFI_IMAGE_SECTION_HEADER *) (CONST VOID *) (
               (CONST CHAR8 *) Context->FileBuffer + Context->SectionsOffset
               );
  //
  // Zero all Image Sections that are flagged as discardable.
  //
  for (SectIndex = 0; SectIndex < Context->NumberOfSections; ++SectIndex) {
    if ((Sections[SectIndex].Characteristics & EFI_IMAGE_SCN_MEM_DISCARDABLE) != 0) {
      ZeroMem (
        (CHAR8 *) Context->ImageBuffer + Sections[SectIndex].VirtualAddress,
        Sections[SectIndex].VirtualSize
        );
    }
  }
}
