/** @file
  Implements APIs to load PE/COFF Images.

  Copyright (c) 2020 - 2021, Marvin Häuser. All rights reserved.<BR>
  Copyright (c) 2020, Vitaly Cheptsov. All rights reserved.<BR>
  Copyright (c) 2020, ISP RAS. All rights reserved.<BR>
  Portions copyright (c) 2006 - 2019, Intel Corporation. All rights reserved.<BR>
  Portions copyright (c) 2008 - 2010, Apple Inc. All rights reserved.<BR>
  Portions copyright (c) 2020, Hewlett Packard Enterprise Development LP. All rights reserved.<BR>

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
  Loads the Image sections into the memory space and initialises any padding
  with zeros.

  @param[in]  Context           The context describing the Image. Must have been
                                initialised by PeCoffInitializeContext().
  @param[in]  LoadedHeaderSize  The size, in Bytes, of the loaded Image Headers.
  @param[out] Destination       The Image destination memory.
  @param[in]  DestinationSize   The size, in Bytes, of Destination.
                                Must be at least
                                Context->SizeOfImage +
                                Context->SizeOfImageDebugAdd. If the section
                                alignment exceeds 4 KB, must be at least
                                Context->SizeOfImage +
                                Context->SizeOfImageDebugAdd+
                                (Context->SectionAlignment - 1).
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
  UINT16                         SectionIndex;
  UINT32                         EffectivePointerToRawData;
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

  for (SectionIndex = 0; SectionIndex < Context->NumberOfSections; ++SectionIndex) {
    //
    // Zero from the end of the previous section to the start of this section.
    //
    ZeroMem (
      (CHAR8 *) Destination + PreviousTopRva,
      Sections[SectionIndex].VirtualAddress - PreviousTopRva
      );
    //
    // Copy the maximum amount of data that fits both sizes.
    //
    if (Sections[SectionIndex].SizeOfRawData <= Sections[SectionIndex].VirtualSize) {
      DataSize = Sections[SectionIndex].SizeOfRawData;
    } else {
      DataSize = Sections[SectionIndex].VirtualSize;
    }
    //
    // Load the current Image section into the memory space.
    //
    if (!PcdGetBool (PcdImageLoaderProhibitTe)) {
      EffectivePointerToRawData = Sections[SectionIndex].PointerToRawData - Context->TeStrippedOffset;
    } else {
      ASSERT (Context->TeStrippedOffset == 0);
      EffectivePointerToRawData = Sections[SectionIndex].PointerToRawData;
    }

    CopyMem (
      (CHAR8 *) Destination + Sections[SectionIndex].VirtualAddress,
      (CONST CHAR8 *) Context->FileBuffer + EffectivePointerToRawData,
      DataSize
      );

    PreviousTopRva = Sections[SectionIndex].VirtualAddress + DataSize;
  }
  //
  // Zero the trailing data after the last Image section.
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
    //
    // Images aligned stricter than by the UEFI page size have an increased
    // destination size to internally align the Image.
    //
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
  // Load all Image sections into the memory space.
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
PeCoffLoadImageInplaceNoBase (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  )
{
  CONST EFI_IMAGE_SECTION_HEADER *Sections;
  UINT32                         AlignedSize;
  UINT16                         SectionIndex;

  ASSERT (Context != NULL);

  Sections = (CONST EFI_IMAGE_SECTION_HEADER *) (CONST VOID *) (
               (CONST CHAR8 *) Context->FileBuffer + Context->SectionsOffset
               );
  //
  // Verify all RVAs and raw file offsets are identical for XIP Images.
  //
  for (SectionIndex = 0; SectionIndex < Context->NumberOfSections; ++SectionIndex) {
    AlignedSize = ALIGN_VALUE (
                    Sections[SectionIndex].VirtualSize,
                    Context->SectionAlignment
                    );
    if (Sections[SectionIndex].PointerToRawData != Sections[SectionIndex].VirtualAddress
     || Sections[SectionIndex].SizeOfRawData != AlignedSize) {
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

RETURN_STATUS
PeCoffLoadImageInplace (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  )
{
  ASSERT (Context != NULL);
  //
  // Verify the Image is located at its preferred load address.
  //
  if (Context->ImageBase != (UINTN) Context->FileBuffer) {
    return RETURN_UNSUPPORTED;
  }

  return PeCoffLoadImageInplaceNoBase (Context);
}

//
// FIXME: Provide a runtime version of this API as well.
//
VOID
PeCoffDiscardSections (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  )
{
  CONST EFI_IMAGE_SECTION_HEADER *Sections;
  UINT32                         SectionIndex;

  ASSERT (Context != NULL);
  //
  // By the PE/COFF specification, the .reloc section is supposed to be
  // discardable, so we must assume it is no longer valid.
  //
  Context->RelocDirRva  = 0;
  Context->RelocDirSize = 0;
  //
  // Zero all Image sections that are flagged as discardable.
  //
  Sections = (CONST EFI_IMAGE_SECTION_HEADER *) (CONST VOID *) (
               (CONST CHAR8 *) Context->FileBuffer + Context->SectionsOffset
               );
  for (SectionIndex = 0; SectionIndex < Context->NumberOfSections; ++SectionIndex) {
    if ((Sections[SectionIndex].Characteristics & EFI_IMAGE_SCN_MEM_DISCARDABLE) != 0) {
      ZeroMem (
        (CHAR8 *) Context->ImageBuffer + Sections[SectionIndex].VirtualAddress,
        Sections[SectionIndex].VirtualSize
        );
    }
  }
}
