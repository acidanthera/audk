/** @file
  Implements APIs to retrieve general information about PE/COFF Images.

  Copyright (c) 2020 - 2021, Marvin Häuser. All rights reserved.<BR>
  Copyright (c) 2020, Vitaly Cheptsov. All rights reserved.<BR>
  Copyright (c) 2020, ISP RAS. All rights reserved.<BR>

  SPDX-License-Identifier: BSD-3-Clause
**/

#include <Base.h>
#include <Uefi/UefiBaseType.h>

#include <Library/DebugLib.h>
#include <Library/PcdLib.h>
#include <Library/PeCoffLib.h>

#include "BaseOverflow.h"
#include "BasePeCoffLibInternals.h"

UINT32
PeCoffGetAddressOfEntryPoint (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  )
{
  ASSERT (Context != NULL);

  return Context->AddressOfEntryPoint;
}

UINT16
PeCoffGetMachine (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  )
{
  ASSERT (Context != NULL);

  return Context->Machine;
}

UINT16
PeCoffGetSubsystem (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  )
{
  ASSERT (Context != NULL);

  return Context->Subsystem;
}

UINT32
PeCoffGetSectionAlignment (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  )
{
  ASSERT (Context != NULL);

  // FIXME: How to handle misaligned sections if the policy allows it?
  return Context->SectionAlignment;
}

UINT32
PeCoffGetSizeOfImage (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  )
{
  ASSERT (Context != NULL);
  //
  // Transparently reserve the force-load space for debug information, if the
  // policy demands it.
  //
  if (PcdGet32 (PcdImageLoaderDebugSupport) >= PCD_DEBUG_SUPPORT_FORCE_LOAD) {
    ASSERT (Context->SizeOfImage + Context->SizeOfImageDebugAdd >= Context->SizeOfImage);
    return Context->SizeOfImage + Context->SizeOfImageDebugAdd;
  }

  ASSERT (Context->SizeOfImageDebugAdd == 0);

  return Context->SizeOfImage;
}

RETURN_STATUS
PeCoffLoaderGetDestinationSize (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  OUT    UINT32                        *Size
  )
{
  BOOLEAN Overflow;
  UINT32  TotalSize;

  ASSERT (Context != NULL);
  ASSERT (Size != NULL);

  TotalSize = PeCoffGetSizeOfImage (Context);
  //
  // If the Image section alignment is larger than the UEFI page size,
  // sufficient alignment cannot be guaranteed by the allocater. Allodate an
  // additional Image page to be able to manually align within the buffer.
  //
  if (PeCoffGetSectionAlignment (Context) > EFI_PAGE_SIZE) {
    Overflow = BaseOverflowAddU32 (
                 TotalSize,
                 PeCoffGetSectionAlignment (Context),
                 &TotalSize
                 );
    if (Overflow) {
      return RETURN_UNSUPPORTED;
    }
  }

  *Size = TotalSize;

  return RETURN_SUCCESS;
}

UINT64
PeCoffGetImageBase (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  )
{
  ASSERT (Context != NULL);

  return Context->ImageBase;
}

UINT32
PeCoffGetSizeOfHeaders (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  )
{
  ASSERT (Context != NULL);

  return Context->SizeOfHeaders;
}

UINT16
PeCoffGetSectionTable (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT    *Context,
  OUT    CONST EFI_IMAGE_SECTION_HEADER  **Sections
  )
{
  ASSERT (Context != NULL);
  ASSERT (Sections != NULL);

  // FIXME: Needs a solution for force-loaded debug info to enforce permissions.
  *Sections = (CONST EFI_IMAGE_SECTION_HEADER *) (CONST VOID *) (
                (CONST CHAR8 *) Context->FileBuffer + Context->SectionsOffset
                );
  return Context->NumberOfSections;
}

// FIXME: Put to use in the callers
BOOLEAN
PeCoffGetRelocsStripped (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  )
{
  ASSERT (Context != NULL);

  return Context->RelocsStripped;
}

// FIXME: How to handle TE XIP?
UINTN
PeCoffLoaderGetImageAddress (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  )
{
  ASSERT (Context != NULL);
  ASSERT (Context->ImageBuffer != NULL);

  return (UINTN) Context->ImageBuffer;
}
