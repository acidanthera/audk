/** @file
  Implements APIs to retrieve general information about PE/COFF Images.

  Copyright (c) 2020 - 2021, Marvin Häuser. All rights reserved.<BR>
  Copyright (c) 2020, Vitaly Cheptsov. All rights reserved.<BR>
  Copyright (c) 2020, ISP RAS. All rights reserved.<BR>

  SPDX-License-Identifier: BSD-3-Clause
**/

#include <Base.h>
#include <Uefi/UefiBaseType.h>
#include <Uefi/UefiSpec.h>

#include <Library/BaseLib.h>
#include <Library/DebugLib.h>
#include <Library/PeCoffLib2.h>

#include "BaseOverflow.h"
#include "BasePeCoffLib2Internals.h"

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

  return Context->SectionAlignment;
}

UINT32
PeCoffGetSizeOfImage (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  )
{
  ASSERT (Context != NULL);

  return Context->SizeOfImage;
}

UINT32
PeCoffGetSizeOfImageInplace (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  )
{
  UINT32 SizeOfImage;

  ASSERT (Context != NULL);

  SizeOfImage = Context->SizeOfImage;
  //
  // SizeOfImage is defined with the full Image header size pre-stripping. As
  // XIP TE Images always have a stripped Image header, subtract the difference.
  //
  if (!PcdGetBool (PcdImageLoaderProhibitTe)) {
    ASSERT (Context->TeStrippedOffset < SizeOfImage);
    SizeOfImage -= Context->TeStrippedOffset;
  } else {
    ASSERT (Context->TeStrippedOffset == 0);
  }

  return SizeOfImage;
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

  *Sections = (CONST EFI_IMAGE_SECTION_HEADER *) (CONST VOID *) (
                (CONST CHAR8 *) Context->FileBuffer + Context->SectionsOffset
                );
  return Context->NumberOfSections;
}

BOOLEAN
PeCoffGetRelocsStripped (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  )
{
  ASSERT (Context != NULL);

  return Context->RelocsStripped;
}

// FIXME: Distinguish between base and buffer (XIP TE)
UINTN
PeCoffLoaderGetImageAddress (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  )
{
  ASSERT (Context != NULL);
  ASSERT (Context->ImageBuffer != NULL);

  return (UINTN) Context->ImageBuffer;
}

UINTN
PeCoffLoaderGetImageEntryPoint (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  )
{
  UINT32 AddressOfEntryPoint;

  ASSERT (Context != NULL);
  ASSERT (Context->ImageBuffer != NULL);

  AddressOfEntryPoint = PeCoffGetAddressOfEntryPoint (Context);

  return (UINTN) ((CONST CHAR8 *) Context->ImageBuffer + AddressOfEntryPoint);
}

RETURN_STATUS
PeCoffGetFixedAddress (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  OUT    UINT64                        *Address
  )
{
  CONST EFI_IMAGE_SECTION_HEADER *Sections;
  UINT16                         NumberOfSections;
  UINT16                         SectionIndex;
  UINT64                         FixedAddress;

  ASSERT (Address != NULL);
  //
  // If this feature is enabled, the build tool will save the address in the
  // PointerToRelocations and PointerToLineNumbers fields of the first Image
  // section header that doesn't hold code. The 64-bit value across those fields
  // will be non-zero if and only if the module has been assigned an address.
  //
  NumberOfSections = PeCoffGetSectionTable (Context, &Sections);
  for (SectionIndex = 0; SectionIndex < NumberOfSections; ++SectionIndex) {
    if ((Sections[SectionIndex].Characteristics & EFI_IMAGE_SCN_CNT_CODE) != 0) {
      continue;
    }

    FixedAddress = ReadUnaligned64 (
                     (CONST VOID *) &Sections[SectionIndex].PointerToRelocations
                     );
    if (FixedAddress != 0) {
      if (!IS_ALIGNED (FixedAddress, Context->SectionAlignment)) {
        return RETURN_UNSUPPORTED;
      }

      *Address = FixedAddress;
      return RETURN_SUCCESS;
    }

    return RETURN_NOT_FOUND;
  }

  return RETURN_NOT_FOUND;
}

VOID
PeCoffDebugPrintSectionTable (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  )
{
  CONST EFI_IMAGE_SECTION_HEADER *Sections;
  UINT16                         NumberOfSections;
  UINT16                         SectionIndex;
  CONST UINT8                    *Name;

  NumberOfSections = PeCoffGetSectionTable (Context, &Sections);

  for (SectionIndex = 0; SectionIndex < NumberOfSections; ++SectionIndex) {
    Name = Sections[SectionIndex].Name;
    DEBUG ((
      DEBUG_VERBOSE,
      "  Section - '%c%c%c%c%c%c%c%c'\n",
      "  VirtualSize          - 0x%08x\n"
      "  VirtualAddress       - 0x%08x\n"
      "  SizeOfRawData        - 0x%08x\n"
      "  PointerToRawData     - 0x%08x\n"
      "  PointerToRelocations - 0x%08x\n"
      "  PointerToLinenumbers - 0x%08x\n"
      "  NumberOfRelocations  - 0x%08x\n"
      "  NumberOfLinenumbers  - 0x%08x\n"
      "  Characteristics      - 0x%08x\n",
      Name[0], Name[1], Name[2], Name[3], Name[4], Name[5], Name[6], Name[7],
      Sections[SectionIndex].VirtualSize,
      Sections[SectionIndex].VirtualAddress,
      Sections[SectionIndex].SizeOfRawData,
      Sections[SectionIndex].PointerToRawData,
      Sections[SectionIndex].PointerToRelocations,
      Sections[SectionIndex].PointerToLinenumbers,
      Sections[SectionIndex].NumberOfRelocations,
      Sections[SectionIndex].NumberOfLinenumbers,
      Sections[SectionIndex].Characteristics
      ));
  }
}
