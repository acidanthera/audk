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
#include <Library/BaseMemoryLib.h>
#include <Library/DebugLib.h>
#include <Library/MemoryAllocationLib.h>
#include <Library/PcdLib.h>
#include <Library/PeCoffLib2.h>

#include "BaseOverflow.h"
#include "BasePeCoffLib2Internals.h"
#include "IndustryStandard/PeImage2.h"

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
  UINT32 SizeOfImage;

  ASSERT (Context != NULL);

  SizeOfImage = Context->SizeOfImage;
  //
  // Transparently reserve the force-load space for debug information, if the
  // policy demands it.
  //
  if (PcdGet32 (PcdImageLoaderDebugSupport) >= PCD_DEBUG_SUPPORT_FORCE_LOAD) {
    ASSERT (SizeOfImage + Context->SizeOfImageDebugAdd >= SizeOfImage);

    SizeOfImage += Context->SizeOfImageDebugAdd;
  } else {
    ASSERT (Context->SizeOfImageDebugAdd == 0);
  }

  return SizeOfImage;
}

UINT32
PeCoffGetSizeOfImageInplace (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  )
{
  UINT32 SizeOfImage;

  ASSERT (Context != NULL);
  //
  // In-place Image loading cannot force-load Debug data, thus omit its size.
  //
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

// FIXME: Put to use in the callers
BOOLEAN
PeCoffGetRelocsStripped (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  )
{
  ASSERT (Context != NULL);

  return Context->RelocsStripped;
}

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
PeCoffLoaderGetRvctSymbolsBaseAddress (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  )
{
  //
  // FIXME: Is RVCT even still used? Why is the Image base the end of the
  //        Image headers? Are the Image headers just prepended to a 0-based
  //        ELF or similar?
  //
  return PeCoffLoaderGetImageAddress (Context) + PeCoffGetSizeOfImage (Context);
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

/**
  Retrieves the memory protection attributes corresponding to PE/COFF Image
  section permissions.

  @param[in] Characteristics  The PE/COFF Image section permissions

  @returns  The memory protection attributes corresponding to the PE/COFF Image
            section permissions.
**/
STATIC
UINT32
InternalCharacteristicsToAttributes (
  IN UINT32  Characteristics
  )
{
  UINT32 Attributes;

  Attributes = 0;
  if ((Characteristics & EFI_IMAGE_SCN_MEM_EXECUTE) == 0) {
    Attributes |= EFI_MEMORY_XP;
  }
  if ((Characteristics & EFI_IMAGE_SCN_MEM_READ) == 0) {
    Attributes |= EFI_MEMORY_RP;
  }
  if ((Characteristics & EFI_IMAGE_SCN_MEM_WRITE) == 0) {
    Attributes |= EFI_MEMORY_RO;
  }

  return Attributes;
}

/**
  Index the read-only padding following an Image record section, if existent.

  @param[in,out] RecordSection  The Image record section for the current memory
                                protection range. May be extended if it is of
                                the same type as the adjacent padding. At least
                                one more record section must be reserved after
                                it in order to index the read-only padding.
  @param[in]     NextAddress    The start address of the next memory permission
                                range. This may be the end address of the Image
                                in order to cover the Image trailer.
  @param[in]     EndAddress     The end address of the current memory permission
                                range. This also denotes the start of the added
                                read-only padding.
  @param[in]     Attributes     The memory protection attributes of the current
                                memory permission range.

  @returns  The amount of Image record sections that have been appended.
**/
STATIC
UINT8
InternalInsertImageRecordSectionPadding (
  IN OUT PE_COFF_IMAGE_RECORD_SECTION  *RecordSection,
  IN     UINTN                         EndAddress,
  IN     UINTN                         NextAddress,
  IN     UINT32                        Attributes
  )
{
  ASSERT (RecordSection != NULL);
  ASSERT (EndAddress <= NextAddress);

  if (NextAddress == EndAddress) {
    return 0;
  }
  //
  // Add a new Image record section or expand the previous one depending on
  // the the permissions of the previous Image record section.
  //
  if (Attributes == (EFI_MEMORY_XP | EFI_MEMORY_RO)) {
    RecordSection->Size += (UINT32) (NextAddress - EndAddress);

    return 0;
  }

  ++RecordSection;
  RecordSection->Address    = EndAddress;
  //
  // This cast is safe because all RVAs are UINT32.
  //
  RecordSection->Size       = (UINT32) (NextAddress - EndAddress);
  RecordSection->Attributes = EFI_MEMORY_XP | EFI_MEMORY_RO;

  return 1;
}

PE_COFF_IMAGE_RECORD *
PeCoffLoaderGetImageRecord (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  )
{
  PE_COFF_IMAGE_RECORD           *ImageRecord;
  UINT32                         MaxRecordSectionsCount;
  UINT32                         NumberOfRecordSections;
  PE_COFF_IMAGE_RECORD_SECTION   *RecordSection;
  UINTN                          ImageAddress;
  UINT32                         SectionAlignment;
  CONST EFI_IMAGE_SECTION_HEADER *Sections;
  UINT16                         NumberOfSections;
  UINT16                         SectionIndex;
  CONST EFI_IMAGE_SECTION_HEADER *Section;
  UINTN                          SectionAddress;
  UINT32                         SectionSize;
  UINT32                         SectionCharacteristics;
  UINTN                          StartAddress;
  UINTN                          EndAddress;
  UINT32                         Characteristics;
  UINT32                         Attributes;

  ASSERT (Context != NULL);
  //
  // Determine the maximum amount of Image record sections and allocate the
  // Image record.
  //
  NumberOfSections = PeCoffGetSectionTable (Context, &Sections);

  STATIC_ASSERT (
    MAX_UINT16 <= MAX_UINT32 / 2 - 1,
    "The following arithmetic may overflow."
    );

  if ((PcdGet32 (PcdImageLoaderAlignmentPolicy) & PCD_ALIGNMENT_POLICY_CONTIGUOUS_SECTIONS) == 0) {
    //
    // In case of contiguous Image sections, there can be two additional record
    // sections (Image Headers and trailer, e.g. debug information).
    //
    MaxRecordSectionsCount = (UINT32) NumberOfSections + 2;
  } else {
    //
    // In case of possibly non-contiguous Image sections, there can be a trailer
    // per Image section (the last Image section's trailer is the same as the
    // Image trailer), as well as additionally the Image Headers.
    //
    MaxRecordSectionsCount = (UINT32) NumberOfSections * 2 + 1;
  }

  ImageRecord = AllocatePool (
                  sizeof (*ImageRecord)
                    + MaxRecordSectionsCount * sizeof (*ImageRecord->Sections)
                  );
  if (ImageRecord == NULL) {
    DEBUG_RAISE ();
    return NULL;
  }

  ImageRecord->Signature = PE_COFF_IMAGE_RECORD_SIGNATURE;
  InitializeListHead (&ImageRecord->Link);

  ImageAddress     = PeCoffLoaderGetImageAddress (Context);
  SectionAlignment = PeCoffGetSectionAlignment (Context);
  //
  // Map the Image Headers as read-only data. If the first Image section is
  // loaded at the start of the Image memory space, the condition
  // SectionAddress != StartAddress does not hold and these definitions will be
  // ignored.
  //
  StartAddress    = ImageAddress;
  EndAddress      = PeCoffGetSizeOfHeaders (Context);
  Characteristics = EFI_IMAGE_SCN_MEM_READ;
  Attributes      = EFI_MEMORY_XP | EFI_MEMORY_RO;
  ASSERT (Attributes == InternalCharacteristicsToAttributes (Characteristics));
  //
  // Create an Image record section for every permission-distinct range of the
  // Image. The current range [StartAddress, EndAddress) shares the memory
  // permissions Charactersitics/Attributes and is extended till a new
  // memory permission configuration is required. Headers and trailers treated
  // as read-only data.
  //
  NumberOfRecordSections = 0;
  for (SectionIndex = 0; SectionIndex < NumberOfSections; ++SectionIndex) {
    Section = Sections + SectionIndex;
    //
    // Skip empty Image sections to avoid unnecessary splitting.
    //
    if (Section->VirtualSize == 0) {
      continue;
    }
    //
    // These arithmetics are safe as guaranteed by PeCoffInitializeContext().
    //
    SectionAddress = ImageAddress + Section->VirtualAddress;
    SectionSize    = ALIGN_VALUE (Section->VirtualSize, SectionAlignment);
    SectionCharacteristics = Section->Characteristics & (EFI_IMAGE_SCN_MEM_EXECUTE | EFI_IMAGE_SCN_MEM_READ | EFI_IMAGE_SCN_MEM_WRITE);
    //
    // Skip Image sections with the same memory permissions as the current range
    // as they can be merged. For this, the Image sections must be adjacent, or
    // the range must have the same memory permissions as the padding inbetween
    // (read-only).
    //
    if ((PcdGet32 (PcdImageLoaderAlignmentPolicy) & PCD_ALIGNMENT_POLICY_CONTIGUOUS_SECTIONS) == 0
     || SectionAddress == EndAddress
     || Characteristics == EFI_IMAGE_SCN_MEM_READ) {
      if (SectionCharacteristics == Characteristics) {
        EndAddress = SectionAddress + SectionSize;
        continue;
      }
    }
    //
    // Only create an entry if the range is not empty, otherwise discard it and
    // start a new one. Even with skipping empty Image sections, this can still
    // happen for the Image Headers when the first Image section starts at 0.
    //
    if (SectionAddress != StartAddress) {
      //
      // Create an Image record section for the current memory permission range.
      //
      RecordSection = &ImageRecord->Sections[NumberOfRecordSections];
      RecordSection->Address    = StartAddress;
      //
      // This cast is safe because all RVAs are UINT32.
      //
      RecordSection->Size       = (UINT32) (EndAddress - StartAddress);
      RecordSection->Attributes = Attributes;
      ++NumberOfRecordSections;
      //
      // If the previous range is not adjacent to the current Image section,
      // report the padding as read-only data.
      //
      if ((PcdGet32 (PcdImageLoaderAlignmentPolicy) & PCD_ALIGNMENT_POLICY_CONTIGUOUS_SECTIONS) != 0) {
        NumberOfRecordSections += InternalInsertImageRecordSectionPadding (
                                    RecordSection,
                                    EndAddress,
                                    SectionAddress,
                                    Attributes
                                    );
      }

      StartAddress = SectionAddress;
    }
    //
    // Start a Image record section with the current Image section.
    //
    EndAddress      = SectionAddress + SectionSize;
    Characteristics = SectionCharacteristics;
    Attributes      = InternalCharacteristicsToAttributes (Characteristics);
  }
  //
  // Image Record sections are only created once a non-empty Image section is
  // encountered that requests a different memory permission configuration.
  // As such, the last memory permission range is never converted in the loop.
  // If the loop never produced such, this is true for the Image Headers, which
  // cannot be empty.
  //
  ASSERT (0 < EndAddress - StartAddress);
  //
  // Create an Image record section for the last Image memory permission range.
  //
  RecordSection = &ImageRecord->Sections[NumberOfRecordSections];
  RecordSection->Address    = StartAddress;
  //
  // This cast is safe because all RVAs are UINT32.
  //
  RecordSection->Size       = (UINT32) (EndAddress - StartAddress);
  RecordSection->Attributes = Attributes;
  ++NumberOfRecordSections;
  //
  // The Image trailer (e.g. the force-loaded debug data), if existent, is
  // treated as padding and as such is reported as read-only data, as intended.
  // Because it is not part of the original Image memory space, this needs to
  // happen whether Image sections are guaranteed to be contiguously form the
  // entire Image memory space or not.
  //
  NumberOfRecordSections += InternalInsertImageRecordSectionPadding (
                              RecordSection,
                              EndAddress,
                              ImageAddress + PeCoffGetSizeOfImage (Context),
                              Attributes
                              );

  ImageRecord->NumberOfSections = NumberOfRecordSections;
  ImageRecord->EndAddress       = ImageAddress + PeCoffGetSizeOfImage (Context);
  //
  // Zero the remaining array entries to avoid uninitialised data.
  //
  ZeroMem (
    ImageRecord->Sections + NumberOfRecordSections,
    (MaxRecordSectionsCount - NumberOfRecordSections) * sizeof (*ImageRecord->Sections)
    );

  return ImageRecord;
}

RETURN_STATUS
PeCoffGetAssignedAddress(
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
