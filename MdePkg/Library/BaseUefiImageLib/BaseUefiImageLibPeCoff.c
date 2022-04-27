/** @file
  UEFI Image Loader library implementation for PE/COFF and TE Images.

  Copyright (c) 2021, Marvin Häuser. All rights reserved.<BR>

  SPDX-License-Identifier: BSD-3-Clause
**/

#include <Base.h>
#include <Uefi/UefiBaseType.h>
#include <Uefi/UefiSpec.h>

#include <Library/BaseLib.h>
#include <Library/BaseMemoryLib.h>
#include <Library/CacheMaintenanceLib.h>
#include <Library/DebugLib.h>
#include <Library/MemoryAllocationLib.h>
#include <Library/PeCoffLib2.h>
#include <Library/PcdLib.h>
#include <Library/UefiImageLib.h>

RETURN_STATUS
UefiImageInitializeContext (
  OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context,
  IN  CONST VOID                       *FileBuffer,
  IN  UINT32                           FileSize
  )
{
  return PeCoffInitializeContext (Context, FileBuffer, FileSize);
}

BOOLEAN
UefiImageHashImageDefault (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context,
  IN OUT VOID                             *HashContext,
  IN     UEFI_IMAGE_LOADER_HASH_UPDATE    HashUpdate
  )
{
  return PeCoffHashImageAuthenticode (Context, HashContext, HashUpdate);
}

RETURN_STATUS
UefiImageLoaderGetDestinationSize (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context,
  OUT    UINT32                           *Size
  )
{
  return PeCoffLoaderGetDestinationSize (Context, Size);
}

RETURN_STATUS
UefiImageLoadImage (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context,
  OUT    VOID                          *Destination,
  IN     UINT32                        DestinationSize
  )
{
  return PeCoffLoadImage (Context, Destination, DestinationSize);
}

BOOLEAN
UefiImageImageIsInplace (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  )
{
  return PeCoffImageIsInplace (Context);
}

RETURN_STATUS
UefiImageLoadImageInplace (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  return PeCoffLoadImageInplace (Context);
}

RETURN_STATUS
UefiImageRelocateImageInplaceForExecution (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  RETURN_STATUS Status;
  UINTN         SizeOfImage;

  Status = PeCoffRelocateImageInplace (Context);
  if (RETURN_ERROR (Status)) {
    DEBUG_RAISE ();
    return Status;
  }

  SizeOfImage = PeCoffGetSizeOfImageInplace (Context);
  //
  // Flush the instruction cache so the image data is written before
  // execution.
  // FIXME: TE XIP
  //
  InvalidateInstructionCacheRange (
    (VOID *) Context->ImageBuffer,
    SizeOfImage
    );

  return RETURN_SUCCESS;
}

RETURN_STATUS
UefiImageLoaderGetRuntimeContextSize (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context,
  OUT    UINT32                           *Size
  )
{
  return PeCoffLoaderGetRuntimeContextSize (Context, Size);
}

RETURN_STATUS
UefiImageRelocateImage (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT    *Context,
  IN     UINT64                             BaseAddress,
  OUT    UEFI_IMAGE_LOADER_RUNTIME_CONTEXT  *RuntimeContext OPTIONAL,
  IN     UINT32                             RuntimeContextSize
  )
{
  return PeCoffRelocateImage (
           Context,
           BaseAddress,
           RuntimeContext,
           RuntimeContextSize
           );
}

// FIXME: Check Subsystem here
RETURN_STATUS
UefiImageLoadImageForExecution (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT    *Context,
  OUT    VOID                               *Destination,
  IN     UINT32                             DestinationSize,
  OUT    UEFI_IMAGE_LOADER_RUNTIME_CONTEXT  *RuntimeContext OPTIONAL,
  IN     UINT32                             RuntimeContextSize
  )
{
  RETURN_STATUS Status;
  UINTN         BaseAddress;
  UINTN         SizeOfImage;
  //
  // Load the Image into the memory space.
  //
  Status = PeCoffLoadImage (Context, Destination, DestinationSize);
  if (RETURN_ERROR (Status)) {
    return Status;
  }
  //
  // Relocate the Image to the address it has been loaded to.
  //
  BaseAddress = PeCoffLoaderGetImageAddress (Context);
  Status = PeCoffRelocateImage (
             Context,
             BaseAddress,
             RuntimeContext,
             RuntimeContextSize
             );
  if (RETURN_ERROR (Status)) {
    return Status;
  }

  SizeOfImage = PeCoffGetSizeOfImage (Context);
  //
  // Flush the instruction cache so the image data is written before execution.
  //
  InvalidateInstructionCacheRange ((VOID *) BaseAddress, SizeOfImage);

  return RETURN_SUCCESS;
}

RETURN_STATUS
UefiImageRuntimeRelocateImage (
  IN OUT VOID                                     *Image,
  IN     UINT32                                   ImageSize,
  IN     UINT64                                   BaseAddress,
  IN     CONST UEFI_IMAGE_LOADER_RUNTIME_CONTEXT  *RuntimeContext
  )
{
  return PeCoffRuntimeRelocateImage (
           Image,
           ImageSize,
           BaseAddress,
           RuntimeContext
           );
}

RETURN_STATUS
UefiImageRuntimeRelocateImageForExecution (
  IN OUT VOID                                     *Image,
  IN     UINT32                                   ImageSize,
  IN     UINT64                                   BaseAddress,
  IN     CONST UEFI_IMAGE_LOADER_RUNTIME_CONTEXT  *RuntimeContext
  )
{
  RETURN_STATUS Status;
  //
  // Relocate the Image to the new address.
  //
  Status = PeCoffRuntimeRelocateImage (
             Image,
             ImageSize,
             BaseAddress,
             RuntimeContext
             );
  if (RETURN_ERROR (Status)) {
    return Status;
  }
  //
  // Flush the instruction cache so the image data is written before execution.
  //
  InvalidateInstructionCacheRange (Image, ImageSize);

  return RETURN_SUCCESS;
}

VOID
UefiImageDiscardSegments (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  PeCoffDiscardSections (Context);
}

RETURN_STATUS
UefiImageGetSymbolsPath (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context,
  OUT    CONST CHAR8                      **SymbolsPath,
  OUT    UINT32                           *SymbolsPathSize
  )
{
  return PeCoffGetPdbPath (Context, SymbolsPath, SymbolsPathSize);
}

// FIXME: Some image prints use this and some don't. Is this really needed?
RETURN_STATUS
UefiImageGetModuleNameFromSymbolsPath (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context,
  OUT    CHAR8                            *ModuleName,
  IN     UINT32                           ModuleNameSize
  )
{
  RETURN_STATUS Status;
  CONST CHAR8   *PdbPath;
  UINT32        PdbSize;
  UINTN         Index;
  UINTN         StartIndex;

  ASSERT (Context != NULL);
  ASSERT (ModuleName != NULL);
  ASSERT (ModuleNameSize >= 4);
  //
  // Retrieve the PDB path.
  //
  Status = PeCoffGetPdbPath (Context, &PdbPath, &PdbSize);
  if (RETURN_ERROR (Status)) {
    return Status;
  }
  //
  // Find the last component of the PDB path, which is the file containing the
  // debug symbols for the Image.
  //
  StartIndex = 0;
  for (Index = 0; PdbPath[Index] != '\0'; Index++) {
    if (PdbPath[Index] == '\\' || PdbPath[Index] == '/') {
      StartIndex = Index + 1;
    }
  }
  //
  // Extract the module name from the debug symbols file and ensure the correct
  // file extensions.
  //
  for (Index = 0; Index < ModuleNameSize - 4; Index++) {
    ModuleName[Index] = PdbPath[Index + StartIndex];
    if (ModuleName[Index] == '\0') {
      ModuleName[Index] = '.';
    }
    if (ModuleName[Index] == '.') {
      ModuleName[Index + 1] = 'e';
      ModuleName[Index + 2] = 'f';
      ModuleName[Index + 3] = 'i';
      Index += 4;
      break;
    }
  }
  //
  // Terminate the newly created module name string.
  //
  ModuleName[Index] = '\0';

  return RETURN_SUCCESS;
}

RETURN_STATUS
UefiImageGetFirstCertificate (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context,
  OUT    CONST WIN_CERTIFICATE            **Certificate
  )
{
  return PeCoffGetFirstCertificate (Context, Certificate);
}

RETURN_STATUS
UefiImageGetNextCertificate (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context,
  IN OUT CONST WIN_CERTIFICATE            **Certificate
  )
{
  return PeCoffGetNextCertificate (Context, Certificate);
}

RETURN_STATUS
UefiImageGetHiiDataRva (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context,
  OUT    UINT32                           *HiiRva,
  OUT    UINT32                           *HiiSize
  )
{
  return PeCoffGetHiiDataRva (Context, HiiRva, HiiSize);
}

UINT32
UefiImageGetEntryPointAddress (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  return PeCoffGetAddressOfEntryPoint (Context);
}

UINT16
UefiImageGetMachine (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  return PeCoffGetMachine (Context);
}

UINT16
UefiImageGetSubsystem (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  return PeCoffGetSubsystem (Context);
}

UINT32
UefiImageGetSegmentAlignment (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  return PeCoffGetSectionAlignment (Context);
}

UINT32
UefiImageGetImageSize (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  return PeCoffGetSizeOfImage (Context);
}

UINT32
UefiImageGetImageSizeInplace (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  return PeCoffGetSizeOfImageInplace (Context);
}

UINT64
UefiImageGetPreferredAddress (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  return PeCoffGetImageBase (Context);
}

BOOLEAN
UefiImageGetRelocsStripped (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  return PeCoffGetRelocsStripped (Context);
}

UINTN
UefiImageLoaderGetImageAddress (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  return PeCoffLoaderGetImageAddress (Context);
}

UINTN
UefiImageLoaderGetImageEntryPoint (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  return PeCoffLoaderGetImageEntryPoint (Context);
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
InternalInsertImageRecordSegmentPadding (
  IN OUT UEFI_IMAGE_RECORD_SEGMENT        *RecordSection,
  IN     UINT32                        EndAddress,
  IN     UINT32                        NextAddress,
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
    RecordSection->Size += NextAddress - EndAddress;

    return 0;
  }

  ++RecordSection;
  RecordSection->Size       = NextAddress - EndAddress;
  RecordSection->Attributes = EFI_MEMORY_XP | EFI_MEMORY_RO;

  return 1;
}

UEFI_IMAGE_RECORD *
UefiImageLoaderGetImageRecord (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  UEFI_IMAGE_RECORD               *ImageRecord;
  UINT32                          MaxNumRecordSegments;
  UINT32                          NumRecordSegments;
  UEFI_IMAGE_RECORD_SEGMENT       *RecordSegment;
  UINTN                           ImageAddress;
  UINT32                          SizeOfImage;
  UINT32                          SectionAlignment;
  CONST EFI_IMAGE_SECTION_HEADER  *Sections;
  UINT16                          NumberOfSections;
  UINT16                          SectionIndex;
  CONST EFI_IMAGE_SECTION_HEADER  *Section;
  UINT32                          SectionAddress;
  UINT32                          SectionSize;
  UINT32                          SectionCharacteristics;
  UINT32                          StartAddress;
  UINT32                          EndAddress;
  UINT32                          Characteristics;
  UINT32                          Attributes;

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
    MaxNumRecordSegments = (UINT32) NumberOfSections + 2;
  } else {
    //
    // In case of possibly non-contiguous Image sections, there can be a trailer
    // per Image section (the last Image section's trailer is the same as the
    // Image trailer), as well as additionally the Image Headers.
    //
    MaxNumRecordSegments = (UINT32) NumberOfSections * 2 + 1;
  }

  ImageRecord = AllocatePool (
                  sizeof (*ImageRecord)
                    + MaxNumRecordSegments * sizeof (*ImageRecord->Segments)
                  );
  if (ImageRecord == NULL) {
    DEBUG_RAISE ();
    return NULL;
  }

  ImageRecord->Signature = UEFI_IMAGE_RECORD_SIGNATURE;
  InitializeListHead (&ImageRecord->Link);

  SectionAlignment = PeCoffGetSectionAlignment (Context);
  //
  // Map the Image Headers as read-only data. If the first Image section is
  // loaded at the start of the Image memory space, the condition
  // SectionAddress != StartAddress does not hold and these definitions will be
  // ignored.
  //
  StartAddress    = 0;
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
  NumRecordSegments = 0;
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
    SectionAddress = Section->VirtualAddress;
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
      RecordSegment = &ImageRecord->Segments[NumRecordSegments];
      RecordSegment->Size       = EndAddress - StartAddress;
      RecordSegment->Attributes = Attributes;
      ++NumRecordSegments;
      //
      // If the previous range is not adjacent to the current Image section,
      // report the padding as read-only data.
      //
      if ((PcdGet32 (PcdImageLoaderAlignmentPolicy) & PCD_ALIGNMENT_POLICY_CONTIGUOUS_SECTIONS) != 0) {
        NumRecordSegments += InternalInsertImageRecordSegmentPadding (
                               RecordSegment,
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
  ASSERT (StartAddress < EndAddress);
  //
  // Create an Image record section for the last Image memory permission range.
  //
  RecordSegment = &ImageRecord->Segments[NumRecordSegments];
  RecordSegment->Size       = EndAddress - StartAddress;
  RecordSegment->Attributes = Attributes;
  ++NumRecordSegments;

  ImageAddress = PeCoffLoaderGetImageAddress (Context);
  SizeOfImage  = PeCoffGetSizeOfImage (Context);
  //
  // The Image trailer, if existent, is treated as padding and as such is
  // reported as read-only data, as intended. Because it is not part of the
  // original Image memory space, this needs to happen whether Image sections
  // are guaranteed to be contiguously form the entire Image memory space or
  // not.
  //
  NumRecordSegments += InternalInsertImageRecordSegmentPadding (
                         RecordSegment,
                         EndAddress,
                         SizeOfImage,
                         Attributes
                         );

  ImageRecord->NumSegments  = NumRecordSegments;
  ImageRecord->StartAddress = ImageAddress;
  ImageRecord->EndAddress   = ImageAddress + SizeOfImage;
  //
  // Zero the remaining array entries to avoid uninitialised data.
  //
  ZeroMem (
    ImageRecord->Segments + NumRecordSegments,
    (MaxNumRecordSegments - NumRecordSegments) * sizeof (*ImageRecord->Segments)
    );

  return ImageRecord;
}

RETURN_STATUS
UefiImageDebugLocateImage (
  OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context,
  IN  UINTN                            Address
  )
{
  return PeCoffDebugLocateImage (Context, Address);
}

RETURN_STATUS
UefiImageGetFixedAddress (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context,
  OUT    UINT64                           *Address
  )
{
  return PeCoffGetFixedAddress (Context, Address);
}

VOID
UefiImageDebugPrintSegments (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *Context
  )
{
  PeCoffDebugPrintSectionTable (Context);
}
