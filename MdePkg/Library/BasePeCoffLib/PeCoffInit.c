/** @file
  Implements APIs to verify PE/COFF Images for further processing.

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

#include <Guid/WinCertificate.h>

#include <Library/BaseMemoryLib.h>
#include <Library/DebugLib.h>
#include <Library/PcdLib.h>
#include <Library/PeCoffLib.h>

#include "BaseOverflow.h"
#include "BasePeCoffLibInternals.h"

//
// FIXME: Provide an API to destruct the context?
//

/**
  Verify the Image section Headers.

  The first Image section must be the beginning of the memory space, or be
  contiguous to the aligned Image Headers.
  Sections must be disjoint and, depending on the policy, contiguous in the
  memory space space.
  The section data must be in bounds bounds of the file buffer.

  @param[in]  Context       The context describing the Image. Must have been
                            initialised by PeCoffInitializeContext().
  @param[in]  FileSize      The size, in Bytes, of Context->FileBuffer.
  @param[out] StartAddress  On output, the RVA of the first Image section.
  @param[out] EndAddress    On output, the end RVA of the last Image section.

  @retval RETURN_SUCCESS  The Image section Headers are well-formed.
  @retval other           The Image section Headers are malformed.
**/
STATIC
RETURN_STATUS
InternalVerifySections (
  IN  CONST PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  IN  UINT32                              FileSize,
  OUT UINT32                              *StartAddress,
  OUT UINT32                              *EndAddress
  )
{
  BOOLEAN                        Overflow;
  UINT32                         NextSectRva;
  UINT32                         SectRawEnd;
  UINT16                         SectIndex;
  CONST EFI_IMAGE_SECTION_HEADER *Sections;

  ASSERT (Context != NULL);
  ASSERT (Context->SizeOfHeaders >= Context->TeStrippedOffset);
  ASSERT (IS_POW2 (Context->SectionAlignment));
  ASSERT (StartAddress != NULL);
  ASSERT (EndAddress != NULL);
  //
  // Images without Sections have no usable data, disallow them.
  //
  if (Context->NumberOfSections == 0) {
    return RETURN_UNSUPPORTED;
  }

  Sections = (CONST EFI_IMAGE_SECTION_HEADER *) (CONST VOID *) (
               (CONST CHAR8 *) Context->FileBuffer + Context->SectionsOffset
               );
  //
  // The first Image section must begin the Image memory space, or it must be
  // adjacent to the Image Headers.
  //
  if (Sections[0].VirtualAddress == 0) {
    // FIXME: Add PCD to disallow.
    //
    // TE Images cannot support loading the Image Headers as part of the first
    // Image section due to its StrippedSize sematics.
    //
    if (Context->ImageType == PeCoffLoaderTypeTe) {
      DEBUG_RAISE ();
      return RETURN_UNSUPPORTED;
    }

    NextSectRva = 0;
  } else {
    //
    // Choose the raw or aligned Image Headers' size depending on whether
    // loading unaligned Sections is allowed.
    //
    if ((PcdGet32 (PcdImageLoaderAlignmentPolicy) & PCD_ALIGNMENT_POLICY_SECTIONS) == 0) {
      Overflow = BaseOverflowAlignUpU32 (
                   Context->SizeOfHeaders,
                   Context->SectionAlignment,
                   &NextSectRva
                   );
      if (Overflow) {
        DEBUG_RAISE ();
        return RETURN_UNSUPPORTED;
      }
    } else {
      NextSectRva = Context->SizeOfHeaders;
    }
  }

  *StartAddress = NextSectRva;
  //
  // Verify all Image sections are valid.
  //
  for (SectIndex = 0; SectIndex < Context->NumberOfSections; ++SectIndex) {
    //
    // Verify the Image section are disjoint (relaxed) or adjacent (strict)
    // depending on whether unaligned Sections may be loaded or not. Unaligned
    // Sections have been observed with iPXE Option ROMs and old Apple OS X
    // bootloaders.
    //
    if ((PcdGet32 (PcdImageLoaderAlignmentPolicy) & PCD_ALIGNMENT_POLICY_SECTIONS) == 0) {
      if (Sections[SectIndex].VirtualAddress != NextSectRva) {
        DEBUG_RAISE ();
        return RETURN_UNSUPPORTED;
      }
    } else {
      if (Sections[SectIndex].VirtualAddress < NextSectRva) {
        DEBUG_RAISE ();
        return RETURN_UNSUPPORTED;
      }
    }
    //
    // Verify the Image sections with data are in bounds of the file buffer.
    //
    if (Sections[SectIndex].SizeOfRawData > 0) {
      if (Context->TeStrippedOffset > Sections[SectIndex].PointerToRawData) {
        DEBUG_RAISE ();
        return RETURN_UNSUPPORTED;
      }

      Overflow = BaseOverflowAddU32 (
                   Sections[SectIndex].PointerToRawData,
                   Sections[SectIndex].SizeOfRawData,
                   &SectRawEnd
                   );
      if (Overflow) {
        DEBUG_RAISE ();
        return RETURN_UNSUPPORTED;
      }

      if (SectRawEnd - Context->TeStrippedOffset > FileSize) {
        DEBUG_RAISE ();
        return RETURN_UNSUPPORTED;
      }
    }
    //
    // Determine the end of the current Image section.
    //
    Overflow = BaseOverflowAddU32 (
                 Sections[SectIndex].VirtualAddress,
                 Sections[SectIndex].VirtualSize,
                 &NextSectRva
                 );
    if (Overflow) {
      DEBUG_RAISE ();
      return RETURN_UNSUPPORTED;
    }
    //
    // VirtualSize does not need to be aligned, so align the result if needed.
    //
    if ((PcdGet32 (PcdImageLoaderAlignmentPolicy) & PCD_ALIGNMENT_POLICY_SECTIONS) == 0) {
      Overflow = BaseOverflowAlignUpU32 (
                   NextSectRva,
                   Context->SectionAlignment,
                   &NextSectRva
                   );
      if (Overflow) {
        DEBUG_RAISE ();
        return RETURN_UNSUPPORTED;
      }
    }
  }

  *EndAddress = NextSectRva;

  return RETURN_SUCCESS;
}

/**
  Verify the basic Image Relocation information.

  The preferred Image load address must be aligned by the section alignment.
  The Relocation Directory must be contained within the Image section memory.
  The Relocation Directory must be sufficiently aligned in memory.

  @param[in] Context       The context describing the Image. Must have been
                           initialised by PeCoffInitializeContext().
  @param[in] StartAddress  The RVA of the first Image section.

  @retval RETURN_SUCCESS  The basic Image Relocation information is well-formed.
  @retval other           The basic Image Relocation information is malformed.
**/
STATIC
RETURN_STATUS
InternalValidateRelocInfo (
  IN CONST PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  IN UINT32                              StartAddress
  )
{
  BOOLEAN Overflow;
  UINT32  SectRvaEnd;

  ASSERT (Context != NULL);
  //
  // If the Base Relocations have not been stripped, verify their Directory.
  //
  if (!Context->RelocsStripped && Context->RelocDirSize != 0) {
    //
    // Verify the Relocation Directory is not empty.
    //
    if (sizeof (EFI_IMAGE_BASE_RELOCATION_BLOCK) > Context->RelocDirSize) {
      DEBUG_RAISE ();
      return RETURN_UNSUPPORTED;
    }
    //
    // Verify the Relocation Directory does not overlap with the Image Headers.
    //
    if (StartAddress > Context->RelocDirRva) {
      DEBUG_RAISE ();
      return RETURN_UNSUPPORTED;
    }
    //
    // Verify the Relocation Directory is contained in the Image memory space.
    //
    Overflow = BaseOverflowAddU32 (
                 Context->RelocDirRva,
                 Context->RelocDirSize,
                 &SectRvaEnd
                 );
    if (Overflow || SectRvaEnd > Context->SizeOfImage) {
      DEBUG_RAISE ();
      return RETURN_UNSUPPORTED;
    }
    //
    // Verify the Relocation Directory start is sufficiently aligned.
    //
    if (!IS_ALIGNED (Context->RelocDirRva, ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK))) {
      DEBUG_RAISE ();
      return RETURN_UNSUPPORTED;
    }
  }
  //
  // Verify the preferred Image load address is sufficiently aligned.
  //
  if (!IS_ALIGNED (Context->ImageBase, (UINT64) Context->SectionAlignment)) {
    DEBUG_RAISE ();
    return RETURN_UNSUPPORTED;
  }

  return RETURN_SUCCESS;
}

/**
  Verify the TE Image and initialise Context.

  Used offsets and ranges must be aligned and in the bounds of the raw file.
  Image section Headers and basic Relocation information must be well-formed.

  @param[in,out] Context   The context describing the Image. Must have been
                           initialised by PeCoffInitializeContext().
  @param[in]     FileSize  The size, in Bytes, of Context->FileBuffer.

  @retval RETURN_SUCCESS  The TE Image is well-formed.
  @retval other           The TE Image is malformed.
**/
STATIC
RETURN_STATUS
InternalInitializeTe (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  IN     UINT32                        FileSize
  )
{
  RETURN_STATUS             Status;
  BOOLEAN                   Overflow;
  CONST EFI_TE_IMAGE_HEADER *TeHdr;
  UINT32                    StartAddress;
  UINT32                    SizeOfImage;

  ASSERT (Context != NULL);
  ASSERT (Context->ExeHdrOffset == 0);
  ASSERT (sizeof (EFI_TE_IMAGE_HEADER) <= FileSize);

  TeHdr = (CONST EFI_TE_IMAGE_HEADER *) (CONST VOID *) (
            (CONST CHAR8 *) Context->FileBuffer
            );

  Context->ImageType = PeCoffLoaderTypeTe;
  //
  // Calculate the size, in Bytes, stripped from the Image Headers.
  //
  Overflow = BaseOverflowSubU16 (
               TeHdr->StrippedSize,
               sizeof (*TeHdr),
               &Context->TeStrippedOffset
               );
  if (Overflow) {
    return RETURN_UNSUPPORTED;
  }

  STATIC_ASSERT (
    MAX_UINT8 * sizeof (EFI_IMAGE_SECTION_HEADER) <= MAX_UINT32 - MAX_UINT16,
    "The following arithmetics may overflow."
    );
  //
  // Calculate SizeOfHeaders in a way that is equivalent to what the size would
  // be if this was the original (unstripped) PE32 binary. As the TE image
  // creation doesn't fix fields up, values work the same way as for PE32.
  // When referencing raw data however, the TE stripped size must be subracted.
  //
  Context->SizeOfHeaders = (UINT32) TeHdr->StrippedSize + (UINT32) TeHdr->NumberOfSections * sizeof (EFI_IMAGE_SECTION_HEADER);
  //
  // Verify that the Image Headers are in bounds of the file buffer.
  //
  if (Context->SizeOfHeaders - Context->TeStrippedOffset > FileSize) {
    DEBUG_RAISE ();
    return RETURN_UNSUPPORTED;
  }

  STATIC_ASSERT (
    IS_ALIGNED (sizeof (*TeHdr), ALIGNOF (EFI_IMAGE_SECTION_HEADER)),
    "The Image section alignment requirements are violated."
    );
  //
  // TE Image sections start right after the Image Headers.
  //
  Context->SectionsOffset = sizeof (EFI_TE_IMAGE_HEADER);
  //
  // TE Images do not store their section alignment. Assume the UEFI Page size
  // by default, as it is the minimum to guarantee memory permission support.
  //
  Context->SectionAlignment = EFI_PAGE_SIZE;
  Context->NumberOfSections = TeHdr->NumberOfSections;
  //
  // Validate the sections.
  // TE images do not have a field to explicitly describe the image size.
  // Set it to the top of the Image's memory space.
  //
  Status = InternalVerifySections (
             Context,
             FileSize,
             &StartAddress,
             &SizeOfImage
             );
  if (Status != RETURN_SUCCESS) {
    return Status;
  }
  //
  // Verify the Image entry point is in bounds of the Image buffer.
  //
  if (TeHdr->AddressOfEntryPoint >= SizeOfImage) {
    DEBUG_RAISE ();
    return RETURN_UNSUPPORTED;
  }

  Context->SizeOfImage         = SizeOfImage;
  Context->Machine             = TeHdr->Machine;
  Context->Subsystem           = TeHdr->Subsystem;
  Context->ImageBase           = TeHdr->ImageBase;
  Context->AddressOfEntryPoint = TeHdr->AddressOfEntryPoint;
  Context->RelocDirRva         = TeHdr->DataDirectory[0].VirtualAddress;
  Context->RelocDirSize        = TeHdr->DataDirectory[0].Size;
  //
  // TE Images do not explicitly store whether their Relocations have been
  // stripped. Assume that if there are no Relocations, they have been stripped
  // to prevent loading into non-preferred memory locations.
  //
  Context->RelocsStripped = TeHdr->DataDirectory[0].Size > 0;
  //
  // Verify basic sanity of the Relocation Directory.
  //
  return InternalValidateRelocInfo (Context, StartAddress);
}

/**
  Verify the PE32 or PE32+ Image and initialise Context.

  Used offsets and ranges must be aligned and in the bounds of the raw file.
  Image section Headers and basic Relocation information must be Well-formed.

  @param[in,out] Context   The context describing the Image. Must have been
                           initialised by PeCoffInitializeContext().
  @param[in]     FileSize  The size, in Bytes, of Context->FileBuffer.

  @retval RETURN_SUCCESS  The PE Image is Well-formed.
  @retval other           The PE Image is malformed.
**/
STATIC
RETURN_STATUS
InternalInitializePe (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  IN     UINT32                        FileSize
  )
{
  BOOLEAN                               Overflow;
  CONST EFI_IMAGE_NT_HEADERS_COMMON_HDR *PeCommon;
  CONST EFI_IMAGE_NT_HEADERS32          *Pe32;
  CONST EFI_IMAGE_NT_HEADERS64          *Pe32Plus;
  CONST CHAR8                           *OptHdrPtr;
  UINT32                                HdrSizeWithoutDataDir;
  UINT32                                MinSizeOfOptionalHeader;
  UINT32                                MinSizeOfHeaders;
  CONST EFI_IMAGE_DATA_DIRECTORY        *RelocDir;
  CONST EFI_IMAGE_DATA_DIRECTORY        *SecDir;
  UINT32                                SecDirEnd;
  UINT32                                NumberOfRvaAndSizes;
  RETURN_STATUS                         Status;
  UINT32                                StartAddress;
  UINT32                                MinSizeOfImage;

  ASSERT (Context != NULL);
  ASSERT (sizeof (EFI_IMAGE_NT_HEADERS_COMMON_HDR) + sizeof (UINT16) <= FileSize - Context->ExeHdrOffset);
  ASSERT (IS_ALIGNED (Context->ExeHdrOffset, ALIGNOF (EFI_IMAGE_NT_HEADERS_COMMON_HDR)));
  //
  // Locate the PE Optional Header.
  //
  OptHdrPtr = (CONST CHAR8 *) Context->FileBuffer + Context->ExeHdrOffset;
  OptHdrPtr += sizeof (EFI_IMAGE_NT_HEADERS_COMMON_HDR);

  STATIC_ASSERT (
    IS_ALIGNED (ALIGNOF (EFI_IMAGE_NT_HEADERS_COMMON_HDR), ALIGNOF (UINT16))
   && IS_ALIGNED (sizeof (EFI_IMAGE_NT_HEADERS_COMMON_HDR), ALIGNOF (UINT16)),
    "The following operation might be an unaligned access."
  );
  //
  // Determine the type of and retrieve data from the PE Optional Header.
  //
  switch (*(CONST UINT16 *) (CONST VOID *) OptHdrPtr) {
    case EFI_IMAGE_NT_OPTIONAL_HDR32_MAGIC:
      //
      // Verify the PE32 header is in bounds of the file buffer.
      //
      if (sizeof (*Pe32) > FileSize - Context->ExeHdrOffset) {
        DEBUG_RAISE ();
        return RETURN_UNSUPPORTED;
      }
      //
      // The PE32 header offset is always sufficiently aligned.
      //
      STATIC_ASSERT (
        ALIGNOF (EFI_IMAGE_NT_HEADERS32) <= ALIGNOF (EFI_IMAGE_NT_HEADERS_COMMON_HDR),
        "The following operations may be unaligned."
        );
      //
      // Populate the common data with information from the Optional Header.
      //
      Pe32 = (CONST EFI_IMAGE_NT_HEADERS32 *) (CONST VOID *) (
               (CONST CHAR8 *) Context->FileBuffer + Context->ExeHdrOffset
               );

      Context->ImageType           = PeCoffLoaderTypePe32;
      Context->Subsystem           = Pe32->Subsystem;
      Context->SizeOfImage         = Pe32->SizeOfImage;
      Context->SizeOfHeaders       = Pe32->SizeOfHeaders;
      Context->ImageBase           = Pe32->ImageBase;
      Context->AddressOfEntryPoint = Pe32->AddressOfEntryPoint;
      Context->SectionAlignment    = Pe32->SectionAlignment;

      RelocDir = Pe32->DataDirectory + EFI_IMAGE_DIRECTORY_ENTRY_BASERELOC;
      SecDir   = Pe32->DataDirectory + EFI_IMAGE_DIRECTORY_ENTRY_SECURITY;
      
      PeCommon              = &Pe32->CommonHeader;
      NumberOfRvaAndSizes   = Pe32->NumberOfRvaAndSizes;
      HdrSizeWithoutDataDir = sizeof (EFI_IMAGE_NT_HEADERS32) - sizeof (EFI_IMAGE_NT_HEADERS_COMMON_HDR);
      
      break;

    case EFI_IMAGE_NT_OPTIONAL_HDR64_MAGIC:
      //
      // Verify the PE32+ header is in bounds of the file buffer.
      //
      if (sizeof (*Pe32Plus) > FileSize - Context->ExeHdrOffset) {
        DEBUG_RAISE ();
        return RETURN_UNSUPPORTED;
      }
      //
      // Verify the PE32+ header offset is sufficiently aligned.
      //
      if (!IS_ALIGNED (Context->ExeHdrOffset, ALIGNOF (EFI_IMAGE_NT_HEADERS64))) {
        DEBUG_RAISE ();
        return RETURN_UNSUPPORTED;
      }
      //
      // Populate the common data with information from the Optional Header.
      //
      Pe32Plus = (CONST EFI_IMAGE_NT_HEADERS64 *) (CONST VOID *) (
                   (CONST CHAR8 *) Context->FileBuffer + Context->ExeHdrOffset
                   );

      Context->ImageType           = PeCoffLoaderTypePe32Plus;
      Context->Subsystem           = Pe32Plus->Subsystem;
      Context->SizeOfImage         = Pe32Plus->SizeOfImage;
      Context->SizeOfHeaders       = Pe32Plus->SizeOfHeaders;
      Context->ImageBase           = Pe32Plus->ImageBase;
      Context->AddressOfEntryPoint = Pe32Plus->AddressOfEntryPoint;
      Context->SectionAlignment    = Pe32Plus->SectionAlignment;

      RelocDir = Pe32Plus->DataDirectory + EFI_IMAGE_DIRECTORY_ENTRY_BASERELOC;
      SecDir   = Pe32Plus->DataDirectory + EFI_IMAGE_DIRECTORY_ENTRY_SECURITY;

      PeCommon              = &Pe32Plus->CommonHeader;
      NumberOfRvaAndSizes   = Pe32Plus->NumberOfRvaAndSizes;
      HdrSizeWithoutDataDir = sizeof (EFI_IMAGE_NT_HEADERS64) - sizeof (EFI_IMAGE_NT_HEADERS_COMMON_HDR);
      
      break;

    default:
      //
      // Disallow Images with unknown PE Optional Header signatures.
      //
      DEBUG_RAISE ();
      return RETURN_UNSUPPORTED;
  }
  //
  // Disallow Images with unknown directories.
  //
  if (NumberOfRvaAndSizes > EFI_IMAGE_NUMBER_OF_DIRECTORY_ENTRIES) {
    DEBUG_RAISE ();
    return RETURN_UNSUPPORTED;
  }
  //
  // Verify the entry point is in bounds of the Image buffer.
  //
  if (Context->AddressOfEntryPoint >= Context->SizeOfImage) {
    DEBUG_RAISE ();
    return RETURN_UNSUPPORTED;
  }
  //
  // Verify the Image alignment is a power of 2.
  //
  if (!IS_POW2 (Context->SectionAlignment)) {
    DEBUG_RAISE ();
    return RETURN_UNSUPPORTED;
  }

  STATIC_ASSERT (
    sizeof (EFI_IMAGE_DATA_DIRECTORY) <= MAX_UINT32 / EFI_IMAGE_NUMBER_OF_DIRECTORY_ENTRIES,
    "The following arithmetics may overflow."
    );
  //
  // Calculate the offset of the Image sections.
  //
  // Context->ExeHdrOffset + sizeof (EFI_IMAGE_NT_HEADERS_COMMON_HDR) cannot overflow because
  //   * ExeFileSize > sizeof (EFI_IMAGE_NT_HEADERS_COMMON_HDR) and
  //   * Context->ExeHdrOffset + ExeFileSize = FileSize
  //
  Overflow = BaseOverflowAddU32 (
               Context->ExeHdrOffset + sizeof (*PeCommon),
               PeCommon->FileHeader.SizeOfOptionalHeader,
               &Context->SectionsOffset
               );
  if (Overflow) {
    DEBUG_RAISE ();
    return RETURN_UNSUPPORTED;
  }
  //
  // Verify the Section Headers offset is sufficiently aligned.
  //
  if (!IS_ALIGNED (Context->SectionsOffset, ALIGNOF (EFI_IMAGE_SECTION_HEADER))) {
    DEBUG_RAISE ();
    return RETURN_UNSUPPORTED;
  }
  //
  // This arithmetics cannot overflow because all values are sufficiently
  // bounded.
  //
  MinSizeOfOptionalHeader = HdrSizeWithoutDataDir +
                              NumberOfRvaAndSizes * sizeof (EFI_IMAGE_DATA_DIRECTORY);

  ASSERT (MinSizeOfOptionalHeader >= HdrSizeWithoutDataDir);

  STATIC_ASSERT (
    sizeof (EFI_IMAGE_SECTION_HEADER) <= (MAX_UINT32 + 1ULL) / (MAX_UINT16 + 1ULL),
    "The following arithmetics may overflow."
    );
  //
  // Calculate the minimum size of the Image Headers.
  //
  Overflow = BaseOverflowAddU32 (
               Context->SectionsOffset,
               (UINT32) PeCommon->FileHeader.NumberOfSections * sizeof (EFI_IMAGE_SECTION_HEADER),
               &MinSizeOfHeaders
               );
  if (Overflow) {
    DEBUG_RAISE ();
    return RETURN_UNSUPPORTED;
  }
  //
  // Verify the Image Header sizes are sane. SizeOfHeaders contains all header
  // components (DOS, PE Common and Optional Header).
  //
  if (MinSizeOfOptionalHeader > PeCommon->FileHeader.SizeOfOptionalHeader) {
    DEBUG_RAISE ();
    return RETURN_UNSUPPORTED;
  }

  if (MinSizeOfHeaders > Context->SizeOfHeaders) {
    DEBUG_RAISE ();
    return RETURN_UNSUPPORTED;
  }
  //
  // Verify the Image Headers are in bounds of the file buffer.
  //
  if (Context->SizeOfHeaders > FileSize) {
    DEBUG_RAISE ();
    return RETURN_UNSUPPORTED;
  }
  //
  // Populate the Image context with information from the Common Header.
  //
  Context->NumberOfSections = PeCommon->FileHeader.NumberOfSections;
  Context->Machine          = PeCommon->FileHeader.Machine;
  Context->RelocsStripped   =
    (
      PeCommon->FileHeader.Characteristics & EFI_IMAGE_FILE_RELOCS_STRIPPED
    ) != 0;

  if (EFI_IMAGE_DIRECTORY_ENTRY_BASERELOC < NumberOfRvaAndSizes) {
    Context->RelocDirRva  = RelocDir->VirtualAddress;
    Context->RelocDirSize = RelocDir->Size;
  } else {
    ASSERT (Context->RelocDirRva == 0 && Context->RelocDirSize == 0);
  }

  if (EFI_IMAGE_DIRECTORY_ENTRY_SECURITY < NumberOfRvaAndSizes) {
    Context->SecDirOffset = SecDir->VirtualAddress;
    Context->SecDirSize   = SecDir->Size;
    //
    // Verify the Security Direction is in bounds of the Image buffer.
    //
    Overflow = BaseOverflowAddU32 (
                 Context->SecDirOffset,
                 Context->SecDirSize,
                 &SecDirEnd
                 );
    if (Overflow || SecDirEnd > FileSize) {
      DEBUG_RAISE ();
      return RETURN_UNSUPPORTED;
    }
    //
    // Verify the Security Directory is sufficiently aligned.
    //
    if (!IS_ALIGNED (Context->SecDirOffset, IMAGE_CERTIFICATE_ALIGN)) {
      DEBUG_RAISE ();
      return RETURN_UNSUPPORTED;
    }
    //
    // Verify the Security Directory size is sufficiently aligned, and that if
    // it is not empty, it can fit at least one certificate.
    //
    if (Context->SecDirSize != 0
     && (!IS_ALIGNED (Context->SecDirSize, IMAGE_CERTIFICATE_ALIGN)
      || Context->SecDirSize < sizeof (WIN_CERTIFICATE))) {
      DEBUG_RAISE ();
      return RETURN_UNSUPPORTED;
    }
  } else {
    //
    // The Image context is zero'd on allocation.
    //
    ASSERT (Context->SecDirOffset == 0);
    ASSERT (Context->SecDirSize == 0);
  }

  ASSERT (Context->TeStrippedOffset == 0);
  //
  // Verify the Image sections are Well-formed.
  //
  Status = InternalVerifySections (
             Context,
             FileSize,
             &StartAddress,
             &MinSizeOfImage
             );
  if (Status != RETURN_SUCCESS) {
    DEBUG_RAISE ();
    return Status;
  }
  //
  // Verify SizeOfImage fits all Image sections.
  //
  if (MinSizeOfImage > Context->SizeOfImage) {
    DEBUG_RAISE ();
    return RETURN_UNSUPPORTED;
  }
  //
  // Verify the basic Relocation information is well-formed.
  //
  Status = InternalValidateRelocInfo (Context, StartAddress);
  if (Status != RETURN_SUCCESS) {
    DEBUG_RAISE ();
  }

  return Status;
}

RETURN_STATUS
PeCoffInitializeContext (
  OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  IN  CONST VOID                    *FileBuffer,
  IN  UINT32                        FileSize
  )
{
  RETURN_STATUS               Status;
  CONST EFI_IMAGE_DOS_HEADER *DosHdr;

  ASSERT (Context != NULL);
  ASSERT (FileBuffer != NULL || FileSize == 0);
  //
  // Initialise the Image context with 0-values.
  //
  ZeroMem (Context, sizeof (*Context));

  Context->FileBuffer = FileBuffer;
  Context->FileSize   = FileSize;
  //
  // Check whether the DOS Image Header is present.
  //
  if (sizeof (*DosHdr) <= FileSize
   && *(CONST UINT16 *) (CONST VOID *) FileBuffer == EFI_IMAGE_DOS_SIGNATURE) {
    DosHdr = (CONST EFI_IMAGE_DOS_HEADER *) (CONST VOID *) (
               (CONST CHAR8 *) FileBuffer
               );
    //
    // Verify the DOS Image Header and the Executable Header are in bounds of
    // the file buffer, and that they are disjoint.
    //
    if (sizeof (EFI_IMAGE_DOS_HEADER) > DosHdr->e_lfanew
     || DosHdr->e_lfanew > FileSize) {
      DEBUG_RAISE ();
      return RETURN_UNSUPPORTED;
    }

    Context->ExeHdrOffset = DosHdr->e_lfanew;
  } else {
    //
    // Assume the Image starts with the Executable Header, determine whether it
    // is a TE Image.
    //
    if (sizeof (EFI_TE_IMAGE_HEADER) <= FileSize
     && *(CONST UINT16 *) (CONST VOID *) FileBuffer == EFI_TE_IMAGE_HEADER_SIGNATURE) {
      //
      // Verify the TE Image Header is well-formed.
      //
      Status = InternalInitializeTe (Context, FileSize);
      if (Status != RETURN_SUCCESS) {
        DEBUG_RAISE ();
        return Status;
      }
      //
      // If debugging is enabled, index the debug information.
      //
      if (PcdGet32 (PcdImageLoaderDebugSupport) >= PCD_DEBUG_SUPPORT_BASIC) {
        PeCoffLoaderRetrieveCodeViewInfo (Context, FileSize);
      }

      return RETURN_SUCCESS;
    }
  }
  //
  // Verify the file buffer can hold a PE Common Header.
  //
  if (FileSize - Context->ExeHdrOffset < sizeof (EFI_IMAGE_NT_HEADERS_COMMON_HDR) + sizeof (UINT16)) {
    DEBUG_RAISE ();
    return RETURN_UNSUPPORTED;
  }
  //
  // Verify the Execution Header offset is sufficiently aligned.
  //
  if (!IS_ALIGNED (Context->ExeHdrOffset, ALIGNOF (EFI_IMAGE_NT_HEADERS_COMMON_HDR))) {
    DEBUG_RAISE ();
    return RETURN_UNSUPPORTED;
  }

  STATIC_ASSERT (
    ALIGNOF (UINT32) <= ALIGNOF (EFI_IMAGE_NT_HEADERS_COMMON_HDR),
    "The following access may be performed unaligned"
    );
  //
  // Verify the Image Executable Header has a PE signature.
  //
  if (*(CONST UINT32 *) (CONST VOID *) ((CONST CHAR8 *) FileBuffer + Context->ExeHdrOffset) != EFI_IMAGE_NT_SIGNATURE) {
    DEBUG_RAISE ();
    return RETURN_UNSUPPORTED;
  }
  //
  // Verify the PE Image Header is well-formed.
  //
  Status = InternalInitializePe (Context, FileSize);
  if (Status != RETURN_SUCCESS) {
    DEBUG_RAISE ();
    return Status;
  }
  //
  // If debugging is enabled, index the debug information.
  //
  if (PcdGet32 (PcdImageLoaderDebugSupport) >= PCD_DEBUG_SUPPORT_BASIC) {
    PeCoffLoaderRetrieveCodeViewInfo (Context, FileSize);
  }

  return RETURN_SUCCESS;
}
