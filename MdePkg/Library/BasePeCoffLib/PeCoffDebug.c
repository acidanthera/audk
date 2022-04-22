/** @file
  Implements APIs to load PE/COFF Debug information.

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

#include "BaseOverflow.h"
#include "BasePeCoffLibInternals.h"

VOID
PeCoffLoaderRetrieveCodeViewInfo (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  IN     UINT32                        FileSize
  )
{
  BOOLEAN                               Overflow;

  CONST EFI_IMAGE_DATA_DIRECTORY        *DebugDir;
  CONST EFI_TE_IMAGE_HEADER             *TeHdr;
  CONST EFI_IMAGE_NT_HEADERS32          *Pe32Hdr;
  CONST EFI_IMAGE_NT_HEADERS64          *Pe32PlusHdr;

  CONST EFI_IMAGE_DEBUG_DIRECTORY_ENTRY *DebugEntries;
  UINT32                                NumDebugEntries;
  UINT32                                DebugIndex;
  CONST EFI_IMAGE_DEBUG_DIRECTORY_ENTRY *CodeViewEntry;

  UINT32                                DebugDirTop;
  UINT32                                DebugDirFileOffset;
  UINT32                                DebugDirSectionOffset;
  UINT32                                DebugDirSectionRawTop;
  UINT32                                DebugEntryTopOffset;
  UINT32                                DebugEntryRvaTop;
  CONST EFI_IMAGE_SECTION_HEADER        *Sections;
  UINT16                                SectIndex;

  UINT32                                DebugSizeOfImage;

  ASSERT (Context != NULL);
  ASSERT (Context->SizeOfImageDebugAdd == 0);
  ASSERT (Context->CodeViewRva == 0);
  //
  // Retrieve the Debug Directory information of the Image.
  //
  switch (Context->ImageType) {
    case PeCoffLoaderTypeTe:
      TeHdr = (CONST EFI_TE_IMAGE_HEADER *) (CONST VOID *) (
                (CONST CHAR8 *) Context->FileBuffer
                );

      DebugDir = &TeHdr->DataDirectory[1];
      break;

    case PeCoffLoaderTypePe32:
      Pe32Hdr = (CONST EFI_IMAGE_NT_HEADERS32 *) (CONST VOID *) (
                  (CONST CHAR8 *) Context->FileBuffer + Context->ExeHdrOffset
                  );

      if (Pe32Hdr->NumberOfRvaAndSizes <= EFI_IMAGE_DIRECTORY_ENTRY_DEBUG) {
        return;
      }

      DebugDir = Pe32Hdr->DataDirectory + EFI_IMAGE_DIRECTORY_ENTRY_DEBUG;
      break;

    case PeCoffLoaderTypePe32Plus:
      Pe32PlusHdr = (CONST EFI_IMAGE_NT_HEADERS64 *) (CONST VOID *) (
                      (CONST CHAR8 *) Context->FileBuffer + Context->ExeHdrOffset
                      );

      if (Pe32PlusHdr->NumberOfRvaAndSizes <= EFI_IMAGE_DIRECTORY_ENTRY_DEBUG) {
        return;
      }

      DebugDir = Pe32PlusHdr->DataDirectory + EFI_IMAGE_DIRECTORY_ENTRY_DEBUG;
      break;

    default:
      ASSERT (FALSE);
      return;
  }

  if (DebugDir->Size == 0) {
    return;
  }

  Overflow = BaseOverflowAddU32 (
               DebugDir->VirtualAddress,
               DebugDir->Size,
               &DebugDirTop
               );
  if (Overflow || DebugDirTop > Context->SizeOfImage) {
    CRITICAL_ERROR (FALSE);
    return;
  }

  //
  // Determine the file offset of the debug directory...  This means we walk
  // the sections to find which section contains the RVA of the debug
  // directory
  //
  Sections = (CONST EFI_IMAGE_SECTION_HEADER *) (CONST VOID *) (
               (CONST CHAR8 *) Context->FileBuffer + Context->SectionsOffset
               );

  for (SectIndex = 0; SectIndex < Context->NumberOfSections; ++SectIndex) {
    if (DebugDir->VirtualAddress >= Sections[SectIndex].VirtualAddress
     && DebugDirTop <= Sections[SectIndex].VirtualAddress + Sections[SectIndex].VirtualSize) {
       break;
     }
  }

  if (SectIndex == Context->NumberOfSections) {
    CRITICAL_ERROR (FALSE);
    return;
  }

  DebugDirSectionOffset = DebugDir->VirtualAddress - Sections[SectIndex].VirtualAddress;
  DebugDirSectionRawTop = DebugDirSectionOffset + DebugDir->Size;
  if (DebugDirSectionRawTop > Sections[SectIndex].SizeOfRawData) {
    CRITICAL_ERROR (FALSE);
    return;
  }

  DebugDirFileOffset = (Sections[SectIndex].PointerToRawData - Context->TeStrippedOffset) + DebugDirSectionOffset;

  if (!IS_ALIGNED (DebugDirFileOffset, ALIGNOF (EFI_IMAGE_DEBUG_DIRECTORY_ENTRY))) {
    CRITICAL_ERROR (FALSE);
    return;
  }

  DebugEntries = (CONST EFI_IMAGE_DEBUG_DIRECTORY_ENTRY *) (CONST VOID *) (
                   (CONST CHAR8 *) Context->FileBuffer + DebugDirFileOffset
                   );

  NumDebugEntries = DebugDir->Size / sizeof (*DebugEntries);

  if (DebugDir->Size % sizeof (*DebugEntries) != 0) {
    CRITICAL_ERROR (FALSE);
    return;
  }

  for (DebugIndex = 0; DebugIndex < NumDebugEntries; ++DebugIndex) {
    if (DebugEntries[DebugIndex].Type == EFI_IMAGE_DEBUG_TYPE_CODEVIEW) {
      break;
    }
  }

  if (DebugIndex == NumDebugEntries) {
    return;
  }

  CodeViewEntry = &DebugEntries[DebugIndex];

  if (CodeViewEntry->SizeOfData < sizeof (UINT32)) {
    CRITICAL_ERROR (FALSE);
    return;
  }

  if (CodeViewEntry->RVA != 0) {
    Overflow = BaseOverflowAddU32 (
                 CodeViewEntry->RVA,
                 CodeViewEntry->SizeOfData,
                 &DebugEntryRvaTop
                 );
    if (Overflow || DebugEntryRvaTop > Context->SizeOfImage
     || !IS_ALIGNED (CodeViewEntry->RVA, ALIGNOF (UINT32))) {
      CRITICAL_ERROR (FALSE);
      return;
    }
  } else {
    if (PcdGet32 (PcdImageLoaderDebugSupport) < PCD_DEBUG_SUPPORT_FORCE_LOAD) {
      return;
    }
    //
    // If the Image does not load the Debug information into memory on its own,
    // request reserved space for it to force-load it.
    //
    Overflow = BaseOverflowSubU32 (
                 CodeViewEntry->FileOffset,
                 Context->TeStrippedOffset,
                 &DebugEntryTopOffset
                 );
    if (Overflow) {
      CRITICAL_ERROR (FALSE);
      return;
    }

    Overflow = BaseOverflowAddU32 (
                 DebugEntryTopOffset,
                 CodeViewEntry->SizeOfData,
                 &DebugEntryTopOffset
                 );
    if (Overflow || DebugEntryTopOffset > FileSize) {
      CRITICAL_ERROR (FALSE);
      return;
    }

    Overflow = BaseOverflowAlignUpU32 (
                 Context->SizeOfImage,
                 ALIGNOF (UINT32),
                 &DebugSizeOfImage
                 );
    if (Overflow) {
      CRITICAL_ERROR (FALSE);
      return;
    }

    Overflow = BaseOverflowAddU32 (
                 DebugSizeOfImage,
                 CodeViewEntry->SizeOfData,
                 &DebugSizeOfImage
                 );
    if (Overflow) {
      CRITICAL_ERROR (FALSE);
      return;
    }

    Overflow = BaseOverflowAlignUpU32 (
                 DebugSizeOfImage,
                 Context->SectionAlignment,
                 &DebugSizeOfImage
                 );
    if (Overflow) {
      CRITICAL_ERROR (FALSE);
      return;
    }
    //
    // Ensure the destination space extension for images aligned more strictly
    // than by page size does not overflow. This may allow images to load that
    // would become too large by force-loading the debug data.
    //
    if (Context->SectionAlignment > EFI_PAGE_SIZE
     && DebugSizeOfImage + Context->SectionAlignment < DebugSizeOfImage) {
      return;
    }

    Context->SizeOfImageDebugAdd = DebugSizeOfImage - Context->SizeOfImage;
    ASSERT (Context->SizeOfImageDebugAdd > 0);
  }

  Context->CodeViewRva = Sections[SectIndex].VirtualAddress + DebugDirSectionOffset + DebugIndex * sizeof (*DebugEntries);
  ASSERT (Context->CodeViewRva >= Sections[SectIndex].VirtualAddress);
  ASSERT (Context->CodeViewRva <= Sections[SectIndex].VirtualAddress + Sections[SectIndex].VirtualSize);
}

VOID
PeCoffLoaderLoadCodeView (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  )
{
  EFI_IMAGE_DEBUG_DIRECTORY_ENTRY *CodeViewEntry;

  ASSERT (Context != NULL);

  if (Context->CodeViewRva == 0) {
    return;
  }

  CodeViewEntry = (EFI_IMAGE_DEBUG_DIRECTORY_ENTRY *) (VOID *) (
                    (CHAR8 *) Context->ImageBuffer + Context->CodeViewRva
                    );
  //
  // Load the Codeview information if present
  //
  if (CodeViewEntry->RVA == 0) {
    ASSERT (Context->SizeOfImageDebugAdd > 0);

    CodeViewEntry->RVA = ALIGN_VALUE (Context->SizeOfImage, ALIGNOF (UINT32));

    ASSERT (Context->SizeOfImageDebugAdd >= (CodeViewEntry->RVA - Context->SizeOfImage) + CodeViewEntry->SizeOfData);

    CopyMem (
      (CHAR8 *) Context->ImageBuffer + CodeViewEntry->RVA,
      (CONST CHAR8 *) Context->FileBuffer + (CodeViewEntry->FileOffset - Context->TeStrippedOffset),
      CodeViewEntry->SizeOfData
      );
  }
}

VOID
PeCoffLoaderLoadCodeViewInplace (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  )
{
  EFI_IMAGE_DEBUG_DIRECTORY_ENTRY *CodeViewEntry;

  ASSERT (Context != NULL);

  if (Context->CodeViewRva == 0) {
    return;
  }

  CodeViewEntry = (EFI_IMAGE_DEBUG_DIRECTORY_ENTRY *) (VOID *) (
                    (CHAR8 *) Context->ImageBuffer + Context->CodeViewRva
                    );
  //
  // Load the Codeview information if present
  //
  if (CodeViewEntry->RVA != 0) {
    if (CodeViewEntry->RVA != CodeViewEntry->FileOffset) {
      CRITICAL_ERROR (FALSE);
      Context->CodeViewRva = 0;
      return;
    }
  } else {
    ASSERT (Context->SizeOfImageDebugAdd > 0);

    CodeViewEntry->RVA = CodeViewEntry->FileOffset;
  }
}

RETURN_STATUS
PeCoffGetPdbPath (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  OUT    CONST CHAR8                   **PdbPath,
  OUT    UINT32                        *PdbPathSize
  )
{
  BOOLEAN                         Overflow;

  EFI_IMAGE_DEBUG_DIRECTORY_ENTRY *CodeViewEntry;
  CONST CHAR8                     *CodeView;
  UINT32                          PdbOffset;
  CONST CHAR8                     *PdbName;
  UINT32                          PdbNameSize;

  ASSERT (Context != NULL);
  ASSERT (PdbPath != NULL);
  ASSERT (PdbPathSize != NULL);

  if (Context->CodeViewRva == 0) {
    return RETURN_NOT_FOUND;
  }

  CodeViewEntry = (EFI_IMAGE_DEBUG_DIRECTORY_ENTRY *) (VOID *) (
                    (CHAR8 *) Context->ImageBuffer + Context->CodeViewRva
                    );

  CodeView = (CONST CHAR8 *) Context->ImageBuffer + CodeViewEntry->RVA;

  switch (*(CONST UINT32 *) (CONST VOID *) CodeView) {
    case CODEVIEW_SIGNATURE_NB10:
      PdbOffset = sizeof (EFI_IMAGE_DEBUG_CODEVIEW_NB10_ENTRY);

      STATIC_ASSERT (
        ALIGNOF (EFI_IMAGE_DEBUG_CODEVIEW_NB10_ENTRY) <= ALIGNOF (UINT32),
        "The structure may be misalignedd."
        );
      break;

    case CODEVIEW_SIGNATURE_RSDS:
      PdbOffset = sizeof (EFI_IMAGE_DEBUG_CODEVIEW_RSDS_ENTRY);

      STATIC_ASSERT (
        ALIGNOF (EFI_IMAGE_DEBUG_CODEVIEW_RSDS_ENTRY) <= ALIGNOF (UINT32),
        "The structure may be misalignedd."
        );
      break;

    case CODEVIEW_SIGNATURE_MTOC:
      PdbOffset = sizeof (EFI_IMAGE_DEBUG_CODEVIEW_MTOC_ENTRY);

      STATIC_ASSERT (
        ALIGNOF (EFI_IMAGE_DEBUG_CODEVIEW_MTOC_ENTRY) <= ALIGNOF (UINT32),
        "The structure may be misalignedd."
        );
      break;

    default:
      CRITICAL_ERROR (FALSE);
      return RETURN_UNSUPPORTED;
  }

  Overflow = BaseOverflowSubU32 (
               CodeViewEntry->SizeOfData,
               PdbOffset,
               &PdbNameSize
               );
  if (Overflow || PdbNameSize == 0) {
    CRITICAL_ERROR (FALSE);
    return RETURN_UNSUPPORTED;
  }

  PdbName = (CONST CHAR8 *) Context->ImageBuffer + CodeViewEntry->RVA + PdbOffset;

  if (PdbName[PdbNameSize - 1] != 0) {
    CRITICAL_ERROR (FALSE);
    return RETURN_UNSUPPORTED;
  }

  *PdbPath     = PdbName;
  *PdbPathSize = PdbNameSize;

  return RETURN_SUCCESS;
}
