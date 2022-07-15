/** @file
  Implements APIs to load PE/COFF debug information.

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
#include <Library/PeCoffLib2.h>

#include "BaseOverflow.h"
#include "BasePeCoffLib2Internals.h"

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
  UINT16                                SectionIndex;

  UINT32                                DebugSizeOfImage;

  ASSERT (Context != NULL);
  ASSERT (Context->SizeOfImageDebugAdd == 0);
  ASSERT (Context->CodeViewRva == 0);
  //
  // Retrieve the Debug Directory of the Image.
  //
  switch (Context->ImageType) {
    case PeCoffLoaderTypeTe:
      if (PcdGetBool (PcdImageLoaderProhibitTe)) {
        ASSERT (FALSE);
        return;
      }

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
  //
  // Verify the Debug Directory is not empty.
  //
  if (DebugDir->Size == 0) {
    return;
  }
  //
  // Verify the Debug Directory has a well-formed size.
  //
  if (DebugDir->Size % sizeof (*DebugEntries) != 0) {
    DEBUG_RAISE ();
    return;
  }
  //
  // Verify the Debug Directory is in bounds of the Image buffer.
  //
  Overflow = BaseOverflowAddU32 (
               DebugDir->VirtualAddress,
               DebugDir->Size,
               &DebugDirTop
               );
  if (Overflow || DebugDirTop > Context->SizeOfImage) {
    DEBUG_RAISE ();
    return;
  }
  //
  // Determine the raw file offset of the Debug Directory.
  //
  Sections = (CONST EFI_IMAGE_SECTION_HEADER *) (CONST VOID *) (
               (CONST CHAR8 *) Context->FileBuffer + Context->SectionsOffset
               );

  for (SectionIndex = 0; SectionIndex < Context->NumberOfSections; ++SectionIndex) {
    if (DebugDir->VirtualAddress >= Sections[SectionIndex].VirtualAddress
     && DebugDirTop <= Sections[SectionIndex].VirtualAddress + Sections[SectionIndex].VirtualSize) {
       break;
     }
  }
  //
  // Verify the Debug Directory was found among the Image sections.
  //
  if (SectionIndex == Context->NumberOfSections) {
    DEBUG_RAISE ();
    return;
  }
  //
  // Verify the Debug Directory data is in bounds of the Image section.
  //
  // This arithmetic cannot overflow because we know
  //   1) DebugDir->VirtualAddress + DebugDir->Size <= MAX_UINT32
  //   2) Sections[SectionIndex].VirtualAddress <= DebugDir->VirtualAddress.
  //
  DebugDirSectionOffset = DebugDir->VirtualAddress - Sections[SectionIndex].VirtualAddress;
  DebugDirSectionRawTop = DebugDirSectionOffset + DebugDir->Size;
  if (DebugDirSectionRawTop > Sections[SectionIndex].SizeOfRawData) {
    DEBUG_RAISE ();
    return;
  }
  //
  // Verify the Debug Directory raw file offset is sufficiently aligned.
  //
  DebugDirFileOffset = Sections[SectionIndex].PointerToRawData + DebugDirSectionOffset;

  if (!PcdGetBool (PcdImageLoaderProhibitTe)) {
    DebugDirFileOffset -= Context->TeStrippedOffset;
  } else {
    ASSERT (Context->TeStrippedOffset == 0);
  }

  if (!IS_ALIGNED (DebugDirFileOffset, ALIGNOF (EFI_IMAGE_DEBUG_DIRECTORY_ENTRY))) {
    DEBUG_RAISE ();
    return;
  }
  //
  // Locate the CodeView entry in the Debug Directory.
  //
  DebugEntries = (CONST EFI_IMAGE_DEBUG_DIRECTORY_ENTRY *) (CONST VOID *) (
                   (CONST CHAR8 *) Context->FileBuffer + DebugDirFileOffset
                   );

  NumDebugEntries = DebugDir->Size / sizeof (*DebugEntries);

  for (DebugIndex = 0; DebugIndex < NumDebugEntries; ++DebugIndex) {
    if (DebugEntries[DebugIndex].Type == EFI_IMAGE_DEBUG_TYPE_CODEVIEW) {
      break;
    }
  }
  //
  // Verify the CodeView entry has been found in the Debug Directory.
  //
  if (DebugIndex == NumDebugEntries) {
    return;
  }
  //
  // Verify the CodeView entry has sufficient space for the signature.
  //
  CodeViewEntry = &DebugEntries[DebugIndex];

  if (CodeViewEntry->SizeOfData < sizeof (UINT32)) {
    DEBUG_RAISE ();
    return;
  }
  //
  // Verify the CodeView entry RVA is sane, or force-load, if permitted, if it
  // is not mapped by a section.
  //
  if (CodeViewEntry->RVA != 0) {
    // FIXME: Verify against first Image section / Headers due to XIP TE.
    //
    // Verify the CodeView entry is in bounds of the Image buffer, and the
    // CodeView entry RVA is sufficiently aligned.
    //
    Overflow = BaseOverflowAddU32 (
                 CodeViewEntry->RVA,
                 CodeViewEntry->SizeOfData,
                 &DebugEntryRvaTop
                 );
    if (Overflow || DebugEntryRvaTop > Context->SizeOfImage
     || !IS_ALIGNED (CodeViewEntry->RVA, ALIGNOF (UINT32))) {
      DEBUG_RAISE ();
      return;
    }
  } else {
    //
    // Force-load the CodeView entry if it is not mapped by an Image section.
    //
    if (PcdGet32 (PcdImageLoaderDebugSupport) < PCD_DEBUG_SUPPORT_FORCE_LOAD) {
      return;
    }
    //
    // If the Image does not load the debug information into memory on its own,
    // request reserved space for it to force-load it.
    //
    if (!PcdGetBool (PcdImageLoaderProhibitTe)) {
      Overflow = BaseOverflowSubU32 (
                   CodeViewEntry->FileOffset,
                   Context->TeStrippedOffset,
                   &DebugEntryTopOffset
                   );
      if (Overflow) {
        DEBUG_RAISE ();
        return;
      }
    } else {
      ASSERT (Context->TeStrippedOffset == 0);
      DebugEntryTopOffset = CodeViewEntry->FileOffset;
    }

    Overflow = BaseOverflowAddU32 (
                 DebugEntryTopOffset,
                 CodeViewEntry->SizeOfData,
                 &DebugEntryTopOffset
                 );
    if (Overflow || DebugEntryTopOffset > FileSize) {
      DEBUG_RAISE ();
      return;
    }
    //
    // The CodeView data must start on a 32-bit boundary.
    //
    Overflow = BaseOverflowAlignUpU32 (
                 Context->SizeOfImage,
                 ALIGNOF (UINT32),
                 &DebugSizeOfImage
                 );
    if (Overflow) {
      DEBUG_RAISE ();
      return;
    }

    Overflow = BaseOverflowAddU32 (
                 DebugSizeOfImage,
                 CodeViewEntry->SizeOfData,
                 &DebugSizeOfImage
                 );
    if (Overflow) {
      DEBUG_RAISE ();
      return;
    }
    //
    // Align the CodeView size by the Image alignment.
    //
    Overflow = BaseOverflowAlignUpU32 (
                 DebugSizeOfImage,
                 Context->SectionAlignment,
                 &DebugSizeOfImage
                 );
    if (Overflow) {
      DEBUG_RAISE ();
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
  //
  // Cache the CodeView RVA.
  //
  Context->CodeViewRva = Sections[SectionIndex].VirtualAddress + DebugDirSectionOffset + DebugIndex * sizeof (*DebugEntries);
  ASSERT (Context->CodeViewRva >= Sections[SectionIndex].VirtualAddress);
  ASSERT (Context->CodeViewRva <= Sections[SectionIndex].VirtualAddress + Sections[SectionIndex].VirtualSize);
}

VOID
PeCoffLoaderLoadCodeView (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  )
{
  EFI_IMAGE_DEBUG_DIRECTORY_ENTRY *CodeViewEntry;
  UINT32                          CodeViewOffset;

  ASSERT (Context != NULL);
  //
  // Verify the CodeView entry is present and well-formed.
  //
  if (Context->CodeViewRva == 0) {
    return;
  }
  //
  // Force-load the CodeView entry if it is not mapped by an Image section.
  //
  CodeViewEntry = (EFI_IMAGE_DEBUG_DIRECTORY_ENTRY *) (VOID *) (
                    (CHAR8 *) Context->ImageBuffer + Context->CodeViewRva
                    );
  if (CodeViewEntry->RVA == 0) {
    ASSERT (PcdGet32 (PcdImageLoaderDebugSupport) >= PCD_DEBUG_SUPPORT_FORCE_LOAD);
    ASSERT (Context->SizeOfImageDebugAdd > 0);
    //
    // This arithmetic cannot overflow because it has been verified during the
    // calculation of SizeOfImageDebugAdd.
    //
    CodeViewEntry->RVA = ALIGN_VALUE (Context->SizeOfImage, ALIGNOF (UINT32));

    ASSERT (Context->SizeOfImageDebugAdd >= (CodeViewEntry->RVA - Context->SizeOfImage) + CodeViewEntry->SizeOfData);

    CodeViewOffset = CodeViewEntry->FileOffset;

    if (!PcdGetBool (PcdImageLoaderProhibitTe)) {
      CodeViewOffset -= Context->TeStrippedOffset;
    } else {
      ASSERT (Context->TeStrippedOffset == 0);
    }

    CopyMem (
      (CHAR8 *) Context->ImageBuffer + CodeViewEntry->RVA,
      (CONST CHAR8 *) Context->FileBuffer + CodeViewOffset,
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
  //
  // Verify the CodeView entry is present and well-formed.
  //
  if (Context->CodeViewRva == 0) {
    return;
  }
  //
  // Force-load the CodeView entry if it is not mapped by an Image section.
  //
  CodeViewEntry = (EFI_IMAGE_DEBUG_DIRECTORY_ENTRY *) (VOID *) (
                    (CHAR8 *) Context->ImageBuffer + Context->CodeViewRva
                    );
  if (CodeViewEntry->RVA != 0) {
    //
    // If the CodeView entry is reported to be part of a Section, its RVA must
    // be equal to the raw file offset as the Image was loaded in-place.
    //
    if (CodeViewEntry->RVA != CodeViewEntry->FileOffset) {
      DEBUG_RAISE ();
      Context->CodeViewRva = 0;
      return;
    }
  } else {
    ASSERT (PcdGet32 (PcdImageLoaderDebugSupport) >= PCD_DEBUG_SUPPORT_FORCE_LOAD);
    ASSERT (Context->SizeOfImageDebugAdd > 0);
    //
    // The CodeView entry is always in the Image memory for inplace-loading.
    // Update the RVA to the raw file offset.
    //
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
  //
  // Verify the CodeView entry is present and well-formed.
  //
  if (Context->CodeViewRva == 0) {
    return RETURN_NOT_FOUND;
  }
  //
  // Retrieve the PDB path offset.
  //
  CodeViewEntry = (EFI_IMAGE_DEBUG_DIRECTORY_ENTRY *) (VOID *) (
                    (CHAR8 *) Context->ImageBuffer + Context->CodeViewRva
                    );

  CodeView = (CONST CHAR8 *) Context->ImageBuffer + CodeViewEntry->RVA;
  //
  // This memory access is safe because we know that
  //   1) IS_ALIGNED (CodeViewEntry->RVA, ALIGNOF (UINT32))
  //   2) sizeof (UINT32) <= CodeViewEntry->SizeOfData.
  //
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
      DEBUG_RAISE ();
      return RETURN_UNSUPPORTED;
  }
  //
  // Verify the PDB path exists and is in bounds of the Image buffer.
  //
  Overflow = BaseOverflowSubU32 (
               CodeViewEntry->SizeOfData,
               PdbOffset,
               &PdbNameSize
               );
  if (Overflow || PdbNameSize == 0) {
    DEBUG_RAISE ();
    return RETURN_UNSUPPORTED;
  }
  //
  // Verify the PDB path is correctly terminated.
  //
  PdbName = (CONST CHAR8 *) Context->ImageBuffer + CodeViewEntry->RVA + PdbOffset;
  if (PdbName[PdbNameSize - 1] != 0) {
    DEBUG_RAISE ();
    return RETURN_UNSUPPORTED;
  }

  *PdbPath     = PdbName;
  *PdbPathSize = PdbNameSize;

  return RETURN_SUCCESS;
}

// FIXME: Some image prints use this and some don't. Is this really needed?
RETURN_STATUS
PeCoffGetModuleNameFromPdb (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  OUT    CHAR8                         *ModuleName,
  IN     UINT32                        ModuleNameSize
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

// FIXME: Docs
STATIC
RETURN_STATUS
InternalDebugLocateImage (
  OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  IN  CHAR8                         *Buffer,
  IN  UINTN                         Address,
  IN  BOOLEAN                       Recurse
  )
{
  RETURN_STATUS                Status;
  RETURN_STATUS                DosStatus;
  PE_COFF_LOADER_IMAGE_CONTEXT DosContext;

  ASSERT (((UINTN) Buffer & 3U) == 0);
  //
  // Align the search buffer to a 4 Byte boundary.
  //
  // Search for the Image Header in 4 Byte steps. All dynamically loaded
  // Images start at a page boundary to allow for Image section protection,
  // but XIP Images may not. As all Image Headers are at least 4 Byte aligned
  // due to natural alignment, even XIP TE Image Headers should start at a
  // 4 Byte boundary.
  //
  // Do not attempt to access memory of the first page as it may be protected as
  // part of NULL dereference detection.
  //
  for (; EFI_PAGE_SIZE <= (UINTN) Buffer; Buffer -= 4) {
    //
    // Try to parse the current memory as PE/COFF or TE Image. Pass MAX_UINT32
    // as the file size as there isn't any more information available. Only the
    // Image Header memory will be accessed as part of initialisation.
    //
    Status = PeCoffInitializeContext (
               Context,
               Buffer,
               MAX_UINT32
               );
    if (RETURN_ERROR (Status)) {
      continue;
    }

    if (!Recurse) {
      //
      // For PE/COFF Images, the PE/COFF Image Header may be discovered while
      // there may still be a preceeding DOS Image Header. All RVAs are relatvie
      // to the start of the Image memory space, of which the DOS Image Header
      // is a part of, if existent. Allow one level of recursion to find a lower
      // Image Base including the DOS Image Header.
      //
      if (Context->ImageType != PeCoffLoaderTypeTe
       && Context->ExeHdrOffset == 0) {
        DosStatus = InternalDebugLocateImage (
                      &DosContext,
                      Buffer - 4,
                      Address,
                      TRUE
                      );
        if (!RETURN_ERROR (DosStatus)) {
          Buffer = DosContext.ImageBuffer;
          CopyMem (Context, &DosContext, sizeof (*Context));
        }
      }
    }
    //
    // We know that (UINTN) Buffer <= Address from the initialisation.
    //
    // FIXME: Set to non-stripped base for XIP TE Images.
    if (Address < (UINTN) Buffer + PeCoffGetSizeOfImage (Context)) {
      Context->ImageBuffer = Buffer;
      //
      // Zero the raw file information as we are initialising from a potentially
      // non-XIP in-memory Image.
      //
      Context->FileBuffer  = NULL;
      Context->FileSize    = 0;

      return RETURN_SUCCESS;
    }
    //
    // Continue for the unlikely case that a PE/COFF or TE Image embeds another
    // one within its data, the outer Image may still follow.
    //
  }

  return RETURN_NOT_FOUND;
}

RETURN_STATUS
PeCoffDebugLocateImage (
  OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  IN  UINTN                         Address
  )
{
  RETURN_STATUS Status;

  Status = RETURN_NOT_FOUND;
  //
  // As this function is intrinsically unsafe, do not allow its usage outside of
  // DEBUG-enabled code.
  //
  DEBUG_CODE_BEGIN ();

  //
  // If the Image Headers are not loaded explicitly, only XIP Images and Images
  // that embed the Image Header in the first Image section can be located. As
  // this is not the case for the majority of Images, don't attempt to locate
  // the Image base to not access too much (potentially protected) memory.
  //
  if (!PcdGetBool (PcdImageLoaderLoadHeader)) {
    DEBUG_RAISE ();
    return RETURN_NOT_FOUND;
  }
  //
  // Align the search buffer to a 4 Byte boundary.
  //
  Status = InternalDebugLocateImage (
             Context,
             (CHAR8 *) (Address & ~(UINTN) 3U),
             Address,
             FALSE
             );

  DEBUG_CODE_END ();

  return Status;
}
