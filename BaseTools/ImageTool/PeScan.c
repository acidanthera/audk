/** @file
  Copyright (c) 2021, Marvin Häuser. All rights reserved.
  Copyright (c) 2022, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause
**/

#include "ImageTool.h"

#include "PeScan.h"

#define PE_COFF_SECT_NAME_RELOC  ".reloc\0"
#define PE_COFF_SECT_NAME_RESRC  ".rsrc\0\0"
#define PE_COFF_SECT_NAME_DEBUG  ".debug\0"

RETURN_STATUS
ScanPeGetRelocInfo (
  OUT image_tool_reloc_info_t       *RelocInfo,
  IN  PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  )
{
  BOOLEAN                                Overflow;
  UINT32                                 RelocBlockRvaMax;
  UINT32                                 TopOfRelocDir;
  UINT32                                 RelocBlockRva;
  const EFI_IMAGE_BASE_RELOCATION_BLOCK  *RelocBlock;
  UINT32                                 RelocBlockSize;
  UINT32                                 SizeOfRelocs;
  UINT32                                 NumRelocs;
  UINT32                                 RelocIndex;
  uint32_t                               RelocDirSize;
  const char                             *ImageBuffer;
  UINT16                                 RelocType;
  UINT16                                 RelocOffset;
  uint32_t                               ToolRelocsSize;

  // FIXME: PE/COFF context access
  RelocBlockRva = Context->RelocDirRva;
  RelocDirSize  = Context->RelocDirSize;
  //
  // Verify the Relocation Directory is not empty.
  //
  if (RelocDirSize == 0) {
    return RETURN_SUCCESS;
  }

  STATIC_ASSERT (
    sizeof (*RelocInfo->Relocs) % sizeof (UINT16) == 0,
    "The division below is inaccurate."
    );

  Overflow = BaseOverflowMulU32 (
               RelocDirSize,
               sizeof (*RelocInfo->Relocs) / sizeof (UINT16),
               &ToolRelocsSize
               );
  if (Overflow) {
    DEBUG_RAISE ();
    return RETURN_OUT_OF_RESOURCES;
  }

  RelocInfo->Relocs = AllocateZeroPool (ToolRelocsSize);
  if (RelocInfo->Relocs == NULL) {
    fprintf (stderr, "ImageTool: Could not allocate memory for Relocs[]\n");
    return RETURN_OUT_OF_RESOURCES;
  }

  TopOfRelocDir = RelocBlockRva + RelocDirSize;

  RelocBlockRvaMax = TopOfRelocDir - sizeof (EFI_IMAGE_BASE_RELOCATION_BLOCK);
  //
  // Align TopOfRelocDir because, if the policy does not demand Relocation Block
  // sizes to be aligned, the code below will manually align them. Thus, the
  // end offset of the last Relocation Block must be compared to a manually
  // aligned Relocation Directoriy end offset.
  //
  Overflow = BaseOverflowAlignUpU32 (
               TopOfRelocDir,
               ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK),
               &TopOfRelocDir
               );
  if (Overflow) {
    fprintf (stderr, "ImageTool: Overflow during TopOfRelocDir calculation\n");
    return RETURN_VOLUME_CORRUPTED;
  }

  //
  // Apply all Base Relocations of the Image.
  //
  ImageBuffer = (char *)PeCoffLoaderGetImageAddress (Context);
  while (RelocBlockRva <= RelocBlockRvaMax) {
    RelocBlock = (const EFI_IMAGE_BASE_RELOCATION_BLOCK *)(const void *)(ImageBuffer + RelocBlockRva);
    //
    // Verify the Base Relocation Block size is well-formed.
    //
    Overflow = BaseOverflowSubU32 (
                 RelocBlock->SizeOfBlock,
                 sizeof (EFI_IMAGE_BASE_RELOCATION_BLOCK),
                 &SizeOfRelocs
                 );
    if (Overflow) {
      fprintf (stderr, "ImageTool: Overflow during SizeOfRelocs calculation\n");
      return RETURN_VOLUME_CORRUPTED;
    }

    //
    // Verify the Base Relocation Block is in bounds of the Relocation
    // Directory.
    //
    if (SizeOfRelocs > RelocBlockRvaMax - RelocBlockRva) {
      fprintf (stderr, "ImageTool:  Base Relocation Block is out of bounds of the Relocation Directory\n");
      return RETURN_VOLUME_CORRUPTED;
    }

    //
    // This arithmetic cannot overflow because we know
    //   1) RelocBlock->SizeOfBlock <= RelocMax <= TopOfRelocDir
    //   2) IS_ALIGNED (TopOfRelocDir, ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK)).
    //
    RelocBlockSize = ALIGN_VALUE (
                       RelocBlock->SizeOfBlock,
                       ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK)
                       );
    //
    // This division is safe due to the guarantee made above.
    //
    NumRelocs = SizeOfRelocs / sizeof (*RelocBlock->Relocations);
    //
    // Process all Base Relocations of the current Block.
    //
    for (RelocIndex = 0; RelocIndex < NumRelocs; ++RelocIndex) {
      RelocType   = IMAGE_RELOC_TYPE (RelocBlock->Relocations[RelocIndex]);
      RelocOffset = IMAGE_RELOC_OFFSET (RelocBlock->Relocations[RelocIndex]);

      switch (RelocType) {
        case EFI_IMAGE_REL_BASED_ABSOLUTE:
          continue;
        case EFI_IMAGE_REL_BASED_HIGHLOW:
        case EFI_IMAGE_REL_BASED_DIR64:
          RelocInfo->Relocs[RelocInfo->NumRelocs].Type = (uint8_t)RelocType;
          break;
        default:
          fprintf (stderr, "ImageTool: Unknown RelocType = 0x%x\n", RelocType);
          return RETURN_UNSUPPORTED;
      }

      RelocInfo->Relocs[RelocInfo->NumRelocs].Target = RelocBlock->VirtualAddress + RelocOffset;
      ++RelocInfo->NumRelocs;
    }

    //
    // This arithmetic cannot overflow because it has been checked that the
    // Image Base Relocation Block is in bounds of the Image buffer.
    //
    RelocBlockRva += RelocBlockSize;
  }

  //
  // Verify the Relocation Directory size matches the contained data.
  //
  if (RelocBlockRva != TopOfRelocDir) {
    fprintf (stderr, "ImageTool: Relocation Directory size does not match the contained data\n");
    return RETURN_VOLUME_CORRUPTED;
  }

  return RETURN_SUCCESS;
}

RETURN_STATUS
ScanPeGetSegmentInfo (
  OUT image_tool_segment_info_t     *SegmentInfo,
  IN  PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  )
{
  const EFI_IMAGE_SECTION_HEADER  *Section;
  uint32_t                        NumSections;
  image_tool_segment_t            *ImageSegment;
  const char                      *ImageBuffer;
  uint32_t                        Index;

  NumSections = PeCoffGetSectionTable (Context, &Section);

  STATIC_ASSERT (
    sizeof (*SegmentInfo->Segments) <= sizeof (*Section),
    "The multiplication below may overflow."
    );

  SegmentInfo->Segments = AllocateZeroPool (
                            NumSections * sizeof (*SegmentInfo->Segments)
                            );
  if (SegmentInfo->Segments == NULL) {
    fprintf (stderr, "ImageTool: Could not allocate memory for Segments[]\n");
    return RETURN_OUT_OF_RESOURCES;
  }

  ImageBuffer = (char *)PeCoffLoaderGetImageAddress (Context);

  ImageSegment = SegmentInfo->Segments;
  for (Index = 0; Index < NumSections; ++Index, ++Section) {
    STATIC_ASSERT (
      sizeof (PE_COFF_SECT_NAME_RELOC) == sizeof (Section->Name) &&
      sizeof (PE_COFF_SECT_NAME_RESRC) == sizeof (Section->Name) &&
      sizeof (PE_COFF_SECT_NAME_DEBUG) == sizeof (Section->Name),
      "Section names exceed section name bounds."
      );

    if (  ((Section->Characteristics & EFI_IMAGE_SCN_MEM_DISCARDABLE) == 0)
       && (memcmp (Section->Name, PE_COFF_SECT_NAME_RELOC, sizeof (Section->Name)) != 0)
       && (memcmp (Section->Name, PE_COFF_SECT_NAME_RESRC, sizeof (Section->Name)) != 0)
       && (memcmp (Section->Name, PE_COFF_SECT_NAME_DEBUG, sizeof (Section->Name)) != 0))
    {
      ImageSegment->Name = AllocateCopyPool (
                             sizeof (Section->Name),
                             Section->Name
                             );
      if (ImageSegment->Name == NULL) {
        fprintf (stderr, "ImageTool: Could not allocate memory for Segment Name\n");
        return RETURN_OUT_OF_RESOURCES;
      }

      ImageSegment->ImageAddress = Section->VirtualAddress;
      ImageSegment->ImageSize    = ALIGN_VALUE (Section->VirtualSize, SegmentInfo->SegmentAlignment);
      ImageSegment->Read         = (Section->Characteristics & EFI_IMAGE_SCN_MEM_READ) != 0;
      ImageSegment->Write        = (Section->Characteristics & EFI_IMAGE_SCN_MEM_WRITE) != 0;
      ImageSegment->Execute      = (Section->Characteristics & EFI_IMAGE_SCN_MEM_EXECUTE) != 0;

      ImageSegment->Data = AllocateCopyPool (
                             ImageSegment->ImageSize,
                             ImageBuffer + Section->VirtualAddress
                             );
      if (ImageSegment->Data == NULL) {
        fprintf (stderr, "ImageTool: Could not allocate memory for Segment Data\n");
        FreePool (ImageSegment->Name);
        return RETURN_OUT_OF_RESOURCES;
      }

      ++SegmentInfo->NumSegments;
      ++ImageSegment;
    }
  }

  return RETURN_SUCCESS;
}
