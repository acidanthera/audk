/** @file
  Provides APIs to load PE/COFF Images.

  Copyright (c) 2020, Marvin Häuser. All rights reserved.<BR>
  Copyright (c) 2020, Vitaly Cheptsov. All rights reserved.<BR>
  Copyright (c) 2020, ISP RAS. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-3-Clause
**/

#ifndef PE_COFF_LOAD_H_
#define PE_COFF_LOAD_H_

/*@ axiomatic ImageLoading {
  @   lemma image_non_empty_sec_proves:
  @     (\forall EFI_IMAGE_SECTION_HEADER *Section;
  @        0 < image_sect_cpy_size (Section) ==> 0 < Section->SizeOfRawData) &&
  @     (\forall EFI_IMAGE_SECTION_HEADER *Section;
  @        image_sect_cpy_size (Section) <= Section->SizeOfRawData);
  @
  @   predicate image_hdr_loaded{L1, L2} (char *Image, char *FileBuffer, integer LoadedSizeOfHeaders) =
  @     char_equals{L2, L1} (
  @       Image,
  @       FileBuffer,
  @       LoadedSizeOfHeaders
  @       );
  @
  @   predicate image_hdr_trail_zero (char *Image, EFI_IMAGE_SECTION_HEADER *Sections, integer LoadedSizeOfHeaders) =
  @     char_zero (
  @       Image + LoadedSizeOfHeaders,
  @       Sections[0].VirtualAddress - LoadedSizeOfHeaders
  @       );
  @
  @   predicate image_sect_data_loaded{L1, L2} (char *Image, char *FileBuffer, EFI_IMAGE_SECTION_HEADER *Section, UINT32 TeStrippedOffset) =
  @     char_equals{L2, L1} (
  @       Image + \at(Section->VirtualAddress, L2),
  @       FileBuffer + (\at(Section->PointerToRawData, L2) - TeStrippedOffset),
  @       \at(image_sect_cpy_size (Section), L2)
  @       );
  @
  @   predicate image_sects_gap_zero (char *Image, EFI_IMAGE_SECTION_HEADER *Section1, EFI_IMAGE_SECTION_HEADER *Section2) =
  @     char_zero (
  @       Image + image_sect_cpy_top (Section1),
  @       Section2->VirtualAddress - image_sect_cpy_top (Section1)
  @       );
  @
  @   predicate image_trail_zero (char *Image, UINT32 ImageSize, EFI_IMAGE_SECTION_HEADER *Sections, UINT16 NumberOfSections) =
  @     char_zero (
  @       Image + image_sect_cpy_top (&Sections[NumberOfSections - 1]),
  @       ImageSize - image_sect_cpy_top (&Sections[NumberOfSections - 1])
  @       );
  @
  @   predicate image_sections_loaded{L1, L2} (char *Image, UINT32 ImageSize, char *FileBuffer, EFI_IMAGE_SECTION_HEADER *Sections, UINT16 NumberOfSections, UINT32 LoadedSizeOfHeaders, UINT16 TeStrippedOffset) =
  @     image_hdr_trail_zero{L2} (Image, Sections, LoadedSizeOfHeaders) &&
  @     (\forall integer i; 0 <= i < NumberOfSections ==>
  @       image_sect_data_loaded{L1, L2} (Image, FileBuffer, Sections + i, TeStrippedOffset)) &&
  @     (\forall integer i; 0 < i < NumberOfSections ==>
  @      image_sects_gap_zero{L2} (Image, Sections + (i - 1), Sections + i)) &&
  @     image_trail_zero{L2} (Image, ImageSize, Sections, NumberOfSections);
  @
  @   predicate image_loaded{L1, L2} (char *Image, UINT32 ImageSize, char *FileBuffer, EFI_IMAGE_SECTION_HEADER *Sections, UINT16 NumberOfSections, UINT32 LoadedSizeOfHeaders, UINT16 TeStrippedOffset) =
  @     image_hdr_loaded{L1, L2} (Image, FileBuffer, LoadedSizeOfHeaders) &&
  @     image_sections_loaded{L1, L2} (Image, ImageSize, FileBuffer, Sections, NumberOfSections, LoadedSizeOfHeaders, TeStrippedOffset);
  @
  @   predicate image_hdr_trail_preserved{L1, L2} (char *Image, EFI_IMAGE_SECTION_HEADER *Sections, UINT32 LoadedSizeOfHeaders) =
  @     char_equals{L1, L2} (
  @       Image + LoadedSizeOfHeaders,
  @       Image + LoadedSizeOfHeaders,
  @       \at(Sections[0].VirtualAddress, L2) - LoadedSizeOfHeaders
  @       );
  @
  @   predicate image_sect_data_preserved{L1, L2} (char *Image, EFI_IMAGE_SECTION_HEADER *Section) =
  @     char_equals{L1, L2} (
  @       Image + \at(Section->VirtualAddress, L2),
  @       Image + \at(Section->VirtualAddress, L2),
  @       \at(image_sect_cpy_size (Section), L2)
  @       );
  @
  @   predicate image_sects_gap_preserved{L1, L2} (char *Image, EFI_IMAGE_SECTION_HEADER *Section1, EFI_IMAGE_SECTION_HEADER *Section2) =
  @     char_equals{L1, L2} (
  @       Image + \at(image_sect_cpy_top (Section1), L2),
  @       Image + \at(image_sect_cpy_top (Section1), L2),
  @       \at(Section2->VirtualAddress - image_sect_cpy_top (Section1), L2)
  @       );
  @
  @   predicate image_sect_discardable{L}(EFI_IMAGE_SECTION_HEADER *Section) =
  @     (Section->Characteristics & ((uint32_t) 1 <<% (uint32_t) 25)) != 0;
  @ }
*/

/**
  Load the Image into the destination memory space.

  @param[in]  Context          The context describing the Image. Must have been
                               initialised by PeCoffInitializeContext().
  @param[out] Destination      The Image destination memory. Must be allocated
                               from page memory.
  @param[in]  DestinationSize  The size, in bytes, of Destination.
                               Must be at least
                               Context->SizeOfImage +
                               Context->SizeOfImageDebugAdd. If the Section
                               Alignment exceeds 4 KB, must be at least
                               Context->SizeOfImage +
                               Context->SizeOfImageDebugAdd
                               Context->SectionAlignment.

  @retval RETURN_SUCCESS  The Image was loaded successfully.
  @retval other           The Image could not be loaded successfully.
**/
/*@ requires \valid(Context);
  @ requires \typeof(Context->FileBuffer) <: \type(char *);
  @
  @ requires \typeof(Destination) <: \type(char *);
  @ requires \valid((char *) Destination + (0 .. DestinationSize - 1));
  @ requires pointer_aligned (Destination, BASE_4KB);
  @ requires Context->SizeOfImage <= DestinationSize;
  @ requires Context->SectionAlignment > BASE_4KB ==>
  @            Context->SizeOfImage + Context->SectionAlignment <= DestinationSize;
  @
  @ requires is_pow2_32 (Context->SectionAlignment);
  @ requires 0 <= image_hdr_raw_size (Context->SizeOfHeaders, Context->TeStrippedOffset);
  @
  @ requires image_context_type_valid (Context);
  @ requires image_context_hdr_valid (Context);
  @ requires Context->SectionsOffset <= MAX_UINT32;
  @
  @ requires 0 < Context->NumberOfSections;
  @
  @ requires \let Sections = image_context_get_sections (Context);
  @          \let NumberOfSections = Context->NumberOfSections;
  @          image_sects_in_image (Context) &&
  @          image_sects_in_file_bounds (Sections, NumberOfSections, Context->TeStrippedOffset, MAX_UINT32) &&
  @          image_sects_disjunct_sorted (Sections, NumberOfSections, Context->SizeOfHeaders, Context->SectionAlignment);
  @
  @ requires \valid ((char *) Context->FileBuffer + (0 .. image_hdr_raw_size (Context->SizeOfHeaders, Context->TeStrippedOffset) - 1));
  @ requires \let Sections = image_context_get_sections (Context);
  @          \let NumberOfSections = Context->NumberOfSections;
  @          \valid (Sections + (0 .. NumberOfSections - 1)) &&
  @          (\forall integer i; 0 <= i < NumberOfSections ==>
  @            \valid ((char *) Context->FileBuffer + ((Sections[i].PointerToRawData - Context->TeStrippedOffset) .. (Sections[i].PointerToRawData - Context->TeStrippedOffset) + Sections[i].SizeOfRawData - 1)));
  @
  @ assigns ((char *) Destination)[0 .. DestinationSize - 1];
  @ assigns Context->ImageBuffer;
  @
  @ ensures \result == RETURN_SUCCESS;
  @ ensures \let Address             = pointer_to_address (Destination);
  @         \let AlignOffset         = align_up (Address, Context->SectionAlignment) - Address;
  @         \let AlignedSize         = (UINT32) (DestinationSize - AlignOffset);
  @         \let AlignedDest         = (char *) Destination + AlignOffset;
  @         \let NumberOfSections    = Context->NumberOfSections;
  @         \let Sections            = image_context_get_sections (Context);
  @         \let LoadedSizeOfHeaders = (UINT32) image_context_get_loaded_hdr_raw_size (Context);
  @         char_zero ((char *) Destination, AlignOffset) &&
  @         image_loaded{Pre, Post} (
  @           AlignedDest,
  @           AlignedSize,
  @           (char *) Context->FileBuffer,
  @           Sections,
  @           NumberOfSections,
  @           LoadedSizeOfHeaders,
  @           Context->TeStrippedOffset
  @           ) &&
  @         Context->ImageBuffer == AlignedDest &&
  @         image_context_ImageBuffer_sane (Context) &&
  @         \valid ((char *) Context->ImageBuffer + (0 .. Context->SizeOfImage - 1)) &&
  @         image_reloc_dir_mem_valid ((char *) Context->ImageBuffer, Context->SizeOfImage, Context->RelocDirRva, Context->RelocDirSize);
*/
RETURN_STATUS
PeCoffLoadImage (
  IN OUT PE_COFF_IMAGE_CONTEXT  *Context,
  OUT    VOID                   *Destination,
  IN     UINT32                 DestinationSize
  );

/**
  Discards optional Image Sections to disguise sensitive data.

  @param[in] Context  The context describing the Image. Must have been loaded by
                      PeCoffLoadImage().
**/
/*@ requires \valid(Context);
  @ requires \typeof(Context->FileBuffer) <: \type(char *);
  @ requires \typeof(Context->ImageBuffer) <: \type(char *);
  @
  @ requires \let Sections = image_context_get_sections (Context);
  @          image_sects_disjunct_sorted (Sections, Context->NumberOfSections, Context->SizeOfHeaders, Context->SectionAlignment);
  @
  @ requires \let Sections = image_context_get_sections (Context);
  @          \valid (Sections + (0 .. Context->NumberOfSections - 1)) &&
  @          (\forall integer i; 0 <= i < Context->NumberOfSections ==>
  @            \valid ((char *) Context->ImageBuffer + (Sections[i].VirtualAddress .. Sections[i].VirtualAddress + Sections[i].VirtualSize)));
  @
  @ assigns ((char *) Context->ImageBuffer)[image_context_get_sections (Context)[0].VirtualAddress .. image_context_get_sections (Context)[Context->NumberOfSections - 1].VirtualAddress + image_context_get_sections (Context)[Context->NumberOfSections - 1].VirtualSize];
  @ assigns *(EFI_IMAGE_BASE_RELOCATION_BLOCK *) ((char *) Context->ImageBuffer + Context->RelocDirRva);
  @ assigns Context->RelocDirRva;
  @ assigns Context->RelocDirSize;
  @
  @ ensures \let Sections = image_context_get_sections (Context);
  @         \forall integer i; 0 <= i < Context->NumberOfSections ==>
  @           (image_sect_discardable (Sections + i) ==>
  @             char_zero (
  @               (char *) Context->ImageBuffer + Sections[i].VirtualAddress,
  @               Sections[i].VirtualSize
  @               )) &&
  @           (!image_sect_discardable (Sections + i) ==>
  @             char_equals{Post, Pre} (
  @               (char *) Context->ImageBuffer + Sections[i].VirtualAddress,
  @               (char *) Context->ImageBuffer + Sections[i].VirtualAddress,
  @               Sections[i].VirtualSize
  @               ));
  @ ensures Context->RelocDirRva == 0;
  @ ensures Context->RelocDirSize == 0;
  @ ensures !image_reloc_dir_correct ((char *) Context->ImageBuffer, \at(Context->SizeOfImage, Pre), \at(Context->RelocDirRva, Pre), \at(Context->RelocDirSize, Pre));
*/
VOID
PeCoffDiscardSections (
  IN OUT PE_COFF_IMAGE_CONTEXT  *Context
  );

#endif // PE_COFF_LOAD_H_
