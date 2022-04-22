/** @file
  Implements APIs to load PE/COFF Images.

  Portions copyright (c) 2006 - 2019, Intel Corporation. All rights reserved.<BR>
  Portions copyright (c) 2008 - 2010, Apple Inc. All rights reserved.<BR>
  Portions Copyright (c) 2020, Hewlett Packard Enterprise Development LP. All rights reserved.<BR>
  Copyright (c) 2020, Marvin Häuser. All rights reserved.<BR>
  Copyright (c) 2020, Vitaly Cheptsov. All rights reserved.<BR>
  Copyright (c) 2020, ISP RAS. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-3-Clause
**/

#include <Uefi.h>

#include "BasePeCoffLibInternals.h"

#include "PeCoffLoad.h"
#include "PeCoffRelocate.h"
#include "PeCoffDebug.h"

/*@ ghost
  @ /@ requires \valid (Context);
  @  @ requires \typeof (Context->ImageBuffer) <: \type(char *);
  @  @ requires \valid ((char *) Context->ImageBuffer + (0 .. Context->SizeOfImage - 1));
  @  @ requires \let Sections         = image_context_get_sections (Context);
  @  @          \let LoadedHeaderSize = (UINT32) image_context_get_loaded_hdr_raw_size (Context);
  @  @          image_loaded{Pre, Pre} (
  @  @            (char *) Context->ImageBuffer,
  @  @            Context->SizeOfImage,
  @  @            (char *) Context->FileBuffer,
  @  @            Sections,
  @  @            Context->NumberOfSections,
  @  @            LoadedHeaderSize,
  @  @            Context->TeStrippedOffset
  @  @            );
  @  @ assigns \nothing;
  @  @ ensures image_reloc_dir_mem_valid ((char *) Context->ImageBuffer, Context->SizeOfImage, Context->RelocDirRva, Context->RelocDirSize);
  @  @/
  @ VOID AvFlagImage (CONST PE_COFF_LOADER_IMAGE_CONTEXT *Context);
*/

/**
  Loads the Image Sections into the memory space and initialises any padding
  with zeros.

  @param[in]  Context           The context describing the Image. Must have been
                                initialised by PeCoffInitializeContext().
  @param[in]  LoadedHeaderSize  The size, in bytes, of the loaded Image Headers.
  @param[out] Destination       The Image destination memory.
  @param[in]  DestinationSize   The size, in bytes, of Destination.
                                Must be at least
                                Context->SizeOfImage +
                                Context->SizeOfImageDebugAdd. If the Section
                                Alignment exceeds 4 KB, must be at least
                                Context->SizeOfImage +
                                Context->SizeOfImageDebugAdd
                                Context->SectionAlignment.
**/
/*@ requires \valid (Context);
  @ requires \typeof(Context->FileBuffer) <: \type(char *);
  @
  @ requires 0 < Context->NumberOfSections;
  @
  @ requires \let Sections = (EFI_IMAGE_SECTION_HEADER *) ((char *) Context->FileBuffer + Context->SectionsOffset);
  @          \valid (Sections + (0 .. Context->NumberOfSections - 1)) &&
  @          (\forall integer i; 0 <= i < Context->NumberOfSections ==>
  @            \valid ((char *) Context->FileBuffer + ((Sections[i].PointerToRawData - Context->TeStrippedOffset) .. (Sections[i].PointerToRawData - Context->TeStrippedOffset) + Sections[i].SizeOfRawData - 1)));
  @
  @ requires \typeof(Destination) <: \type(char *);
  @ requires \valid ((char *) Destination + (0 .. DestinationSize - 1));
  @
  @ requires \let Sections = (EFI_IMAGE_SECTION_HEADER *) ((char *) Context->FileBuffer + Context->SectionsOffset);
  @          (\forall integer i; 0 <= i < Context->NumberOfSections ==>
  @            LoadedHeaderSize <= Sections[i].VirtualAddress);
  @
  @ requires \let Sections = (EFI_IMAGE_SECTION_HEADER *) ((char *) Context->FileBuffer + Context->SectionsOffset);
  @          (\forall integer i; 0 <= i < Context->NumberOfSections ==>
  @            image_sect_cpy_top (Sections + i) <= DestinationSize) &&
  @          image_sects_in_file_bounds (Sections, Context->NumberOfSections, Context->TeStrippedOffset, MAX_UINT32) &&
  @          image_sects_disjunct_sorted (Sections, Context->NumberOfSections, Context->SizeOfHeaders, Context->SectionAlignment);
  @
  @ assigns ((char *) Destination)[LoadedHeaderSize .. DestinationSize - 1];
  @
  @ ensures \let Sections = (EFI_IMAGE_SECTION_HEADER *) ((char *) Context->FileBuffer + Context->SectionsOffset);
  @         image_sections_loaded{Pre, Post} (
  @           (char *) Destination,
  @           DestinationSize,
  @           (char *) Context->FileBuffer,
  @           Sections,
  @           Context->NumberOfSections,
  @           LoadedHeaderSize,
  @           Context->TeStrippedOffset
  @           );
*/
STATIC
VOID
InternalLoadSections (
  IN  CONST PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  IN  UINT32                       LoadedHeaderSize,
  OUT VOID                         *Destination,
  IN  UINT32                       DestinationSize
  )
{
  CONST EFI_IMAGE_SECTION_HEADER *Sections;
  UINT16                         Index;
  UINT32                         DataSize;
  UINT32                         PreviousTopRva;

  /*@ assigns Sections;
    @ ensures Sections == (EFI_IMAGE_SECTION_HEADER *) ((char *) Context->FileBuffer + Context->SectionsOffset);
    @ ensures \valid(Sections + (0 .. Context->NumberOfSections - 1));
  */
  Sections = (CONST EFI_IMAGE_SECTION_HEADER *) (CONST VOID *) (
               (CONST CHAR8 *) Context->FileBuffer + Context->SectionsOffset
               );
  //
  // As the loop zero's the data from the end of the previous section, start
  // with the size of the loaded Image Headers to zero their trailing data.
  //
  /*@ assigns PreviousTopRva;
    @ ensures PreviousTopRva == LoadedHeaderSize;
  */
  PreviousTopRva = LoadedHeaderSize;

  /*@ loop assigns Index, DataSize, PreviousTopRva, ((char *) Destination)[LoadedHeaderSize .. DestinationSize - 1];
    @
    @ loop invariant 0 <= Index <= Context->NumberOfSections;
    @
    @ loop invariant 0 == Index ==>
    @                  PreviousTopRva == LoadedHeaderSize;
    @ loop invariant 0 < Index ==>
    @                  PreviousTopRva == image_sect_cpy_top (&Sections[Index - 1]);
    @
    @ loop invariant Index < Context->NumberOfSections ==>
    @                  LoadedHeaderSize <= PreviousTopRva <= Sections[Index].VirtualAddress;
    @ loop invariant \forall integer i; 0 <= i < Index ==>
    @                  Sections[i].VirtualAddress <= PreviousTopRva;
    @ loop invariant \forall integer i; 0 <= i < Index ==>
    @                  image_sect_cpy_top (Sections + i) <= PreviousTopRva;
    @
    @ loop invariant 0 < Index ==>
    @                  image_hdr_trail_zero (
    @                    (char *) Destination,
    @                    Sections,
    @                    LoadedHeaderSize
    @                    );
    @
    @ loop invariant \forall integer i; 0 <= i < Index ==>
    @                  image_sect_data_loaded{Pre, Here} (
    @                    (char *) Destination,
    @                    (char *) Context->FileBuffer,
    @                    Sections + i,
    @                    Context->TeStrippedOffset
    @                    );
    @
    @ loop invariant \forall integer i; 0 < i < Index ==>
    @                  image_sects_gap_zero (
    @                    (char *) Destination,
    @                    Sections + (i - 1),
    @                    Sections + i
    @                    );
    @
    @ loop variant Context->NumberOfSections - Index;
  */
  for (Index = 0; Index < Context->NumberOfSections; ++Index) {
    /*@ assigns DataSize;
      @ ensures DataSize == image_sect_cpy_size (&Sections[Index]);
    */
    if (Sections[Index].VirtualSize < Sections[Index].SizeOfRawData) {
      DataSize = Sections[Index].VirtualSize;
    } else {
      DataSize = Sections[Index].SizeOfRawData;
    }

    /*@ assigns ((char *) Destination)[PreviousTopRva .. Sections[Index].VirtualAddress - 1];
      @
      @ ensures image_hdr_trail_zero (
      @           (char *) Destination,
      @           Sections,
      @           LoadedHeaderSize
      @           );
      @
      @ ensures \forall integer i; 0 < i <= Index ==>
      @           image_sects_gap_zero (
      @             (char *) Destination,
      @             Sections + (i - 1),
      @             Sections + i
      @             );
      @
      @ ensures \forall integer i; 0 <= i < Index ==>
      @           image_sect_data_loaded{Pre, Post} (
      @             (char *) Destination,
      @             (char *) Context->FileBuffer,
      @             Sections + i,
      @             Context->TeStrippedOffset
      @             );
    */
    {
      //
      // Zero from the end of the previous Section to the start of this Section.
      //
      /*@ requires 0 == Index ==>
        @            PreviousTopRva == LoadedHeaderSize;
        @ requires 0 < Index ==>
        @            PreviousTopRva == image_sect_cpy_top (&Sections[Index - 1]);
        @
        @ requires LoadedHeaderSize <= PreviousTopRva;
        @ requires \forall integer i; 0 <= i < Index ==>
        @            Sections[i].VirtualAddress <= PreviousTopRva;
        @ requires \forall integer i; 0 <= i < Index ==>
        @            image_sect_cpy_top (Sections + i) <= PreviousTopRva;
        @
        @ requires 0 < Index ==>
        @            image_hdr_trail_zero (
        @              (char *) Destination,
        @              Sections,
        @              LoadedHeaderSize
        @              );
        @
        @ requires \forall integer i; 0 <= i < Index ==>
        @            image_sect_data_loaded{Pre, Here} (
        @              (char *) Destination,
        @              (char *) Context->FileBuffer,
        @              Sections + i,
        @              Context->TeStrippedOffset
        @              );
        @
        @ requires \forall integer i; 0 < i < Index ==>
        @            image_sects_gap_zero (
        @              (char *) Destination,
        @              Sections + (i - 1),
        @              Sections + i
        @              );
        @
        @ assigns ((char *) Destination)[PreviousTopRva .. Sections[Index].VirtualAddress - 1];
        @
        @ ensures char_equals{Old, Post}(
        @           (char *) Destination,
        @           (char *) Destination,
        @           PreviousTopRva
        @           );
        @
        @ ensures 0 < Index ==>
        @           image_hdr_trail_zero{Old} (
        @             (char *) Destination,
        @             Sections,
        @             LoadedHeaderSize
        @             );
        @ ensures 0 < Index ==>
        @           image_hdr_trail_preserved{Old, Post} (
        @             (char *) Destination,
        @             Sections,
        @             LoadedHeaderSize
        @             );
        @
        @ ensures \forall integer i; 0 < i <= Index && i != Index ==>
        @           image_sects_gap_zero{Old} (
        @             (char *) Destination,
        @             Sections + (i - 1),
        @             Sections + i
        @             );
        @ ensures (char_equals{Old, Post}(
        @           (char *) Destination,
        @           (char *) Destination,
        @           Sections[Index].VirtualAddress
        @           )) ==>
        @           (\forall integer i; 0 < i <= Index && i != Index ==>
        @           image_sects_gap_preserved{Old, Post} (
        @             (char *) Destination,
        @             Sections + (i - 1),
        @             Sections + i
        @             ));
        @
        @ ensures \forall integer i; 0 <= i < Index ==>
        @           image_sect_data_loaded{Pre, Post} (
        @             (char *) Destination,
        @             (char *) Context->FileBuffer,
        @             Sections + i,
        @             Context->TeStrippedOffset
        @             );
        @ ensures (char_equals{Old, Post}(
        @           (char *) Destination,
        @           (char *) Destination,
        @           PreviousTopRva
        @           )) ==>
        @           (\forall integer i; 0 <= i < Index ==>
        @           image_sect_data_preserved{Old, Post} (
        @             (char *) Destination,
        @             Sections + i
        @             ));
        @
        @ ensures 0 == Index ==>
        @           image_hdr_trail_zero (
        @             (char *) Destination,
        @             Sections,
        @             LoadedHeaderSize
        @             );
        @ ensures \forall integer i; 0 < i <= Index && i == Index ==>
        @           image_sects_gap_zero (
        @             (char *) Destination,
        @             Sections + (i - 1),
        @             Sections + i
        @             );
      */
      ZeroMem ((CHAR8 *) Destination + PreviousTopRva, Sections[Index].VirtualAddress - PreviousTopRva);

      /*@ assert \forall integer i; 0 < i <= Index && i != Index ==>
        @          image_sects_gap_zero (
        @            (char *) Destination,
        @            Sections + (i - 1),
        @            Sections + i
        @            );
      */

      /*@ assert \forall integer i; 0 < i <= Index ==>
        @          image_sects_gap_zero (
        @            (char *) Destination,
        @            Sections + (i - 1),
        @            Sections + i
        @            );
      */

      /*@ assert image_hdr_trail_zero (
        @          (char *) Destination,
        @          Sections,
        @          LoadedHeaderSize
        @          );
      */
    }

    /*@ assigns ((char *) Destination)[Sections[Index].VirtualAddress .. image_sect_cpy_top (&Sections[Index]) - 1];
      @
      @ ensures image_hdr_trail_zero (
      @           (char *) Destination,
      @           Sections,
      @           LoadedHeaderSize
      @           );
      @
      @ ensures \forall integer i; 0 < i <= Index ==>
      @           image_sects_gap_zero (
      @             (char *) Destination,
      @             Sections + (i - 1),
      @             Sections + i
      @             );
      @
      @ ensures \forall integer i; 0 <= i <= Index ==>
      @           image_sect_data_loaded{Pre, Post} (
      @             (char *) Destination,
      @             (char *) Context->FileBuffer,
      @             Sections + i,
      @             Context->TeStrippedOffset
      @             );
    */
    {
      //
      // Load the current Section into memory.
      //
      /*@ requires DataSize == image_sect_cpy_size (&Sections[Index]);
        @
        @ requires LoadedHeaderSize <= Sections[Index].VirtualAddress;
        @ requires \forall integer i; 0 <= i < Index ==>
        @            Sections[i].VirtualAddress <= Sections[Index].VirtualAddress;
        @ requires \forall integer i; 0 <= i < Index ==>
        @            image_sect_cpy_top (Sections + i) <= Sections[Index].VirtualAddress;
        @
        @ requires 0 < DataSize ==>
        @            Context->TeStrippedOffset <= Sections[Index].PointerToRawData;
        @ requires image_sect_cpy_size (&Sections[Index]) <= Sections[Index].SizeOfRawData;
        @ requires 0 < DataSize ==>
        @            0 < Sections[Index].SizeOfRawData;
        @
        @ requires image_hdr_trail_zero (
        @            (char *) Destination,
        @            Sections,
        @            LoadedHeaderSize
        @            );
        @
        @ requires \forall integer i; 0 <= i < Index ==>
        @            image_sect_data_loaded{Pre, Here} (
        @              (char *) Destination,
        @              (char *) Context->FileBuffer,
        @              Sections + i,
        @              Context->TeStrippedOffset
        @              );
        @
        @ requires \forall integer i; 0 < i <= Index && i != Index ==>
        @            image_sects_gap_zero (
        @              (char *) Destination,
        @              Sections + (i - 1),
        @              Sections + i
        @              );
        @
        @ assigns ((char *) Destination)[Sections[Index].VirtualAddress .. image_sect_cpy_top (&Sections[Index]) - 1];
        @
        @ ensures char_equals{Old, Post}(
        @           (char *) Destination,
        @           (char *) Destination,
        @           Sections[Index].VirtualAddress
        @           );
        @
        @ ensures image_hdr_trail_zero{Old} (
        @           (char *) Destination,
        @           Sections,
        @           LoadedHeaderSize
        @           );
        @ ensures image_hdr_trail_preserved{Old, Post} (
        @           (char *) Destination,
        @           Sections,
        @           LoadedHeaderSize
        @           );
        @
        @ ensures \forall integer i; 0 < i <= Index ==>
        @            image_sects_gap_zero{Old} (
        @              (char *) Destination,
        @              Sections + (i - 1),
        @              Sections + i
        @              );
        @ ensures (char_equals{Old, Post}(
        @           (char *) Destination,
        @           (char *) Destination,
        @           Sections[Index].VirtualAddress
        @           )) ==>
        @           (\forall integer i; 0 < i <= Index ==>
        @             image_sects_gap_preserved{Old, Post} (
        @               (char *) Destination,
        @               Sections + (i - 1),
        @               Sections + i
        @               ));
        @
        @ ensures \forall integer i; 0 <= i <= Index && i != Index ==>
        @           image_sect_data_loaded{Pre, Old} (
        @             (char *) Destination,
        @             (char *) Context->FileBuffer,
        @             Sections + i,
        @             Context->TeStrippedOffset
        @             );
        @ ensures (char_equals{Old, Post}(
        @           (char *) Destination,
        @           (char *) Destination,
        @           Sections[Index].VirtualAddress
        @           )) ==>
        @           (\forall integer i; 0 <= i <= Index && i != Index ==>
        @             image_sect_data_preserved{Old,Post} (
        @               (char *) Destination,
        @               Sections + i
        @               ));
        @
        @ ensures \forall integer i; 0 <= i <= Index && i == Index ==>
        @           image_sect_data_loaded{Pre, Post} (
        @             (char *) Destination,
        @             (char *) Context->FileBuffer,
        @             Sections + i,
        @             Context->TeStrippedOffset
        @             );
      */
      CopyMem (
        (CHAR8 *) Destination + Sections[Index].VirtualAddress,
        (CONST CHAR8 *) Context->FileBuffer + (Sections[Index].PointerToRawData -/*@%*/ Context->TeStrippedOffset),
        DataSize
        );

      /*@ assert \forall integer i; 0 <= i <= Index && i != Index ==>
        @          image_sect_data_loaded{Pre, Here} (
        @            (char *) Destination,
        @            (char *) Context->FileBuffer,
        @            Sections + i,
        @            Context->TeStrippedOffset
        @            );
      */

      /*@ assert \forall integer i; 0 <= i <= Index ==>
        @          image_sect_data_loaded{Pre, Here} (
        @            (char *) Destination,
        @            (char *) Context->FileBuffer,
        @            Sections + i,
        @            Context->TeStrippedOffset
        @            );
      */

      /*@ assert image_hdr_trail_zero (
        @          (char *) Destination,
        @          Sections,
        @          LoadedHeaderSize
        @          );
      */

      /*@ assert \forall integer i; 0 < i <= Index ==>
        @          image_sects_gap_zero (
        @            (char *) Destination,
        @            Sections + (i - 1),
        @            Sections + i
        @            );
      */
    }

    /*@ requires DataSize == image_sect_cpy_size (&Sections[Index]);
      @ assigns PreviousTopRva;
      @ ensures PreviousTopRva == image_sect_cpy_top (&Sections[Index]);
    */
    PreviousTopRva = Sections[Index].VirtualAddress + DataSize;
  }
  //
  // Zero the trailer after the last Image Section.
  //
  /*@ requires 0 < Index == Context->NumberOfSections;
    @
    @ requires image_sect_cpy_top (&Sections[Context->NumberOfSections - 1]) == PreviousTopRva <= DestinationSize;
    @
    @ requires LoadedHeaderSize <= Sections[0].VirtualAddress <= PreviousTopRva;
    @ requires \forall integer i; 0 <= i < Context->NumberOfSections ==>
    @            Sections[i].VirtualAddress <= PreviousTopRva;
    @ requires \forall integer i; 0 <= i < Context->NumberOfSections ==>
    @            image_sect_cpy_top (Sections + i) <= PreviousTopRva;
    @
    @ requires image_hdr_trail_zero (
    @            (char *) Destination,
    @            Sections,
    @            LoadedHeaderSize
    @            );
    @
    @ requires \forall integer i; 0 <= i < Context->NumberOfSections ==>
    @            image_sect_data_loaded{Pre, Here} (
    @              (char *) Destination,
    @              (char *) Context->FileBuffer,
    @              Sections + i,
    @              Context->TeStrippedOffset
    @              );
    @
    @ requires \forall integer i; 0 < i < Context->NumberOfSections ==>
    @            image_sects_gap_zero (
    @              (char *) Destination,
    @              Sections + (i - 1),
    @              Sections + i
    @              );
    @
    @ assigns ((char *) Destination)[PreviousTopRva .. DestinationSize - 1];
    @
    @ ensures char_equals{Old, Post}(
    @           (char *) Destination,
    @           (char *) Destination,
    @           PreviousTopRva
    @           );
    @
    @ ensures image_hdr_trail_zero{Old} (
    @           (char *) Destination,
    @           Sections,
    @           LoadedHeaderSize
    @           );
    @ ensures image_hdr_trail_preserved{Old, Post} (
    @           (char *) Destination,
    @           Sections,
    @           LoadedHeaderSize
    @           );
    @
    @ ensures \forall integer i; 0 < i < Context->NumberOfSections ==>
    @           image_sects_gap_zero{Old} (
    @             (char *) Destination,
    @             Sections + (i - 1),
    @             Sections + i
    @             );
    @ ensures (char_equals{Old, Post}(
    @           (char *) Destination,
    @           (char *) Destination,
    @           PreviousTopRva
    @           )) ==>
    @           (\forall integer i; 0 < i < Context->NumberOfSections ==>
    @             image_sects_gap_preserved{Old, Post} (
    @               (char *) Destination,
    @               Sections + (i - 1),
    @               Sections + i
    @               ));
    @
    @ ensures \forall integer i; 0 <= i < Context->NumberOfSections ==>
    @           image_sect_data_loaded{Pre, Old} (
    @             (char *) Destination,
    @             (char *) Context->FileBuffer,
    @             Sections + i,
    @             Context->TeStrippedOffset
    @             );
    @ ensures (char_equals{Old, Post}(
    @           (char *) Destination,
    @           (char *) Destination,
    @           PreviousTopRva
    @           )) ==>
    @           (\forall integer i; 0 <= i < Context->NumberOfSections ==>
    @             image_sect_data_preserved{Old,Post} (
    @               (char *) Destination,
    @               Sections + i
    @               ));
    @
    @ ensures image_trail_zero (
    @           (char *) Destination,
    @           DestinationSize,
    @           Sections,
    @           Context->NumberOfSections
    @           );
  */
  ZeroMem (
    (CHAR8 *) Destination + PreviousTopRva,
    DestinationSize - PreviousTopRva
    );

  /*@ assert image_hdr_trail_zero (
    @          (char *) Destination,
    @          Sections,
    @          LoadedHeaderSize
    @          );
  */

  /*@ assert \forall integer i; 0 < i < Context->NumberOfSections ==>
    @          image_sects_gap_zero (
    @            (char *) Destination,
    @            Sections + (i - 1),
    @            Sections + i
    @            );
  */

  /*@ assert \forall integer i; 0 <= i < Context->NumberOfSections ==>
    @          image_sect_data_loaded{Pre, Here} (
    @            (char *) Destination,
    @            (char *) Context->FileBuffer,
    @            Sections + i,
    @            Context->TeStrippedOffset
    @            );
  */
}

RETURN_STATUS
PeCoffLoadImage (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  OUT    VOID                   *Destination,
  IN     UINT32                 DestinationSize
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
  ASSERT (DestinationSize >= Context->SectionAlignment);

  /*@ assigns \nothing;
    @ ensures is_pow2_32 (BASE_4KB);
    @ ensures is_pow2_32 (AV_MAX_ALIGN);
  */
  {
    //@ assert BASE_4KB != 0;
    //@ assert ((uint32_t) BASE_4KB & ((uint32_t) BASE_4KB -% 1U)) == 0;
    //@ assert is_pow2_32 ((uint32_t) BASE_4KB);
    //@ assert is_pow2_32 (BASE_4KB);

    //@ assert AV_MAX_ALIGN != 0;
    //@ assert ((uint32_t) AV_MAX_ALIGN & ((uint32_t) AV_MAX_ALIGN -% 1U)) == 0;
    //@ assert is_pow2_32 ((uint32_t) AV_MAX_ALIGN);
    //@ assert is_pow2_32 (AV_MAX_ALIGN);
  }
  //@ assert is_aligned_N (pointer_to_address (Destination), BASE_4KB);
  //@ assert is_aligned_N (pointer_to_address (Destination), AV_MAX_ALIGN);
  //@ assert pointer_max_aligned (Destination);
  //
  // Correctly align the Image data in memory.
  //
  /*@ assigns AlignedDest, AlignedSize, AlignedAddress, AlignOffset, ((char *) Destination)[0 .. align_up (pointer_to_address (Destination), Context->SectionAlignment) - pointer_to_address (Destination) - 1];
    @ ensures AlignedDest == (char *) Destination + AlignOffset;
    @ ensures \valid (AlignedDest + (0 .. AlignedSize - 1));
    @ ensures AlignOffset == align_up (pointer_to_address (Destination), Context->SectionAlignment) - pointer_to_address (Destination);
    @ ensures char_zero ((char *) Destination, AlignOffset);
    @ ensures AlignedSize == DestinationSize - AlignOffset;
    @ ensures Context->SizeOfImage <= AlignedSize;
    @ ensures pointer_max_aligned (AlignedDest);
  */
  if (Context->SectionAlignment <= EFI_PAGE_SIZE) {
    //
    // The caller is required to allocate page memory, hence we have at least
    // 4 KB alignment guaranteed.
    //
    //@ assert is_pow2_32 (BASE_4KB);
    /*@ assert is_aligned_N (pointer_to_address (Destination), BASE_4KB) ==>
      @          is_aligned_N (pointer_to_address (Destination), Context->SectionAlignment);
    */
    //@ assert align_up (pointer_to_address (Destination), Context->SectionAlignment) == pointer_to_address (Destination);

    /*@ assigns AlignedDest;
      @ ensures AlignedDest == Destination;
      @ ensures pointer_max_aligned (AlignedDest);
    */
    AlignedDest = Destination;

    /*@ assigns AlignedSize;
      @ ensures AlignedSize == DestinationSize;
    */
    AlignedSize = DestinationSize;

    /*@ assigns AlignOffset;
      @ ensures AlignOffset == align_up (pointer_to_address (Destination), Context->SectionAlignment) - pointer_to_address (Destination);
    */
    AlignOffset = 0;

    //@ assert char_zero ((char *) Destination, AlignOffset);
  } else {
    /*@ assigns Address;
      @ ensures Address == pointer_to_address (Destination);
      @ ensures Address + Context->SectionAlignment <= Address + DestinationSize <= MAX_UINTN;
      @ ensures is_aligned_N (pointer_to_address (Destination), AV_MAX_ALIGN);
    */
    Address = PTR_TO_ADDR (Destination, DestinationSize);

    /*@ requires is_pow2_N ((UINTN) Context->SectionAlignment);
      @ requires align_safe_N (Address, Context->SectionAlignment);
      @ assigns AlignedAddress;
      @ ensures AlignedAddress == align_up (Address, Context->SectionAlignment);
      @ ensures is_aligned_N (AlignedAddress, AV_MAX_ALIGN);
    */
    AlignedAddress = ALIGN_VALUE (Address, (UINTN) Context->SectionAlignment);

    /*@ assigns AlignOffset;
      @ ensures AlignOffset == align_up (Address, Context->SectionAlignment) - Address;
      @ ensures pointer_to_address (Destination) + AlignOffset == AlignedAddress;
      @ ensures AlignOffset < Context->SectionAlignment <= DestinationSize;
    */
    AlignOffset = (UINT32) (AlignedAddress - Address);

    /*@ assigns AlignedSize;
      @ ensures AlignedSize == DestinationSize - AlignOffset;
      @ ensures Context->SizeOfImage <= AlignedSize;
    */
    AlignedSize = DestinationSize - AlignOffset;

    ASSERT (Context->SizeOfImage <= AlignedSize);

    /*@ requires pointer_to_address ((char *) Destination + AlignOffset) == pointer_to_address (Destination) + AlignOffset == AlignedAddress;
      @ assigns AlignedDest;
      @ ensures AlignedDest == (char *) Destination + AlignOffset;
      @ ensures \valid(AlignedDest + (0 .. AlignedSize - 1));
      @ ensures pointer_to_address (AlignedDest) == AlignedAddress;
      @ ensures pointer_max_aligned (AlignedDest);
    */
    AlignedDest = (CHAR8 *) Destination + AlignOffset;

    /*@ assigns ((char *) Destination)[0 .. AlignOffset - 1];
      @ ensures char_zero ((char *) Destination, AlignOffset);
    */
    ZeroMem (Destination, AlignOffset);
  }

  ASSERT (AlignedSize >= Context->SizeOfImage);

  /*@ assigns Sections;
    @ ensures Sections == image_context_get_sections (Context);
    @ ensures \valid(Sections + (0 .. Context->NumberOfSections - 1));
  */
  Sections = (CONST EFI_IMAGE_SECTION_HEADER *) (CONST VOID *) (
               (CONST CHAR8 *) Context->FileBuffer + Context->SectionsOffset
               );
  //
  // If configured, load the Image Headers into the memory space.
  //
  /*@ assigns LoadedHeaderSize, ((char *) Destination)[AlignOffset .. DestinationSize - 1];
    @ ensures LoadedHeaderSize == image_context_get_loaded_hdr_raw_size (Context);
    @ ensures (\forall integer i; 0 <= i < Context->NumberOfSections ==>
    @           LoadedHeaderSize <= Sections[i].VirtualAddress);
    @ ensures image_hdr_loaded{Pre, Post} (
    @           AlignedDest,
    @           (char *) Context->FileBuffer,
    @           LoadedHeaderSize
    @           );
  */
  if (Sections[0].VirtualAddress != 0 && PcdGetBool (PcdImageLoaderLoadHeader)) {
    /*@ requires Context->TeStrippedOffset <= Context->SizeOfHeaders;
      @ assigns LoadedHeaderSize;
      @ ensures LoadedHeaderSize == image_hdr_raw_size (Context->SizeOfHeaders, Context->TeStrippedOffset);
      @ ensures (\forall integer i; 0 <= i < Context->NumberOfSections ==>
      @           LoadedHeaderSize <= Sections[i].VirtualAddress);
    */
    LoadedHeaderSize = (Context->SizeOfHeaders - Context->TeStrippedOffset);

    /*@ requires LoadedHeaderSize <= AlignedSize;
      @ assigns ((char *) Destination)[AlignOffset .. AlignOffset + image_hdr_raw_size (Context->SizeOfHeaders, Context->TeStrippedOffset) - 1];
      @ ensures char_equals{Post, Pre} (
      @           AlignedDest,
      @           (char *) Context->FileBuffer,
      @           LoadedHeaderSize
      @           );
    */
    CopyMem (AlignedDest, Context->FileBuffer, LoadedHeaderSize);
  } else {
    /*@ assigns LoadedHeaderSize;
      @ ensures LoadedHeaderSize == 0;
      @ ensures (\forall integer i; 0 <= i < Context->NumberOfSections ==>
      @           LoadedHeaderSize <= Sections[i].VirtualAddress);
    */
    LoadedHeaderSize = 0;
  }

  /*@ assigns ((char *) Destination)[AlignOffset + LoadedHeaderSize .. DestinationSize - 1];
    @ ensures char_equals{Old, Post} (
    @           AlignedDest,
    @           AlignedDest,
    @           LoadedHeaderSize
    @           );
    @ ensures image_sections_loaded{Pre, Post} (
    @           AlignedDest,
    @           AlignedSize,
    @           (char *) Context->FileBuffer,
    @           Sections,
    @           Context->NumberOfSections,
    @           LoadedHeaderSize,
    @           Context->TeStrippedOffset
    @           );
  */
  InternalLoadSections (
    Context,
    LoadedHeaderSize,
    AlignedDest,
    AlignedSize
    );

  /*@ assert image_hdr_loaded{Pre, Here} (
    @          AlignedDest,
    @          (char *) Context->FileBuffer,
    @          LoadedHeaderSize
    @          );
  */

  /*@ assert \let Address             = pointer_to_address (Destination);
    @        \let AlignOffset         = align_up (Address, Context->SectionAlignment) - Address;
    @        \let AlignedSize         = (UINT32) (DestinationSize - AlignOffset);
    @        \let AlignedDest         = (char *) Destination + AlignOffset;
    @        \let Sections            = image_context_get_sections (Context);
    @        \let LoadedHeaderSize = (UINT32) image_context_get_loaded_hdr_raw_size (Context);
    @        image_loaded{Pre, Here} (
    @          AlignedDest,
    @          AlignedSize,
    @          (char *) Context->FileBuffer,
    @          Sections,
    @          Context->NumberOfSections,
    @          LoadedHeaderSize,
    @          Context->TeStrippedOffset
    @          );
  */

  /*@ assigns Context->ImageBuffer;
    @ ensures Context->ImageBuffer == AlignedDest;
    @ ensures image_context_ImageBuffer_sane (Context);
  */
  Context->ImageBuffer = AlignedDest;

  /*@ assigns \nothing;
    @ ensures image_reloc_dir_mem_valid ((char *) Context->ImageBuffer, Context->SizeOfImage, Context->RelocDirRva, Context->RelocDirSize);
  */
  //@ ghost AvFlagImage (Context);
  //
  // If debugging is enabled, force-load its contents into the memory space.
  //
  //@ assigns \nothing;
  if (PcdGetBool (PcdImageLoaderSupportDebug)) {
    PeCoffLoaderLoadCodeView (Context);
  }

  return RETURN_SUCCESS;
}

/*@ ghost
  @/@ assigns *(EFI_IMAGE_BASE_RELOCATION_BLOCK *) ((char *) Image + RelocDirRva);
  @ @
  @ @ behavior reloc_valid:
  @ @   assumes image_reloc_dir_correct ((char *) Image, ImageSize, RelocDirRva, RelocDirSize);
  @ @   ensures !image_reloc_dir_correct ((char *) Image, ImageSize, RelocDirRva, RelocDirSize);
  @ @
  @ @ behavior reloc_nvalid:
  @ @   assumes !image_reloc_dir_correct ((char *) Image, ImageSize, RelocDirRva, RelocDirSize);
  @ @   assigns \nothing;
  @ @   ensures !image_reloc_dir_correct ((char *) Image, ImageSize, RelocDirRva, RelocDirSize);
  @ @
  @ @ disjoint behaviors;
  @ @ complete behaviors;
  @/
  @ VOID
  @ AvInvalidateRelocDir (
  @   IN OUT VOID    *Image,
  @   IN     UINT32  ImageSize,
  @   IN     UINT32  RelocDirRva,
  @   IN     UINT32  RelocDirSize
  @   );
*/

//
// FIXME: Provide a Runtime version of this API as well.
//
VOID
PeCoffDiscardSections (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  )
{
  CONST EFI_IMAGE_SECTION_HEADER *Sections;
  UINT32                         SectIndex;
  BOOLEAN                        Discardable;

  ASSERT (Context != NULL);

  /*@ assigns *(EFI_IMAGE_BASE_RELOCATION_BLOCK *) ((char *) Context->ImageBuffer + Context->RelocDirRva);
    @ ensures !image_reloc_dir_correct ((char *) Context->ImageBuffer, \at(Context->SizeOfImage, Pre), \at(Context->RelocDirRva, Pre), \at(Context->RelocDirSize, Pre));
  */
  //@ ghost AvInvalidateRelocDir (Context->ImageBuffer, Context->SizeOfImage, Context->RelocDirRva, Context->RelocDirSize);
  //
  // By the PE/COFF specification, the .reloc section is supposed to be
  // discardable, so we must assume it is no longer valid.
  //
  /*@ assigns Context->RelocDirRva;
    @ ensures Context->RelocDirRva == 0;
  */
  Context->RelocDirRva = 0;

  /*@ assigns Context->RelocDirSize;
    @ ensures Context->RelocDirSize == 0;
  */
  Context->RelocDirSize = 0;

  /*@ assigns Sections;
    @ ensures Sections == image_context_get_sections (Context);
    @ ensures \valid(Sections + (0 .. Context->NumberOfSections - 1));
  */
  Sections = (CONST EFI_IMAGE_SECTION_HEADER *) (CONST VOID *) (
               (CONST CHAR8 *) Context->FileBuffer + Context->SectionsOffset
               );
  //
  // Discard all Image Sections that are flagged as optional.
  //
  /*@ loop assigns ((char *) Context->ImageBuffer)[Sections[0].VirtualAddress .. Sections[Context->NumberOfSections - 1].VirtualAddress + Sections[Context->NumberOfSections - 1].VirtualSize];
    @ loop invariant 0 <= SectIndex <= Context->NumberOfSections;
    @ loop invariant \forall integer i; 0 <= i < Context->NumberOfSections ==>
    @                  \forall integer j; 0 <= j < i ==>
    @                    Sections[j].VirtualAddress <= Sections[i].VirtualAddress &&
    @                    Sections[j].VirtualAddress + Sections[j].VirtualSize <= Sections[i].VirtualAddress;
    @ loop invariant \forall integer i; 0 <= i < SectIndex ==>
    @                  (image_sect_discardable (Sections + i) ==>
    @                    char_zero{Here} (
    @                      (char *) Context->ImageBuffer + Sections[i].VirtualAddress,
    @                      Sections[i].VirtualSize
    @                      ));
    @ loop invariant \forall integer i; 0 <= i < SectIndex ==>
    @                  (!image_sect_discardable (Sections + i) ==>
    @                    char_equals{Here, Pre} (
    @                      (char *) Context->ImageBuffer + Sections[i].VirtualAddress,
    @                      (char *) Context->ImageBuffer + Sections[i].VirtualAddress,
    @                      Sections[i].VirtualSize
    @                      ));
    @ loop invariant \forall integer i; SectIndex <= i < Context->NumberOfSections ==>
    @                   char_equals{Here, Pre} (
    @                     (char *) Context->ImageBuffer + Sections[i].VirtualAddress,
    @                     (char *) Context->ImageBuffer + Sections[i].VirtualAddress,
    @                     Sections[i].VirtualSize
    @                     );
    @ loop variant Context->NumberOfSections - SectIndex;
  */
  for (SectIndex = 0; SectIndex < Context->NumberOfSections; ++SectIndex) {
    /*@ assigns Discardable;
      @ ensures Discardable <==> image_sect_discardable (Sections + SectIndex);
    */
    Discardable = (Sections[SectIndex].Characteristics & EFI_IMAGE_SCN_MEM_DISCARDABLE) != 0;

    /*@ assigns ((char *) Context->ImageBuffer)[Sections[SectIndex].VirtualAddress .. Sections[SectIndex].VirtualAddress + Sections[SectIndex].VirtualSize - 1];
      @ ensures image_sect_discardable (Sections + SectIndex) ==>
      @           char_zero{Post} (
      @             (char *) Context->ImageBuffer + Sections[SectIndex].VirtualAddress,
      @             Sections[SectIndex].VirtualSize
      @             );
      @ ensures !image_sect_discardable (Sections + SectIndex) ==>
      @           char_equals{Post, Old} (
      @             (char *) Context->ImageBuffer + Sections[SectIndex].VirtualAddress,
      @             (char *) Context->ImageBuffer + Sections[SectIndex].VirtualAddress,
      @             Sections[SectIndex].VirtualSize
      @             );
      @ ensures \forall integer i; 0 <= i < SectIndex ==>
      @           char_equals{Post, Old} (
      @             (char *) Context->ImageBuffer + Sections[i].VirtualAddress,
      @             (char *) Context->ImageBuffer + Sections[i].VirtualAddress,
      @             Sections[i].VirtualSize
      @             );
      @ ensures \forall integer i; SectIndex < i < Context->NumberOfSections ==>
      @           char_equals{Post, Old} (
      @             (char *) Context->ImageBuffer + Sections[i].VirtualAddress,
      @             (char *) Context->ImageBuffer + Sections[i].VirtualAddress,
      @             Sections[i].VirtualSize
      @             );
    */
    if (Discardable) {
      //@ assert image_sect_discardable (Sections + SectIndex);
      /*@ assigns ((char *) Context->ImageBuffer)[Sections[SectIndex].VirtualAddress .. Sections[SectIndex].VirtualAddress + Sections[SectIndex].VirtualSize - 1];
        @ ensures char_zero (
        @           (char *) Context->ImageBuffer + Sections[SectIndex].VirtualAddress,
        @           Sections[SectIndex].VirtualSize
        @           );
        @ ensures \forall integer i; 0 <= i < SectIndex ==>
        @           char_equals{Post, Old} (
        @             (char *) Context->ImageBuffer + Sections[i].VirtualAddress,
        @             (char *) Context->ImageBuffer + Sections[i].VirtualAddress,
        @             Sections[i].VirtualSize
        @             );
        @ ensures \forall integer i; SectIndex < i < Context->NumberOfSections  ==>
        @           char_equals{Post, Old} (
        @             (char *) Context->ImageBuffer + Sections[i].VirtualAddress,
        @             (char *) Context->ImageBuffer + Sections[i].VirtualAddress,
        @             Sections[i].VirtualSize
        @             );
      */
      ZeroMem (
        (CHAR8 *) Context->ImageBuffer + Sections[SectIndex].VirtualAddress,
        Sections[SectIndex].VirtualSize
        );
    }

    /*@ assigns \nothing;
      @ ensures \forall integer i; 0 <= i <= SectIndex ==>
      @           (image_sect_discardable (Sections + i) ==>
      @             char_zero{Here} (
      @               (char *) Context->ImageBuffer + Sections[i].VirtualAddress,
      @               Sections[i].VirtualSize
      @               ));
    */
    {
      /*@ assert \forall integer i; 0 <= i <= SectIndex && i == SectIndex ==>
        @          (image_sect_discardable (Sections + i) ==>
        @            char_zero{Here} (
        @              (char *) Context->ImageBuffer + Sections[i].VirtualAddress,
        @              Sections[i].VirtualSize
        @              ));
      */

      /*@ assert \forall integer i; 0 <= i <= SectIndex ==>
        @          (image_sect_discardable (Sections + i) ==>
        @            char_zero{Here} (
        @              (char *) Context->ImageBuffer + Sections[i].VirtualAddress,
        @              Sections[i].VirtualSize
        @              ));
      */
    }

    /*@ assigns \nothing;
      @ ensures \forall integer i; 0 <= i <= SectIndex ==>
      @           (!image_sect_discardable (Sections + i) ==>
      @             char_equals{Here, Pre} (
      @               (char *) Context->ImageBuffer + Sections[i].VirtualAddress,
      @               (char *) Context->ImageBuffer + Sections[i].VirtualAddress,
      @               Sections[i].VirtualSize
      @               ));
    */
    {
      /*@ assert \forall integer i; 0 <= i <= SectIndex && i == SectIndex ==>
        @          (!image_sect_discardable (Sections + SectIndex) ==>
        @            char_equals{Here, Pre} (
        @              (char *) Context->ImageBuffer + Sections[SectIndex].VirtualAddress,
        @              (char *) Context->ImageBuffer + Sections[SectIndex].VirtualAddress,
        @              Sections[SectIndex].VirtualSize
        @              ));
      */

      /*@ assert \forall integer i; 0 <= i <= SectIndex ==>
        @          (!image_sect_discardable (Sections + i) ==>
        @            char_equals{Here, Pre} (
        @              (char *) Context->ImageBuffer + Sections[i].VirtualAddress,
        @              (char *) Context->ImageBuffer + Sections[i].VirtualAddress,
        @              Sections[i].VirtualSize
        @              ));
      */
    }

    /*@ assert \forall integer i; SectIndex < i < Context->NumberOfSections ==>
      @          char_equals{Here, Pre} (
      @            (char *) Context->ImageBuffer + Sections[i].VirtualAddress,
      @            (char *) Context->ImageBuffer + Sections[i].VirtualAddress,
      @            Sections[i].VirtualSize
      @            );
    */
  }
}
