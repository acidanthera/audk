/** @file
  Implements APIs to verify PE/COFF Images for further processing.

  Portions copyright (c) 2006 - 2019, Intel Corporation. All rights reserved.<BR>
  Portions copyright (c) 2008 - 2010, Apple Inc. All rights reserved.<BR>
  Portions Copyright (c) 2020, Hewlett Packard Enterprise Development LP. All rights reserved.<BR>
  Copyright (c) 2020, Marvin Häuser. All rights reserved.<BR>
  Copyright (c) 2020, Vitaly Cheptsov. All rights reserved.<BR>
  Copyright (c) 2020, ISP RAS. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-3-Clause
**/

/** @file
  Base PE/COFF loader supports loading any PE32/PE32+ or TE image, but
  only supports relocating IA32, x64, IPF, and EBC images.

  Caution: This file requires additional review when modified.
  This library will have external input - PE/COFF image.
  This external input must be validated carefully to avoid security issue like
  buffer overflow, integer overflow.

  PeCoffInitializeContext() routine will do basic check for whole PE/COFF image.

  Copyright (c) 2006 - 2019, Intel Corporation. All rights reserved.<BR>
  Portions copyright (c) 2008 - 2009, Apple Inc. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-2-Clause-Patent

**/
#include <Uefi.h>
#include <Library/DebugLib.h>
#include "BasePeCoffLibInternals.h"

#include "PeCoffInit.h"
#include "PeCoffDebug.h"

//
// FIXME: Provide an API to destruct the context.
//

/*@ ghost
  @ /@ requires n == sizeof (PE_COFF_LOADER_IMAGE_CONTEXT) &&
  @  @          \valid(dest);
  @  @ assigns *dest \from val;
  @  @ allocates \nothing;
  @  @ ensures val == 0 ==>
  @  @           dest->ExeHdrOffset == 0 &&
  @  @           dest->SizeOfImageDebugAdd == 0 &&
  @  @           dest->TeStrippedOffset == 0 &&
  @  @           dest->RelocDirRva == 0 &&
  @  @           dest->RelocDirSize == 0;
  @  @
  @  @/
  @ extern void *memset_PE_COFF_LOADER_IMAGE_CONTEXT (PE_COFF_LOADER_IMAGE_CONTEXT *dest, int val, size_t n);
*/

/*@ ghost
  @ /@ requires \typeof(FileBuffer) <: \type(char *);
  @  @ requires \valid((char *) FileBuffer + (0 .. FileSize - 1));
  @  @ assigns \nothing;
  @  @ ensures image_signature_dos ((char *) FileBuffer, FileSize) ==>
  @  @           \valid ((EFI_IMAGE_DOS_HEADER *) ((char *) FileBuffer + 0));
  @  @ ensures \let ExeHdrOffset = image_exe_hdr_offset ((char *) FileBuffer, FileSize);
  @  @         image_te_file_hdrs_validity ((char *) FileBuffer, FileSize) &&
  @  @         image_pe32_file_hdrs_validity ((char *) FileBuffer, ExeHdrOffset, FileSize) &&
  @  @         image_pe32plus_file_hdrs_validity ((char *) FileBuffer, ExeHdrOffset, FileSize);
  @  @/
  @ VOID AvFlagRawFile (CONST VOID *FileBuffer, UINT32 FileSize);
*/

/**
  Verify the Image Section Headers.

  The first section must be the beginning of the virtual address space or be
  contiguous to the aligned Image Headers.
  Sections must be disjunct and, in strict mode, contiguous in virtual space.
  Section data must be in file bounds.

  @param[in]  Context       The context describing the Image. Must have been
                            initialised by PeCoffInitializeContext().
  @param[in]  FileSize      The size, in bytes, of Context->FileBuffer.
  @param[out] StartAddress  On output, the RVA of the first Image Section.
  @param[out] EndAddress    On output, the size of the virtual address space.

  @retval RETURN_SUCCESS  The Image Section Headers are correct.
  @retval other           The Image section Headers are malformed.
**/
/*@ requires \valid(Context);
  @ requires \typeof(Context->FileBuffer) <: \type(char *);
  @ requires 0 <= image_hdr_raw_size (Context->SizeOfHeaders, Context->TeStrippedOffset);
  @ requires Context->ImageType != ImageTypeTe ==> Context->TeStrippedOffset == 0;
  @ requires is_pow2_32 (Context->SectionAlignment);
  @
  @ requires \let Sections = image_context_get_sections (Context);
  @          \valid(Sections + (0 .. Context->NumberOfSections - 1));
  @ requires 0 < Context->NumberOfSections;
  @ requires 0 < image_hdr_virtual_size (Context->SizeOfHeaders, Context->SectionAlignment);
  @
  @ requires \valid(StartAddress);
  @ requires \valid(EndAddress);
  @
  @ assigns *StartAddress, *EndAddress;
  @
  @ behavior sects_valid:
  @   assumes \let Sections = image_context_get_sections (Context);
  @           image_sects_sane (Sections, Context->NumberOfSections, Context->SizeOfHeaders, Context->SectionAlignment, Context->TeStrippedOffset, FileSize, Context->ImageType);
  @   ensures \result == RETURN_SUCCESS;
  @   ensures \let Sections = image_context_get_sections (Context);
  @           *StartAddress == image_context_get_loaded_hdr_virtual_size (Context) &&
  @           *EndAddress   == (!PcdGetBool (PcdImageLoaderTolerantLoad) ?
  @             align_up (image_sect_top (&Sections[Context->NumberOfSections - 1]), Context->SectionAlignment) :
  @             image_sect_top (&Sections[Context->NumberOfSections - 1])) &&
  @           (\forall integer i; 0 <= i < Context->NumberOfSections ==>
  @             image_sect_top (Sections + i) <= *EndAddress);
  @
  @ behavior sects_nvalid:
  @   assumes \let Sections = image_context_get_sections (Context);
  @           !image_sects_sane (Sections, Context->NumberOfSections, Context->SizeOfHeaders, Context->SectionAlignment, Context->TeStrippedOffset, FileSize, Context->ImageType);
  @   ensures \result != RETURN_SUCCESS;
  @
  @ disjoint behaviors;
  @ complete behaviors;
*/
STATIC
RETURN_STATUS
InternalVerifySections (
  IN  CONST PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  IN  UINT32                       FileSize,
  OUT UINT32                       *StartAddress,
  OUT UINT32                       *EndAddress
  )
{
  BOOLEAN                        Result;
  UINT32                         NextSectRva;
  UINT32                         SectRawEnd;
  UINT16                         SectIndex;
  CONST EFI_IMAGE_SECTION_HEADER *Sections;

  ASSERT (Context != NULL);
  ASSERT (Context->SizeOfHeaders >= Context->TeStrippedOffset);
  ASSERT (IS_POW2 (Context->SectionAlignment));
  ASSERT (Context->NumberOfSections > 0);
  ASSERT (StartAddress != NULL);
  ASSERT (EndAddress != NULL);

  /*@ assigns Sections;
    @ ensures Sections == image_context_get_sections (Context);
    @ ensures \valid(Sections + (0 .. Context->NumberOfSections - 1));
  */
  Sections = (CONST EFI_IMAGE_SECTION_HEADER *) (CONST VOID *) (
               (CONST CHAR8 *) Context->FileBuffer + Context->SectionsOffset
               );
  //
  // The first Image Section must begin the Image memory space, or it must be
  // adjacent to the Image Headers.
  //
  /*@ assigns Result, NextSectRva, Context->TeStrippedOffset;
    @ ensures NextSectRva == image_sect_correct_address (Sections, 0, Context->SizeOfHeaders, Context->SectionAlignment) &&
    @         (Context->ImageType == ImageTypeTe ==>
    @           Sections[0].VirtualAddress != 0);
  */
  if (Sections[0].VirtualAddress == 0) {
    /*@ assigns \nothing;
      @ ensures Context->ImageType == ImageTypeTe ==>
      @           Sections[0].VirtualAddress != 0;
    */
    if (Context->ImageType == ImageTypeTe) {
      ASSERT (FALSE);
      /*@ assert !(Context->ImageType == ImageTypeTe ==>
        @          Sections[0].VirtualAddress != 0);
      */
      //@ assert !image_sects_sane (Sections, Context->NumberOfSections, Context->SizeOfHeaders, Context->SectionAlignment, Context->TeStrippedOffset, FileSize, Context->ImageType);
      return RETURN_UNSUPPORTED;
    }

    /*@ assigns NextSectRva;
      @ ensures NextSectRva == 0;
    */
    NextSectRva = 0;
  } else {
    /*@ assigns Result, NextSectRva;
      @ ensures NextSectRva == image_sect_correct_address (Sections, 0, Context->SizeOfHeaders, Context->SectionAlignment);
    */
    if (!PcdGetBool (PcdImageLoaderTolerantLoad)) {
      /*@ assigns Result, NextSectRva;
        @ ensures !Result <==> NextSectRva == align_up (Context->SizeOfHeaders, Context->SectionAlignment);
        @ ensures Result  <==> align_up (Context->SizeOfHeaders, Context->SectionAlignment) > MAX_UINT32;
      */
      Result = BaseOverflowAlignUpU32 (
                Sections[0].VirtualAddress,
                Context->SectionAlignment,
                &NextSectRva
                );

      /*@ assigns \nothing;
        @ ensures NextSectRva == image_sect_correct_address (Sections, 0, Context->SizeOfHeaders, Context->SectionAlignment);
      */
      if (Result) {
        ASSERT (FALSE);
        //@ assert align_up (Context->SizeOfHeaders, Context->SectionAlignment) > MAX_UINT32;
        /*@ assert 0 < Context->NumberOfSections &&
          @        Sections[0].VirtualAddress != image_context_get_loaded_hdr_virtual_size (Context);
        */
        /*@ assert !(0 < Context->NumberOfSections ==>
          @          Sections[0].VirtualAddress == image_context_get_loaded_hdr_virtual_size (Context));
        */
        //@ assert !image_sects_correct_addresses (Sections, Context->NumberOfSections, Context->SizeOfHeaders, Context->SectionAlignment);
        //@ assert !image_sects_sane (Sections, Context->NumberOfSections, Context->SizeOfHeaders, Context->SectionAlignment, Context->TeStrippedOffset, FileSize, Context->ImageType);
        return RETURN_UNSUPPORTED;
      }
    } else {
      /*@ assigns NextSectRva;
        @ ensures NextSectRva == Context->SizeOfHeaders;
      */
      NextSectRva = Context->SizeOfHeaders;
    }
  }

  /*@ assigns *StartAddress;
    @ ensures *StartAddress == image_context_get_loaded_hdr_virtual_size (Context);
  */
  *StartAddress = NextSectRva;
  //
  // Ensure all Image Sections are valid.
  //
  /*@ loop assigns SectIndex, SectRawEnd, NextSectRva, Result;
    @
    @ loop invariant 0 <= SectIndex <= Context->NumberOfSections;
    @
    @ loop invariant image_sects_in_file_bounds (Sections, SectIndex, Context->TeStrippedOffset, FileSize);
    @ loop invariant !PcdGetBool (PcdImageLoaderTolerantLoad) ==>
    @                  image_sects_correct_addresses (Sections, SectIndex, Context->SizeOfHeaders, Context->SectionAlignment);
    @ loop invariant image_sects_disjunct_sorted (Sections, SectIndex, Context->SizeOfHeaders, Context->SectionAlignment);
    @
    @ loop invariant image_loaded_hdr_virtual_size (Sections, Context->SizeOfHeaders, Context->SectionAlignment) <= NextSectRva;
    @ loop invariant !PcdGetBool (PcdImageLoaderTolerantLoad) ==>
    @                  NextSectRva == image_sect_correct_address (Sections, SectIndex, Context->SizeOfHeaders, Context->SectionAlignment);
    @
    @ loop invariant 0 == SectIndex ==>
    @                  NextSectRva == image_context_get_loaded_hdr_virtual_size (Context);
    @ loop invariant PcdGetBool (PcdImageLoaderTolerantLoad) ==>
    @                  0 < SectIndex ==>
    @                    NextSectRva == image_sect_top (Sections + SectIndex - 1);
    @
    @ loop invariant \forall integer i; 0 <= i < SectIndex ==>
    @                   image_sect_top (Sections + i) <= NextSectRva;
    @
    @ loop variant Context->NumberOfSections - SectIndex;
  */
  DEBUG ((DEBUG_INFO, "Align: %u\n", Context->SectionAlignment));
  for (SectIndex = 0; SectIndex < Context->NumberOfSections; ++SectIndex) {
    DEBUG ((DEBUG_INFO, "%a: %x || [%x, %x)", Sections[SectIndex].Name, NextSectRva, Sections[SectIndex].VirtualAddress, Sections[SectIndex].VirtualAddress + Sections[SectIndex].VirtualSize));
    //
    // Ensure the Image Section are disjunct (relaxed) or adjacent (strict).
    //
    /*@ requires !PcdGetBool (PcdImageLoaderTolerantLoad) ==>
      @            NextSectRva == image_sect_correct_address (Sections, SectIndex, Context->SizeOfHeaders, Context->SectionAlignment);
      @ assigns \nothing;
      @ ensures !PcdGetBool (PcdImageLoaderTolerantLoad) ==>
      @           Sections[SectIndex].VirtualAddress == image_sect_correct_address (Sections, SectIndex, Context->SizeOfHeaders, Context->SectionAlignment);
      @ ensures !PcdGetBool (PcdImageLoaderTolerantLoad) && 0 < SectIndex ==>
      @           image_sect_top (Sections + SectIndex - 1) <= NextSectRva;
      @ ensures !PcdGetBool (PcdImageLoaderTolerantLoad) ==>
      @           NextSectRva <= Sections[SectIndex].VirtualAddress;
      @ ensures !PcdGetBool (PcdImageLoaderTolerantLoad) ==>
      @           image_sect_disjunct_sorted (Sections, SectIndex);
    */
    if (!PcdGetBool (PcdImageLoaderTolerantLoad) && Sections[SectIndex].VirtualAddress != NextSectRva) {
      ASSERT (FALSE);
      //@ assert !image_sects_correct_addresses (Sections, Context->NumberOfSections, Context->SizeOfHeaders, Context->SectionAlignment);
      //@ assert !image_sects_sane (Sections, Context->NumberOfSections, Context->SizeOfHeaders, Context->SectionAlignment, Context->TeStrippedOffset, FileSize, Context->ImageType);
      return RETURN_UNSUPPORTED;
    }

    /*@ assigns \nothing;
      @ ensures PcdGetBool (PcdImageLoaderTolerantLoad) && 0 < SectIndex ==>
      @           image_sect_top (Sections + SectIndex - 1) <= Sections[SectIndex].VirtualAddress;
      @ ensures PcdGetBool (PcdImageLoaderTolerantLoad) ==>
      @           image_sect_disjunct_sorted (Sections, SectIndex);
      @ ensures PcdGetBool (PcdImageLoaderTolerantLoad) ==>
      @           NextSectRva <= Sections[SectIndex].VirtualAddress;
    */
    if (PcdGetBool (PcdImageLoaderTolerantLoad) && Sections[SectIndex].VirtualAddress < NextSectRva) {
      ASSERT (FALSE);
      //@ assert !image_sects_disjunct_sorted (Sections, Context->NumberOfSections, Context->SizeOfHeaders, Context->SectionAlignment);
      //@ assert !image_sects_sane (Sections, Context->NumberOfSections, Context->SizeOfHeaders, Context->SectionAlignment, Context->TeStrippedOffset, FileSize, Context->ImageType);
      return RETURN_UNSUPPORTED;
    }

    //@ assert NextSectRva <= Sections[SectIndex].VirtualAddress;

    /*@ assert \forall integer i; 0 <= i <= SectIndex && i != SectIndex ==>
      @          image_sect_disjunct_sorted (Sections, i);
    */

    /*@ assert \forall integer i; 0 <= i <= SectIndex && i == SectIndex ==>
      @          image_sect_disjunct_sorted (Sections, i);
    */

    /*@ assert ((\forall integer i; 0 <= i <= SectIndex && i != SectIndex ==>
      @           image_sect_disjunct_sorted (Sections, i)) &&
      @         (\forall integer i; 0 <= i <= SectIndex && i == SectIndex ==>
      @           image_sect_disjunct_sorted (Sections, i))) ==>
      @         (\forall integer i; 0 <= i <= SectIndex ==>
      @           image_sect_disjunct_sorted (Sections, i));
    */

    /*@ assert (\forall integer i; 0 <= i <= SectIndex ==>
      @          image_sect_disjunct_sorted (Sections, i));
    */
    //
    // Ensure Image Sections with data are in bounds.
    //
    /*@ assigns Result, SectRawEnd;
      @ ensures 0 < Sections[SectIndex].SizeOfRawData ==>
      @           Context->TeStrippedOffset <= Sections[SectIndex].PointerToRawData &&
      @           Sections[SectIndex].PointerToRawData + Sections[SectIndex].SizeOfRawData <= MAX_UINT32 &&
      @           (Sections[SectIndex].PointerToRawData - Context->TeStrippedOffset) + Sections[SectIndex].SizeOfRawData <= FileSize;
    */
    if (Sections[SectIndex].SizeOfRawData > 0) {
      /*@ assigns \nothing;
        @ ensures Context->TeStrippedOffset <= Sections[SectIndex].PointerToRawData;
      */
      if (Context->TeStrippedOffset > Sections[SectIndex].PointerToRawData) {
        ASSERT (FALSE);
        //@ assert !image_sects_in_file_bounds (Sections, Context->NumberOfSections, Context->TeStrippedOffset, FileSize);
        //@ assert !image_sects_sane (Sections, Context->NumberOfSections, Context->SizeOfHeaders, Context->SectionAlignment, Context->TeStrippedOffset, FileSize, Context->ImageType);
        return RETURN_UNSUPPORTED;
      }

      /*@ assigns Result, SectRawEnd;
        @ ensures !Result <==> SectRawEnd == Sections[SectIndex].PointerToRawData + Sections[SectIndex].SizeOfRawData;
        @ ensures Result  <==> Sections[SectIndex].PointerToRawData + Sections[SectIndex].SizeOfRawData > MAX_UINT32;
      */
      Result = BaseOverflowAddU32 (
                 Sections[SectIndex].PointerToRawData,
                 Sections[SectIndex].SizeOfRawData,
                 &SectRawEnd
                 );

      /*@ assigns \nothing;
        @ ensures SectRawEnd == Sections[SectIndex].PointerToRawData + Sections[SectIndex].SizeOfRawData;
      */
      if (Result) {
        ASSERT (FALSE);
        //@ assert Sections[SectIndex].SizeOfRawData > 0;
        /*@ assert \exists integer i; 0 <= i < Context->NumberOfSections &&
          @          (0 < Sections[i].SizeOfRawData ==>
          @            Sections[i].PointerToRawData + Sections[i].SizeOfRawData > MAX_UINT32);
        */
        /*@ assert !(\forall integer i; 0 <= i < Context->NumberOfSections ==>
          @          0 < Sections[i].SizeOfRawData ==>
          @            Sections[i].PointerToRawData + Sections[i].SizeOfRawData <= MAX_UINT32);
        */
        //@ assert !image_sects_in_file_bounds (Sections, Context->NumberOfSections, Context->TeStrippedOffset, FileSize);
        //@ assert !image_sects_sane (Sections, Context->NumberOfSections, Context->SizeOfHeaders, Context->SectionAlignment, Context->TeStrippedOffset, FileSize, Context->ImageType);
        return RETURN_UNSUPPORTED;
      }

      /*@ requires Context->TeStrippedOffset <= SectRawEnd;
        @ assigns \nothing;
        @ ensures (Sections[SectIndex].PointerToRawData - Context->TeStrippedOffset) + Sections[SectIndex].SizeOfRawData <= FileSize;
      */
      if ((SectRawEnd - Context->TeStrippedOffset) > FileSize) {
        ASSERT (FALSE);
        //@ assert !image_sects_in_file_bounds (Sections, Context->NumberOfSections, Context->TeStrippedOffset, FileSize);
        //@ assert !image_sects_sane (Sections, Context->NumberOfSections, Context->SizeOfHeaders, Context->SectionAlignment, Context->TeStrippedOffset, FileSize, Context->ImageType);
        return RETURN_UNSUPPORTED;
      }
    }
    //
    // Determine the end of the current Image Section.
    //
    /*@ assigns Result, NextSectRva;
      @ ensures Result <==> Sections[SectIndex].VirtualAddress + Sections[SectIndex].VirtualSize > MAX_UINT32;
      @ ensures !Result <==> NextSectRva == Sections[SectIndex].VirtualAddress + Sections[SectIndex].VirtualSize;
      @
    */
    Result = BaseOverflowAddU32 (
              Sections[SectIndex].VirtualAddress,
              Sections[SectIndex].VirtualSize,
              &NextSectRva
              );
    DEBUG ((DEBUG_INFO, "- %u\n", NextSectRva));

    /*@ assigns \nothing;
      @ ensures NextSectRva == image_sect_top (Sections + SectIndex);
      @ ensures image_loaded_hdr_virtual_size (Sections, Context->SizeOfHeaders, Context->SectionAlignment) <= \old(NextSectRva) <= NextSectRva;
    */
    if (Result) {
      ASSERT (FALSE);
      //@ assert image_sect_top (Sections + SectIndex) > MAX_UINT32;
      //@ assert align_up (image_sect_top (Sections + SectIndex), Context->SectionAlignment) > MAX_UINT32;
      /*@ assert SectIndex < Context->NumberOfSections - 1 ==>
        @          Sections[SectIndex + 1].VirtualAddress != image_sect_correct_address (Sections, SectIndex + 1, Context->SizeOfHeaders, Context->SectionAlignment);
      */
      /*@ assert SectIndex == Context->NumberOfSections - 1 ==>
        @          !(image_sect_top (Sections + Context->NumberOfSections - 1) <= MAX_UINT32);
      */
      //@ assert !image_sects_sane (Sections, Context->NumberOfSections, Context->SizeOfHeaders, Context->SectionAlignment, Context->TeStrippedOffset, FileSize, Context->ImageType);
      return RETURN_UNSUPPORTED;
    }
    //
    // SectionSize does not need to be aligned, so align the result.
    //
    /*@ assigns Result, NextSectRva;
      @ ensures !PcdGetBool (PcdImageLoaderTolerantLoad) ==>
      @           NextSectRva == image_sect_correct_address (Sections, SectIndex + 1, Context->SizeOfHeaders, Context->SectionAlignment);
      @ ensures PcdGetBool (PcdImageLoaderTolerantLoad) ==>
      @           NextSectRva == image_sect_top (Sections + SectIndex);
      @ ensures image_loaded_hdr_virtual_size (Sections, Context->SizeOfHeaders, Context->SectionAlignment) <= \old(NextSectRva) <= NextSectRva;
    */
    if (!PcdGetBool (PcdImageLoaderTolerantLoad)) {
      /*@ requires NextSectRva == image_sect_top (Sections + SectIndex);
        @ assigns Result, NextSectRva;
        @ ensures !Result <==>
        @           NextSectRva == align_up (image_sect_top (Sections + SectIndex), Context->SectionAlignment);
        @ ensures Result <==>
        @           align_up (image_sect_top (Sections + SectIndex), Context->SectionAlignment) > MAX_UINT32;
        @ ensures !Result ==>
        @           image_loaded_hdr_virtual_size (Sections, Context->SizeOfHeaders, Context->SectionAlignment) <= \old(NextSectRva) <= NextSectRva;
      */
      Result = BaseOverflowAlignUpU32 (
                NextSectRva,
                Context->SectionAlignment,
                &NextSectRva
                );

      /*@ assigns \nothing;
        @ ensures NextSectRva == image_sect_correct_address (Sections, SectIndex + 1, Context->SizeOfHeaders, Context->SectionAlignment);
        @ ensures image_loaded_hdr_virtual_size (Sections, Context->SizeOfHeaders, Context->SectionAlignment) <= \old(NextSectRva) <= NextSectRva;
      */
      if (Result) {
        ASSERT (FALSE);
        //@ assert align_up (image_sect_top (Sections + SectIndex), Context->SectionAlignment) > MAX_UINT32;
        /*@ assert SectIndex < Context->NumberOfSections - 1 ==>
          @          image_sect_correct_address (Sections, SectIndex + 1, Context->SizeOfHeaders, Context->SectionAlignment) > MAX_UINT32;
        */
        /*@ assert SectIndex < Context->NumberOfSections - 1 ==>
          @          Sections[SectIndex + 1].VirtualAddress != image_sect_correct_address (Sections, SectIndex + 1, Context->SizeOfHeaders, Context->SectionAlignment);
        */
        /*@ assert SectIndex < Context->NumberOfSections - 1 ==>
          @          !(\forall integer i; 0 <= i < Context->NumberOfSections ==>
          @            Sections[i].VirtualAddress == image_sect_correct_address (Sections, i, Context->SizeOfHeaders, Context->SectionAlignment));
        */
        /*@ assert SectIndex < Context->NumberOfSections - 1 ==>
          @          !image_sects_correct_addresses (Sections, Context->NumberOfSections, Context->SizeOfHeaders, Context->SectionAlignment);
        */
        /*@ assert SectIndex == Context->NumberOfSections - 1 ==>
          @          !(align_up (image_sect_top (Sections + Context->NumberOfSections - 1), Context->SectionAlignment) <= MAX_UINT32);
        */
        //@ assert !image_sects_sane (Sections, Context->NumberOfSections, Context->SizeOfHeaders, Context->SectionAlignment, Context->TeStrippedOffset, FileSize, Context->ImageType);
        return RETURN_UNSUPPORTED;
      }
    }

    /*@ assert (\forall integer i; 0 <= i <= SectIndex ==>
      @          image_sect_disjunct_sorted (Sections, i));
    */
  }

  //@ assert Context->NumberOfSections - SectIndex == 0;

  /*@ assert Context->ImageType == ImageTypeTe ==>
    @          Sections[0].VirtualAddress != 0;
  */

  /*@ requires 0 < SectIndex == Context->NumberOfSections;
    @ requires !PcdGetBool (PcdImageLoaderTolerantLoad) ==>
    @            NextSectRva == align_up (image_sect_top (&Sections[SectIndex - 1]), Context->SectionAlignment);
    @ requires PcdGetBool (PcdImageLoaderTolerantLoad) ==>
    @            NextSectRva == image_sect_top (&Sections[SectIndex - 1]);
    @ assigns *EndAddress;
    @ ensures !PcdGetBool (PcdImageLoaderTolerantLoad) ==>
    @           *EndAddress == align_up (image_sect_top (&Sections[Context->NumberOfSections - 1]), Context->SectionAlignment);
    @ ensures PcdGetBool (PcdImageLoaderTolerantLoad) ==>
    @           *EndAddress == image_sect_top (&Sections[Context->NumberOfSections - 1]);
  */
  *EndAddress = NextSectRva;

  //@ assert image_sects_sane (Sections, Context->NumberOfSections, Context->SizeOfHeaders, Context->SectionAlignment, Context->TeStrippedOffset, FileSize, Context->ImageType);

  return RETURN_SUCCESS;
}

/**
  Verify the basic Image Relocation information.

  The preferred Image load address must be aligned by the Section Alignment.
  The Relocation Directory must be contained within the Image Section memory.
  The Relocation Directory must be correctly aligned in memory.

  @param[in]  Context       The context describing the Image. Must have been
                            initialised by PeCoffInitializeContext().
  @param[out] StartAddress  The RVA of the first Image Section.

  @retval RETURN_SUCCESS  The basic Image Relocation information is correct.
  @retval other           The basic Image Relocation information is malformed.
**/
/*@ requires \valid(Context);
  @ requires is_pow2_32 (Context->SectionAlignment);
  @
  @ requires \let Sections = image_context_get_sections (Context);
  @          StartAddress == image_loaded_hdr_virtual_size (Sections, Context->SizeOfHeaders, Context->SectionAlignment);
  @
  @ assigns \nothing;
  @
  @ behavior valid_relocinfo:
  @   assumes image_context_reloc_info_sane (Context);
  @   ensures \result == RETURN_SUCCESS;
  @
  @ behavior nvalid_relocinfo:
  @   assumes !image_context_reloc_info_sane (Context);
  @ ensures \result != RETURN_SUCCESS;
*/
STATIC
RETURN_STATUS
InternalValidateRelocInfo (
  IN CONST PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  IN UINT32                       StartAddress
  )
{
  BOOLEAN Result;
  UINT32  SectRvaEnd;

  ASSERT (Context != NULL);
  //
  // If the Base Relocations have not been stripped, verify their Directory.
  //
  /*@ assigns Result, SectRvaEnd;
    @
    @ ensures !Context->RelocsStripped ==>
    @           \let Sections      = image_context_get_sections (Context);
    @           image_reloc_dir_sane (Context->RelocDirRva, Context->RelocDirSize, Context->RelocsStripped, StartAddress, Context->SizeOfImage);
  */
  // FIXME: Prove new condition
  if (!Context->RelocsStripped && Context->RelocDirSize) {
    //
    // Ensure the Relocation Directory is not empty.
    //
    /*@ assigns \nothing;
      @ ensures sizeof (EFI_IMAGE_BASE_RELOCATION_BLOCK) <= Context->RelocDirSize;
    */
    if (sizeof (EFI_IMAGE_BASE_RELOCATION_BLOCK) > Context->RelocDirSize) {
      //@ assert !(sizeof (EFI_IMAGE_BASE_RELOCATION_BLOCK) <= Context->RelocDirSize);
      //@ assert !image_reloc_dir_sane (Context->RelocDirRva, Context->RelocDirSize, Context->RelocsStripped, StartAddress, Context->SizeOfImage);
      ASSERT (FALSE);
      return RETURN_UNSUPPORTED;
    }

    /*@ assigns Result, SectRvaEnd;
      @ ensures Result  <==> Context->RelocDirRva + Context->RelocDirSize > MAX_UINT32;
      @ ensures !Result <==> SectRvaEnd == Context->RelocDirRva + Context->RelocDirSize;
    */
    Result = BaseOverflowAddU32 (
               Context->RelocDirRva,
               Context->RelocDirSize,
               &SectRvaEnd
               );
    /*@ assigns \nothing;
      @ ensures SectRvaEnd == Context->RelocDirRva + Context->RelocDirSize;
    */
    if (Result) {
      //@ assert !(Context->RelocDirRva + Context->RelocDirSize <= Context->SizeOfImage);
      //@ assert !image_reloc_dir_sane (Context->RelocDirRva, Context->RelocDirSize, Context->RelocsStripped, StartAddress, Context->SizeOfImage);
      ASSERT (FALSE);
      return RETURN_UNSUPPORTED;
    }
    //
    // Ensure the Relocation Directory does not overlap with the Image Header.
    //
    /*@ assigns \nothing;
      @ ensures StartAddress <= Context->RelocDirRva;
    */
    if (StartAddress > Context->RelocDirRva) {
      //@ assert !(StartAddress <= Context->RelocDirRva);
      //@ assert !image_reloc_dir_sane (Context->RelocDirRva, Context->RelocDirSize, Context->RelocsStripped, StartAddress, Context->SizeOfImage);
      ASSERT (FALSE);
      return RETURN_UNSUPPORTED;
    }
    //
    // Ensure the Relocation Directory is contained in the Image memory space.
    //
    /*@ requires SectRvaEnd == Context->RelocDirRva + Context->RelocDirSize;
      @ assigns \nothing;
      @ ensures Context->RelocDirRva + Context->RelocDirSize <= Context->SizeOfImage;
    */
    if (SectRvaEnd > Context->SizeOfImage) {
      //@ assert !(Context->RelocDirRva + Context->RelocDirSize <= Context->SizeOfImage);
      //@ assert !image_reloc_dir_sane (Context->RelocDirRva, Context->RelocDirSize, Context->RelocsStripped, StartAddress, Context->SizeOfImage);
      ASSERT (FALSE);
      return RETURN_UNSUPPORTED;
    }
    //
    // Ensure the Relocation Directory start is correctly aligned.
    //
    /*@ assigns \nothing;
      @ ensures is_aligned_32 (Context->RelocDirRva, AV_ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK));
    */
    if (!IS_ALIGNED (Context->RelocDirRva, OC_ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK))) {
      ASSERT (FALSE);
      return RETURN_UNSUPPORTED;
    }
  }
  //
  // Ensure the preferred load address is correctly aligned.
  //
  /*@ assigns \nothing;
    @ ensures image_base_sane (Context->ImageBase, Context->SectionAlignment);
  */
  if (!IS_ALIGNED (Context->ImageBase, (UINT64) Context->SectionAlignment)) {
    //@ assert !is_aligned_64 (Context->ImageBase, Context->SectionAlignment);
    //@ assert !image_base_sane (Context->ImageBase, Context->SectionAlignment);
    ASSERT (FALSE);
    return RETURN_UNSUPPORTED;
  }

  //@ assert image_context_reloc_info_sane (Context);

  return RETURN_SUCCESS;
}

/**
  Verify the TE Image and initialise Context.

  Used offsets and ranges must be aligned and in the bounds of the raw file.
  Image Section Headers and basic Relocation information must be correct.

  @param[in,out] Context   The context describing the Image. Must have been
                           initialised by PeCoffInitializeContext().
  @param[in]     FileSize  The size, in bytes, of Context->FileBuffer.

  @retval RETURN_SUCCESS  The TE Image is correct.
  @retval other           The TE Image is malformed.
**/
/*@ requires \valid(Context);
  @ requires \typeof(Context->FileBuffer) <: \type(char *);
  @ requires pointer_max_aligned(Context->FileBuffer);
  @ requires \valid ((char *) Context->FileBuffer + (0 .. FileSize - 1));
  @ requires \valid(image_te_get_hdr ((char *) Context->FileBuffer));
  @ requires Context->ExeHdrOffset == 0;
  @ requires Context->ExeHdrOffset + sizeof (EFI_TE_IMAGE_HEADER) <= FileSize;
  @
  @ requires \let TeHdr       = image_te_get_hdr ((char *) Context->FileBuffer);
  @          \let SectsOffset = image_te_get_sections_offset ((char *) Context->FileBuffer);
  @          SectsOffset + TeHdr->NumberOfSections * sizeof (EFI_IMAGE_SECTION_HEADER) <= FileSize ==>
  @            image_te_sections_validity ((char *) Context->FileBuffer);
  @
  @ assigns Context->SectionsOffset;
  @ assigns Context->NumberOfSections;
  @ assigns Context->ImageType;
  @ assigns Context->AddressOfEntryPoint;
  @ assigns Context->RelocsStripped;
  @ assigns Context->SectionAlignment;
  @ assigns Context->TeStrippedOffset;
  @ assigns Context->SizeOfHeaders;
  @ assigns Context->SizeOfImage;
  @ assigns Context->RelocDirRva;
  @ assigns Context->RelocDirSize;
  @ assigns Context->ImageBase;
  @ assigns Context->Subsystem;
  @ assigns Context->Machine;
  @
  @ behavior te_valid:
  @   assumes image_te_valid ((char *) Context->FileBuffer, FileSize);
  @   ensures image_context_fields_correct (Context) &&
  @           image_context_hdr_valid (Context) &&
  @           image_context_file_char_valid (Context) &&
  @           image_context_reloc_info_sane (Context) &&
  @           image_context_sects_sane (Context, FileSize) &&
  @           image_sects_in_image (Context) &&
  @           image_datadirs_in_hdr (Context) &&
  @           \typeof (Context->FileBuffer) <: \type (char *) &&
  @           is_pow2_32 (Context->SectionAlignment) &&
  @           Context->AddressOfEntryPoint < Context->SizeOfImage &&
  @           0 < image_hdr_virtual_size (Context->SizeOfHeaders, Context->SectionAlignment) &&
  @           Context->SectionsOffset <= MAX_UINT32 &&
  @           0 < Context->NumberOfSections &&
  @           \let Sections         = image_context_get_sections (Context);
  @           \let NumberOfSections = Context->NumberOfSections;
  @           \valid (Sections + (0 .. NumberOfSections - 1));
  @   ensures \result == RETURN_SUCCESS;
  @
  @ behavior te_nvalid:
  @   assumes !image_te_valid ((char *) Context->FileBuffer, FileSize);
  @   ensures \result != RETURN_SUCCESS;
  @
  @ complete behaviors;
  @ disjoint behaviors;
*/
STATIC
RETURN_STATUS
InternalInitializeTe (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  IN     UINT32                 FileSize
  )
{
  RETURN_STATUS             Status;
  BOOLEAN                   Result;
  CONST EFI_TE_IMAGE_HEADER *TeHdr;
  UINT32                    StartAddress;
  UINT32                    SizeOfImage;

  ASSERT (Context != NULL);
  ASSERT (sizeof (EFI_TE_IMAGE_HEADER) <= FileSize);
  ASSERT (FileSize >= sizeof (EFI_TE_IMAGE_HEADER));

  /*@ assigns Context->ImageType;
    @ ensures Context->ImageType == ImageTypeTe;
    @ ensures image_context_type_valid (Context);
  */
  Context->ImageType = ImageTypeTe;

  /*@ assigns TeHdr;
    @ ensures TeHdr == image_te_get_hdr ((char *) Context->FileBuffer);
    @ ensures image_context_hdr_valid (Context);
    @ ensures \valid(TeHdr);
  */
  TeHdr = (CONST EFI_TE_IMAGE_HEADER *) (CONST VOID *) (
            (CONST CHAR8 *) Context->FileBuffer + 0
            );

#ifndef PRODUCTION
  UINT16 TeStrippedOffset;
#endif
  /*@ assigns Result, TeStrippedOffset;
    @ ensures Result <==> TeHdr->StrippedSize - sizeof (EFI_TE_IMAGE_HEADER) < 0;
    @ ensures !Result <==> TeStrippedOffset == TeHdr->StrippedSize - sizeof (EFI_TE_IMAGE_HEADER);
  */
  Result = BaseOverflowSubU16 (
             TeHdr->StrippedSize,
             sizeof (*TeHdr),
  #ifdef PRODUCTION
             &Context->TeStrippedOffset
  #else
             &TeStrippedOffset
  #endif
             );
  /*@ assigns Context->TeStrippedOffset;
    @ ensures !Result <==> Context->TeStrippedOffset == TeHdr->StrippedSize - sizeof (EFI_TE_IMAGE_HEADER);
  */
  //@ ghost Context->TeStrippedOffset = TeStrippedOffset;

  /*@ assigns \nothing;
    @ ensures Context->TeStrippedOffset == TeHdr->StrippedSize - sizeof (EFI_TE_IMAGE_HEADER);
  */
  if (Result) {
    //@ assert !(0 <= TeHdr->StrippedSize - sizeof (EFI_TE_IMAGE_HEADER));
    /*@ assert !image_te_valid ((char *) Context->FileBuffer, FileSize);
    */
    return RETURN_UNSUPPORTED;
  }

  /*@ assigns \nothing;
    @ ensures 0 < TeHdr->NumberOfSections;
  */
  if (TeHdr->NumberOfSections == 0) {
    //@ assert !(0 < TeHdr->NumberOfSections);
    /*@ assert !image_te_valid ((char *) Context->FileBuffer, FileSize);
    */
    return RETURN_UNSUPPORTED;
  }

  STATIC_ASSERT (
    IS_ALIGNED (sizeof (*TeHdr), OC_ALIGNOF (EFI_IMAGE_SECTION_HEADER)),
    "The section alignment requirements are violated."
    );
  //
  // Assign SizeOfHeaders in a way that is equivalent to what the size would
  // be if this was the original (unstripped) PE32 binary. As the TE image
  // creation fixes no fields up, tests work the same way as for PE32.
  // when referencing raw data however, the offset must be subracted.
  //
  STATIC_ASSERT (
    MAX_UINT8 * sizeof (EFI_IMAGE_SECTION_HEADER) <= MAX_UINT32 - MAX_UINT16,
    "The following arithmetic may overflow."
    );

  /*@ assigns Context->SizeOfHeaders;
    @ ensures Context->SizeOfHeaders == TeHdr->StrippedSize + TeHdr->NumberOfSections * sizeof (EFI_IMAGE_SECTION_HEADER);
  */
  Context->SizeOfHeaders = (UINT32) TeHdr->StrippedSize + (UINT32) TeHdr->NumberOfSections * sizeof (EFI_IMAGE_SECTION_HEADER);
  //
  // Ensure that all headers are in bounds of the file buffer.
  //
  /*@ assigns \nothing;
    @ ensures 0 <= image_hdr_raw_size (Context->SizeOfHeaders, Context->TeStrippedOffset) <= FileSize;
    @ ensures image_te_get_sections_offset ((char *) Context->FileBuffer) + TeHdr->NumberOfSections * sizeof (EFI_IMAGE_SECTION_HEADER) <= FileSize;
    @ ensures \valid ((char *) Context->FileBuffer + (0 .. image_hdr_raw_size (Context->SizeOfHeaders, Context->TeStrippedOffset) - 1));
    @ ensures image_te_sections_validity ((char *) Context->FileBuffer);
  */
  if ((Context->SizeOfHeaders - Context->TeStrippedOffset) > FileSize) {
    //@ assert !(0 <= image_hdr_raw_size (Context->SizeOfHeaders, Context->TeStrippedOffset) <= FileSize);
    /*@ assert !image_te_valid ((char *) Context->FileBuffer, FileSize);
    */
    return RETURN_UNSUPPORTED;
  }

  /*@ assigns Context->SectionsOffset;
    @ ensures Context->SectionsOffset == image_te_get_sections_offset ((char *) Context->FileBuffer);
    @ ensures image_context_get_sections (Context) == image_te_get_sections ((char *) Context->FileBuffer);
    @ ensures is_aligned_32 (Context->SectionsOffset, AV_ALIGNOF (EFI_IMAGE_SECTION_HEADER));
  */
  Context->SectionsOffset = sizeof (EFI_TE_IMAGE_HEADER);

  //@ assert pointer_aligned ((char *) Context->FileBuffer + Context->SectionsOffset, AV_ALIGNOF (EFI_IMAGE_SECTION_HEADER));
  //@ assert pointer_aligned ((char *) Context->FileBuffer + image_te_get_sections_offset ((char *) Context->FileBuffer), AV_ALIGNOF (EFI_IMAGE_SECTION_HEADER));
  //@ assert \valid(image_context_get_sections (Context) + (0 .. TeHdr->NumberOfSections - 1));

  /*@ assigns Context->SectionAlignment;
    @ ensures Context->SectionAlignment == BASE_4KB;
    @ ensures is_pow2_32 (Context->SectionAlignment);
  */
  Context->SectionAlignment = BASE_4KB;

  /*@ assigns Context->NumberOfSections;
    @ ensures Context->NumberOfSections == TeHdr->NumberOfSections;
    @ ensures 0 < Context->NumberOfSections;
  */
  Context->NumberOfSections = TeHdr->NumberOfSections;
  //
  // Validate the sections.
  // TE images do not have a field to explicitly describe the image size.
  // Set it to the top of the image's virtual space.
  //
  /*@ assigns Status, StartAddress, SizeOfImage;
    @ ensures Status == RETURN_SUCCESS <==>
    @           \let Sections = image_context_get_sections (Context);
    @           image_sects_sane (
    @             Sections,
    @             TeHdr->NumberOfSections,
    @             Context->SizeOfHeaders,
    @             BASE_4KB,
    @             Context->TeStrippedOffset,
    @             FileSize,
    @             ImageTypeTe
    @             );
    @ ensures Status == RETURN_SUCCESS ==>
    @           SizeOfImage == image_te_SizeOfImage ((char *) Context->FileBuffer);
    @ ensures Status == RETURN_SUCCESS ==>
    @           \let Sections = image_context_get_sections (Context);
    @           (\forall integer i; 0 <= i < TeHdr->NumberOfSections ==>
    @             image_sect_top (Sections + i) <= SizeOfImage);
  */
  Status = InternalVerifySections (
             Context,
             FileSize,
             &StartAddress,
             &SizeOfImage
             );

  /*@ assigns \nothing;
    @ ensures \let Sections = image_context_get_sections (Context);
    @         SizeOfImage == image_te_SizeOfImage ((char *) Context->FileBuffer);
    @ ensures \let Sections = image_context_get_sections (Context);
    @         image_sects_sane (
    @           Sections,
    @           TeHdr->NumberOfSections,
    @           Context->SizeOfHeaders,
    @           BASE_4KB,
    @           Context->TeStrippedOffset,
    @           FileSize,
    @           ImageTypeTe
    @           );
    @ ensures \let Sections = image_context_get_sections (Context);
    @         \forall integer i; 0 <= i < TeHdr->NumberOfSections  ==>
    @           0 < Sections[i].SizeOfRawData ==>
    @             \valid ((char *) Context->FileBuffer + ((Sections[i].PointerToRawData - Context->TeStrippedOffset) .. (Sections[i].PointerToRawData - Context->TeStrippedOffset) + Sections[i].SizeOfRawData - 1));
    @ ensures \let Sections = image_context_get_sections (Context);
    @         \forall integer i; 0 <= i < TeHdr->NumberOfSections  ==>
    @           0 == Sections[i].SizeOfRawData ==>
    @             \valid ((char *) Context->FileBuffer + ((Sections[i].PointerToRawData - Context->TeStrippedOffset) .. (Sections[i].PointerToRawData - Context->TeStrippedOffset) + Sections[i].SizeOfRawData - 1));
    @ ensures \let Sections = image_context_get_sections (Context);
    @         \forall integer i; 0 <= i < TeHdr->NumberOfSections ==>
    @           image_sect_top (Sections + i) <= SizeOfImage;
  */
  if (Status != RETURN_SUCCESS) {
    /*@ assert \let Sections      = image_te_get_sections ((char *) Context->FileBuffer);
      @        \let SizeOfHeaders = image_te_SizeOfHeaders ((char *) Context->FileBuffer);
      @        !image_sects_sane (
      @          Sections,
      @          TeHdr->NumberOfSections,
      @          SizeOfHeaders,
      @          BASE_4KB,
      @          TeHdr->StrippedSize - sizeof (EFI_TE_IMAGE_HEADER),
      @          FileSize,
      @          ImageTypeTe
      @          );
    */
    /*@ assert !image_te_valid ((char *) Context->FileBuffer, FileSize);
    */
    //@ assert Status != RETURN_SUCCESS;
    return Status;
  }

  /*@ assigns \nothing;
    @ ensures TeHdr->AddressOfEntryPoint < image_te_SizeOfImage ((char *) Context->FileBuffer);
  */
  if (TeHdr->AddressOfEntryPoint >= SizeOfImage) {
    //@ assert TeHdr->AddressOfEntryPoint >= image_te_SizeOfImage ((char *) Context->FileBuffer);
    //@ assert !image_te_valid ((char *) Context->FileBuffer, FileSize);
    return RETURN_UNSUPPORTED;
  }

  /*@ assert \let Sections = image_context_get_sections (Context);
    @        \forall integer i; 0 <= i < TeHdr->NumberOfSections  ==>
    @          \valid ((char *) Context->FileBuffer + ((Sections[i].PointerToRawData - Context->TeStrippedOffset) .. (Sections[i].PointerToRawData - Context->TeStrippedOffset) + Sections[i].SizeOfRawData - 1));
  */

  /*@ assigns Context->SizeOfImage;
    @ ensures \let Sections = image_context_get_sections (Context);
    @         Context->SizeOfImage == image_te_SizeOfImage ((char *) Context->FileBuffer);
  */
  Context->SizeOfImage         = SizeOfImage;

  //@ assert image_sects_in_image (Context);

  /*@ assigns Context->Machine;
    @ ensures Context->Machine == TeHdr->Machine;
  */
  Context->Machine             = TeHdr->Machine;

  /*@ assigns Context->Subsystem;
    @ ensures Context->Subsystem == TeHdr->Subsystem;
  */
  Context->Subsystem           = TeHdr->Subsystem;

  /*@ assigns Context->ImageBase;
    @ ensures Context->ImageBase == TeHdr->ImageBase;
  */
  Context->ImageBase           = TeHdr->ImageBase;

  /*@ assigns Context->RelocsStripped;
    @ ensures Context->RelocsStripped == (image_context_get_reloc_dir (Context)->Size > 0);
  */
  Context->RelocsStripped      = TeHdr->DataDirectory[0].Size > 0;

  /*@ assigns Context->AddressOfEntryPoint;
    @ ensures Context->AddressOfEntryPoint == TeHdr->AddressOfEntryPoint;
  */
  Context->AddressOfEntryPoint = TeHdr->AddressOfEntryPoint;

  //@ assert image_context_debug_dir_exists (Context);

  /*@ assigns Context->RelocDirRva;
    @ ensures Context->RelocDirRva == image_context_get_reloc_dir (Context)->VirtualAddress;
  */
  Context->RelocDirRva         = TeHdr->DataDirectory[0].VirtualAddress;

  /*@ assigns Context->RelocDirSize;
    @ ensures Context->RelocDirSize == image_context_get_reloc_dir (Context)->Size;
  */
  Context->RelocDirSize        = TeHdr->DataDirectory[0].Size;

  /*@ assigns Status;
    @ ensures Status == RETURN_SUCCESS <==>
    @           image_context_reloc_info_sane (Context);
  */
  Status = InternalValidateRelocInfo (Context, StartAddress);

  /*@ assert Status == RETURN_SUCCESS <==>
    @          image_te_valid ((char *) Context->FileBuffer, FileSize);
  */

  return Status;
}

/**
  Verify the PE32 or PE32+ Image and initialise Context.

  Used offsets and ranges must be aligned and in the bounds of the raw file.
  Image Section Headers and basic Relocation information must be correct.

  @param[in,out] Context   The context describing the Image. Must have been
                           initialised by PeCoffInitializeContext().
  @param[in]     FileSize  The size, in bytes, of Context->FileBuffer.

  @retval RETURN_SUCCESS  The PE Image is correct.
  @retval other           The PE Image is malformed.
**/
/*@ requires \valid(Context);
  @ requires \typeof(Context->FileBuffer) <: \type(char *);
  @ requires pointer_max_aligned(Context->FileBuffer);
  @ requires \valid((char *) Context->FileBuffer + (0 .. FileSize - 1));
  @ requires image_signature_pe ((char *) Context->FileBuffer, Context->ExeHdrOffset, FileSize);
  @ requires image_pe32_file_hdrs_validity ((char *) Context->FileBuffer, Context->ExeHdrOffset, FileSize) &&
  @          image_pe32plus_file_hdrs_validity ((char *) Context->FileBuffer, Context->ExeHdrOffset, FileSize);
  @ requires Context->TeStrippedOffset == 0 && Context->RelocDirRva == 0 && Context->RelocDirSize == 0;
  @ requires is_aligned_32 (Context->ExeHdrOffset, AV_ALIGNOF (EFI_IMAGE_NT_HEADERS_COMMON_HDR));
  @
  @ assigns Context->SectionsOffset;
  @ assigns Context->NumberOfSections;
  @ assigns Context->ImageType;
  @ assigns Context->AddressOfEntryPoint;
  @ assigns Context->RelocsStripped;
  @ assigns Context->SectionAlignment;
  @ assigns Context->TeStrippedOffset;
  @ assigns Context->SizeOfHeaders;
  @ assigns Context->SizeOfImage;
  @ assigns Context->RelocDirRva;
  @ assigns Context->RelocDirSize;
  @ assigns Context->ImageBase;
  @ assigns Context->Subsystem;
  @ assigns Context->Machine;
  @
  @ behavior pe_valid:
  @   assumes valid_pe ((char *) Context->FileBuffer, Context->ExeHdrOffset, FileSize);
  @   ensures image_context_fields_correct (Context) &&
  @           image_context_hdr_valid (Context) &&
  @           image_context_file_char_valid (Context) &&
  @           image_context_reloc_info_sane (Context) &&
  @           image_context_sects_sane (Context, FileSize) &&
  @           image_sects_in_image (Context) &&
  @           image_datadirs_in_hdr (Context) &&
  @           \typeof (Context->FileBuffer) <: \type (char *) &&
  @           is_pow2_32 (Context->SectionAlignment) &&
  @           Context->AddressOfEntryPoint < Context->SizeOfImage &&
  @           0 < image_hdr_virtual_size (Context->SizeOfHeaders, Context->SectionAlignment) &&
  @           Context->SectionsOffset <= MAX_UINT32 &&
  @           0 < Context->NumberOfSections &&
  @           \let Sections         = image_context_get_sections (Context);
  @           \let NumberOfSections = Context->NumberOfSections;
  @           \valid (Sections + (0 .. NumberOfSections - 1));
  @   ensures \result == RETURN_SUCCESS;
  @
  @ behavior pe_nvalid:
  @   assumes \let OptHdrPtr = (char *) Context->FileBuffer + Context->ExeHdrOffset + sizeof (EFI_IMAGE_NT_HEADERS_COMMON_HDR);
  @           !valid_pe ((char *) Context->FileBuffer, Context->ExeHdrOffset, FileSize);
  @   ensures \result != RETURN_SUCCESS;
  @
  @ disjoint behaviors;
  @ complete behaviors;
*/
STATIC
RETURN_STATUS
InternalInitializePe (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  IN     UINT32                 FileSize
  )
{
  BOOLEAN                               Result;
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
  ASSERT (IS_ALIGNED (Context->ExeHdrOffset, OC_ALIGNOF (EFI_IMAGE_NT_HEADERS_COMMON_HDR)));

  //@ assert is_aligned_32 ((uint32_t) sizeof (EFI_IMAGE_NT_HEADERS_COMMON_HDR), AV_ALIGNOF (UINT16));

  /*@ assert AV_ALIGNOF (UINT16) <= AV_ALIGNOF (EFI_IMAGE_NT_HEADERS_COMMON_HDR) ==>
    @          is_aligned_32 (Context->ExeHdrOffset, AV_ALIGNOF (UINT16));
  */
  //@ assert is_aligned_32 (Context->ExeHdrOffset, AV_ALIGNOF (UINT16));

  /*@ requires pointer_max_aligned(Context->FileBuffer);
    @ requires is_aligned_N (Context->ExeHdrOffset, AV_ALIGNOF (UINT16));
    @ requires pointer_max_aligned(Context->FileBuffer) && is_aligned_N (Context->ExeHdrOffset, AV_ALIGNOF (UINT16)) ==>
    @            pointer_aligned((char *) Context->FileBuffer + Context->ExeHdrOffset, AV_ALIGNOF (UINT16));
    @ assigns OptHdrPtr;
    @ ensures OptHdrPtr == (char *) Context->FileBuffer + Context->ExeHdrOffset;
    @ ensures pointer_aligned(OptHdrPtr, AV_ALIGNOF (UINT16));
  */
  OptHdrPtr = (CONST CHAR8 *) Context->FileBuffer + Context->ExeHdrOffset;

  /*@ requires pointer_aligned(OptHdrPtr, AV_ALIGNOF (UINT16));
    @ requires is_aligned_N ((UINT32) sizeof (EFI_IMAGE_NT_HEADERS_COMMON_HDR), AV_ALIGNOF (UINT16));
    @ requires pointer_aligned(OptHdrPtr, AV_ALIGNOF (UINT16)) && is_aligned_N ((UINT32) sizeof (EFI_IMAGE_NT_HEADERS_COMMON_HDR), AV_ALIGNOF (UINT16)) ==>
    @            pointer_aligned(OptHdrPtr + sizeof (EFI_IMAGE_NT_HEADERS_COMMON_HDR), AV_ALIGNOF (UINT16));
    @ assigns OptHdrPtr;
    @ ensures OptHdrPtr == (char *) Context->FileBuffer + Context->ExeHdrOffset + sizeof (EFI_IMAGE_NT_HEADERS_COMMON_HDR);
    @ ensures pointer_aligned(OptHdrPtr, AV_ALIGNOF (UINT16));
  */
  OptHdrPtr += sizeof (EFI_IMAGE_NT_HEADERS_COMMON_HDR);

  STATIC_ASSERT (
    IS_ALIGNED (OC_ALIGNOF (EFI_IMAGE_NT_HEADERS_COMMON_HDR), OC_ALIGNOF (UINT16))
   && IS_ALIGNED (sizeof (EFI_IMAGE_NT_HEADERS_COMMON_HDR), OC_ALIGNOF (UINT16)),
    "The following operation might be an unaligned access."
  );
  //
  // Determine the type of and retrieve data from the PE Optional Header.
  //
  /*@ assigns Pe32;
    @ assigns Pe32Plus;
    @ assigns HdrSizeWithoutDataDir;
    @ assigns NumberOfRvaAndSizes;
    @ assigns PeCommon;
    @ assigns Context->ImageType;
    @ assigns Context->Subsystem;
    @ assigns Context->SizeOfImage;
    @ assigns Context->SizeOfHeaders;
    @ assigns Context->AddressOfEntryPoint;
    @ assigns Context->SectionAlignment;
    @ assigns Context->ImageBase;
    @
    @ ensures \valid(PeCommon);
    @ ensures Context->ImageType == ImageTypePe32 ||
    @         Context->ImageType == ImageTypePe32Plus;
    @ ensures image_context_hdr_valid (Context);
    @ ensures RelocDir == image_context_get_reloc_dir (Context);
    @ ensures (image_signature_pe32 ((char *) Context->FileBuffer, Context->ExeHdrOffset, FileSize) &&
    @           Context->ImageType == ImageTypePe32 &&
    @           image_context_fields_correct_pe32_opt (Context) &&
    @           Pe32 == image_pe32_get_hdr ((char *) Context->FileBuffer, Context->ExeHdrOffset) &&
    @           PeCommon == &Pe32->CommonHeader &&
    @           NumberOfRvaAndSizes == Pe32->NumberOfRvaAndSizes &&
    @           HdrSizeWithoutDataDir == sizeof (EFI_IMAGE_NT_HEADERS32) - sizeof (EFI_IMAGE_NT_HEADERS_COMMON_HDR)) ||
    @         (image_signature_pe32plus ((char *) Context->FileBuffer, Context->ExeHdrOffset, FileSize) &&
    @           Context->ImageType == ImageTypePe32Plus &&
    @           image_context_fields_correct_pe32plus_opt (Context) &&
    @           Pe32Plus == image_pe32plus_get_hdr ((char *) Context->FileBuffer, Context->ExeHdrOffset) &&
    @           PeCommon == &Pe32Plus->CommonHeader &&
    @           NumberOfRvaAndSizes == Pe32Plus->NumberOfRvaAndSizes &&
    @           HdrSizeWithoutDataDir == sizeof (EFI_IMAGE_NT_HEADERS64) - sizeof (EFI_IMAGE_NT_HEADERS_COMMON_HDR));
  */
  switch (READ_ALIGNED_16 (OptHdrPtr)) {
    case EFI_IMAGE_NT_OPTIONAL_HDR32_MAGIC:
      /*@ assigns \nothing;
        @ ensures Context->ExeHdrOffset + sizeof (EFI_IMAGE_NT_HEADERS32) <= FileSize;
      */
      if (sizeof (*Pe32) > FileSize - Context->ExeHdrOffset) {
        /*@ assert image_pe32_valid ((char *) Context->FileBuffer, Context->ExeHdrOffset, FileSize) ==>
          @          Context->ExeHdrOffset + sizeof (EFI_IMAGE_NT_HEADERS32) <= Context->SizeOfHeaders;
        */
        //@ assert !valid_pe ((char *) Context->FileBuffer, Context->ExeHdrOffset, FileSize);
        ASSERT (FALSE);
        return RETURN_UNSUPPORTED;
      }
      //
      // INTEGRATION: Condition superfluous, see STATIC_ASSERT below.
      // BUG: AV crash...?!
      //
      /*@ assigns \nothing;
        @ ensures is_aligned_32 (Context->ExeHdrOffset, AV_ALIGNOF (EFI_IMAGE_NT_HEADERS32));
        @ ensures image_signature_pe32 ((char *) Context->FileBuffer, Context->ExeHdrOffset, FileSize);
        @ ensures pointer_aligned (image_pe32_get_hdr ((char *) Context->FileBuffer, Context->ExeHdrOffset), AV_ALIGNOF (EFI_IMAGE_NT_HEADERS32));
      */
      /*@ ghost
        @ if (!IS_ALIGNED (Context->ExeHdrOffset, OC_ALIGNOF (EFI_IMAGE_NT_HEADERS32))) {
        @   //@ assert !is_aligned_32 (Context->ExeHdrOffset, AV_ALIGNOF (EFI_IMAGE_NT_HEADERS32));
        @   //@ assert !image_signature_pe32 ((char *) Context->FileBuffer, Context->ExeHdrOffset, FileSize);
        @   //@ assert !valid_pe ((char *) Context->FileBuffer, Context->ExeHdrOffset, FileSize);
        @   return RETURN_UNSUPPORTED;
        @ }
      */

      STATIC_ASSERT (
        OC_ALIGNOF (EFI_IMAGE_NT_HEADERS_COMMON_HDR) == OC_ALIGNOF (EFI_IMAGE_NT_HEADERS32),
        "The following operations may be unaligned."
        );

      /*@ assigns Context->ImageType;
        @ ensures Context->ImageType == ImageTypePe32;
        @ ensures image_context_type_valid (Context);
      */
      Context->ImageType = ImageTypePe32;
      //@ assert image_context_hdr_valid (Context);

      /*@ assigns Pe32;
        @ ensures Pe32 == image_pe32_get_hdr ((char *) Context->FileBuffer, Context->ExeHdrOffset);
        @ ensures \valid(Pe32);
      */
      Pe32 = (CONST EFI_IMAGE_NT_HEADERS32 *) (CONST VOID *) (
               (CONST CHAR8 *) Context->FileBuffer + Context->ExeHdrOffset
               );

      /*@ assigns Context->Subsystem;
        @ ensures Context->Subsystem == Pe32->Subsystem;
      */
      Context->Subsystem    = Pe32->Subsystem;

      /*@ assigns RelocDir;
        @ ensures RelocDir == image_pe32_get_reloc_dir ((char *) Context->FileBuffer, Context->ExeHdrOffset);
        @ ensures RelocDir == image_context_get_reloc_dir (Context);
      */
      RelocDir = Pe32->DataDirectory + EFI_IMAGE_DIRECTORY_ENTRY_BASERELOC;

      SecDir = Pe32->DataDirectory + EFI_IMAGE_DIRECTORY_ENTRY_SECURITY;

      /*@ assigns Context->SizeOfImage;
        @ ensures Context->SizeOfImage == Pe32->SizeOfImage;
      */
      Context->SizeOfImage         = Pe32->SizeOfImage;

      /*@ assigns Context->SizeOfHeaders;
        @ ensures Context->SizeOfHeaders == Pe32->SizeOfHeaders;
      */
      Context->SizeOfHeaders       = Pe32->SizeOfHeaders;

      /*@ assigns Context->ImageBase;
        @ ensures Context->ImageBase == Pe32->ImageBase;
      */
      Context->ImageBase           = Pe32->ImageBase;

      /*@ assigns Context->AddressOfEntryPoint;
        @ ensures Context->AddressOfEntryPoint == Pe32->AddressOfEntryPoint;
      */
      Context->AddressOfEntryPoint = Pe32->AddressOfEntryPoint;

      /*@ assigns Context->SectionAlignment;
        @ ensures Context->SectionAlignment == Pe32->SectionAlignment;
      */
      Context->SectionAlignment    = Pe32->SectionAlignment;

      /*@ assigns PeCommon;
        @ ensures PeCommon == &Pe32->CommonHeader;
      */
      PeCommon = &Pe32->CommonHeader;

      /*@ assigns NumberOfRvaAndSizes;
        @ ensures NumberOfRvaAndSizes == Pe32->NumberOfRvaAndSizes;
      */
      NumberOfRvaAndSizes   = Pe32->NumberOfRvaAndSizes;

      /*@ assigns HdrSizeWithoutDataDir;
        @ ensures HdrSizeWithoutDataDir == sizeof (EFI_IMAGE_NT_HEADERS32) - sizeof (EFI_IMAGE_NT_HEADERS_COMMON_HDR);
      */
      HdrSizeWithoutDataDir = sizeof (EFI_IMAGE_NT_HEADERS32) - sizeof (EFI_IMAGE_NT_HEADERS_COMMON_HDR);
      break;

    case EFI_IMAGE_NT_OPTIONAL_HDR64_MAGIC:
      /*@ assigns \nothing;
        @ ensures Context->ExeHdrOffset + sizeof (EFI_IMAGE_NT_HEADERS64) <= FileSize;
      */
      if (sizeof (*Pe32Plus) > FileSize - Context->ExeHdrOffset) {
        /*@ assert image_pe32plus_valid ((char *) Context->FileBuffer, Context->ExeHdrOffset, FileSize) ==>
          @          Context->ExeHdrOffset + sizeof (EFI_IMAGE_NT_HEADERS64) <= Context->SizeOfHeaders;
        */
        //@ assert !valid_pe ((char *) Context->FileBuffer, Context->ExeHdrOffset, FileSize);
        ASSERT (FALSE);
        return RETURN_UNSUPPORTED;
      }
      //
      // BUG: AV crash...?!
      //
      /*@ assigns \nothing;
        @ ensures is_aligned_32 (Context->ExeHdrOffset, AV_ALIGNOF (EFI_IMAGE_NT_HEADERS64));
        @ ensures image_signature_pe32plus ((char *) Context->FileBuffer, Context->ExeHdrOffset, FileSize);
        @ ensures pointer_aligned (image_pe32plus_get_hdr ((char *) Context->FileBuffer, Context->ExeHdrOffset), AV_ALIGNOF (EFI_IMAGE_NT_HEADERS64));
      */
      if (!IS_ALIGNED (Context->ExeHdrOffset, OC_ALIGNOF (EFI_IMAGE_NT_HEADERS64))) {
        //@ assert !valid_pe ((char *) Context->FileBuffer, Context->ExeHdrOffset, FileSize);
        ASSERT (FALSE);
        return RETURN_UNSUPPORTED;
      }

      /*@ assigns Context->ImageType;
        @ ensures Context->ImageType == ImageTypePe32Plus;
        @ ensures image_context_type_valid (Context);
      */
      Context->ImageType = ImageTypePe32Plus;
      //@ assert image_context_hdr_valid (Context);

      /*@ assigns Pe32Plus;
        @ ensures Pe32Plus == image_pe32plus_get_hdr ((char *) Context->FileBuffer, Context->ExeHdrOffset);
        @ ensures \valid(Pe32Plus);
      */
      Pe32Plus = (CONST EFI_IMAGE_NT_HEADERS64 *) (CONST VOID *) (
                   (CONST CHAR8 *) Context->FileBuffer + Context->ExeHdrOffset
                   );

      /*@ assigns Context->Subsystem;
        @ ensures Context->Subsystem == Pe32Plus->Subsystem;
      */
      Context->Subsystem           = Pe32Plus->Subsystem;

      /*@ assigns RelocDir;
        @ ensures RelocDir == image_pe32plus_get_reloc_dir ((char *) Context->FileBuffer, Context->ExeHdrOffset);
      */
      RelocDir = Pe32Plus->DataDirectory + EFI_IMAGE_DIRECTORY_ENTRY_BASERELOC;
      //@ assert RelocDir == image_context_get_reloc_dir (Context);

      SecDir = Pe32Plus->DataDirectory + EFI_IMAGE_DIRECTORY_ENTRY_SECURITY;

      /*@ assigns Context->SizeOfImage;
        @ ensures Context->SizeOfImage == Pe32Plus->SizeOfImage;
      */
      Context->SizeOfImage         = Pe32Plus->SizeOfImage;

      /*@ assigns Context->SizeOfHeaders;
        @ ensures Context->SizeOfHeaders == Pe32Plus->SizeOfHeaders;
      */
      Context->SizeOfHeaders       = Pe32Plus->SizeOfHeaders;

      /*@ assigns Context->ImageBase;
        @ ensures Context->ImageBase == Pe32Plus->ImageBase;
      */
      Context->ImageBase           = Pe32Plus->ImageBase;

      /*@ assigns Context->AddressOfEntryPoint;
        @ ensures Context->AddressOfEntryPoint == Pe32Plus->AddressOfEntryPoint;
      */
      Context->AddressOfEntryPoint = Pe32Plus->AddressOfEntryPoint;

      /*@ assigns Context->SectionAlignment;
        @ ensures Context->SectionAlignment == Pe32Plus->SectionAlignment;
      */
      Context->SectionAlignment    = Pe32Plus->SectionAlignment;

      /*@ assigns PeCommon;
        @ ensures PeCommon == &Pe32Plus->CommonHeader;
      */
      PeCommon = &Pe32Plus->CommonHeader;

      /*@ assigns NumberOfRvaAndSizes;
        @ ensures NumberOfRvaAndSizes == Pe32Plus->NumberOfRvaAndSizes;
      */
      NumberOfRvaAndSizes   = Pe32Plus->NumberOfRvaAndSizes;

      /*@ assigns HdrSizeWithoutDataDir;
        @ ensures HdrSizeWithoutDataDir == sizeof (EFI_IMAGE_NT_HEADERS64) - sizeof (EFI_IMAGE_NT_HEADERS_COMMON_HDR);
      */
      HdrSizeWithoutDataDir = sizeof (EFI_IMAGE_NT_HEADERS64) - sizeof (EFI_IMAGE_NT_HEADERS_COMMON_HDR);
      break;

    default:
      // assert !valid_pe ((char *) Context->FileBuffer, Context->ExeHdrOffset, FileSize);
      ASSERT (FALSE);
      return RETURN_UNSUPPORTED;
  }
  //
  // Do not load images with unknown directories.
  //
  /*@ assigns \nothing;
    @ ensures NumberOfRvaAndSizes <= EFI_IMAGE_NUMBER_OF_DIRECTORY_ENTRIES;
  */
  if (NumberOfRvaAndSizes > EFI_IMAGE_NUMBER_OF_DIRECTORY_ENTRIES) {
    //@ assert !valid_pe ((char *) Context->FileBuffer, Context->ExeHdrOffset, FileSize);
    ASSERT (FALSE);
    return RETURN_UNSUPPORTED;
  }

  /*@ assigns \nothing;
    @ ensures 0 < PeCommon->FileHeader.NumberOfSections;
  */
  if (PeCommon->FileHeader.NumberOfSections == 0) {
    //@ assert !valid_pe ((char *) Context->FileBuffer, Context->ExeHdrOffset, FileSize);
    ASSERT (FALSE);
    return RETURN_UNSUPPORTED;
  }

  /*@ assigns \nothing;
    @ ensures Context->AddressOfEntryPoint < Context->SizeOfImage;
  */
  if (Context->AddressOfEntryPoint >= Context->SizeOfImage) {
    //@ assert Context->AddressOfEntryPoint >= Context->SizeOfImage;
    //@ assert !valid_pe ((char *) Context->FileBuffer, Context->ExeHdrOffset, FileSize);
    ASSERT (FALSE);
    return RETURN_UNSUPPORTED;
  }

  /*@ assigns \nothing;
    @ ensures is_pow2_32 (Context->SectionAlignment);
  */
  if (!IS_POW2 (Context->SectionAlignment)) {
    //@ assert !is_pow2_32 (Context->SectionAlignment);
    //@ assert !valid_pe ((char *) Context->FileBuffer, Context->ExeHdrOffset, FileSize);
    ASSERT (FALSE);
    return RETURN_UNSUPPORTED;
  }

  STATIC_ASSERT (
    sizeof (EFI_IMAGE_DATA_DIRECTORY) <= MAX_UINT32 / EFI_IMAGE_NUMBER_OF_DIRECTORY_ENTRIES,
    "The following arithmetic may overflow."
    );
  //
  // Context->ExeHdrOffset + sizeof (EFI_IMAGE_NT_HEADERS_COMMON_HDR) cannot overflow because
  //   * ExeFileSize > sizeof (EFI_IMAGE_NT_HEADERS_COMMON_HDR) and
  //   * Context->ExeHdrOffset + ExeFileSize = FileSize
  //
#ifndef PRODUCTION
  UINT32 SectionsOffset;
#endif
  /*@ assigns Result, SectionsOffset;
    @ ensures Result <==> Context->ExeHdrOffset + sizeof (EFI_IMAGE_NT_HEADERS_COMMON_HDR) + PeCommon->FileHeader.SizeOfOptionalHeader > MAX_UINT32;
    @ ensures !Result <==> SectionsOffset == image_pecommon_get_sections_offset (PeCommon, Context->ExeHdrOffset);
  */
  Result = BaseOverflowAddU32 (
             Context->ExeHdrOffset + sizeof (*PeCommon),
             PeCommon->FileHeader.SizeOfOptionalHeader,
#ifdef PRODUCTION
             &Context->SectionsOffset
#else
             &SectionsOffset
#endif
             );
  /*@ assigns Context->SectionsOffset;
    @ ensures !Result <==> Context->SectionsOffset == image_pecommon_get_sections_offset (PeCommon, Context->ExeHdrOffset);
  */
  //@ ghost Context->SectionsOffset = SectionsOffset;

  /*@ assigns \nothing;
    @ ensures Context->SectionsOffset == image_pecommon_get_sections_offset (PeCommon, Context->ExeHdrOffset);
  */
  if (Result) {
    /*@ assert (Context->ImageType == ImageTypePe32 ==>
      @          image_pe32_get_min_SizeOfHeaders ((char *) Context->FileBuffer, Context->ExeHdrOffset) > MAX_UINT32 &&
      @          !(image_pe32_get_min_SizeOfHeaders ((char *) Context->FileBuffer, Context->ExeHdrOffset) < Pe32->SizeOfHeaders)) &&
      @        (Context->ImageType == ImageTypePe32Plus ==>
      @          image_pe32plus_get_min_SizeOfHeaders ((char *) Context->FileBuffer, Context->ExeHdrOffset) > MAX_UINT32 &&
      @          !(image_pe32plus_get_min_SizeOfHeaders ((char *) Context->FileBuffer, Context->ExeHdrOffset) < Pe32Plus->SizeOfHeaders));
    */
    //@ assert !valid_pe ((char *) Context->FileBuffer, Context->ExeHdrOffset, FileSize);
    ASSERT (FALSE);
    return RETURN_UNSUPPORTED;
  }
  //
  // Ensure the section headers offset is properly aligned.
  //
  /*@ assigns \nothing;
    @ ensures is_aligned_32 (Context->SectionsOffset, AV_ALIGNOF (EFI_IMAGE_SECTION_HEADER));
  */
  if (!IS_ALIGNED (Context->SectionsOffset, OC_ALIGNOF (EFI_IMAGE_SECTION_HEADER))) {
    //@ assert Context->SectionsOffset == image_pecommon_get_sections_offset (PeCommon, Context->ExeHdrOffset);
    //@ assert !is_aligned_32 (Context->SectionsOffset, AV_ALIGNOF (EFI_IMAGE_SECTION_HEADER));
    //@ assert !is_aligned_32 ((UINT32) image_pecommon_get_sections_offset (PeCommon, Context->ExeHdrOffset), AV_ALIGNOF (EFI_IMAGE_SECTION_HEADER));
    //@ assert !valid_pe ((char *) Context->FileBuffer, Context->ExeHdrOffset, FileSize);
    ASSERT (FALSE);
    return RETURN_UNSUPPORTED;
  }

  //@ assert pointer_max_aligned ((char *) Context->FileBuffer);
  //@ assert is_aligned_32 ((UINT32) image_pecommon_get_sections_offset (PeCommon, Context->ExeHdrOffset), AV_ALIGNOF (EFI_IMAGE_SECTION_HEADER));
  //@ assert is_aligned_N ((UINT32) image_pecommon_get_sections_offset (PeCommon, Context->ExeHdrOffset), AV_ALIGNOF (EFI_IMAGE_SECTION_HEADER));
  /*@ assert pointer_max_aligned ((char *) Context->FileBuffer) && is_aligned_N ((UINT32) image_pecommon_get_sections_offset (PeCommon, Context->ExeHdrOffset), AV_ALIGNOF (EFI_IMAGE_SECTION_HEADER)) ==>
    @          pointer_aligned ((char *) Context->FileBuffer + image_pecommon_get_sections_offset (PeCommon, Context->ExeHdrOffset), AV_ALIGNOF (EFI_IMAGE_SECTION_HEADER));
  */
  //@ assert pointer_aligned ((char *) Context->FileBuffer + image_pecommon_get_sections_offset (PeCommon, Context->ExeHdrOffset), AV_ALIGNOF (EFI_IMAGE_SECTION_HEADER));
  //
  // MinSizeOfOptionalHeader cannot overflow because NumberOfRvaAndSizes has
  // been verified and the other two components are validated constants.
  //
  /*@ assigns MinSizeOfOptionalHeader;
    @ ensures (Context->ImageType == ImageTypePe32 ==>
    @           MinSizeOfOptionalHeader == image_pe32_get_min_SizeOfOptionalHeader ((char *) Context->FileBuffer, Context->ExeHdrOffset)) &&
    @         (Context->ImageType == ImageTypePe32Plus ==>
    @           MinSizeOfOptionalHeader == image_pe32plus_get_min_SizeOfOptionalHeader ((char *) Context->FileBuffer, Context->ExeHdrOffset));
  */
  MinSizeOfOptionalHeader = HdrSizeWithoutDataDir +
                              NumberOfRvaAndSizes * sizeof (EFI_IMAGE_DATA_DIRECTORY);

  ASSERT (MinSizeOfOptionalHeader >= HdrSizeWithoutDataDir);

  STATIC_ASSERT (
    sizeof (EFI_IMAGE_SECTION_HEADER) <= (MAX_UINT32 + 1ULL) / (MAX_UINT16 + 1ULL),
    "The following arithmetic may overflow."
    );

  /*@ assigns Result, MinSizeOfHeaders;
    @ ensures Result <==>
    @           Context->SectionsOffset + PeCommon->FileHeader.NumberOfSections * sizeof (EFI_IMAGE_SECTION_HEADER) > MAX_UINT32;
    @ ensures !Result <==>
    @           MinSizeOfHeaders == Context->SectionsOffset + PeCommon->FileHeader.NumberOfSections * sizeof (EFI_IMAGE_SECTION_HEADER);
  */
  Result = BaseOverflowAddU32 (
             Context->SectionsOffset,
             (UINT32) PeCommon->FileHeader.NumberOfSections * sizeof (EFI_IMAGE_SECTION_HEADER),
             &MinSizeOfHeaders
             );

  /*@ assigns \nothing;
    @ ensures (Context->ImageType == ImageTypePe32 ==>
    @           MinSizeOfHeaders == image_pe32_get_min_SizeOfHeaders ((char *) Context->FileBuffer, Context->ExeHdrOffset)) &&
    @         (Context->ImageType == ImageTypePe32Plus ==>
    @           MinSizeOfHeaders == image_pe32plus_get_min_SizeOfHeaders ((char *) Context->FileBuffer, Context->ExeHdrOffset));
  */
  if (Result) {
    /*@ assert (Context->ImageType == ImageTypePe32 ==>
      @          image_pe32_get_min_SizeOfHeaders ((char *) Context->FileBuffer, Context->ExeHdrOffset) > MAX_UINT32 &&
      @          !(image_pe32_get_min_SizeOfHeaders ((char *) Context->FileBuffer, Context->ExeHdrOffset) <= Pe32->SizeOfHeaders)) &&
      @        (Context->ImageType == ImageTypePe32Plus ==>
      @          image_pe32plus_get_min_SizeOfHeaders ((char *) Context->FileBuffer, Context->ExeHdrOffset) > MAX_UINT32 &&
      @          !(image_pe32plus_get_min_SizeOfHeaders ((char *) Context->FileBuffer, Context->ExeHdrOffset) <= Pe32Plus->SizeOfHeaders));
    */
    //@ assert !valid_pe ((char *) Context->FileBuffer, Context->ExeHdrOffset, FileSize);
    ASSERT (FALSE);
    return RETURN_UNSUPPORTED;
  }
  //
  // Ensure the header sizes are sane. SizeOfHeaders contains all header
  // components (DOS, PE Common and Optional Header).
  //
  /*@ assigns \nothing;
    @ ensures MinSizeOfOptionalHeader <= PeCommon->FileHeader.SizeOfOptionalHeader;
  */
  if (MinSizeOfOptionalHeader > PeCommon->FileHeader.SizeOfOptionalHeader) {
    /*@ assert (Context->ImageType == ImageTypePe32 ==>
      @          !(image_pe32_get_min_SizeOfOptionalHeader ((char *) Context->FileBuffer, Context->ExeHdrOffset) <= Pe32->CommonHeader.FileHeader.SizeOfOptionalHeader)) &&
      @        (Context->ImageType == ImageTypePe32Plus ==>
      @          !(image_pe32plus_get_min_SizeOfOptionalHeader ((char *) Context->FileBuffer, Context->ExeHdrOffset) <= Pe32Plus->CommonHeader.FileHeader.SizeOfOptionalHeader));
    */
    //@ assert !valid_pe ((char *) Context->FileBuffer, Context->ExeHdrOffset, FileSize);
    ASSERT (FALSE);
    return RETURN_UNSUPPORTED;
  }

  /*@ assigns \nothing;
    @ ensures MinSizeOfHeaders <= Context->SizeOfHeaders;
    @ ensures image_datadirs_in_hdr (Context);
  */
  if (MinSizeOfHeaders > Context->SizeOfHeaders) {
    /*@ assert (Context->ImageType == ImageTypePe32 ==>
      @          !(image_pe32_get_min_SizeOfHeaders ((char *) Context->FileBuffer, Context->ExeHdrOffset) <= Pe32->SizeOfHeaders)) &&
      @        (Context->ImageType == ImageTypePe32Plus ==>
      @          !(image_pe32plus_get_min_SizeOfHeaders ((char *) Context->FileBuffer, Context->ExeHdrOffset) <= Pe32Plus->SizeOfHeaders));
    */
    //@ assert !valid_pe ((char *) Context->FileBuffer, Context->ExeHdrOffset, FileSize);
    ASSERT (FALSE);
    return RETURN_UNSUPPORTED;
  }
  //
  // Ensure that all headers are in bounds of the file buffer.
  //
  /*@ assigns \nothing;
    @ ensures 0 <= image_hdr_raw_size (Context->SizeOfHeaders, 0) <= FileSize;
    @ ensures \valid ((char *) Context->FileBuffer + (0 .. image_hdr_raw_size (Context->SizeOfHeaders, 0) - 1));
  */
  if (Context->SizeOfHeaders > FileSize) {
    /*@ assert (Context->ImageType == ImageTypePe32 ==>
      @          !(Pe32->SizeOfHeaders <= FileSize)) &&
      @        (Context->ImageType == ImageTypePe32Plus ==>
      @          !(Pe32Plus->SizeOfHeaders <= FileSize));
    */
    //@ assert !valid_pe ((char *) Context->FileBuffer, Context->ExeHdrOffset, FileSize);
    ASSERT (FALSE);
    return RETURN_UNSUPPORTED;
  }

  /*@ assert (Context->ImageType == ImageTypePe32 ==>
    @          pointer_aligned ((char *) Context->FileBuffer + image_pecommon_get_sections_offset (&Pe32->CommonHeader, Context->ExeHdrOffset), AV_ALIGNOF (EFI_IMAGE_SECTION_HEADER))) &&
    @        (Context->ImageType == ImageTypePe32Plus ==>
    @          pointer_aligned ((char *) Context->FileBuffer + image_pecommon_get_sections_offset (&Pe32Plus->CommonHeader, Context->ExeHdrOffset), AV_ALIGNOF (EFI_IMAGE_SECTION_HEADER)));
  */
  /*@ assert (Context->ImageType == ImageTypePe32 ==>
    @          \valid(image_pe32_get_sections ((char *) Context->FileBuffer, Context->ExeHdrOffset) + (0 .. Pe32->CommonHeader.FileHeader.NumberOfSections - 1))) &&
    @        (Context->ImageType == ImageTypePe32Plus ==>
    @          \valid(image_pe32plus_get_sections ((char *) Context->FileBuffer, Context->ExeHdrOffset) + (0 .. Pe32Plus->CommonHeader.FileHeader.NumberOfSections - 1)));
  */
  //@ assert \valid(image_context_get_sections (Context) + (0 .. PeCommon->FileHeader.NumberOfSections - 1));

  /*@ assigns Context->NumberOfSections;
    @ assigns Context->RelocsStripped;
    @ assigns Context->Machine;
    @ assigns Context->TeStrippedOffset;
    @ assigns Context->RelocDirRva, Context->RelocDirSize;
    @
    @ ensures image_context_fields_correct_pe_common (Context, PeCommon);
    @ ensures 0 < Context->NumberOfSections;
  */
  {
    /*@ assigns Context->NumberOfSections;
      @ ensures Context->NumberOfSections == PeCommon->FileHeader.NumberOfSections;
    */
    Context->NumberOfSections = PeCommon->FileHeader.NumberOfSections;
    //
    // If there's no relocations, then make sure it's not a runtime driver.
    //
    /*@ assigns Context->RelocsStripped;
      @ ensures Context->RelocsStripped == (image_pe_common_relocs_stripped (PeCommon) ? TRUE : FALSE);
    */
    Context->RelocsStripped =
      (
        PeCommon->FileHeader.Characteristics & EFI_IMAGE_FILE_RELOCS_STRIPPED
      ) != 0;

    /*@ assigns Context->Machine;
      @ ensures Context->Machine == PeCommon->FileHeader.Machine;
    */
    Context->Machine = PeCommon->FileHeader.Machine;

    //@ assert Context->TeStrippedOffset == 0;
    ASSERT (Context->TeStrippedOffset == 0);

    /*@ requires EFI_IMAGE_DIRECTORY_ENTRY_BASERELOC < NumberOfRvaAndSizes ==>
      @            \valid(RelocDir);
      @ assigns Context->RelocDirRva, Context->RelocDirSize;
      @ ensures image_context_reloc_dir_exists (Context) ==>
      @           Context->RelocDirRva  == image_context_get_reloc_dir (Context)->VirtualAddress &&
      @           Context->RelocDirSize == image_context_get_reloc_dir (Context)->Size;
      @ ensures !image_context_reloc_dir_exists (Context) ==>
      @           Context->RelocDirRva  == 0 &&
      @           Context->RelocDirSize == 0;
    */
    if (EFI_IMAGE_DIRECTORY_ENTRY_BASERELOC < NumberOfRvaAndSizes) {
      /*@ assert (Context->ImageType == ImageTypePe32 ==>
        @          EFI_IMAGE_DIRECTORY_ENTRY_BASERELOC < Pe32->NumberOfRvaAndSizes) &&
        @        (Context->ImageType == ImageTypePe32Plus ==>
        @          EFI_IMAGE_DIRECTORY_ENTRY_BASERELOC < Pe32Plus->NumberOfRvaAndSizes);
      */

      //@ assert image_context_reloc_dir_exists (Context);

      /*@ assigns Context->RelocDirRva;
        @ ensures Context->RelocDirRva == image_context_get_reloc_dir (Context)->VirtualAddress;
      */
      Context->RelocDirRva  = RelocDir->VirtualAddress;

      /*@ assigns Context->RelocDirSize;
        @ ensures Context->RelocDirSize == image_context_get_reloc_dir (Context)->Size;
      */
      Context->RelocDirSize = RelocDir->Size;
    } else {
      /*@ assert (Context->ImageType == ImageTypePe32 ==>
        @          EFI_IMAGE_DIRECTORY_ENTRY_BASERELOC >= Pe32->NumberOfRvaAndSizes) &&
        @        (Context->ImageType == ImageTypePe32Plus ==>
        @          EFI_IMAGE_DIRECTORY_ENTRY_BASERELOC >= Pe32Plus->NumberOfRvaAndSizes);
      */
      //@ assert !image_context_reloc_dir_exists (Context);
      //@ assert Context->RelocDirRva == 0 && Context->RelocDirSize == 0;
      ASSERT (Context->RelocDirRva == 0 && Context->RelocDirSize == 0);
    }
  }

  if (EFI_IMAGE_DIRECTORY_ENTRY_SECURITY < NumberOfRvaAndSizes) {
    Context->SecDirRva  = SecDir->VirtualAddress;
    Context->SecDirSize = SecDir->Size;

    Result = BaseOverflowAddU32 (
      Context->SecDirRva,
      Context->SecDirSize,
      &SecDirEnd
      );
    if (Result || SecDirEnd > FileSize) {
      ASSERT (FALSE);
      return RETURN_UNSUPPORTED;
    }

    if (!IS_ALIGNED (Context->SecDirRva, OC_ALIGNOF (WIN_CERTIFICATE))
     || (Context->SecDirSize != 0 && Context->SecDirSize < sizeof (WIN_CERTIFICATE))) {
       ASSERT (FALSE);
      return RETURN_UNSUPPORTED;
    }
  } else {
    ASSERT (Context->SecDirRva == 0 && Context->SecDirSize == 0);
  }

  /*@ assigns StartAddress, MinSizeOfImage;
    @ ensures \let Sections = (EFI_IMAGE_SECTION_HEADER *) ((char *) Context->FileBuffer + Context->SectionsOffset);
    @         Status == RETURN_SUCCESS <==>
    @           image_sects_sane (Sections, PeCommon->FileHeader.NumberOfSections, Context->SizeOfHeaders, Context->SectionAlignment, Context->TeStrippedOffset, FileSize, Context->ImageType);
    @ ensures \let Sections = (EFI_IMAGE_SECTION_HEADER *) ((char *) Context->FileBuffer + Context->SectionsOffset);
    @         Status == RETURN_SUCCESS ==>
    @           StartAddress == image_loaded_hdr_virtual_size (Sections, Context->SizeOfHeaders, Context->SectionAlignment) &&
    @           MinSizeOfImage == (!PcdGetBool (PcdImageLoaderTolerantLoad) ?
    @             align_up (image_sect_top (&Sections[PeCommon->FileHeader.NumberOfSections - 1]), Context->SectionAlignment) :
    @             image_sect_top (&Sections[PeCommon->FileHeader.NumberOfSections - 1]));
    @
    @ ensures Status == RETURN_SUCCESS ==>
    @           \let Sections = image_context_get_sections (Context);
    @           (\forall integer i; 0 <= i < PeCommon->FileHeader.NumberOfSections ==>
    @             image_sect_top (Sections + i) <= MinSizeOfImage);
  */
  Status = InternalVerifySections (
             Context,
             FileSize,
             &StartAddress,
             &MinSizeOfImage
             );

  /*@ assigns \nothing;
    @ ensures \let Sections = (EFI_IMAGE_SECTION_HEADER *) ((char *) Context->FileBuffer + Context->SectionsOffset);
    @         image_sects_sane (Sections, PeCommon->FileHeader.NumberOfSections, Context->SizeOfHeaders, Context->SectionAlignment, Context->TeStrippedOffset, FileSize, Context->ImageType) &&
    @         (Context->ImageType == ImageTypePe32 ==>
    @           StartAddress == image_loaded_hdr_virtual_size (Sections, Pe32->SizeOfHeaders, Pe32->SectionAlignment) &&
    @           MinSizeOfImage == image_pe32_get_min_SizeOfImage ((char *) Context->FileBuffer, Context->ExeHdrOffset)) &&
    @         (Context->ImageType == ImageTypePe32Plus ==>
    @           StartAddress == image_loaded_hdr_virtual_size (Sections, Pe32Plus->SizeOfHeaders, Pe32Plus->SectionAlignment) &&
    @           MinSizeOfImage == image_pe32plus_get_min_SizeOfImage ((char *) Context->FileBuffer, Context->ExeHdrOffset));
    @ ensures \let Sections = image_context_get_sections (Context);
    @         \forall integer i; 0 <= i < PeCommon->FileHeader.NumberOfSections ==>
    @           0 < Sections[i].SizeOfRawData ==>
    @             \valid ((char *) Context->FileBuffer + ((Sections[i].PointerToRawData - Context->TeStrippedOffset) .. (Sections[i].PointerToRawData - Context->TeStrippedOffset) + Sections[i].SizeOfRawData - 1));
    @ ensures \let Sections = image_context_get_sections (Context);
    @         \forall integer i; 0 <= i < PeCommon->FileHeader.NumberOfSections  ==>
    @           0 == Sections[i].SizeOfRawData ==>
    @             \valid ((char *) Context->FileBuffer + ((Sections[i].PointerToRawData - Context->TeStrippedOffset) .. (Sections[i].PointerToRawData - Context->TeStrippedOffset) + Sections[i].SizeOfRawData - 1));
    @ ensures \let Sections = image_context_get_sections (Context);
    @         \forall integer i; 0 <= i < PeCommon->FileHeader.NumberOfSections ==>
    @           image_sect_top (Sections + i) <= MinSizeOfImage;
  */
  if (Status != RETURN_SUCCESS) {
    ASSERT_EFI_ERROR (Status);
    /*@ assert \let Sections = (EFI_IMAGE_SECTION_HEADER *) ((char *) Context->FileBuffer + Context->SectionsOffset);
      @        !image_sects_sane (Sections, PeCommon->FileHeader.NumberOfSections, Context->SizeOfHeaders, Context->SectionAlignment, 0, FileSize, Context->ImageType);
    */
    //@ assert !valid_pe ((char *) Context->FileBuffer, Context->ExeHdrOffset, FileSize);
    return Status;
  }

  /*@ assert \let Sections = image_context_get_sections (Context);
    @        \forall integer i; 0 <= i < PeCommon->FileHeader.NumberOfSections  ==>
    @          \valid ((char *) Context->FileBuffer + ((Sections[i].PointerToRawData - Context->TeStrippedOffset) .. (Sections[i].PointerToRawData - Context->TeStrippedOffset) + Sections[i].SizeOfRawData - 1));
  */
  //
  // Ensure SizeOfImage is equal to the top of the image's virtual space.
  //
  /*@ assigns \nothing;
    @ ensures MinSizeOfImage <= Context->SizeOfImage;
    @ ensures image_sects_in_image (Context);
  */
  if (MinSizeOfImage > Context->SizeOfImage) {
    DEBUG ((DEBUG_WARN, "SOI %u vs %u\n", MinSizeOfImage, Context->SizeOfImage));
    /*@ assert \let Sections = (EFI_IMAGE_SECTION_HEADER *) ((char *) Context->FileBuffer + Context->SectionsOffset);
      @        (Context->ImageType == ImageTypePe32 ==>
      @          !(image_pe32_get_min_SizeOfImage ((char *) Context->FileBuffer, Context->ExeHdrOffset) <= Pe32->SizeOfImage)) &&
      @        (Context->ImageType == ImageTypePe32Plus ==>
      @          !(image_pe32plus_get_min_SizeOfImage ((char *) Context->FileBuffer, Context->ExeHdrOffset) <= Pe32Plus->SizeOfImage));
    */
    //@ assert !valid_pe ((char *) Context->FileBuffer, Context->ExeHdrOffset, FileSize);
    ASSERT (FALSE);
    return RETURN_UNSUPPORTED;
  }

  /*@ assigns Status;
    @ ensures Status == RETURN_SUCCESS <==>
    @           image_context_reloc_info_sane (Context);
    @ ensures Context->ImageType == ImageTypePe32 ==>
    @          (Status == RETURN_SUCCESS <==>
    @            image_pe32_reloc_info_valid ((char *) Context->FileBuffer, Context->ExeHdrOffset));
    @ ensures Context->ImageType == ImageTypePe32Plus ==>
    @          (Status == RETURN_SUCCESS <==>
    @            image_pe32plus_reloc_info_valid ((char *) Context->FileBuffer, Context->ExeHdrOffset));
  */
  Status = InternalValidateRelocInfo (Context, StartAddress);
  ASSERT_EFI_ERROR (Status);

  /*@ assert Status == RETURN_SUCCESS ==>
    @          valid_pe ((char *) Context->FileBuffer, Context->ExeHdrOffset, FileSize);
  */

  return Status;
}

RETURN_STATUS
PeCoffInitializeContext (
  OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  IN  CONST VOID             *FileBuffer,
  IN  UINT32                 FileSize
  )
{
  RETURN_STATUS               Status;
  CONST EFI_IMAGE_DOS_HEADER *DosHdr;

  ASSERT (Context != NULL);
  ASSERT (FileBuffer != NULL || FileSize == 0);

  /*@ assigns *Context;
    @ ensures Context->ExeHdrOffset == 0;
    @ ensures Context->SizeOfImageDebugAdd == 0;
    @ ensures Context->TeStrippedOffset == 0;
    @ ensures Context->RelocDirRva == 0;
    @ ensures Context->RelocDirSize == 0;
  */
  ZeroMem (Context, sizeof (*Context));

  /*@ assigns \nothing;
    @ ensures image_signature_dos ((char *) FileBuffer, FileSize) ==>
    @           \valid ((EFI_IMAGE_DOS_HEADER *) ((char *) FileBuffer + 0));
    @ ensures \let ExeHdrOffset = image_exe_hdr_offset ((char *) FileBuffer, FileSize);
    @         image_te_file_hdrs_validity ((char *) FileBuffer, FileSize) &&
    @         image_pe32_file_hdrs_validity ((char *) FileBuffer, ExeHdrOffset, FileSize) &&
    @         image_pe32plus_file_hdrs_validity ((char *) FileBuffer, ExeHdrOffset, FileSize);
  */
  //@ ghost AvFlagRawFile (FileBuffer, FileSize);

  /*@ assigns Context->FileBuffer;
    @ ensures Context->FileBuffer == FileBuffer;
    @ ensures image_context_FileBuffer_sane (Context);
  */
  Context->FileBuffer = FileBuffer;

  //@ assert pointer_aligned (FileBuffer, AV_ALIGNOF (UINT16));
  //
  // Check whether the DOS Image Header is present.
  //
  /*@ assigns DosHdr, Status;
    @ assigns Context->ExeHdrOffset;
    @ assigns Context->ImageType;
    @ assigns Context->SectionsOffset;
    @ assigns Context->NumberOfSections;
    @ assigns Context->AddressOfEntryPoint;
    @ assigns Context->RelocsStripped;
    @ assigns Context->SectionAlignment;
    @ assigns Context->TeStrippedOffset;
    @ assigns Context->SizeOfHeaders;
    @ assigns Context->SizeOfImage;
    @ assigns Context->RelocDirRva;
    @ assigns Context->RelocDirSize;
    @ assigns Context->ImageBase;
    @ assigns Context->Subsystem;
    @ assigns Context->Machine;
    @
    @ ensures Context->ExeHdrOffset == image_exe_hdr_offset ((char *) FileBuffer, FileSize);
    @ ensures image_signature_dos ((char *) FileBuffer, FileSize) ==>
    @           image_dos_sane ((char *) FileBuffer, FileSize);
    @ ensures !image_signature_te ((char *) FileBuffer, FileSize);
  */
  if (FileSize >= sizeof (*DosHdr)
   && READ_ALIGNED_16 (FileBuffer) == EFI_IMAGE_DOS_SIGNATURE) {
    //@ assert \valid ((EFI_IMAGE_DOS_HEADER *) ((char *) FileBuffer + 0));

    /*@ assigns DosHdr;
      @ ensures DosHdr == (EFI_IMAGE_DOS_HEADER *) ((char *) FileBuffer + 0);
      @ ensures \valid(DosHdr);
    */
    DosHdr = (CONST EFI_IMAGE_DOS_HEADER *) (CONST VOID *) (
               (CONST CHAR8 *) FileBuffer + 0
               );
    //
    // When the DOS Image Header is present, verify the offset and
    // retrieve the size of the executable image.
    //
    /*@ assigns \nothing;
      @ ensures image_dos_sane ((char *) FileBuffer, FileSize);
    */
    if (sizeof (EFI_IMAGE_DOS_HEADER) > DosHdr->e_lfanew
     || DosHdr->e_lfanew > FileSize) {
      //@ assert !image_dos_sane ((char *) FileBuffer, FileSize);
      ASSERT (FALSE);
      return RETURN_UNSUPPORTED;
    }

    /*@ assigns Context->ExeHdrOffset;
      @ ensures Context->ExeHdrOffset == image_exe_hdr_offset ((char *) FileBuffer, FileSize);
    */
    Context->ExeHdrOffset = DosHdr->e_lfanew;
  } else {
    //
    // If the DOS Image Header is not present, assume the Image starts with the
    // Executable Header.
    //
    //@ assert Context->ExeHdrOffset == 0;
    //@ assert Context->ExeHdrOffset == image_exe_hdr_offset ((char *) FileBuffer, FileSize);

    /*@ assigns Status;
      @ assigns Context->ImageType;
      @ assigns Context->SectionsOffset;
      @ assigns Context->NumberOfSections;
      @ assigns Context->AddressOfEntryPoint;
      @ assigns Context->RelocsStripped;
      @ assigns Context->SectionAlignment;
      @ assigns Context->TeStrippedOffset;
      @ assigns Context->SizeOfHeaders;
      @ assigns Context->SizeOfImage;
      @ assigns Context->RelocDirRva;
      @ assigns Context->RelocDirSize;
      @ assigns Context->ImageBase;
      @ assigns Context->Subsystem;
      @ assigns Context->Machine;
      @ ensures !image_signature_te ((char *) FileBuffer, FileSize);
    */
    if (FileSize >= sizeof (EFI_TE_IMAGE_HEADER)
     && READ_ALIGNED_16 (FileBuffer) == EFI_TE_IMAGE_HEADER_SIGNATURE) {
      /*@ assert \let TeHdr = image_te_get_hdr ((char *) FileBuffer);
        @        \valid (TeHdr) &&
        @        (\let SectsOffset = image_te_get_sections_offset ((char *) FileBuffer);
        @        SectsOffset + TeHdr->NumberOfSections * sizeof (EFI_IMAGE_SECTION_HEADER) <= FileSize ==>
        @          image_te_sections_validity ((char *) FileBuffer));
      */

      /*@ requires image_signature_te ((char *) FileBuffer, FileSize);
        @
        @ assigns Status;
        @ assigns Context->ImageType;
        @ assigns Context->SectionsOffset;
        @ assigns Context->NumberOfSections;
        @ assigns Context->AddressOfEntryPoint;
        @ assigns Context->RelocsStripped;
        @ assigns Context->SectionAlignment;
        @ assigns Context->TeStrippedOffset;
        @ assigns Context->SizeOfHeaders;
        @ assigns Context->SizeOfImage;
        @ assigns Context->RelocDirRva;
        @ assigns Context->RelocDirSize;
        @ assigns Context->ImageBase;
        @ assigns Context->Subsystem;
        @ assigns Context->Machine;
        @
        @ ensures Status == RETURN_SUCCESS <==>
        @           image_signature_te ((char *) FileBuffer, FileSize) &&
        @           image_te_valid ((char *) FileBuffer, FileSize);
      */
      Status = InternalInitializeTe (Context, FileSize);
      ASSERT_EFI_ERROR (Status);

      //@ assigns \nothing;
      if (PcdGetBool (PcdImageLoaderSupportDebug) && Status == RETURN_SUCCESS) {
        PeCoffLoaderRetrieveCodeViewInfo (Context, FileSize);
      }

      return Status;
    }
  }
  //
  // Use Signature to determine and handle the image format (PE32(+) / TE).
  //
  /*@ assigns \nothing;
    @ ensures FileSize - Context->ExeHdrOffset >= sizeof (EFI_IMAGE_NT_HEADERS_COMMON_HDR) + sizeof (UINT16);
  */
  if (FileSize - Context->ExeHdrOffset < sizeof (EFI_IMAGE_NT_HEADERS_COMMON_HDR) + sizeof (UINT16)) {
    //@ assert FileSize - Context->ExeHdrOffset < sizeof (EFI_IMAGE_NT_HEADERS_COMMON_HDR) + sizeof (UINT16);
    //@ assert !image_signature_pe ((char *) FileBuffer, Context->ExeHdrOffset, FileSize);
    ASSERT (FALSE);
    return RETURN_UNSUPPORTED;
  }

  /*@ assigns \nothing;
    @ ensures is_aligned_32 (Context->ExeHdrOffset, AV_ALIGNOF (EFI_IMAGE_NT_HEADERS_COMMON_HDR));
  */
  if (!IS_ALIGNED (Context->ExeHdrOffset, OC_ALIGNOF (EFI_IMAGE_NT_HEADERS_COMMON_HDR))) {
    //@ assert !is_aligned_32 (Context->ExeHdrOffset, AV_ALIGNOF (EFI_IMAGE_NT_HEADERS_COMMON_HDR));
    //@ assert !image_signature_pe ((char *) FileBuffer, Context->ExeHdrOffset, FileSize);
    ASSERT (FALSE);
    return RETURN_UNSUPPORTED;
  }

  STATIC_ASSERT (
    OC_ALIGNOF (UINT32) <= OC_ALIGNOF (EFI_IMAGE_NT_HEADERS_COMMON_HDR),
    "The following access may be performed unaligned"
    );

  /*@ assert (is_aligned_N (Context->ExeHdrOffset, AV_ALIGNOF (EFI_IMAGE_NT_HEADERS_COMMON_HDR)) ==>
    @          is_aligned_N (Context->ExeHdrOffset, AV_ALIGNOF (UINT32))) &&
    @        (is_aligned_N (Context->ExeHdrOffset, AV_ALIGNOF (UINT32)) ==>
    @          pointer_aligned ((char *) FileBuffer + Context->ExeHdrOffset, AV_ALIGNOF (UINT32)));
  */
  //@ assert pointer_aligned ((char *) FileBuffer + Context->ExeHdrOffset, AV_ALIGNOF (UINT32));
  //
  // Ensure the Image Executable Header has a PE signature.
  //
  /*@ assigns \nothing;
    @ ensures uint32_from_char ((char *) FileBuffer + Context->ExeHdrOffset) == EFI_IMAGE_NT_SIGNATURE;
  */
  if (READ_ALIGNED_32 ((CONST CHAR8 *) FileBuffer + Context->ExeHdrOffset) != EFI_IMAGE_NT_SIGNATURE) {
    //@ assert uint32_from_char ((char *) FileBuffer + Context->ExeHdrOffset) != EFI_IMAGE_NT_SIGNATURE;
    //@ assert !image_signature_pe ((char *) FileBuffer, Context->ExeHdrOffset, FileSize);
    ASSERT (FALSE);
    return RETURN_UNSUPPORTED;
  }

  /*@ requires image_signature_pe ((char *) FileBuffer, Context->ExeHdrOffset, FileSize);
    @
    @ assigns Status;
    @ assigns Context->ImageType;
    @ assigns Context->SectionsOffset;
    @ assigns Context->NumberOfSections;
    @ assigns Context->AddressOfEntryPoint;
    @ assigns Context->RelocsStripped;
    @ assigns Context->SectionAlignment;
    @ assigns Context->TeStrippedOffset;
    @ assigns Context->SizeOfHeaders;
    @ assigns Context->SizeOfImage;
    @ assigns Context->RelocDirRva;
    @ assigns Context->RelocDirSize;
    @ assigns Context->ImageBase;
    @ assigns Context->Subsystem;
    @ assigns Context->Machine;
    @
    @ ensures Status == RETURN_SUCCESS <==>
    @           image_signature_pe ((char *) FileBuffer, Context->ExeHdrOffset, FileSize) &&
    @           valid_pe ((char *) FileBuffer, Context->ExeHdrOffset, FileSize);
  */
  Status = InternalInitializePe (Context, FileSize);
  ASSERT_EFI_ERROR (Status);
  //
  // If debugging is enabled, retrieve information on the debug data.
  //
  //@ assigns \nothing;
  if (PcdGetBool (PcdImageLoaderSupportDebug) && Status == RETURN_SUCCESS) {
    PeCoffLoaderRetrieveCodeViewInfo (Context, FileSize);
  }

  return Status;
}
