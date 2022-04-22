/** @file
  Implements APIs to verify the Authenticode Signature of PE/COFF Images.

  Portions copyright (c) 2006 - 2019, Intel Corporation. All rights reserved.<BR>
  Portions Copyright (c) 2016, Hewlett Packard Enterprise Development LP. All rights reserved.<BR>
  Copyright (c) 2020, Marvin Häuser. All rights reserved.<BR>
  Copyright (c) 2020, Vitaly Cheptsov. All rights reserved.<BR>
  Copyright (c) 2020, ISP RAS. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-3-Clause
**/

#include "BaseOverflow.h"
#include "BasePeCoffLibInternals.h"

#include "PeCoffHash.h"
#include "ProcessorBind.h"

#include <Library/MemoryAllocationLib.h>

#ifndef PRODUCTION
#include "AvSectionSort.h"
#endif

//
// TODO: Import Authenticode fixes and improvements.
//

/**
  Hashes the Image Section data in ascending order of raw file apprearance.

  @param[in]     Context      The context describing the Image. Must have been
                              initialised by PeCoffInitializeContext().
  @param[in]     HashUpdate   The data hashing function.
  @param[in,out] HashContext  The context of the current hash.

  @returns  Whether hashing has been successful.
**/
/*@ requires \valid(Context);
  @ requires \typeof(Context->FileBuffer) <: \type(char *);
  @ requires 0 < Context->NumberOfSections;
  @ requires Context->TeStrippedOffset == 0;
  @
  @ requires \let Sections = (EFI_IMAGE_SECTION_HEADER *) ((char *) Context->FileBuffer + Context->SectionsOffset);
  @          \valid(Sections + (0 .. Context->NumberOfSections - 1)) &&
  @          (\forall integer i; 0 <= i < Context->NumberOfSections ==>
  @             Sections[i].PointerToRawData + Sections[i].SizeOfRawData <= MAX_UINT32 &&
  @             \valid((char *) Context->FileBuffer + ((Sections[i].PointerToRawData - Context->TeStrippedOffset) .. (Sections[i].PointerToRawData - Context->TeStrippedOffset) + Sections[i].SizeOfRawData - 1)));
  @
  @ requires HashContext != \null;
*/
STATIC
BOOLEAN
InternalHashSections (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
#ifdef PRODUCTION
  IN     PE_COFF_HASH_UPDATE          HashUpdate,
#endif
  IN OUT VOID                         *HashContext
  )
{
  BOOLEAN                        Result;

  CONST EFI_IMAGE_SECTION_HEADER *Sections;
  CONST EFI_IMAGE_SECTION_HEADER **SortedSections;
  UINT16                         SectIndex;
  UINT16                         SectionPos;
  UINT32                         SectionTop;
  //
  // 9. Build a temporary table of pointers to all of the section headers in the
  //   image. The NumberOfSections field of COFF File Header indicates how big
  //   the table should be. Do not include any section headers in the table
  //   whose SizeOfRawData field is zero.
  //
  /*@ assigns SortedSections;
    @ ensures SortedSections != \null ==>
    @           \valid(SortedSections + (0 .. Context->NumberOfSections - 1));
  */
  SortedSections = AllocatePool (
                     (UINT32) Context->NumberOfSections * sizeof (*SortedSections)
                     );

  /*@ assigns \nothing;
    @ ensures \valid(SortedSections + (0 .. Context->NumberOfSections - 1));
  */
  if (SortedSections == NULL) {
    return FALSE;
  }

  /*@ ensures Sections == (EFI_IMAGE_SECTION_HEADER *) ((char *) Context->FileBuffer + Context->SectionsOffset);
    @ ensures \valid(Sections + (0 .. Context->NumberOfSections - 1)) &&
    @         (\forall integer i; 0 <= i < Context->NumberOfSections ==>
    @            Sections[i].PointerToRawData + Sections[i].SizeOfRawData <= MAX_UINT32 &&
    @            \valid((char *) Context->FileBuffer + ((Sections[i].PointerToRawData - Context->TeStrippedOffset) .. (Sections[i].PointerToRawData - Context->TeStrippedOffset) + Sections[i].SizeOfRawData - 1)));
  */
  Sections = (CONST EFI_IMAGE_SECTION_HEADER *) (CONST VOID *) (
               (CONST CHAR8 *) Context->FileBuffer + Context->SectionsOffset
               );
  //
  // 10. Using the PointerToRawData field (offset 20) in the referenced
  //     SectionHeader structure as a key, arrange the table's elements in
  //     ascending order. In other words, sort the section headers in ascending
  //     order according to the disk-file offset of the sections.
  //
  /*@ assigns SortedSections[0];
    @ ensures SortedSections[0] == Sections + 0;
  */
  SortedSections[0] = &Sections[0];
  //
  // Perform Insertion Sort.
  //
  /*@ loop assigns SectIndex, SectionPos, SortedSections[0 .. Context->NumberOfSections - 1];
    @
    @ loop invariant 1 <= SectIndex <= Context->NumberOfSections;
    @
    @ loop invariant SortedSects(SortedSections, SectIndex);
    @
    @ loop invariant \forall integer i; 0 <= i < SectIndex ==>
    @                  \exists integer j; 0 <= j < SectIndex &&
    @                    SortedSections[j] == Sections + i;
    @
    @ loop invariant \forall integer i; 0 <= i < SectIndex ==>
    @                  \valid(SortedSections[i]) &&
    @                  SortedSections[i]->PointerToRawData + SortedSections[i]->SizeOfRawData <= MAX_UINT32 &&
    @                  \valid((char *) Context->FileBuffer + ((SortedSections[i]->PointerToRawData - Context->TeStrippedOffset) .. (SortedSections[i]->PointerToRawData - Context->TeStrippedOffset) + SortedSections[i]->SizeOfRawData - 1));
    @
    @ loop variant Context->NumberOfSections - SectIndex;
  */
  for (SectIndex = 1; SectIndex < Context->NumberOfSections; ++SectIndex) {
    /*@ loop assigns SectionPos, SortedSections[1 .. Context->NumberOfSections - 1];
      @
      @ loop invariant 0 <= SectionPos <= SectIndex;
      @ loop invariant 0 < SectionPos ==> 0 <= SectionPos - 1 < SectIndex;
      @
      @ loop invariant SortedSects(SortedSections, SectIndex);
      @ loop invariant SectionPos < SectIndex ==>
      @                  SortedSects(SortedSections, SectIndex + 1);
      @
      @ loop invariant \forall integer i; SectionPos < i <= SectIndex ==>
      @                  Sections[SectIndex].PointerToRawData <= SortedSections[i]->PointerToRawData;
      @
      @ loop invariant \forall integer i; 0 <= i < SectIndex ==>
      @                  \exists integer j; 0 <= j <= SectIndex && j != SectionPos &&
      @                    SortedSections[j] == Sections + i;
      @
      @ loop invariant \forall integer i; 0 <= i < SectIndex ==>
      @                  \valid(SortedSections[i]) &&
      @                  SortedSections[i]->PointerToRawData + SortedSections[i]->SizeOfRawData <= MAX_UINT32 &&
      @                  \valid((char *) Context->FileBuffer + ((SortedSections[i]->PointerToRawData - Context->TeStrippedOffset) .. (SortedSections[i]->PointerToRawData - Context->TeStrippedOffset) + SortedSections[i]->SizeOfRawData - 1));
      @ loop invariant SectionPos < SectIndex ==>
      @                  \forall integer i; 0 <= i <= SectIndex ==>
      @                    \valid(SortedSections[i]) &&
      @                    SortedSections[i]->PointerToRawData + SortedSections[i]->SizeOfRawData <= MAX_UINT32 &&
      @                    \valid((char *) Context->FileBuffer + ((SortedSections[i]->PointerToRawData - Context->TeStrippedOffset) .. (SortedSections[i]->PointerToRawData - Context->TeStrippedOffset) + SortedSections[i]->SizeOfRawData - 1));
      @
      @ loop invariant 0 < SectionPos ==>
      @                  \valid(SortedSections[SectionPos - 1]);
      @
      @ loop variant SectionPos;
    */
    for (SectionPos = SectIndex;
     0 < SectionPos
     && SortedSections[SectionPos - 1]->PointerToRawData > Sections[SectIndex].PointerToRawData;
     --SectionPos) {
      /*@ requires 0 < SectionPos <= SectIndex;
        @
        @ requires \valid(SortedSections[SectionPos - 1]) &&
        @         SortedSections[SectionPos - 1]->PointerToRawData + SortedSections[SectionPos - 1]->SizeOfRawData <= MAX_UINT32 &&
        @          \valid((char *) Context->FileBuffer + ((SortedSections[SectionPos - 1]->PointerToRawData - Context->TeStrippedOffset) .. (SortedSections[SectionPos - 1]->PointerToRawData - Context->TeStrippedOffset) + SortedSections[SectionPos - 1]->SizeOfRawData - 1));
        @
        @ requires \forall integer i; 0 <= i <= SectionPos - 1 ==>
        @            SortedSections[i]->PointerToRawData <= SortedSections[SectionPos - 1]->PointerToRawData;
        @ requires \forall integer i; SectionPos - 1 <= i < SectIndex ==>
        @            SortedSections[SectionPos - 1]->PointerToRawData <= SortedSections[i]->PointerToRawData;
        @ requires SectionPos < SectIndex ==>
        @            \forall integer i; SectionPos - 1 <= i <= SectIndex ==>
        @              SortedSections[SectionPos - 1]->PointerToRawData <= SortedSections[i]->PointerToRawData;
        @
        @ assigns SortedSections[SectionPos];
        @
        @ ensures sects_all_but_one_preserved{Old,Post}(SortedSections, SectIndex+1, SectionPos);
        @
        @ ensures \forall integer i; 0 <= i <= SectionPos ==>
        @           SortedSections[i]->PointerToRawData <= SortedSections[SectionPos]->PointerToRawData;
        @ ensures \forall integer i; SectionPos <= i <= SectIndex ==>
        @           SortedSections[SectionPos]->PointerToRawData <= SortedSections[i]->PointerToRawData;
        @
        @ ensures SortedSections[SectionPos] == SortedSections[SectionPos - 1];
        @
        @ ensures \valid(SortedSections[SectionPos]) &&
        @         SortedSections[SectionPos]->PointerToRawData + SortedSections[SectionPos]->SizeOfRawData <= MAX_UINT32 &&
        @         \valid((char *) Context->FileBuffer + ((SortedSections[SectionPos]->PointerToRawData - Context->TeStrippedOffset) .. (SortedSections[SectionPos]->PointerToRawData - Context->TeStrippedOffset) + SortedSections[SectionPos]->SizeOfRawData - 1));
      */
      SortedSections[SectionPos] = SortedSections[SectionPos - 1];

      //@ assert SortedSects(SortedSections, SectIndex);

      //@ assert SortedSects(SortedSections, SectIndex + 1);

      /*@ assert \forall integer i; 0 <= i < SectIndex ==>
        @           \exists integer j; 0 <= j <= SectIndex && j != SectionPos &&
        @             SortedSections[j] == Sections + i;
      */

      /*@ assert \forall integer i; 0 <= i < SectIndex ==>
        @          (\exists integer j; 0 <= j <= SectIndex && j != SectionPos &&
        @             SortedSections[j] == Sections + i) &&
        @          ((\exists integer j; 0 <= j <= SectIndex && j != SectionPos &&
        @             SortedSections[j] == Sections + i) ==>
        @             (\exists integer j; 0 <= j <= SectIndex && j != SectionPos - 1 &&
        @               SortedSections[j] == Sections + i));
      */

      /*@ assert \forall integer i; 0 <= i < SectIndex ==>
        @           \exists integer j; 0 <= j <= SectIndex && j != SectionPos - 1 &&
        @             SortedSections[j] == Sections + i;
      */

      /*@ assert \forall integer i; 0 <= i <= SectIndex ==>
        @          \valid(SortedSections[i]) &&
        @          SortedSections[i]->PointerToRawData + SortedSections[i]->SizeOfRawData <= MAX_UINT32 &&
        @          \valid((char *) Context->FileBuffer + ((SortedSections[i]->PointerToRawData - Context->TeStrippedOffset) .. (SortedSections[i]->PointerToRawData - Context->TeStrippedOffset) + SortedSections[i]->SizeOfRawData - 1));
      */
    }

    /*@ assert \forall integer i; 0 <= i < SectionPos ==>
      @          SortedSections[i]->PointerToRawData <= SortedSections[SectionPos - 1]->PointerToRawData <= Sections[SectIndex].PointerToRawData;
    */

    /*@ assert \forall integer i; 0 <= i < SectionPos ==>
      @          SortedSections[i]->PointerToRawData <= Sections[SectIndex].PointerToRawData;
    */

    /*@ requires 0 <= SectionPos <= SectIndex;
      @
      @ requires \forall integer i; 0 <= i < SectionPos ==>
      @            SortedSections[i]->PointerToRawData <= Sections[SectIndex].PointerToRawData;
      @ requires \forall integer i; SectionPos < i <= SectIndex ==>
      @            Sections[SectIndex].PointerToRawData <= SortedSections[i]->PointerToRawData;
      @
      @ assigns SortedSections[SectionPos];
      @
      @ ensures SortedSections[SectionPos] == Sections + SectIndex;
      @
      @ ensures sects_all_but_one_preserved{Old,Post}(SortedSections, SectIndex+1, SectionPos);
      @
      @ ensures \forall integer i; 0 <= i <= SectionPos ==>
      @           SortedSections[i]->PointerToRawData <= SortedSections[SectionPos]->PointerToRawData;
      @ ensures \forall integer i; SectionPos <= i <= SectIndex ==>
      @           SortedSections[SectionPos]->PointerToRawData <= SortedSections[i]->PointerToRawData;
      @
      @ ensures \exists integer j; 0 <= j <= SectIndex &&
      @           SortedSections[j] == Sections + SectIndex;
      @
      @ ensures \valid(SortedSections[SectionPos]) &&
      @         SortedSections[SectionPos]->PointerToRawData + SortedSections[SectionPos]->SizeOfRawData <= MAX_UINT32 &&
      @         \valid((char *) Context->FileBuffer + ((SortedSections[SectionPos]->PointerToRawData - Context->TeStrippedOffset) .. (SortedSections[SectionPos]->PointerToRawData - Context->TeStrippedOffset) + SortedSections[SectionPos]->SizeOfRawData - 1));
    */
    SortedSections[SectionPos] = &Sections[SectIndex];

    //@ assert SortedSects(SortedSections, SectIndex);

    //@ assert SortedSects(SortedSections, SectIndex + 1);

    /*@ assert \forall integer i; 0 <= i < SectIndex ==>
      @          \exists integer j; 0 <= j <= SectIndex &&
      @            SortedSections[j] == Sections + i;
    */

    /*@ assert \forall integer i; 0 <= i <= SectIndex ==>
      @           \exists integer j; 0 <= j <= SectIndex &&
      @             SortedSections[j] == Sections + i;
    */

    /*@ assert \forall integer i; 0 <= i <= SectIndex ==>
      @          \valid(SortedSections[i]) &&
      @          SortedSections[i]->PointerToRawData + SortedSections[i]->SizeOfRawData <= MAX_UINT32 &&
      @          \valid((char *) Context->FileBuffer + ((SortedSections[i]->PointerToRawData - Context->TeStrippedOffset) .. (SortedSections[i]->PointerToRawData - Context->TeStrippedOffset) + SortedSections[i]->SizeOfRawData - 1));
    */
  }

  /*@ assigns Result;
    @ ensures Result;
  */
  Result = TRUE;

  /*@ assigns SectionTop;
    @ ensures PcdGetBool (PcdImageLoaderHashProhibitOverlap) ==>
                SectionTop == 0;
  */
  SectionTop = 0;

  // 13. Repeat steps 11 and 12 for all of the sections in the sorted table.
  //
  /*@ loop assigns SectIndex, Result, SectionTop;
    @
    @ loop invariant 0 <= SectIndex <= Context->NumberOfSections;
    @
    @ loop invariant Result;
    @
    @ loop invariant PcdGetBool (PcdImageLoaderHashProhibitOverlap) ==>
    @                  0 == SectIndex ==>
    @                    SectionTop == 0;
    @ loop invariant PcdGetBool (PcdImageLoaderHashProhibitOverlap) ==>
    @                  0 < SectIndex ==>
    @                    SectionTop == SortedSections[SectIndex - 1]->PointerToRawData + SortedSections[SectIndex - 1]->SizeOfRawData;
    @
    @ loop invariant PcdGetBool (PcdImageLoaderHashProhibitOverlap) ==>
    @                  \forall integer i; 0 <= i < SectIndex ==>
    @                    \forall integer j; 0 <= j < i ==>
    @                      (SortedSections[j]->PointerToRawData - Context->TeStrippedOffset) + SortedSections[j]->SizeOfRawData <= SortedSections[i]->PointerToRawData;
    @
    @ loop invariant \forall integer i; 0 <= i < Context->NumberOfSections ==>
    @                  \valid(SortedSections[i]) &&
    @                  SortedSections[i]->PointerToRawData + SortedSections[i]->SizeOfRawData <= MAX_UINT32 &&
    @                  \valid((char *) Context->FileBuffer + ((SortedSections[i]->PointerToRawData - Context->TeStrippedOffset) .. (SortedSections[i]->PointerToRawData - Context->TeStrippedOffset) + SortedSections[i]->SizeOfRawData - 1));
    @
    @ loop variant Context->NumberOfSections - SectIndex;
  */
  for (SectIndex = 0; SectIndex < Context->NumberOfSections; ++SectIndex) {
    /*@ requires Context->TeStrippedOffset == 0;
      @
      @ requires 0 < SectIndex ==>
      @            PcdGetBool (PcdImageLoaderHashProhibitOverlap) ==>
      @              SectionTop == SortedSections[SectIndex - 1]->PointerToRawData + SortedSections[SectIndex - 1]->SizeOfRawData;
      @
      @ assigns Result, SectionTop;
      @
      @ ensures Result;
      @
      @ ensures PcdGetBool (PcdImageLoaderHashProhibitOverlap) ==>
      @           \forall integer i; 0 <= i <= SectIndex ==>
      @             SortedSections[i]->PointerToRawData + SortedSections[i]->SizeOfRawData <= SectionTop;
      @
      @ ensures PcdGetBool (PcdImageLoaderHashProhibitOverlap) ==>
      @           \forall integer i; 0 <= i <= SectIndex ==>
      @             \forall integer j; 0 <= j < i ==>
      @               (SortedSections[j]->PointerToRawData - Context->TeStrippedOffset) + SortedSections[j]->SizeOfRawData <= SortedSections[i]->PointerToRawData;
      @
      @ ensures PcdGetBool (PcdImageLoaderHashProhibitOverlap) ==>
      @           SectionTop == SortedSections[SectIndex]->PointerToRawData + SortedSections[SectIndex]->SizeOfRawData;
    */
    if (PcdGetBool (PcdImageLoaderHashProhibitOverlap)) {
      /*@ assigns Result;
        @
        @ ensures Result;
        @
        @ ensures 0 < SectIndex ==>
        @           SortedSections[SectIndex - 1]->PointerToRawData + SortedSections[SectIndex - 1]->SizeOfRawData <= SortedSections[SectIndex]->PointerToRawData;
        @
        @ ensures \forall integer j; 0 <= j < SectIndex ==>
        @           (SortedSections[j]->PointerToRawData - Context->TeStrippedOffset) + SortedSections[j]->SizeOfRawData <= SectionTop <= SortedSections[SectIndex]->PointerToRawData;
      */
      if (SectionTop > SortedSections[SectIndex]->PointerToRawData) {
        Result = FALSE;
        break;
      }

      /*@ assert \forall integer j; 0 <= j < SectIndex ==>
        @           (SortedSections[j]->PointerToRawData - Context->TeStrippedOffset) + SortedSections[j]->SizeOfRawData <= SortedSections[SectIndex]->PointerToRawData;
      */

      /*@ assert \forall integer i; 0 <= i < SectIndex ==>
        @          \forall integer j; 0 <= j < i ==>
        @            (SortedSections[j]->PointerToRawData - Context->TeStrippedOffset) + SortedSections[j]->SizeOfRawData <= SortedSections[i]->PointerToRawData;
      */

      /*@ assert \forall integer i; 0 <= i <= SectIndex ==>
        @          \forall integer j; 0 <= j < i ==>
        @            (SortedSections[j]->PointerToRawData - Context->TeStrippedOffset) + SortedSections[j]->SizeOfRawData <= SortedSections[i]->PointerToRawData;
      */

      /*@ assigns SectionTop;
        @ ensures SectionTop == SortedSections[SectIndex]->PointerToRawData + SortedSections[SectIndex]->SizeOfRawData;
        @ ensures SortedSections[SectIndex]->PointerToRawData + SortedSections[SectIndex]->SizeOfRawData <= SectionTop;
      */
      SectionTop = SortedSections[SectIndex]->PointerToRawData + SortedSections[SectIndex]->SizeOfRawData;

      /*@ assert \forall integer i; 0 <= i <= SectIndex ==>
        @          SortedSections[i]->PointerToRawData + SortedSections[i]->SizeOfRawData <= SectionTop;
      */
    }
    //
    // 11. Walk through the sorted table, load the corresponding section into
    //     memory, and hash the entire section. Use the SizeOfRawData field in the
    //     SectionHeader structure to determine the amount of data to hash.
    //
    /*@ assigns Result;
      @ ensures Result;
    */
    if (SortedSections[SectIndex]->SizeOfRawData > 0) {
      /*@ requires Context->TeStrippedOffset == 0;
        @ assigns Result;
      */
      Result = HashUpdate (
                 HashContext,
                 (CONST CHAR8 *) Context->FileBuffer + SortedSections[SectIndex]->PointerToRawData,
                 SortedSections[SectIndex]->SizeOfRawData
                 );

      /*@ assigns \nothing;
        @ ensures Result;
      */
      if (!Result) {
        break;
      }
    }
  }

  FreePool (SortedSections);
  return Result;
}

BOOLEAN
PeCoffHashImage (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
#ifdef PRODUCTION
  IN     PE_COFF_HASH_UPDATE          HashUpdate,
#endif
  IN OUT VOID                         *HashContext
  )
{
  BOOLEAN                      Result;
  UINT32                       NumberOfRvaAndSizes;
  UINT32                       ChecksumOffset;
  UINT32                       SecurityDirOffset;
  UINT32                       CurrentOffset;
  UINT32                       HashSize;
  CONST EFI_IMAGE_NT_HEADERS32 *Pe32;
  CONST EFI_IMAGE_NT_HEADERS64 *Pe32Plus;
  //
  // Preconditions:
  // 1. Load the image header into memory.
  // 2. Initialize a hash algorithm context.
  //

  //
  // This step can be moved here because steps 1 to 5 do not modify the Image.
  //
  // 6. Get the Attribute Certificate Table address and size from the
  //    Certificate Table entry. For details, see section 5.7 of the PE/COFF
  //    specification.
  //
  /*@ requires image_context_type_valid (Context);
    @
    @ assigns Pe32, Pe32Plus, ChecksumOffset, SecurityDirOffset, NumberOfRvaAndSizes, Context->SectionsOffset, Context->NumberOfSections;
    @
    @ ensures Context->ImageType == ImageTypePe32 || Context->ImageType == ImageTypePe32Plus;
    @ ensures Context->TeStrippedOffset == 0;
    @ ensures ChecksumOffset + sizeof (UINT32) < image_hdr_raw_size (Context->SizeOfHeaders, Context->TeStrippedOffset);
    @
    @ ensures EFI_IMAGE_DIRECTORY_ENTRY_SECURITY < NumberOfRvaAndSizes ==>
    @           SecurityDirOffset + sizeof (EFI_IMAGE_DATA_DIRECTORY) <= image_hdr_raw_size (Context->SizeOfHeaders, Context->TeStrippedOffset);
  */
  switch (Context->ImageType) { /* LCOV_EXCL_BR_LINE */
    case ImageTypeTe:
      //
      // TE images are not to be signed, as they are supposed to only be part of
      // Firmware Volumes, which may be signed as a whole.
      //
      /*@ assigns \nothing;
        @ ensures Context->ImageType != ImageTypeTe;
      */
      return FALSE;

    case ImageTypePe32:
      /*@ assigns Pe32;
        @ ensures Pe32 == image_pe32_get_hdr ((char *) Context->FileBuffer, Context->ExeHdrOffset);
      */
      Pe32 = (CONST EFI_IMAGE_NT_HEADERS32 *) (CONST VOID *) (
               (CONST CHAR8 *) Context->FileBuffer + Context->ExeHdrOffset
               );

      /*@ assigns ChecksumOffset;
        @ ensures ChecksumOffset + sizeof (UINT32) < Context->ExeHdrOffset + sizeof (EFI_IMAGE_NT_HEADERS32) <= image_hdr_raw_size (Context->SizeOfHeaders, Context->TeStrippedOffset);
      */
      ChecksumOffset = Context->ExeHdrOffset + OFFSET_OF (EFI_IMAGE_NT_HEADERS32, CheckSum);

      /*@ assigns SecurityDirOffset;
        @ ensures EFI_IMAGE_DIRECTORY_ENTRY_SECURITY < Pe32->NumberOfRvaAndSizes ==>
        @           SecurityDirOffset + sizeof (EFI_IMAGE_DATA_DIRECTORY) <= Context->ExeHdrOffset + sizeof (EFI_IMAGE_NT_HEADERS32) + (EFI_IMAGE_DIRECTORY_ENTRY_SECURITY + 1) * sizeof (EFI_IMAGE_DATA_DIRECTORY) <= image_hdr_raw_size (Context->SizeOfHeaders, Context->TeStrippedOffset);
      */
      SecurityDirOffset = Context->ExeHdrOffset + (UINT32) OFFSET_OF (EFI_IMAGE_NT_HEADERS32, DataDirectory) +/*@%*/ (UINT32) (EFI_IMAGE_DIRECTORY_ENTRY_SECURITY * sizeof (EFI_IMAGE_DATA_DIRECTORY));

      /*@ assigns NumberOfRvaAndSizes;
        @ ensures NumberOfRvaAndSizes == Pe32->NumberOfRvaAndSizes;
      */
      NumberOfRvaAndSizes = Pe32->NumberOfRvaAndSizes;

      break;

    case ImageTypePe32Plus:
      /*@ assigns Pe32Plus;
        @ ensures Pe32Plus == image_pe32plus_get_hdr ((char *) Context->FileBuffer, Context->ExeHdrOffset);
      */
      Pe32Plus = (CONST EFI_IMAGE_NT_HEADERS64 *) (CONST VOID *) (
                   (CONST CHAR8 *) Context->FileBuffer + Context->ExeHdrOffset
                   );

      /*@ assigns ChecksumOffset;
        @ ensures ChecksumOffset + sizeof (UINT32) < Context->ExeHdrOffset + sizeof (EFI_IMAGE_NT_HEADERS64) <= image_hdr_raw_size (Context->SizeOfHeaders, Context->TeStrippedOffset);
      */
      ChecksumOffset = Context->ExeHdrOffset + OFFSET_OF (EFI_IMAGE_NT_HEADERS64, CheckSum);

      /*@ assigns SecurityDirOffset;
        @ ensures EFI_IMAGE_DIRECTORY_ENTRY_SECURITY < Pe32Plus->NumberOfRvaAndSizes ==>
        @           SecurityDirOffset + sizeof (EFI_IMAGE_DATA_DIRECTORY) <= Context->ExeHdrOffset + sizeof (EFI_IMAGE_NT_HEADERS64) + (EFI_IMAGE_DIRECTORY_ENTRY_SECURITY + 1) * sizeof (EFI_IMAGE_DATA_DIRECTORY) <= image_hdr_raw_size (Context->SizeOfHeaders, Context->TeStrippedOffset);
      */
      SecurityDirOffset = Context->ExeHdrOffset + (UINT32) OFFSET_OF (EFI_IMAGE_NT_HEADERS64, DataDirectory) +/*@%*/ (UINT32) (EFI_IMAGE_DIRECTORY_ENTRY_SECURITY * sizeof (EFI_IMAGE_DATA_DIRECTORY));

      /*@ assigns NumberOfRvaAndSizes;
        @ ensures NumberOfRvaAndSizes == Pe32Plus->NumberOfRvaAndSizes;
      */
      NumberOfRvaAndSizes = Pe32Plus->NumberOfRvaAndSizes;

      break;

  /* LCOV_EXCL_START */
    default:
      ASSERT (FALSE);
      return FALSE;
  }
  /* LCOV_EXCL_STOP */
  //
  // 3. Hash the image header from its base to immediately before the start of
  //    the checksum address, as specified in Optional Header Windows-Specific
  //    Fields.
  //
  /*@ requires 0 < ChecksumOffset;
    @ requires ChecksumOffset < image_hdr_raw_size (Context->SizeOfHeaders, Context->TeStrippedOffset);
    @ requires \valid((char *) Context->FileBuffer + (0 .. ChecksumOffset - 1));
    @
    @ assigns Result;
  */
  Result = HashUpdate (HashContext, Context->FileBuffer, ChecksumOffset);

  /*@ assigns \nothing;
    @ ensures Result;
  */
  if (!Result) {
    return FALSE;
  }
  //
  // 4. Skip over the checksum, which is a 4-byte field.
  //
  /*@ requires ChecksumOffset + sizeof (UINT32) < image_hdr_raw_size (Context->SizeOfHeaders, Context->TeStrippedOffset);
    @
    @ assigns CurrentOffset;
    @
    @ ensures CurrentOffset == ChecksumOffset + sizeof (UINT32);
    @ ensures CurrentOffset < image_hdr_raw_size (Context->SizeOfHeaders, Context->TeStrippedOffset);
  */
  CurrentOffset = ChecksumOffset + sizeof (UINT32);
  //
  // 5. Hash everything from the end of the checksum field to immediately before
  //    the start of the Certificate Table entry, as specified in Optional
  //    Header Data Directories.
  //
  //@ assigns HashSize, Result, CurrentOffset;
  if (EFI_IMAGE_DIRECTORY_ENTRY_SECURITY < NumberOfRvaAndSizes) {
    /*@ requires CurrentOffset < SecurityDirOffset;
      @
      @ assigns HashSize;
      @
      @ ensures HashSize == SecurityDirOffset - CurrentOffset;
      @ ensures CurrentOffset + HashSize <= image_hdr_raw_size (Context->SizeOfHeaders, Context->TeStrippedOffset);
    */
    HashSize = SecurityDirOffset - CurrentOffset;

    /*@ requires \valid((char *) Context->FileBuffer + (CurrentOffset .. CurrentOffset + HashSize - 1));
      @ assigns Result;
    */
    Result = HashUpdate (
               HashContext,
               (CONST CHAR8 *) Context->FileBuffer + CurrentOffset,
               HashSize
               );
    /*@ assigns \nothing;
      @ ensures Result;
    */
    if (!Result) {
      return FALSE;
    }
    //
    // Skip over the security directory. If no further directory exists, this
    // will point to the top of the directory.
    //
    /*@ requires SecurityDirOffset + sizeof (EFI_IMAGE_DATA_DIRECTORY) <= image_hdr_raw_size (Context->SizeOfHeaders, Context->TeStrippedOffset);

      @ assigns CurrentOffset;

      @ ensures CurrentOffset == SecurityDirOffset + sizeof (EFI_IMAGE_DATA_DIRECTORY);
      @ ensures CurrentOffset <= image_hdr_raw_size (Context->SizeOfHeaders, Context->TeStrippedOffset);
    */
    CurrentOffset = SecurityDirOffset + sizeof (EFI_IMAGE_DATA_DIRECTORY);
  }
  //
  // 7. Exclude the Certificate Table entry from the calculation and hash
  //    everything from the end of the Certificate Table entry to the end of
  //    image header, including Section Table (headers).The Certificate Table
  //    entry is 8 bytes long, as specified in Optional Header Data Directories.
  //
  /*@ requires CurrentOffset <= image_hdr_raw_size (Context->SizeOfHeaders, Context->TeStrippedOffset);
    @ assigns HashSize;
    @ ensures HashSize == image_hdr_raw_size (Context->SizeOfHeaders, Context->TeStrippedOffset) - CurrentOffset;
  */
  HashSize = Context->SizeOfHeaders - CurrentOffset;

  /*@ requires CurrentOffset + HashSize <= image_hdr_raw_size (Context->SizeOfHeaders, Context->TeStrippedOffset);
    @ requires \valid((char *) Context->FileBuffer + (CurrentOffset .. CurrentOffset + HashSize - 1));
    @ assigns Result;
  */
  Result = HashUpdate (
             HashContext,
             (CONST CHAR8 *) Context->FileBuffer + CurrentOffset,
             HashSize
             );

  /*@ assigns \nothing;
    @ ensures Result;
  */
  if (!Result) {
    return FALSE;
  }

  //@ assigns \nothing;
  return InternalHashSections (
           Context,
#ifdef PRODUCTION
           HashUpdate,
#endif
           HashContext
           );

  //
  // Please not that this implementation currently lacks the hashing of trailing
  // data.
  //

  //
  // This step must be performed by the caller after this routine succeeded.
  // 15. Finalize the hash algorithm context.
  //
}

// FIXME: optimise

RETURN_STATUS
PeCoffGetFirstCertificate (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  OUT    CONST WIN_CERTIFICATE         **Certificate
  )
{
  CONST WIN_CERTIFICATE *WinCertificate;

  if (Context->SecDirSize == 0) {
    return RETURN_NOT_FOUND;
  }

  WinCertificate = (CONST WIN_CERTIFICATE *) (CONST VOID *) (
    (CONST UINT8 *) Context->FileBuffer + Context->SecDirRva
    );
  if (WinCertificate->dwLength < sizeof (WIN_CERTIFICATE)
   || !IS_ALIGNED (WinCertificate->dwLength, OC_ALIGNOF (WIN_CERTIFICATE))
   || WinCertificate->dwLength > Context->SecDirSize) {
    return RETURN_UNSUPPORTED;
  }

  *Certificate = WinCertificate;
  return RETURN_SUCCESS;
}

RETURN_STATUS
PeCoffGetNextCertificate (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  OUT    CONST WIN_CERTIFICATE         **Certificate
  )
{
  BOOLEAN               Result;
  UINT32                CertOffset;
  UINT32                CertEnd;
  CONST WIN_CERTIFICATE *WinCertificate;

  WinCertificate = *Certificate;
  CertOffset  = (UINT32) ((UINTN) WinCertificate - Context->SecDirRva);
  CertOffset += WinCertificate->dwLength;
  if (CertOffset == Context->SecDirSize) {
    return RETURN_NOT_FOUND;
  }
  if (Context->SecDirSize - CertOffset < sizeof (WIN_CERTIFICATE)) {
    return RETURN_UNSUPPORTED;
  }

  WinCertificate = (CONST WIN_CERTIFICATE *) (CONST VOID *) (
    (CONST UINT8 *) Context->FileBuffer + CertOffset
    );
  if (WinCertificate->dwLength < sizeof (WIN_CERTIFICATE)
   || !IS_ALIGNED (WinCertificate->dwLength, OC_ALIGNOF (WIN_CERTIFICATE))) {
    return RETURN_UNSUPPORTED;
  }

  Result = BaseOverflowAddU32 (
    CertOffset,
    WinCertificate->dwLength,
    &CertEnd
    );
  if (Result || CertEnd > Context->SecDirSize) {
    return RETURN_UNSUPPORTED;
  }

  *Certificate = WinCertificate;
  return RETURN_SUCCESS;
}
