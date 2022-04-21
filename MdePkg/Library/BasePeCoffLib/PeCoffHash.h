/** @file
  Provides APIs to verify the Authenticode Signature of PE/COFF Images.

  Copyright (c) 2020, Marvin Häuser. All rights reserved.<BR>
  Copyright (c) 2020, Vitaly Cheptsov. All rights reserved.<BR>
  Copyright (c) 2020, ISP RAS. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-3-Clause
**/

#ifndef PE_COFF_HASH_H_
#define PE_COFF_HASH_H_

/**
  Adds the digest of Data to HashContext. This function can be called multiple
  times to compute the digest of discontinuous data.

  @param[in,out] HashContext  The context of the current hash.
  @param[in]     Data         Pointer to the data to be hashed.
  @param[in]     DataSize     The size, in bytes, of Data.

  @returns  Whether hashing has been successful.
**/
/*@ requires HashContext != \null;
  @ requires \valid((char *) Data + (0 .. DataSize - 1));
  @
  @ assigns \nothing;
*/
typedef
BOOLEAN
(EFIAPI *PE_COFF_HASH_UPDATE)(
  IN OUT VOID        *HashContext,
  IN     CONST VOID  *Data,
  IN     UINTN       DataSize
  );

/**
  Hashes the Image using the Authenticode (PE/COFF Specification 8.1 Appendix A)
  algorithm.

  @param[in]     Context      The context describing the Image. Must have been
                              initialised by PeCoffInitializeContext().
  @param[in]     HashUpdate   The data hashing function.
  @param[in,out] HashContext  The context of the current hash.

  @returns  Whether hashing has been successful.
**/
/*@ requires \valid(Context);
  @ requires \typeof(Context->FileBuffer) <: \type(char *);
  @ requires \valid((char *) Context->FileBuffer + (0 .. image_hdr_raw_size (Context->SizeOfHeaders, Context->TeStrippedOffset) - 1));
  @ requires Context->ImageType != ImageTypeTe ==>
  @            Context->TeStrippedOffset == 0;
  @
  @ requires image_context_type_valid (Context);
  @ requires image_context_hdr_valid (Context);
  @ requires image_datadirs_in_hdr (Context);
  @ requires 0 < Context->NumberOfSections;
  @ requires \let s = image_context_get_sections (Context);
  @          \let n = Context->NumberOfSections;
  @          \valid(s + (0 .. n - 1)) &&
  @          (\forall integer i; 0 <= i < n ==>
  @            s[i].SizeOfRawData > 0 ==>
  @              s[i].PointerToRawData + s[i].SizeOfRawData <= MAX_UINT32 &&
  @              \valid((char *) Context->FileBuffer + ((s[i].PointerToRawData - Context->TeStrippedOffset) .. (s[i].PointerToRawData - Context->TeStrippedOffset) + s[i].SizeOfRawData - 1)));
  @
  @ requires HashContext != \null;
  @
  @ assigns \nothing;
*/
BOOLEAN
PeCoffHashImage (
  IN     CONST PE_COFF_IMAGE_CONTEXT  *Context,
#ifdef PRODUCTION
  IN     PE_COFF_HASH_UPDATE          HashUpdate,
#endif
  IN OUT VOID                         *HashContext
  );

#endif // PE_COFF_HASH_H_
