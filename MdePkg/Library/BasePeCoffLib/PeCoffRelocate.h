/** @file
  Provides APIs to relocate PE/COFF Images.

  Copyright (c) 2020, Marvin Häuser. All rights reserved.<BR>
  Copyright (c) 2020, Vitaly Cheptsov. All rights reserved.<BR>
  Copyright (c) 2020, ISP RAS. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-3-Clause
**/

#ifndef PE_COFF_RELOCATE_H_
#define PE_COFF_RELOCATE_H_

#define IMAGE_RELOC_TYPE_SUPPORTED(Type) \
  ((Type) == EFI_IMAGE_REL_BASED_ABSOLUTE) || \
  ((Type) == EFI_IMAGE_REL_BASED_HIGHLOW) || \
  ((Type) == EFI_IMAGE_REL_BASED_DIR64) || \
  ((Type) == EFI_IMAGE_REL_BASED_ARM_MOV32T && PcdGetBool (PcdImageLoaderSupportArmThumb))

#define IMAGE_RELOC_SUPPORTED(Reloc) \
  IMAGE_RELOC_TYPE_SUPPORTED (IMAGE_RELOC_TYPE (Reloc))

/*@ axiomatic ImageRelocApplication {
  @   logic integer image_reloc_type_size (UINT16 Type) =
  @     (Type == EFI_IMAGE_REL_BASED_HIGHLOW    ? 4 :
  @     (Type == EFI_IMAGE_REL_BASED_DIR64      ? 8 :
  @     (Type == EFI_IMAGE_REL_BASED_ARM_MOV32T ? 8 :
  @                                               0)));
  @
  @   logic UINT16 image_reloc_type (UINT16 Relocation) =
  @     (Relocation & 0xF000) >> 12;
  @
  @   logic UINT16 image_reloc_offset (UINT16 Relocation) =
  @     Relocation & 0x0FFF;
  @
  @   lemma image_reloc_type_eq:
  @     \forall UINT16 Relocation;
  @       IMAGE_RELOC_TYPE(Relocation) == image_reloc_type (Relocation);
  @
  @   lemma image_reloc_offset_eq:
  @     \forall UINT16 Relocation;
  @       IMAGE_RELOC_OFFSET(Relocation) == image_reloc_offset (Relocation);
  @
  @   logic integer image_reloc_size (UINT16 Relocation) =
  @     image_reloc_type_size (image_reloc_type (Relocation));
  @
  @   predicate image_reloc_type_supported (UINT16 Type) =
  @     (Type == EFI_IMAGE_REL_BASED_ABSOLUTE) ||
  @     (Type == EFI_IMAGE_REL_BASED_HIGHLOW) ||
  @     (Type == EFI_IMAGE_REL_BASED_DIR64) ||
  @     (Type == EFI_IMAGE_REL_BASED_ARM_MOV32T && PcdGetBool (PcdImageLoaderSupportArmThumb));
  @
  @   predicate image_reloc_supported (UINT16 Relocation) =
  @     image_reloc_type_supported (image_reloc_type (Relocation));
  @
  @   logic integer image_reloc_target_value{L} (char *RelocTarget, UINT16 RelocType) =
  @     (RelocType == EFI_IMAGE_REL_BASED_HIGHLOW ?
  @       uint32_from_char (RelocTarget) :
  @     (RelocType == EFI_IMAGE_REL_BASED_DIR64 || RelocType == EFI_IMAGE_REL_BASED_ARM_MOV32T ?
  @       uint64_from_char (RelocTarget) :
  @     0));
  @
  @   logic integer image_reloc_value{L} (char *Image, EFI_IMAGE_BASE_RELOCATION_BLOCK *BaseReloc, UINT32 RelocIndex) =
  @     \let RelocTarget = BaseReloc->VirtualAddress + image_reloc_offset (BaseReloc->Relocations[RelocIndex]);
  @     \let RelocType   = image_reloc_type (BaseReloc->Relocations[RelocIndex]);
  @     image_reloc_target_value (Image + RelocTarget, RelocType);
  @
  @   predicate image_fixup_applied_highlow{Pre,Post}(char *Fixup, UINT64 Adjust) =
  @     \at(uint32_from_char (Fixup), Post) == (UINT32) \at(uint32_from_char (Fixup), Pre) +% (UINT32 %) Adjust;
  @
  @   predicate image_fixup_applied_dir64{Pre,Post}(char *Fixup, UINT64 Adjust) =
  @     \at(uint64_from_char (Fixup), Post) == (UINT64) \at(uint64_from_char (Fixup), Pre) +% Adjust;
  @
  @   predicate image_reloc_applied_highlow{Pre,Post}(char *Image, EFI_IMAGE_BASE_RELOCATION_BLOCK *BaseReloc, UINT32 RelocIndex, UINT64 Adjust) =
  @     \let Fixup = \at(Image + BaseReloc->VirtualAddress + image_reloc_offset (BaseReloc->Relocations[RelocIndex]), Pre);
  @     image_fixup_applied_highlow{Pre,Post} (Fixup, Adjust);
  @
  @   predicate image_reloc_applied_dir64{Pre,Post}(char *Image, EFI_IMAGE_BASE_RELOCATION_BLOCK *BaseReloc, UINT32 RelocIndex, UINT64 Adjust) =
  @     \let Fixup = \at(Image + BaseReloc->VirtualAddress + image_reloc_offset (BaseReloc->Relocations[RelocIndex]), Pre);
  @     image_fixup_applied_dir64{Pre,Post} (Fixup, Adjust);
  @ }
*/

/*@ axiomatic ImageRelocDirValidity {
  @   logic integer image_base_reloc_offset_index (char *Image, UINT32 RelocDirRva, UINT32 RelocDirSize, integer Index);
  @
  @   axiom image_base_reloc_offset_index_def:
  @     \forall char *Image, UINT32 RelocDirRva, UINT32 RelocDirSize, integer RelocOffset, UINT32 Index;
  @       \let BaseReloc = (EFI_IMAGE_BASE_RELOCATION_BLOCK *) (Image + RelocOffset);
  @       RelocOffset == image_base_reloc_offset_index (Image, RelocDirRva, RelocDirSize, Index) <==>
  @       RelocOffset + BaseReloc->SizeOfBlock == image_base_reloc_offset_index (Image, RelocDirRva, RelocDirSize, Index + 1);
  @
  @   logic UINT32 image_base_reloc_num (char *Image, UINT32 RelocDirRva, UINT32 RelocDirSize);
  @
  @   predicate image_is_base_reloc_num (char *Image, UINT32 RelocDirRva, UINT32 RelocDirSize, UINT32 Index) =
  @     ((\forall integer i; 0 <= i < Index ==>
  @       \let RelocOffset = image_base_reloc_offset_index (Image, RelocDirRva, RelocDirSize, i);
  @       image_base_reloc_exists (RelocOffset, RelocDirRva, RelocDirSize) &&
  @       image_base_reloc_sane (Image, RelocOffset, RelocDirRva, RelocDirSize)) &&
  @     \let TopOffset = image_base_reloc_offset_index (Image, RelocDirRva, RelocDirSize, Index);
  @     !image_base_reloc_exists (TopOffset, RelocDirRva, RelocDirSize));
  @
  @   axiom image_base_reloc_num_def{L}:
  @     \forall char *Image, UINT32 RelocDirRva, UINT32 RelocDirSize, UINT32 NumRelocs;
  @       image_is_base_reloc_num (Image, RelocDirRva, RelocDirSize, NumRelocs) <==>
  @       (NumRelocs == image_base_reloc_num (Image, RelocDirRva, RelocDirSize));
  @
  @   logic integer image_base_reloc_num_relocs (EFI_IMAGE_BASE_RELOCATION_BLOCK *BaseReloc) =
  @     (BaseReloc->SizeOfBlock - sizeof (EFI_IMAGE_BASE_RELOCATION_BLOCK)) / sizeof (UINT16);
  @
  @   predicate image_base_reloc_exists (integer BaseRelocOffset, UINT32 RelocDirRva, UINT32 RelocDirSize) =
  @     RelocDirRva <= BaseRelocOffset <= RelocDirRva + RelocDirSize - sizeof (EFI_IMAGE_BASE_RELOCATION_BLOCK);
  @
  @   predicate image_base_reloc_sane (char *Image, integer BaseRelocOffset, UINT32 RelocDirRva, UINT32 RelocDirSize) =
  @     \let BaseReloc = (EFI_IMAGE_BASE_RELOCATION_BLOCK *) (Image + BaseRelocOffset);
  @     sizeof (EFI_IMAGE_BASE_RELOCATION_BLOCK) <= BaseReloc->SizeOfBlock &&
  @     is_aligned_32 (BaseReloc->SizeOfBlock, AV_ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK)) &&
  @     BaseRelocOffset + BaseReloc->SizeOfBlock <= RelocDirRva + RelocDirSize;
  @
  @   predicate image_reloc_sane (EFI_IMAGE_BASE_RELOCATION_BLOCK *BaseReloc, integer RelocIndex, UINT32 RelocDirRva, UINT32 RelocDirSize, UINT32 SizeOfImage) =
  @     \let RelocTarget = BaseReloc->VirtualAddress + image_reloc_offset (BaseReloc->Relocations[RelocIndex]);
  @     \let TopOfReloc  = RelocTarget + image_reloc_size (BaseReloc->Relocations[RelocIndex]);
  @     image_reloc_supported (BaseReloc->Relocations[RelocIndex]) &&
  @     (image_reloc_type (BaseReloc->Relocations[RelocIndex]) != EFI_IMAGE_REL_BASED_ABSOLUTE ==>
  @       (TopOfReloc <= RelocDirRva ||
  @       RelocDirRva + RelocDirSize <= RelocTarget && TopOfReloc <= SizeOfImage)) &&
  @     (image_reloc_type (BaseReloc->Relocations[RelocIndex]) == EFI_IMAGE_REL_BASED_ARM_MOV32T ==>
  @       is_aligned_32 ((UINT32) RelocTarget, AV_ALIGNOF (UINT16)));
  @
  @   predicate image_context_reloc_sane (PE_COFF_IMAGE_CONTEXT *Context, EFI_IMAGE_BASE_RELOCATION_BLOCK *RelocWalker, integer RelocIndex) =
  @     image_reloc_sane (RelocWalker, RelocIndex, Context->RelocDirRva, Context->RelocDirSize, Context->SizeOfImage);
  @
  @   predicate image_reloc_correct (char *Image, integer RelocOffset, UINT32 SizeOfImage, UINT32 RelocDirRva, UINT32 RelocDirSize) =
  @     image_base_reloc_exists (RelocOffset, RelocDirRva, RelocDirSize) &&
  @     image_base_reloc_sane (Image, RelocOffset, RelocDirRva, RelocDirSize) &&
  @     \let BaseReloc = (EFI_IMAGE_BASE_RELOCATION_BLOCK *) (Image + RelocOffset);
  @     \let NumRelocs = image_base_reloc_num_relocs (BaseReloc);
  @     (\forall integer i; 0 <= i < NumRelocs ==>
  @       image_reloc_sane (BaseReloc, i, RelocDirRva, RelocDirSize, SizeOfImage));
  @
  @   predicate image_base_reloc_mem_valid (char *Image, EFI_IMAGE_BASE_RELOCATION_BLOCK *BaseReloc, UINT32 SizeOfImage, UINT32 RelocDirRva, UINT32 RelocDirSize) =
  @     \let NumRelocs = image_base_reloc_num_relocs (BaseReloc);
  @     \valid (BaseReloc->Relocations + (0 .. NumRelocs - 1)) &&
  @     (\forall integer i; 0 <= i < NumRelocs ==>
  @       image_reloc_sane (BaseReloc, i, RelocDirRva, RelocDirSize, SizeOfImage) ==>
  @         \let RelocTarget = BaseReloc->VirtualAddress + image_reloc_offset (BaseReloc->Relocations[i]);
  @         \valid (Image + (RelocTarget .. RelocTarget + image_reloc_size (BaseReloc->Relocations[i]) - 1)));
  @
  @   predicate image_base_reloc_validity (char *Image, integer RelocOffset, UINT32 SizeOfImage, UINT32 RelocDirRva, UINT32 RelocDirSize) =
  @     \let BaseReloc = (EFI_IMAGE_BASE_RELOCATION_BLOCK *) (Image + RelocOffset);
  @     (image_base_reloc_exists (RelocOffset, RelocDirRva, RelocDirSize) && pointer_aligned (Image + RelocOffset, AV_ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK)) ==>
  @       \valid (BaseReloc)) &&
  @     (image_base_reloc_exists (RelocOffset, RelocDirRva, RelocDirSize) && image_base_reloc_sane (Image, RelocOffset, RelocDirRva, RelocDirSize) <==>
  @       image_base_reloc_mem_valid (Image, BaseReloc, SizeOfImage, RelocDirRva, RelocDirSize));
  @
  @   predicate image_reloc_dir_mem_valid (char *Image, UINT32 SizeOfImage, UINT32 RelocDirRva, UINT32 RelocDirSize) =
  @     RelocDirRva == image_base_reloc_offset_index (Image, RelocDirRva, RelocDirSize, 0) &&
  @     image_base_reloc_validity (Image, RelocDirRva, SizeOfImage, RelocDirRva, RelocDirSize) &&
  @     (\forall integer i; 1 <= i ==>
  @       \let PreviousOffset = image_base_reloc_offset_index (Image, RelocDirRva, RelocDirSize, i - 1);
  @       \let CurrentOffset  = image_base_reloc_offset_index (Image, RelocDirRva, RelocDirSize, i);
  @       image_base_reloc_exists (PreviousOffset, RelocDirRva, RelocDirSize) && image_base_reloc_sane (Image, PreviousOffset, RelocDirRva, RelocDirSize) <==>
  @         image_base_reloc_validity (Image, CurrentOffset, SizeOfImage, RelocDirRva, RelocDirSize));
  @
  @   predicate image_relocs_correct (char *Image, UINT32 SizeOfImage, UINT32 RelocDirRva, UINT32 RelocDirSize, UINT32 NumRelocs) =
  @     \forall integer i; 0 <= i < NumRelocs ==>
  @       \let CurrentOffset = image_base_reloc_offset_index (Image, RelocDirRva, RelocDirSize, i);
  @       image_reloc_correct (Image, CurrentOffset, SizeOfImage, RelocDirRva, RelocDirSize);
  @
  @   predicate image_reloc_dir_correct (char *Image, UINT32 SizeOfImage, UINT32 RelocDirRva, UINT32 RelocDirSize) =
  @     (\exists UINT32 NumRelocs; NumRelocs == image_base_reloc_num (Image, RelocDirRva, RelocDirSize)) &&
  @     \let NumRelocs = image_base_reloc_num (Image, RelocDirRva, RelocDirSize);
  @     image_relocs_correct (Image, SizeOfImage, RelocDirRva, RelocDirSize, NumRelocs) &&
  @     image_base_reloc_offset_index (Image, RelocDirRva, RelocDirSize, NumRelocs) == RelocDirRva + RelocDirSize;
  @
  @   predicate image_reloc_dir_valid (char *Image, UINT32 RelocDirRva, UINT32 RelocDirSize) =
  @     is_aligned_32 (RelocDirRva, AV_ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK)) &&
  @     (\forall integer i; 0 <= i < image_base_reloc_num (Image, RelocDirRva, RelocDirSize) ==>
  @       \let BaseRelocOffset = image_base_reloc_offset_index (Image, RelocDirRva, RelocDirSize, i);
  @       \let BaseReloc       = (EFI_IMAGE_BASE_RELOCATION_BLOCK *) (Image + BaseRelocOffset);
  @       \let NumRelocs       = image_base_reloc_num_relocs (BaseReloc);
  @       \valid (BaseReloc) &&
  @       \valid (BaseReloc->Relocations + (0 .. NumRelocs - 1)) &&
  @       (\forall integer j; 0 <= j < NumRelocs ==>
  @         \let RelocTarget = BaseReloc->VirtualAddress + image_reloc_offset (BaseReloc->Relocations[j]);
  @         \valid (Image + (RelocTarget .. RelocTarget + image_reloc_size (BaseReloc->Relocations[j]) - 1))));
  @ }
*/

//
// 4 byte alignment has been replaced with OC_ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK)
// for proof simplicity. This obviously was the original intention of the
// specification. Assert in case the equality is not given.
//
STATIC_ASSERT (
  sizeof (UINT32) == OC_ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK),
  "The current model violates the PE specification"
  );

/**
  Retrieves the size required to bookkeep Runtime Relocation information.

  @param[in]  Context  The context describing the Image. Must have been loaded
                       by PeCoffLoadImage().
  @param[out] Size     On output, the size, in bytes, of the bookkeeping buffer.

  @retval RETURN_SUCCESS  The Runtime context size for the Image was retrieved
                          successfully.
  @retval other           The Runtime context size for the Image could not be
                          retrieved successfully.
**/
/*@ requires \valid(Context);
  @ requires \valid(Size);
  @ requires image_context_reloc_info_sane (Context);
  @ requires !Context->RelocsStripped;
  @
  @ assigns *Size;
  @
  @ behavior valid_nstripped:
  @   assumes image_context_runtime_fixup_size (Context) <= MAX_UINT32;
  @   ensures *Size == image_context_runtime_fixup_size (Context);
  @   ensures \result == RETURN_SUCCESS;
  @
  @ behavior invalid:
  @   assumes image_context_runtime_fixup_size (Context) > MAX_UINT32;
  @   ensures \result != RETURN_SUCCESS;
  @
  @ complete behaviors;
  @ disjoint behaviors;
*/
RETURN_STATUS
PeCoffRelocationDataSize (
  IN  CONST PE_COFF_IMAGE_CONTEXT  *Context,
  OUT UINT32                       *Size
  );

/**
  Relocate Image for boot-time usage.

  @param[in]  Context             The context describing the Image. Must have
                                  been loaded by PeCoffLoadImage().
  @param[in]  BaseAddress         The address to relocate the Image to.
  @param[out] RelocationData      If not NULL, on output, a buffer bookkeeping
                                  data required for Runtime Relocation.
  @param[in]  RelocationDataSize  The size, in bytes, of RelocationData. Must be
                                  at least as big as PeCoffRelocationDataSize().

  @retval RETURN_SUCCESS  The Image has been relocated successfully.
  @retval other           The Image could not be relocated successfully.
**/
/*@ requires \valid(Context);
  @ requires \typeof(Context->ImageBuffer) <: \type(char *);
  @ requires pointer_max_aligned(Context->ImageBuffer);
  @ requires image_context_reloc_info_sane (Context);
  @
  @ requires RelocationData != \null ==> \valid(RelocationData);
  @ requires RelocationData != \null ==> \valid(RelocationData->FixupData + (0 .. (RelocationDataSize - sizeof (PE_COFF_RUNTIME_CONTEXT)) / sizeof (UINT64) - 1));
  @ requires RelocationData == \null <==> RelocationDataSize == 0;
  @ requires RelocationData != \null ==> RelocationDataSize == sizeof (PE_COFF_RUNTIME_CONTEXT) + Context->RelocDirSize / sizeof (UINT16) * sizeof (UINT64);
  @ requires image_reloc_dir_mem_valid ((char *) Context->ImageBuffer, Context->SizeOfImage, Context->RelocDirRva, Context->RelocDirSize);
  @ requires !Context->RelocsStripped;
  @
  @ assigns ((char *) Context->ImageBuffer)[0 .. Context->SizeOfImage - 1];
  @ assigns RelocationData->RelocDirRva;
  @ assigns RelocationData->RelocDirSize;
  @ assigns RelocationData->FixupData[0 .. (RelocationDataSize - sizeof (PE_COFF_RUNTIME_CONTEXT)) / sizeof (UINT64) - 1];
  @
  @ behavior inplace_link_valid_fixup_data:
  @   assumes RelocationData == \null &&
  @           BaseAddress == Context->ImageBase;
  @   assumes RelocationData != \null;
  @   ensures RelocationData->RelocDirRva == Context->RelocDirRva &&
  @           RelocationData->RelocDirSize == Context->RelocDirSize;
  @   ensures \result == RETURN_SUCCESS;
  @
  @ behavior inplace_link_nvalid_fixup_data:
  @   assumes RelocationData == \null &&
  @           BaseAddress == Context->ImageBase;
  @   assumes RelocationData == \null;
  @   assigns ((char *) Context->ImageBuffer)[0 .. Context->SizeOfImage - 1];
  @   ensures \result == RETURN_SUCCESS;
  @
  @ behavior relocs_valid_valid_fixup_data:
  @   assumes !(RelocationData == \null &&
  @           BaseAddress == Context->ImageBase) &&
  @           image_reloc_dir_correct ((char *) Context->ImageBuffer, Context->SizeOfImage, Context->RelocDirRva, Context->RelocDirSize);
  @   assumes RelocationData != \null;
  @   ensures RelocationData->RelocDirRva == Context->RelocDirRva &&
  @           RelocationData->RelocDirSize == Context->RelocDirSize;
  @   ensures image_reloc_dir_valid ((char *) Context->ImageBuffer, RelocationData->RelocDirRva, RelocationData->RelocDirSize);
  @   ensures \result == RETURN_SUCCESS;
  @
  @ behavior relocs_valid_nvalid_fixup_data:
  @   assumes !(RelocationData == \null &&
  @           BaseAddress == Context->ImageBase) &&
  @           image_reloc_dir_correct ((char *) Context->ImageBuffer, Context->SizeOfImage, Context->RelocDirRva, Context->RelocDirSize);
  @   assumes RelocationData == \null;
  @   assigns ((char *) Context->ImageBuffer)[0 .. Context->SizeOfImage - 1];
  @   ensures \result == RETURN_SUCCESS;
  @
  @ behavior nvalid_relocs_valid_fixup_data:
  @   assumes !(RelocationData == \null &&
  @           BaseAddress == Context->ImageBase) &&
  @           !image_reloc_dir_correct ((char *) Context->ImageBuffer, Context->SizeOfImage, Context->RelocDirRva, Context->RelocDirSize);
  @   assumes RelocationData != \null;
  @   ensures \result != RETURN_SUCCESS;
  @
  @ behavior nvalid_relocs_nvalid_fixup_data:
  @   assumes !(RelocationData == \null &&
  @           BaseAddress == Context->ImageBase) &&
  @           !image_reloc_dir_correct ((char *) Context->ImageBuffer, Context->SizeOfImage, Context->RelocDirRva, Context->RelocDirSize);
  @   assumes RelocationData == \null;
  @   assigns ((char *) Context->ImageBuffer)[0 .. Context->SizeOfImage - 1];
  @   ensures \result != RETURN_SUCCESS;
  @
  @ disjoint behaviors;
  @ complete behaviors;
*/
RETURN_STATUS
PeCoffRelocateImage (
  IN  CONST PE_COFF_IMAGE_CONTEXT  *Context,
  IN  UINTN                        BaseAddress,
  OUT PE_COFF_RUNTIME_CONTEXT      *RelocationData OPTIONAL,
  IN  UINT32                       RelocationDataSize
  );

/**
  Relocate Image for Runtime usage.

  @param[in]  Image           The Image destination memory. Must have been
                              relocated by PeCoffRelocateImage().
  @param[in]  ImageSize       The size, in bytes, of Image.
  @param[in]  BaseAddress     The address to relocate the Image to.
  @param[in]  RelocationData  The Relocation context obtained by
                              PeCoffRelocateImage().

  @retval RETURN_SUCCESS  The Image has been relocated successfully.
  @retval other           The Image could not be relocated successfully.
**/
/*@ requires \typeof (Image) <: \type (char *);
  @ requires pointer_max_aligned(Image);
  @ requires \valid (RelocationData);
  @
  @ requires \let NumRelocEntries = RelocationData->RelocDirSize / sizeof (UINT16);
  @          \valid (RelocationData->FixupData + (0 .. NumRelocEntries - 1));
  @
  @ requires RelocationData->RelocDirRva + RelocationData->RelocDirSize <= ImageSize;
  @ requires \exists UINT32 NumRelocs; NumRelocs == image_base_reloc_num ((char *) Image, RelocationData->RelocDirRva, RelocationData->RelocDirSize);
  @ requires \let NumRelocs = image_base_reloc_num ((char *) Image, RelocationData->RelocDirRva, RelocationData->RelocDirSize);
  @          image_base_reloc_offset_index ((char *) Image, RelocationData->RelocDirRva, RelocationData->RelocDirSize, NumRelocs) == RelocationData->RelocDirRva + RelocationData->RelocDirSize;
  @ requires RelocationData->RelocDirRva == image_base_reloc_offset_index ((char *) Image, RelocationData->RelocDirRva, RelocationData->RelocDirSize, 0);
  @ requires image_reloc_dir_correct ((char *) Image, ImageSize, RelocationData->RelocDirRva, RelocationData->RelocDirSize);
  @ requires image_reloc_dir_valid ((char *) Image, RelocationData->RelocDirRva, RelocationData->RelocDirSize);
  @
  @ assigns ((char *) Image)[0 .. ImageSize - 1];
  @
  @ behavior inplace_link:
  @   assumes BaseAddress == pointer_to_address (Image);
  @   assigns \nothing;
  @   ensures \result == RETURN_SUCCESS;
  @
  @ behavior allow_target_mismatch:
  @   assumes BaseAddress != pointer_to_address (Image) &&
  @           PcdGetBool (PcdImageLoaderRtRelocAllowTargetMismatch);
  @   ensures \result == RETURN_SUCCESS;
  @
  @ behavior new_disallow_target_mismatch:
  @   assumes BaseAddress != pointer_to_address (Image) &&
  @           !PcdGetBool (PcdImageLoaderRtRelocAllowTargetMismatch);
  @
  @ disjoint behaviors;
  @ complete behaviors;
*/
RETURN_STATUS
PeCoffRelocateImageForRuntime (
  IN OUT VOID                           *Image,
  IN     UINT32                         ImageSize,
  IN     UINTN                          BaseAddress,
  IN     CONST PE_COFF_RUNTIME_CONTEXT  *RelocationData
  );

#endif // PE_COFF_RELOCATE_H_
