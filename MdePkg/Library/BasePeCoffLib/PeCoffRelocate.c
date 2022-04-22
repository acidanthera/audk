/** @file
  Implements APIs to relocate PE/COFF Images.

  Portions copyright (c) 2006 - 2019, Intel Corporation. All rights reserved.<BR>
  Portions copyright (c) 2008 - 2010, Apple Inc. All rights reserved.<BR>
  Portions Copyright (c) 2020, Hewlett Packard Enterprise Development LP. All rights reserved.<BR>
  Copyright (c) 2020, Marvin Häuser. All rights reserved.<BR>
  Copyright (c) 2020, Vitaly Cheptsov. All rights reserved.<BR>
  Copyright (c) 2020, ISP RAS. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-3-Clause
**/

#include "BasePeCoffLibInternals.h"

#include "PeCoffRelocate.h"

/**
  Retrieve the immediate data encoded in an ARM MOVT or MOVW immediate
  instruciton.

  @param[in] Instruction  Pointer to an ARM MOVT or MOVW immediate instruction.

  @returns  The Immediate address encoded in the instruction.
**/
/*@ requires \typeof(Instruction) <: \type(char *);
  @ requires pointer_aligned (Instruction, OC_ALIGNOF (UINT16));
  @ requires \valid((char *) Instruction + (0 .. 3));
  @ assigns \nothing;
*/
STATIC
UINT16
ThumbMovtImmediateAddress (
  IN CONST VOID  *Instruction
  )
{
  UINT32 Movt;
  UINT16 Movt1;
  UINT16 Movt2;
  UINT16 Address;
  //
  // Thumb2 is two separate 16-bit instructions working together, e.g.
  // MOVT R0, #0 is 0x0000f2c0 or 0xf2c0 0x0000
  //
  Movt1 = READ_ALIGNED_16 (Instruction);
  Movt2 = READ_ALIGNED_16 ((CONST CHAR8 *) Instruction + sizeof (UINT16));
  Movt  = COMPOSE_32 (Movt1, Movt2);
  //
  // imm16 = imm4:i:imm3:imm8
  //         imm4 -> Bit19:Bit16
  //         i    -> Bit26
  //         imm3 -> Bit14:Bit12
  //         imm8 -> Bit7:Bit0
  //
  Address  = (UINT16) (Movt & 0x000000FFU);         // imm8
  Address |= (UINT16) ((Movt >> 4U) & 0x0000F700U); // imm4 imm3
  Address |= (UINT16) ((Movt & BIT26) >> 15U);      // i, Bit26->11
  return Address;
}

/**
  Update an ARM MOVT or MOVW immediate instruction immediate data.

  @param[in,out] Instruction  Pointer to an ARM MOVT or MOVW immediate
                              instruction.
  @param[in]     Address      New address to patch into the instruction.
**/
/*@ requires \typeof(Instruction) <: \type(char *);
  @ requires pointer_aligned (Instruction, OC_ALIGNOF (UINT16));
  @ requires \valid(((char *) Instruction) + (0 .. 3));
  @ assigns ((char *) Instruction)[0 .. 3];
*/
STATIC
VOID
ThumbMovtImmediatePatch (
  IN OUT VOID    *Instruction,
  IN     UINT16  Address
  )
{
  UINT16 Patch;
  UINT16 PatchedInstruction;
  //
  // First 16-bit chunk of instruction.
  //
  Patch  = (Address & 0xF000U) >> 12U; // imm4
  Patch |= (Address & BIT11) >> 1U;    // i, Bit11->10
  //
  // Mask out instruction bits and or in address.
  //
  PatchedInstruction = READ_ALIGNED_16 (Instruction);
  WRITE_ALIGNED_16 (Instruction, (PatchedInstruction & ~(UINT16) 0x040FU) | Patch);
  //
  // Second 16-bit chunk of instruction.
  //
  Patch  = Address & 0x000000FFU;                  // imm8
  Patch |= ((UINT32) Address << 4U) & 0x00007000U; // imm3
  //
  // Mask out instruction bits and or in address.
  //
  PatchedInstruction = READ_ALIGNED_16 ((CHAR8 *) Instruction + sizeof (UINT16));
  WRITE_ALIGNED_16 (
    (CHAR8 *) Instruction + sizeof (UINT16),
    (PatchedInstruction & ~(UINT16) 0x70FFU) | Patch
    );
}

/**
  Retrieve the immediate data encoded in an ARM MOVW/MOVT instruciton pair.

  @param[in] Instructions  Pointer to an ARM MOVW/MOVT insturction pair.

  @returns  The Immediate address encoded in the instructions.
**/
/*@ requires \typeof(Instructions) <: \type(char *);
  @ requires pointer_aligned (Instructions, OC_ALIGNOF (UINT16));
  @ requires \valid((char *) Instructions + (0 .. 7));
  @ assigns \nothing;
*/
STATIC
UINT32
ThumbMovwMovtImmediateAddress (
  IN CONST VOID  *Instructions
  )
{
  CONST CHAR8 *Word;
  CONST CHAR8 *Top;

  /*@ assigns Word;
    @ ensures pointer_aligned (Word, OC_ALIGNOF (UINT16));
  */
  Word = Instructions;                                // MOVW

  //@ assert is_aligned_N ((UINT32) (2 * sizeof (UINT16)), OC_ALIGNOF (UINT16));

  /*@ assigns Top;
    @ ensures pointer_aligned (Top, OC_ALIGNOF (UINT16));
  */
  Top  = (CONST CHAR8 *) Instructions + 2 * sizeof (UINT16);  // MOVT

  return (UINT32) (((UINT32) ThumbMovtImmediateAddress (Top) << 16U) | ThumbMovtImmediateAddress (Word));
}

/**
  Update an ARM MOVW/MOVT immediate instruction instruction pair.

  @param[in,out] Instructions  Pointer to ARM MOVW/MOVT instruction pair.
  @param[in]     Address       New address to patch into the instructions.
**/
/*@ requires \typeof(Instructions) <: \type(char *);
  @ requires pointer_aligned (Instructions, OC_ALIGNOF (UINT16));
  @ requires \valid((char *) Instructions + (0 .. 7));
  @ assigns ((char *) Instructions)[0 .. 7];
*/
STATIC
VOID
ThumbMovwMovtImmediatePatch (
  IN OUT VOID    *Instructions,
  IN     UINT32  Address
  )
{
  CHAR8 *Word;
  CHAR8 *Top;

  /*@ assigns Word;
    @ ensures Word == (char *) Instructions;
    @ ensures pointer_aligned (Word, OC_ALIGNOF (UINT16));
  */
  Word = Instructions;                                  // MOVW

  //@ assert is_aligned_N ((UINT32) (2 * sizeof (UINT16)), OC_ALIGNOF (UINT16));

  /*@ assigns Top;
    @ ensures Top == (char *) Instructions + 2 * sizeof (UINT16);
    @ ensures pointer_aligned (Top, OC_ALIGNOF (UINT16));
  */
  Top  = (CHAR8 *) Instructions + 2 * sizeof (UINT16);  // MOVT

  //@ assigns ((char *) Instructions)[0 .. 3];
  ThumbMovtImmediatePatch (Word, (UINT16) (Address & 0x0000FFFFU));

  //@ assigns ((char *) Instructions)[4 .. 7];
  ThumbMovtImmediatePatch (Top, (UINT16) ((Address & 0xFFFF0000U) >> 16U));
}

/**
  Relocate an ARM MOVW/MOVT immediate instruction instruction pair.

  @param[in,out] Instructions  Pointer to ARM MOVW/MOVT instruction pair.
  @param[in]     Adjust        The delta to add to the addresses.
**/
/*@ requires \typeof(Fixup) <: \type(char *);
  @ requires pointer_aligned (Fixup, OC_ALIGNOF (UINT16));
  @ requires \valid((char *) Fixup + (0 .. 7));
  @ assigns ((char *) Fixup)[0 .. 7];
*/
STATIC
VOID
ThumbMovwMovtImmediateFixup (
  IN OUT VOID    *Fixup,
  IN     UINT64  Adjust
  )
{
  UINT32 Fixup32;

  //@ assigns Fixup32;
  Fixup32 = ThumbMovwMovtImmediateAddress (Fixup) +/*@%*/ (UINT32)/*@%*/ Adjust;

  //@ assigns ((char *) Fixup)[0 .. 7];
  ThumbMovwMovtImmediatePatch (Fixup, Fixup32);
}

/**
  Apply an Image Base Relocation.

  Only a subset of the PE/COFF Base Relocation types are permited.
  The Base Relocation target must be in bounds, aligned, and must not overlap
  with the Relocation Directory.

  @param[in]  Context     The context describing the Image. Must have been
                          loaded by PeCoffLoadImage().
  @param[in]  RelocBlock  The Base Relocation Block to apply from.
  @param[in]  RelocIndex  The index of the Base Relocation to apply.
  @param[in]  Adjust      The delta to add to the addresses.
  @param[out] FixupData   On input, a pointer to a bookkeeping value or NULL.
                          On output, a value to preserve for Runtime Relocation.

  @retval RETURN_SUCCESS  The Base Relocation has been applied successfully.
  @retval other           The Base Relocation could not be applied successfully.
**/
/*@ requires FixupData != \null ==> \valid(FixupData + RelocIndex);
  @ requires \valid(Context);
  @ requires \typeof(Context->ImageBuffer) <: \type(char *);
  @ requires pointer_max_aligned(Context->ImageBuffer);
  @ requires \valid(RelocBlock);
  @ requires RelocIndex < (RelocBlock->SizeOfBlock - sizeof (EFI_IMAGE_BASE_RELOCATION_BLOCK)) / sizeof (UINT16);
  @ requires Context->RelocDirRva < Context->RelocDirRva + Context->RelocDirSize <= Context->SizeOfImage;
  @ requires image_base_reloc_mem_valid ((char *) Context->ImageBuffer, RelocBlock, Context->SizeOfImage, Context->RelocDirRva, Context->RelocDirSize);
  @
  @ assigns ((char *) Context->ImageBuffer)[0 .. Context->SizeOfImage - 1];
  @ assigns FixupData[RelocIndex];
  @
  @ behavior valid_abs_valid_fixup_data:
  @   assumes image_reloc_type (RelocBlock->Relocations[RelocIndex]) == EFI_IMAGE_REL_BASED_ABSOLUTE;
  @   assumes FixupData != \null;
  @   ensures FixupData[RelocIndex] == 0;
  @   ensures \result == RETURN_SUCCESS;
  @
  @ behavior valid_abs_nvalid_fixup_data:
  @   assumes image_reloc_type (RelocBlock->Relocations[RelocIndex]) == EFI_IMAGE_REL_BASED_ABSOLUTE;
  @   assumes FixupData == \null;
  @   assigns ((char *) Context->ImageBuffer)[0 .. Context->SizeOfImage - 1];
  @   ensures \result == RETURN_SUCCESS;
  @
  @ behavior valid_highlow_valid_fixup_data:
  @   assumes image_reloc_type (RelocBlock->Relocations[RelocIndex]) == EFI_IMAGE_REL_BASED_HIGHLOW &&
  @           (RelocBlock->VirtualAddress + image_reloc_offset (RelocBlock->Relocations[RelocIndex]) < RelocBlock->VirtualAddress + image_reloc_offset (RelocBlock->Relocations[RelocIndex]) + image_reloc_size (RelocBlock->Relocations[RelocIndex]) <= Context->RelocDirRva ||
  @           Context->RelocDirRva + Context->RelocDirSize <= RelocBlock->VirtualAddress + image_reloc_offset (RelocBlock->Relocations[RelocIndex]) && RelocBlock->VirtualAddress + image_reloc_offset (RelocBlock->Relocations[RelocIndex]) + image_reloc_size (RelocBlock->Relocations[RelocIndex]) <= Context->SizeOfImage);
  @   assumes FixupData != \null;
  @   ensures image_reloc_applied_highlow{Pre,Post} ((char *) Context->ImageBuffer, RelocBlock, RelocIndex, Adjust) &&
  @           FixupData[RelocIndex] == image_reloc_value{Post} ((char *) Context->ImageBuffer, RelocBlock, RelocIndex);
  @   ensures \result == RETURN_SUCCESS;
  @
  @ behavior valid_highlow_nvalid_fixup_data:
  @   assumes image_reloc_type (RelocBlock->Relocations[RelocIndex]) == EFI_IMAGE_REL_BASED_HIGHLOW &&
  @           (RelocBlock->VirtualAddress + image_reloc_offset (RelocBlock->Relocations[RelocIndex]) < RelocBlock->VirtualAddress + image_reloc_offset (RelocBlock->Relocations[RelocIndex]) + image_reloc_size (RelocBlock->Relocations[RelocIndex]) <= Context->RelocDirRva ||
  @           Context->RelocDirRva + Context->RelocDirSize <= RelocBlock->VirtualAddress + image_reloc_offset (RelocBlock->Relocations[RelocIndex]) && RelocBlock->VirtualAddress + image_reloc_offset (RelocBlock->Relocations[RelocIndex]) + image_reloc_size (RelocBlock->Relocations[RelocIndex]) <= Context->SizeOfImage);
  @   assumes FixupData == \null;
  @   assigns ((char *) Context->ImageBuffer)[0 .. Context->SizeOfImage - 1];
  @   ensures image_reloc_applied_highlow{Pre,Post} ((char *) Context->ImageBuffer, RelocBlock, RelocIndex, Adjust);
  @   ensures \result == RETURN_SUCCESS;
  @
  @ behavior valid_dir64_valid_fixup_data:
  @   assumes image_reloc_type (RelocBlock->Relocations[RelocIndex]) == EFI_IMAGE_REL_BASED_DIR64 &&
  @           (RelocBlock->VirtualAddress + image_reloc_offset (RelocBlock->Relocations[RelocIndex]) < RelocBlock->VirtualAddress + image_reloc_offset (RelocBlock->Relocations[RelocIndex]) + image_reloc_size (RelocBlock->Relocations[RelocIndex]) <= Context->RelocDirRva ||
  @           Context->RelocDirRva + Context->RelocDirSize <= RelocBlock->VirtualAddress + image_reloc_offset (RelocBlock->Relocations[RelocIndex]) && RelocBlock->VirtualAddress + image_reloc_offset (RelocBlock->Relocations[RelocIndex]) + image_reloc_size (RelocBlock->Relocations[RelocIndex]) <= Context->SizeOfImage);
  @   assumes FixupData != \null;
  @   ensures image_reloc_applied_dir64{Pre,Post} ((char *) Context->ImageBuffer, RelocBlock, RelocIndex, Adjust) &&
  @           FixupData[RelocIndex] == image_reloc_value{Post} ((char *) Context->ImageBuffer, RelocBlock, RelocIndex);
  @   ensures \result == RETURN_SUCCESS;
  @
  @ behavior valid_dir64_nvalid_fixup_data:
  @   assumes image_reloc_type (RelocBlock->Relocations[RelocIndex]) == EFI_IMAGE_REL_BASED_DIR64 &&
  @           (RelocBlock->VirtualAddress + image_reloc_offset (RelocBlock->Relocations[RelocIndex]) < RelocBlock->VirtualAddress + image_reloc_offset (RelocBlock->Relocations[RelocIndex]) + image_reloc_size (RelocBlock->Relocations[RelocIndex]) <= Context->RelocDirRva ||
  @           Context->RelocDirRva + Context->RelocDirSize <= RelocBlock->VirtualAddress + image_reloc_offset (RelocBlock->Relocations[RelocIndex]) && RelocBlock->VirtualAddress + image_reloc_offset (RelocBlock->Relocations[RelocIndex]) + image_reloc_size (RelocBlock->Relocations[RelocIndex]) <= Context->SizeOfImage);
  @   assumes FixupData == \null;
  @   assigns ((char *) Context->ImageBuffer)[0 .. Context->SizeOfImage - 1];
  @   ensures image_reloc_applied_dir64{Pre,Post} ((char *) Context->ImageBuffer, RelocBlock, RelocIndex, Adjust);
  @   ensures \result == RETURN_SUCCESS;
  @
  @ behavior valid_mov32t_valid_fixup_data:
  @   assumes image_reloc_type (RelocBlock->Relocations[RelocIndex]) == EFI_IMAGE_REL_BASED_ARM_MOV32T && PcdGetBool (PcdImageLoaderSupportArmThumb) &&
  @           (RelocBlock->VirtualAddress + image_reloc_offset (RelocBlock->Relocations[RelocIndex]) < RelocBlock->VirtualAddress + image_reloc_offset (RelocBlock->Relocations[RelocIndex]) + image_reloc_size (RelocBlock->Relocations[RelocIndex]) <= Context->RelocDirRva ||
  @           Context->RelocDirRva + Context->RelocDirSize <= RelocBlock->VirtualAddress + image_reloc_offset (RelocBlock->Relocations[RelocIndex]) && RelocBlock->VirtualAddress + image_reloc_offset (RelocBlock->Relocations[RelocIndex]) + image_reloc_size (RelocBlock->Relocations[RelocIndex]) <= Context->SizeOfImage);
  @   assumes is_aligned_32 (RelocBlock->VirtualAddress +% (UINT32) image_reloc_offset (RelocBlock->Relocations[RelocIndex]), AV_ALIGNOF (UINT16));
  @   assumes FixupData != \null;
  @   ensures FixupData[RelocIndex] == image_reloc_value{Post} ((char *) Context->ImageBuffer, RelocBlock, RelocIndex);
  @   ensures \result == RETURN_SUCCESS;
  @
  @ behavior valid_mov32t_nvalid_fixup_data:
  @   assumes image_reloc_type (RelocBlock->Relocations[RelocIndex]) == EFI_IMAGE_REL_BASED_ARM_MOV32T && PcdGetBool (PcdImageLoaderSupportArmThumb) &&
  @           (RelocBlock->VirtualAddress + image_reloc_offset (RelocBlock->Relocations[RelocIndex]) < RelocBlock->VirtualAddress + image_reloc_offset (RelocBlock->Relocations[RelocIndex]) + image_reloc_size (RelocBlock->Relocations[RelocIndex]) <= Context->RelocDirRva ||
  @           Context->RelocDirRva + Context->RelocDirSize <= RelocBlock->VirtualAddress + image_reloc_offset (RelocBlock->Relocations[RelocIndex]) && RelocBlock->VirtualAddress + image_reloc_offset (RelocBlock->Relocations[RelocIndex]) + image_reloc_size (RelocBlock->Relocations[RelocIndex]) <= Context->SizeOfImage);
  @   assumes is_aligned_32 (RelocBlock->VirtualAddress +% (UINT32) image_reloc_offset (RelocBlock->Relocations[RelocIndex]), AV_ALIGNOF (UINT16));
  @   assumes FixupData == \null;
  @   assigns ((char *) Context->ImageBuffer)[0 .. Context->SizeOfImage - 1];
  @   ensures \result == RETURN_SUCCESS;
  @
  @ behavior invalid:
  @   assumes !image_context_reloc_sane (Context, RelocBlock, RelocIndex);
  @   assigns \nothing;
  @   ensures \result != RETURN_SUCCESS;
  @
  @ complete behaviors;
  @ disjoint behaviors;
*/
STATIC
RETURN_STATUS
InternalApplyRelocation (
  IN  CONST PE_COFF_LOADER_IMAGE_CONTEXT            *Context,
  IN  CONST EFI_IMAGE_BASE_RELOCATION_BLOCK  *RelocBlock,
  IN  UINT32                                 RelocIndex,
  IN  UINT64                                 Adjust,
  OUT UINT64                                 *FixupData OPTIONAL
  )
{
  UINT16  RelocType;
  UINT16  RelocOff;
  BOOLEAN Result;
  UINT32  RelocTarget;
  UINT32  RemRelocTargetSize;
  UINT32  Fixup32;
  UINT64  Fixup64;
  CHAR8   *Fixup;

  /*@ assigns RelocType;
    @ ensures RelocType == image_reloc_type (RelocBlock->Relocations[RelocIndex]);
  */
  RelocType = IMAGE_RELOC_TYPE (RelocBlock->Relocations[RelocIndex]);

  /*@ assigns RelocOff;
    @ ensures RelocOff == image_reloc_offset (RelocBlock->Relocations[RelocIndex]);
  */
  RelocOff = IMAGE_RELOC_OFFSET (RelocBlock->Relocations[RelocIndex]);
  //
  // Absolute Base Relocations are used for padding any must be skipped.
  //
  /*@ assigns FixupData[RelocIndex];
    @ ensures image_reloc_type (RelocBlock->Relocations[RelocIndex]) != EFI_IMAGE_REL_BASED_ABSOLUTE;
  */
  if (RelocType == EFI_IMAGE_REL_BASED_ABSOLUTE) {
    /*@ assigns FixupData[RelocIndex];
      @ ensures FixupData != \null ==>
      @           FixupData[RelocIndex] == 0;
    */
    if (FixupData != NULL) {
      /*@ assigns FixupData[RelocIndex];
        @ ensures FixupData[RelocIndex] == 0;
      */
      FixupData[RelocIndex] = 0;
    }

    //@ assert image_context_reloc_sane (Context, RelocBlock, RelocIndex);
    return RETURN_SUCCESS;
  }
  //
  // Determine the Base Relocation target address.
  //
  /*@ assigns Result, RelocTarget;
    @ ensures !Result <==> RelocTarget == RelocBlock->VirtualAddress + image_reloc_offset (RelocBlock->Relocations[RelocIndex]);
    @ ensures Result <==> RelocBlock->VirtualAddress + image_reloc_offset (RelocBlock->Relocations[RelocIndex]) > MAX_UINT32;
  */
  Result = BaseOverflowAddU32 (
             RelocBlock->VirtualAddress,
             RelocOff,
             &RelocTarget
             );

  /*@ assigns \nothing;
    @ ensures RelocTarget == RelocBlock->VirtualAddress + image_reloc_offset (RelocBlock->Relocations[RelocIndex]);
  */
  if (Result) {
    //@ assert RelocBlock->VirtualAddress + image_reloc_offset (RelocBlock->Relocations[RelocIndex]) > MAX_UINT32;
    //@ assert !(RelocBlock->VirtualAddress + image_reloc_offset (RelocBlock->Relocations[RelocIndex]) + image_reloc_size (RelocBlock->Relocations[RelocIndex]) <= Context->SizeOfImage);
    //@ assert !image_context_reloc_sane (Context, RelocBlock, RelocIndex);
    ASSERT (FALSE);
    return RETURN_UNSUPPORTED;
  }

  /*@ assigns Result, RemRelocTargetSize;
    @ ensures !Result <==> RemRelocTargetSize == Context->SizeOfImage - RelocTarget;
    @ ensures Result <==> Context->SizeOfImage < RelocBlock->VirtualAddress + image_reloc_offset (RelocBlock->Relocations[RelocIndex]);
  */
  Result = BaseOverflowSubU32 (
             Context->SizeOfImage,
             RelocTarget,
             &RemRelocTargetSize
             );

  /*@ assigns \nothing;
    @ ensures RemRelocTargetSize == Context->SizeOfImage - RelocTarget;
    @ ensures RelocTarget + RemRelocTargetSize <= Context->SizeOfImage;
  */
  if (Result) {
    //@ assert !(RelocBlock->VirtualAddress + image_reloc_offset (RelocBlock->Relocations[RelocIndex]) + image_reloc_size (RelocBlock->Relocations[RelocIndex]) <= Context->SizeOfImage);
    //@ assert !image_context_reloc_sane (Context, RelocBlock, RelocIndex);
    ASSERT (FALSE);
    return RETURN_UNSUPPORTED;
  }

  /*@ assert image_reloc_supported (RelocBlock->Relocations[RelocIndex]) && (image_reloc_type (RelocBlock->Relocations[RelocIndex]) == EFI_IMAGE_REL_BASED_ARM_MOV32T ==> is_aligned_32 (RelocTarget, AV_ALIGNOF (UINT16))) ==>
    @          \let s = image_reloc_size (RelocBlock->Relocations[RelocIndex]);
    @          s <= RemRelocTargetSize ==>
    @            ((RelocTarget + image_reloc_size (RelocBlock->Relocations[RelocIndex]) <= Context->RelocDirRva ||
    @            Context->RelocDirRva + Context->RelocDirSize <= RelocTarget) ==>
    @              \valid((char *) Context->ImageBuffer + (RelocTarget .. RelocTarget + s - 1)));
  */

  /*@ assigns Fixup;
    @ ensures Fixup == (char *) Context->ImageBuffer + RelocTarget;
    @ ensures image_reloc_supported (RelocBlock->Relocations[RelocIndex]) && (image_reloc_type (RelocBlock->Relocations[RelocIndex]) == EFI_IMAGE_REL_BASED_ARM_MOV32T ==> is_aligned_32 (RelocTarget, AV_ALIGNOF (UINT16))) ==>
    @         \let s = image_reloc_size (RelocBlock->Relocations[RelocIndex]);
    @           s <= RemRelocTargetSize ==>
    @             ((RelocTarget + image_reloc_size (RelocBlock->Relocations[RelocIndex]) <= Context->RelocDirRva ||
    @             Context->RelocDirRva + Context->RelocDirSize <= RelocTarget) ==>
    @               \valid(Fixup + (0 .. s - 1)));
  */
  Fixup = (CHAR8 *) Context->ImageBuffer + RelocTarget;
  //
  // Apply the Base Relocation fixup per type.
  // If RelocationData is not NULL, store the current value of the fixup
  // target to determine whether it has been changed during runtime
  // execution.
  //
  // It is not clear how EFI_IMAGE_REL_BASED_HIGH and
  // EFI_IMAGE_REL_BASED_LOW are supposed to be handled. While the PE
  // specification suggests to just add the high or low part of the
  // displacement, there are concerns about how it's supposed to deal with
  // wraparounds. As they are virtually non-existent, they are unsupported for
  // the time being.
  //
  /*@ assigns Fixup32, Fixup64, FixupData[RelocIndex], ((char *) Context->ImageBuffer)[0 .. Context->SizeOfImage - 1];
    @ ensures image_reloc_supported (RelocBlock->Relocations[RelocIndex]);
    @ ensures image_context_reloc_sane (Context, RelocBlock, RelocIndex);
  */
  switch (RelocType) {
    case EFI_IMAGE_REL_BASED_HIGHLOW:
      /*@ assigns \nothing;
        @ ensures image_reloc_size (RelocBlock->Relocations[RelocIndex]) <= RemRelocTargetSize;
      */
      if (sizeof (UINT32) > RemRelocTargetSize) {
        //@ assert !(image_reloc_size (RelocBlock->Relocations[RelocIndex]) <= RemRelocTargetSize);
        //@ assert !image_context_reloc_sane (Context, RelocBlock, RelocIndex);
        ASSERT (FALSE);
        return RETURN_UNSUPPORTED;
      }
      //
      // Ensure the Base Relocation does not target the Relocation Directory.
      //
      /*@ assigns \nothing;
        @ ensures RelocTarget + image_reloc_size (RelocBlock->Relocations[RelocIndex]) <= Context->RelocDirRva ||
        @         Context->RelocDirRva + Context->RelocDirSize <= RelocTarget;
        @ ensures \valid(Fixup + (0 .. 3));
      */
      if (RelocTarget + sizeof (UINT32) > Context->RelocDirRva
       && Context->RelocDirRva + Context->RelocDirSize > RelocTarget) {
        /*@ assert !(RelocTarget + image_reloc_size (RelocBlock->Relocations[RelocIndex]) <= Context->RelocDirRva ||
          @        Context->RelocDirRva + Context->RelocDirSize <= RelocTarget);
        */
        //@ assert !image_context_reloc_sane (Context, RelocBlock, RelocIndex);
        ASSERT (FALSE);
        return RETURN_UNSUPPORTED;
      }

      /*@ requires Fixup == (char *) Context->ImageBuffer + RelocBlock->VirtualAddress + image_reloc_offset (RelocBlock->Relocations[RelocIndex]);
        @ assigns Fixup32;
        @ ensures Fixup32 == image_reloc_value ((char *) Context->ImageBuffer, RelocBlock, RelocIndex);
      */
      Fixup32 = ReadUnaligned32 (Fixup);

      /*@ requires Fixup32 == image_reloc_value ((char *) Context->ImageBuffer, RelocBlock, RelocIndex);
        @ assigns Fixup32;
        @ ensures Fixup32 == (UINT32) image_reloc_value ((char *) Context->ImageBuffer, RelocBlock, RelocIndex) +% (UINT32 %) Adjust;
      */
      Fixup32 +=/*@%*/ (UINT32)/*@%*/ Adjust;

      /*@ requires Fixup == (char *) Context->ImageBuffer + RelocBlock->VirtualAddress + image_reloc_offset (RelocBlock->Relocations[RelocIndex]);
        @ requires Fixup32 == (UINT32) image_reloc_value ((char *) Context->ImageBuffer, RelocBlock, RelocIndex) +% (UINT32 %) Adjust;
        @ assigns Fixup[0 .. 3];
        @ ensures image_reloc_value ((char *) Context->ImageBuffer, RelocBlock, RelocIndex) == Fixup32;
        @ ensures image_reloc_applied_highlow{Old,Here} ((char *) Context->ImageBuffer, RelocBlock, RelocIndex, Adjust);
      */
      WriteUnaligned32 (Fixup, Fixup32);

      /*@ requires Fixup32 == image_reloc_value ((char *) Context->ImageBuffer, RelocBlock, RelocIndex);
        @ assigns FixupData[RelocIndex];
        @ ensures FixupData != \null ==> FixupData[RelocIndex] == image_reloc_value ((char *) Context->ImageBuffer, RelocBlock, RelocIndex);
      */
      if (FixupData != NULL) {
        /*@ requires Fixup32 == image_reloc_value ((char *) Context->ImageBuffer, RelocBlock, RelocIndex);
          @ assigns FixupData[RelocIndex];
          @ ensures FixupData[RelocIndex] == image_reloc_value ((char *) Context->ImageBuffer, RelocBlock, RelocIndex);
        */
        FixupData[RelocIndex] = Fixup32;
      }

      //@ assert image_context_reloc_sane (Context, RelocBlock, RelocIndex);
      break;

    case EFI_IMAGE_REL_BASED_DIR64:
      /*@ assigns \nothing;
        @ ensures image_reloc_size (RelocBlock->Relocations[RelocIndex]) <= RemRelocTargetSize;
      */
      if (sizeof (UINT64) > RemRelocTargetSize) {
        //@ assert !(image_reloc_size (RelocBlock->Relocations[RelocIndex]) <= RemRelocTargetSize);
        //@ assert !image_context_reloc_sane (Context, RelocBlock, RelocIndex);
        ASSERT (FALSE);
        return RETURN_UNSUPPORTED;
      }
      //
      // Ensure the Base Relocation does not target the Relocation Directory.
      //
      /*@ assigns \nothing;
        @ ensures RelocTarget + image_reloc_size (RelocBlock->Relocations[RelocIndex]) <= Context->RelocDirRva ||
        @         Context->RelocDirRva + Context->RelocDirSize <= RelocTarget;
        @ ensures \valid(Fixup + (0 .. 7));
      */
      if (RelocTarget + sizeof (UINT64) > Context->RelocDirRva
       && Context->RelocDirRva + Context->RelocDirSize > RelocTarget) {
        /*@ assert !(RelocTarget + image_reloc_size (RelocBlock->Relocations[RelocIndex]) <= Context->RelocDirRva ||
          @        Context->RelocDirRva + Context->RelocDirSize <= RelocTarget);
        */
        //@ assert !image_context_reloc_sane (Context, RelocBlock, RelocIndex);
        ASSERT (FALSE);
        return RETURN_UNSUPPORTED;
      }

      /*@ requires Fixup == (char *) Context->ImageBuffer + RelocBlock->VirtualAddress + image_reloc_offset (RelocBlock->Relocations[RelocIndex]);
        @ assigns Fixup64;
        @ ensures Fixup64 == uint64_from_char ((char *) Context->ImageBuffer + RelocTarget);
        @ ensures Fixup64 == image_reloc_value ((char *) Context->ImageBuffer, RelocBlock, RelocIndex);
      */
      Fixup64 = ReadUnaligned64 (Fixup);

      /*@ requires Fixup64 == (UINT64) image_reloc_value ((char *) Context->ImageBuffer, RelocBlock, RelocIndex);
        @ assigns Fixup64;
        @ ensures Fixup64 == (UINT64) image_reloc_value ((char *) Context->ImageBuffer, RelocBlock, RelocIndex) +% Adjust;
      */
      Fixup64 +=/*@%*/ Adjust;

      /*@ requires Fixup == (char *) Context->ImageBuffer + RelocBlock->VirtualAddress + image_reloc_offset (RelocBlock->Relocations[RelocIndex]);
        @ requires Fixup64 == (UINT64) image_reloc_value ((char *) Context->ImageBuffer, RelocBlock, RelocIndex) +% Adjust;
        @ assigns Fixup[0 .. 7];
        @ ensures image_reloc_value ((char *) Context->ImageBuffer, RelocBlock, RelocIndex) == Fixup64;
        @ ensures image_reloc_applied_dir64{Old,Here} ((char *) Context->ImageBuffer, RelocBlock, RelocIndex, Adjust);
      */
      WriteUnaligned64 (Fixup, Fixup64);

      /*@ requires Fixup64 == image_reloc_value ((char *) Context->ImageBuffer, RelocBlock, RelocIndex);
        @ assigns FixupData[RelocIndex];
        @ ensures FixupData != \null ==> FixupData[RelocIndex] == image_reloc_value ((char *) Context->ImageBuffer, RelocBlock, RelocIndex);
      */
      if (FixupData != NULL) {
        /*@ requires Fixup64 == image_reloc_value ((char *) Context->ImageBuffer, RelocBlock, RelocIndex);
          @ assigns FixupData[RelocIndex];
          @ ensures FixupData[RelocIndex] == image_reloc_value ((char *) Context->ImageBuffer, RelocBlock, RelocIndex);
        */
        FixupData[RelocIndex] = Fixup64;
      }

      //@ assert image_context_reloc_sane (Context, RelocBlock, RelocIndex);
      break;

    case EFI_IMAGE_REL_BASED_ARM_MOV32T:
      /*@ ensures PcdGetBool (PcdImageLoaderSupportArmThumb);
        @ assigns \nothing;
      */
      if (!PcdGetBool (PcdImageLoaderSupportArmThumb)) {
        //@ assert !PcdGetBool (PcdImageLoaderSupportArmThumb);
        //@ assert !image_context_reloc_sane (Context, RelocBlock, RelocIndex);
        ASSERT (FALSE);
        return RETURN_UNSUPPORTED;
      }

      /*@ assigns \nothing;
        @ ensures image_reloc_size (RelocBlock->Relocations[RelocIndex]) <= RemRelocTargetSize;
      */
      if (sizeof (UINT64) > RemRelocTargetSize) {
        //@ assert !(image_reloc_size (RelocBlock->Relocations[RelocIndex]) <= RemRelocTargetSize);
        //@ assert !image_context_reloc_sane (Context, RelocBlock, RelocIndex);
        ASSERT (FALSE);
        return RETURN_UNSUPPORTED;
      }

      // FIXME: 32-bit
      /*@ assigns \nothing;
        @ ensures is_aligned_32 (RelocTarget, AV_ALIGNOF (UINT16));
      */
      if (!IS_ALIGNED (RelocTarget, OC_ALIGNOF (UINT16))) {
        //@ assert !is_aligned_32 (RelocTarget, AV_ALIGNOF (UINT16));
        //@ assert !image_context_reloc_sane (Context, RelocBlock, RelocIndex);
        ASSERT (FALSE);
        return RETURN_UNSUPPORTED;
      }
      //
      // Ensure the Base Relocation does not target the Relocation Directory.
      //
      //@ assert is_aligned_N (RelocTarget, AV_ALIGNOF (UINT16));
      //@ assert pointer_max_aligned (Context->ImageBuffer);
      /*@ assert is_aligned_N (RelocTarget, AV_ALIGNOF (UINT16)) && pointer_max_aligned (Context->ImageBuffer) ==>
        @          pointer_aligned ((char *) Context->ImageBuffer + RelocTarget, AV_ALIGNOF (UINT16));
      */
      //@ assert pointer_aligned (Fixup, OC_ALIGNOF (UINT16));

      /*@ assigns \nothing;
        @ ensures RelocTarget + image_reloc_size (RelocBlock->Relocations[RelocIndex]) <= Context->RelocDirRva ||
        @         Context->RelocDirRva + Context->RelocDirSize <= RelocTarget;
        @ ensures \valid(Fixup + (0 .. 7));
      */
      if (RelocTarget + sizeof (UINT64) > Context->RelocDirRva
       && Context->RelocDirRva + Context->RelocDirSize > RelocTarget) {
        /*@ assert !(RelocTarget + image_reloc_size (RelocBlock->Relocations[RelocIndex]) <= Context->RelocDirRva ||
          @        Context->RelocDirRva + Context->RelocDirSize <= RelocTarget);
        */
        //@ assert !image_context_reloc_sane (Context, RelocBlock, RelocIndex);
        ASSERT (FALSE);
        return RETURN_UNSUPPORTED;
      }

      //@ assigns Fixup[0 .. 7];
      ThumbMovwMovtImmediateFixup (Fixup, Adjust);

      /*@ requires Fixup == (char *) Context->ImageBuffer + RelocBlock->VirtualAddress + image_reloc_offset (RelocBlock->Relocations[RelocIndex]);
        @ assigns FixupData[RelocIndex];
        @ ensures FixupData != \null ==> FixupData[RelocIndex] == image_reloc_value ((char *) Context->ImageBuffer, RelocBlock, RelocIndex);
      */
      if (FixupData != NULL) {
        /*@ requires Fixup == (char *) Context->ImageBuffer + RelocBlock->VirtualAddress + image_reloc_offset (RelocBlock->Relocations[RelocIndex]);
          @ assigns FixupData[RelocIndex];
          @ ensures FixupData[RelocIndex] == image_reloc_value ((char *) Context->ImageBuffer, RelocBlock, RelocIndex);
        */
        FixupData[RelocIndex] = ReadUnaligned64 (Fixup);
      }

      //@ assert is_aligned_32 (RelocTarget, AV_ALIGNOF (UINT16));
      //@ assert image_context_reloc_sane (Context, RelocBlock, RelocIndex);
      break;

    default:
      //@ assert !image_context_reloc_sane (Context, RelocBlock, RelocIndex);
      ASSERT (FALSE);
      return RETURN_UNSUPPORTED;
  }

  return RETURN_SUCCESS;
}

RETURN_STATUS
PeCoffRelocateImage (
  IN  CONST PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  IN  UINT64                       BaseAddress,
  OUT PE_COFF_RUNTIME_CONTEXT      *RelocationData OPTIONAL,
  IN  UINT32                       RelocationDataSize
  )
{
  BOOLEAN                               Result;
  RETURN_STATUS                         Status;

  UINT64                                Adjust;
  CONST EFI_IMAGE_BASE_RELOCATION_BLOCK *RelocWalker;

  UINT32                                SizeOfRelocs;
  UINT32                                NumRelocs;

  UINT32                                RelocDataIndex;

  UINT32                                RelocOffset;
  UINT32                                RelocMax;

  UINT32                                RelocIndex;

  UINT64                                *WalkerFixupData;

  ASSERT (Context != NULL);
  ASSERT (!Context->RelocsStripped);
  ASSERT (RelocationData != NULL || RelocationDataSize == 0);
  ASSERT (RelocationData == NULL || RelocationDataSize >= sizeof (PE_COFF_RUNTIME_CONTEXT) + Context->RelocDirSize * (sizeof (UINT64) / sizeof (UINT16)));

  if (Context->RelocDirSize == 0) {
    return RETURN_SUCCESS;
  }
  //
  // Calculate the Image displacement from its prefered load address.
  //
  /*@ assigns Adjust;
    @ ensures Adjust == BaseAddress -% Context->ImageBase;
  */
  Adjust = BaseAddress -/*@%*/ Context->ImageBase;
  //
  // Runtime drivers should unconditionally go through the full Relocation
  // procedure early to eliminate the possibility of errors later at runtime.
  // Runtime drivers don't have their Base Relocations stripped, this is
  // verified during context creation.
  // Skip explicit Relocation when the Image is already loaded at its
  // prefered location.
  //
  /*@ assigns \nothing;
    @ ensures RelocationData != \null || BaseAddress != Context->ImageBase;
  */
  if (RelocationData == NULL && Adjust == 0) {
    return RETURN_SUCCESS;
  }

  /*@ assigns RelocationData->RelocDirRva, RelocationData->RelocDirSize;
    @ ensures RelocationData != \null ==>
    @           RelocationData->RelocDirRva == Context->RelocDirRva &&
    @           RelocationData->RelocDirSize == Context->RelocDirSize;
  */
  if (RelocationData != NULL) {
    /*@ assigns RelocationData->RelocDirRva;
      @ ensures RelocationData->RelocDirRva == Context->RelocDirRva;
    */
    RelocationData->RelocDirRva = Context->RelocDirRva;

    /*@ assigns RelocationData->RelocDirSize;
      @ ensures RelocationData->RelocDirSize == Context->RelocDirSize;
    */
    RelocationData->RelocDirSize = Context->RelocDirSize;
  }
  //
  // Apply Base Relocation fixups to the image.
  //
  /*@ assigns RelocOffset;
    @ ensures RelocOffset == Context->RelocDirRva;
    @ ensures is_aligned_32 (RelocOffset, AV_ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK));
  */
  RelocOffset = Context->RelocDirRva;

  /*@ assigns RelocMax;
    @ ensures RelocMax == Context->RelocDirRva + Context->RelocDirSize - sizeof (EFI_IMAGE_BASE_RELOCATION_BLOCK);
    @ ensures RelocOffset <= RelocMax;
  */
  RelocMax = Context->RelocDirRva + Context->RelocDirSize - sizeof (EFI_IMAGE_BASE_RELOCATION_BLOCK);

  /*@ assigns RelocDataIndex;
    @ ensures RelocDataIndex == 0;
  */
  RelocDataIndex = 0;

  //@ ghost UINT32 BaseRelocIndex = 0;
  //
  // Process all Base Relocation Blocks.
  //
  /*@ loop assigns ((char *) Context->ImageBuffer)[0  .. Context->SizeOfImage - 1];
    @ loop assigns RelocationData->FixupData[0 .. (RelocationDataSize - sizeof (PE_COFF_RUNTIME_CONTEXT)) / sizeof (UINT64) - 1];
    @ loop assigns RelocOffset, RelocWalker, SizeOfRelocs, NumRelocs, Result, Status, RelocDataIndex;
    @
    @ loop invariant Context->RelocDirRva <= RelocOffset <= Context->RelocDirRva + Context->RelocDirSize;
    @ loop invariant is_aligned_32 (RelocOffset, AV_ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK));
    @
    @ loop invariant RelocDataIndex <= (RelocOffset - Context->RelocDirRva) / sizeof (UINT16) <= Context->RelocDirSize / sizeof (UINT16);
    @
    @ loop invariant RelocMax == Context->RelocDirRva + Context->RelocDirSize - sizeof (EFI_IMAGE_BASE_RELOCATION_BLOCK);
    @
    @ loop invariant RelocOffset <= RelocMax <==> image_base_reloc_exists (RelocOffset, Context->RelocDirRva, Context->RelocDirSize);
    @ loop invariant RelocOffset <= RelocMax ==>
    @                  (\forall UINT32 i; 0 <= i <= BaseRelocIndex ==>
    @                    !image_is_base_reloc_num ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize, i));
    @
    @ loop invariant image_base_reloc_validity ((char *) Context->ImageBuffer, RelocOffset, Context->SizeOfImage, Context->RelocDirRva, Context->RelocDirSize);
    @
    @ loop invariant BaseRelocIndex <= RelocOffset - Context->RelocDirRva;
    @ loop invariant RelocOffset == image_base_reloc_offset_index ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize, BaseRelocIndex);
    @
    @ loop invariant Context->RelocDirRva < RelocOffset ==>
    @                  \let PreviousOffset = image_base_reloc_offset_index ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize, BaseRelocIndex - 1);
    @                  image_base_reloc_exists (PreviousOffset, Context->RelocDirRva, Context->RelocDirSize) && image_base_reloc_sane ((char *) Context->ImageBuffer, PreviousOffset, Context->RelocDirRva, Context->RelocDirSize);
    @
    @ loop invariant \forall integer i; 0 <= i < BaseRelocIndex ==>
    @                  \let CurRelocOffset = image_base_reloc_offset_index ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize, i);
    @                  image_reloc_correct ((char *) Context->ImageBuffer, CurRelocOffset, Context->SizeOfImage, Context->RelocDirRva, Context->RelocDirSize);
    @
    @ loop invariant \forall integer i; 0 <= i < BaseRelocIndex ==>
    @                  \let BaseRelocOffset = image_base_reloc_offset_index ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize, i);
    @                  \let BaseReloc       = (EFI_IMAGE_BASE_RELOCATION_BLOCK *) ((char *) Context->ImageBuffer + BaseRelocOffset);
    @                  \let NumRelocs       = image_base_reloc_num_relocs (BaseReloc);
    @                  \valid (BaseReloc) &&
    @                  \valid (BaseReloc->Relocations + (0 .. NumRelocs - 1)) &&
    @                  (\forall integer i; 0 <= i < NumRelocs ==>
    @                    \let RelocTarget = BaseReloc->VirtualAddress + image_reloc_offset (BaseReloc->Relocations[i]);
    @                    \valid ((char *) Context->ImageBuffer + (RelocTarget .. RelocTarget + image_reloc_size (BaseReloc->Relocations[i]) - 1)));
    @
    @ loop variant RelocMax - RelocOffset;
  */
  while (RelocOffset <= RelocMax) {
    /*@ requires image_base_reloc_exists (RelocOffset, Context->RelocDirRva, Context->RelocDirSize);
      @ requires pointer_aligned ((char *) Context->ImageBuffer + RelocOffset, AV_ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK));
      @ assigns RelocWalker;
      @ ensures RelocWalker == (EFI_IMAGE_BASE_RELOCATION_BLOCK *) ((char *) Context->ImageBuffer + RelocOffset);
      @ ensures \valid(RelocWalker);
    */
    RelocWalker = (CONST EFI_IMAGE_BASE_RELOCATION_BLOCK *) (CONST VOID *) (
                    (CONST CHAR8 *) Context->ImageBuffer + RelocOffset
                    );

    /*@ assigns Result, SizeOfRelocs;
      @ ensures !Result <==> SizeOfRelocs == RelocWalker->SizeOfBlock - sizeof (EFI_IMAGE_BASE_RELOCATION_BLOCK);
      @ ensures Result <==> 0 > RelocWalker->SizeOfBlock - sizeof (EFI_IMAGE_BASE_RELOCATION_BLOCK);
    */
    Result = BaseOverflowSubU32 (
               RelocWalker->SizeOfBlock,
               sizeof (EFI_IMAGE_BASE_RELOCATION_BLOCK),
               &SizeOfRelocs
               );
    //
    // Ensure there is at least one entry.
    // Ensure the block's size is padded to ensure proper alignment.
    //
    /*@ assigns \nothing;
      @ ensures SizeOfRelocs == RelocWalker->SizeOfBlock - sizeof (EFI_IMAGE_BASE_RELOCATION_BLOCK);
      @ ensures sizeof (EFI_IMAGE_BASE_RELOCATION_BLOCK) <= RelocWalker->SizeOfBlock;
    */
    if (Result) {
      //@ assert sizeof (EFI_IMAGE_BASE_RELOCATION_BLOCK) > RelocWalker->SizeOfBlock;
      /*@ assert \let RelocOffset = image_base_reloc_offset_index ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize, BaseRelocIndex);
        @        !image_base_reloc_sane ((char *) Context->ImageBuffer, RelocOffset, Context->RelocDirRva, Context->RelocDirSize);
      */
      /*@ assert \forall UINT32 i; BaseRelocIndex < i ==>
        @          \exists UINT32 j; 0 <= j < i &&
        @            \let RelocOffset = image_base_reloc_offset_index ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize, j);
        @            !image_base_reloc_exists (RelocOffset, Context->RelocDirRva, Context->RelocDirSize) ||
        @            !image_base_reloc_sane ((char *) Context->ImageBuffer, RelocOffset, Context->RelocDirRva, Context->RelocDirSize);
      */
      /*@ assert \forall UINT32 i; BaseRelocIndex < i ==>
        @          !(\forall UINT32 j; 0 <= j < i ==>
        @            \let RelocOffset = image_base_reloc_offset_index ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize, j);
        @            image_base_reloc_exists (RelocOffset, Context->RelocDirRva, Context->RelocDirSize) &&
        @            image_base_reloc_sane ((char *) Context->ImageBuffer, RelocOffset, Context->RelocDirRva, Context->RelocDirSize));
      */
      /*@ assert \forall UINT32 i; BaseRelocIndex < i ==>
        @          !image_is_base_reloc_num ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize, i);
      */
      //@ assert !\exists UINT32 NumRelocs; image_is_base_reloc_num ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize, NumRelocs);
      /*@ assert \forall UINT32 NumRelocs;
        @          image_is_base_reloc_num ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize, NumRelocs) <==>
        @          NumRelocs == image_base_reloc_num ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize);
      */
      /*@ assert (\forall UINT32 NumRelocs;
        @          image_is_base_reloc_num ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize, NumRelocs) <==>
        @          NumRelocs == image_base_reloc_num ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize)) ==>
        @         ((\exists UINT32 NumRelocs; image_is_base_reloc_num ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize, NumRelocs) <==>
        @         \exists UINT32 NumRelocs; NumRelocs == image_base_reloc_num ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize)));
      */
      //@ assert !\exists UINT32 NumRelocs; NumRelocs == image_base_reloc_num ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize);
      //@ assert !image_reloc_dir_correct ((char *) Context->ImageBuffer, Context->SizeOfImage, Context->RelocDirRva, Context->RelocDirSize);
      ASSERT (FALSE);
      return RETURN_UNSUPPORTED;
    }

    /*@ assigns \nothing;
      @ ensures RelocOffset + RelocWalker->SizeOfBlock <= Context->RelocDirRva + Context->RelocDirSize;
    */
    if (SizeOfRelocs > RelocMax - RelocOffset) {
      //@ assert RelocOffset + RelocWalker->SizeOfBlock > Context->RelocDirRva + Context->RelocDirSize;
      /*@ assert \let RelocOffset = image_base_reloc_offset_index ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize, BaseRelocIndex);
        @        !image_base_reloc_sane ((char *) Context->ImageBuffer, RelocOffset, Context->RelocDirRva, Context->RelocDirSize);
      */
      /*@ assert \forall UINT32 i; BaseRelocIndex < i ==>
        @          \exists UINT32 j; 0 <= j < i &&
        @            \let RelocOffset = image_base_reloc_offset_index ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize, j);
        @            !image_base_reloc_exists (RelocOffset, Context->RelocDirRva, Context->RelocDirSize) ||
        @            !image_base_reloc_sane ((char *) Context->ImageBuffer, RelocOffset, Context->RelocDirRva, Context->RelocDirSize);
      */
      /*@ assert \forall UINT32 i; BaseRelocIndex < i ==>
        @          !(\forall UINT32 j; 0 <= j < i ==>
        @            \let RelocOffset = image_base_reloc_offset_index ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize, j);
        @            image_base_reloc_exists (RelocOffset, Context->RelocDirRva, Context->RelocDirSize) &&
        @            image_base_reloc_sane ((char *) Context->ImageBuffer, RelocOffset, Context->RelocDirRva, Context->RelocDirSize));
      */
      /*@ assert \forall UINT32 i; BaseRelocIndex < i ==>
        @          !image_is_base_reloc_num ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize, i);
      */
      //@ assert !\exists UINT32 NumRelocs; image_is_base_reloc_num ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize, NumRelocs);
      /*@ assert \forall UINT32 NumRelocs;
        @          image_is_base_reloc_num ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize, NumRelocs) <==>
        @          NumRelocs == image_base_reloc_num ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize);
      */
      /*@ assert (\forall UINT32 NumRelocs;
        @          image_is_base_reloc_num ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize, NumRelocs) <==>
        @          NumRelocs == image_base_reloc_num ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize)) ==>
        @         ((\exists UINT32 NumRelocs; image_is_base_reloc_num ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize, NumRelocs) <==>
        @         \exists UINT32 NumRelocs; NumRelocs == image_base_reloc_num ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize)));
      */
      //@ assert !\exists UINT32 NumRelocs; NumRelocs == image_base_reloc_num ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize);
      //@ assert !image_reloc_dir_correct ((char *) Context->ImageBuffer, Context->SizeOfImage, Context->RelocDirRva, Context->RelocDirSize);
      ASSERT (FALSE);
      return RETURN_UNSUPPORTED;
    }

    /*@ assigns \nothing;
      @ ensures is_aligned_32 (RelocWalker->SizeOfBlock, AV_ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK));
    */
    if (!IS_ALIGNED (RelocWalker->SizeOfBlock, OC_ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK))) {
      //@ assert !is_aligned_32 (RelocWalker->SizeOfBlock, AV_ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK));
      /*@ assert \let RelocOffset = image_base_reloc_offset_index ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize, BaseRelocIndex);
        @        !image_base_reloc_sane ((char *) Context->ImageBuffer, RelocOffset, Context->RelocDirRva, Context->RelocDirSize);
      */
      /*@ assert \forall UINT32 i; BaseRelocIndex < i ==>
        @          \exists UINT32 j; 0 <= j < i &&
        @            \let RelocOffset = image_base_reloc_offset_index ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize, j);
        @            !image_base_reloc_exists (RelocOffset, Context->RelocDirRva, Context->RelocDirSize) ||
        @            !image_base_reloc_sane ((char *) Context->ImageBuffer, RelocOffset, Context->RelocDirRva, Context->RelocDirSize);
      */
      /*@ assert \forall UINT32 i; BaseRelocIndex < i ==>
        @          !(\forall UINT32 j; 0 <= j < i ==>
        @            \let RelocOffset = image_base_reloc_offset_index ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize, j);
        @            image_base_reloc_exists (RelocOffset, Context->RelocDirRva, Context->RelocDirSize) &&
        @            image_base_reloc_sane ((char *) Context->ImageBuffer, RelocOffset, Context->RelocDirRva, Context->RelocDirSize));
      */
      /*@ assert \forall UINT32 i; BaseRelocIndex < i ==>
        @          !image_is_base_reloc_num ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize, i);
      */
      //@ assert !\exists UINT32 NumRelocs; image_is_base_reloc_num ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize, NumRelocs);
      /*@ assert \forall UINT32 NumRelocs;
        @          image_is_base_reloc_num ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize, NumRelocs) <==>
        @          NumRelocs == image_base_reloc_num ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize);
      */
      /*@ assert (\forall UINT32 NumRelocs;
        @          image_is_base_reloc_num ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize, NumRelocs) <==>
        @          NumRelocs == image_base_reloc_num ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize)) ==>
        @         ((\exists UINT32 NumRelocs; image_is_base_reloc_num ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize, NumRelocs) <==>
        @         \exists UINT32 NumRelocs; NumRelocs == image_base_reloc_num ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize)));
      */
      //@ assert !\exists UINT32 NumRelocs; NumRelocs == image_base_reloc_num ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize);
      //@ assert !image_reloc_dir_correct ((char *) Context->ImageBuffer, Context->SizeOfImage, Context->RelocDirRva, Context->RelocDirSize);
      DEBUG ((DEBUG_INFO, "RelocSize %u\n", RelocWalker->SizeOfBlock));
      ASSERT (FALSE);
      return RETURN_UNSUPPORTED;
    }

    /*@ assert image_base_reloc_sane ((char *) Context->ImageBuffer, RelocOffset, Context->RelocDirRva, Context->RelocDirSize) &&
      @        image_base_reloc_mem_valid ((char *) Context->ImageBuffer, RelocWalker, Context->SizeOfImage, Context->RelocDirRva, Context->RelocDirSize) &&
      @        image_base_reloc_validity ((char *) Context->ImageBuffer, RelocOffset + RelocWalker->SizeOfBlock, Context->SizeOfImage, Context->RelocDirRva, Context->RelocDirSize);
    */
    //
    // This division is safe due to the guarantee made above.
    //
    /*@ assigns NumRelocs;
      @ ensures NumRelocs == image_base_reloc_num_relocs (RelocWalker);
    */
    NumRelocs = SizeOfRelocs / sizeof (*RelocWalker->Relocations);
    //
    // Apply all Base Relocation fixups of the current block.
    //
    /*@ assigns WalkerFixupData;
      @ ensures RelocationData != \null ==>
      @           WalkerFixupData == &RelocationData->FixupData[RelocDataIndex];
      @ ensures RelocationData == \null ==>
      @           WalkerFixupData == \null;
      @ ensures WalkerFixupData == &RelocationData->FixupData[RelocDataIndex] || WalkerFixupData == \null;
    */
    if (RelocationData != NULL) {
      /*@ assigns WalkerFixupData;
        @ ensures WalkerFixupData == &RelocationData->FixupData[RelocDataIndex];
        @ ensures WalkerFixupData != \null;
      */
      WalkerFixupData = &RelocationData->FixupData[RelocDataIndex];
    } else {
      /*@ assigns WalkerFixupData;
        @ ensures WalkerFixupData == \null;
      */
      WalkerFixupData = NULL;
    }
    //
    // Process all Base Relocations of the current Block.
    //
    /*@ loop assigns RelocIndex, Result, RelocationData->FixupData[RelocDataIndex .. RelocDataIndex + NumRelocs - 1], ((char *) Context->ImageBuffer)[0 .. Context->SizeOfImage - 1];
      @
      @ loop invariant 0 <= RelocIndex <= image_base_reloc_num_relocs (RelocWalker);
      @ loop invariant 0 <= RelocIndex <= NumRelocs;
      @ loop invariant \valid(RelocWalker->Relocations + (0 .. image_base_reloc_num_relocs (RelocWalker) - 1));
      @ loop invariant RelocationData != \null ==> \valid(RelocationData->FixupData + (0 .. image_base_reloc_num_relocs (RelocWalker) - 1));
      @ loop invariant image_base_reloc_mem_valid ((char *) Context->ImageBuffer, RelocWalker, Context->SizeOfImage, Context->RelocDirRva, Context->RelocDirSize);
      @ loop invariant \forall integer i; 0 <= i < RelocIndex ==>
      @                  image_reloc_sane (RelocWalker, i, Context->RelocDirRva, Context->RelocDirSize, Context->SizeOfImage);
      @ loop invariant WalkerFixupData == &RelocationData->FixupData[RelocDataIndex] || WalkerFixupData == \null;
      @
      @ loop invariant \forall integer i; 0 <= i < RelocIndex ==>
      @                  \let RelocTarget = RelocWalker->VirtualAddress + image_reloc_offset (RelocWalker->Relocations[i]);
      @                  \valid ((char *) Context->ImageBuffer + (RelocTarget .. RelocTarget + image_reloc_size (RelocWalker->Relocations[i]) - 1));
      @
      @ loop variant image_base_reloc_num_relocs (RelocWalker) - RelocIndex;
    */
    for (RelocIndex = 0; RelocIndex < NumRelocs; ++RelocIndex) {
      //
      // Apply the Base Relocation fixup per type.
      // If RelocationData is not NULL, store the current value of the fixup
      // target to determine whether it has been changed during runtime
      // execution.
      //
      // It is not clear how EFI_IMAGE_REL_BASED_HIGH and
      // EFI_IMAGE_REL_BASED_LOW are supposed to be handled. While PE reference
      // suggests to just add the high or low part of the displacement, there
      // are concerns about how it's supposed to deal with wraparounds.
      // As neither LLD,
      //

      /*@ assigns Status, RelocationData->FixupData[RelocDataIndex .. RelocDataIndex + NumRelocs - 1], ((char *) Context->ImageBuffer)[0 .. Context->SizeOfImage - 1];
        @ ensures Status == RETURN_SUCCESS <==> image_reloc_sane (RelocWalker, RelocIndex, Context->RelocDirRva, Context->RelocDirSize, Context->SizeOfImage);
      */
      Status = InternalApplyRelocation (
                 Context,
                 RelocWalker,
                 RelocIndex,
                 Adjust,
                 WalkerFixupData
                 );

      /*@ assigns \nothing;
        @ ensures image_reloc_sane (RelocWalker, RelocIndex, Context->RelocDirRva, Context->RelocDirSize, Context->SizeOfImage);
      */
      if (Status != RETURN_SUCCESS) {
        /*@ assert \let RelocOffset = image_base_reloc_offset_index ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize, BaseRelocIndex);
          @        \let BaseReloc = (EFI_IMAGE_BASE_RELOCATION_BLOCK *) ((char *) Context->ImageBuffer + RelocOffset);
          @        \let NumRelocs = image_base_reloc_num_relocs (BaseReloc);
          @        \exists integer i; 0 <= i < NumRelocs && i == RelocIndex &&
          @          !image_reloc_sane (BaseReloc, RelocIndex, Context->RelocDirRva, Context->RelocDirSize, Context->SizeOfImage);
        */
        /*@ assert \let RelocOffset = image_base_reloc_offset_index ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize, BaseRelocIndex);
          @        !image_reloc_correct ((char *) Context->ImageBuffer, RelocOffset, Context->SizeOfImage, Context->RelocDirRva, Context->RelocDirSize);
        */
        /*@ assert (\exists UINT32 NumRelocs; image_is_base_reloc_num ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize, NumRelocs)) ==>
          @          BaseRelocIndex < image_base_reloc_num ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize);
        */
        /*@ assert (\exists UINT32 NumRelocs; image_is_base_reloc_num ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize, NumRelocs)) ==>
          @            !(\forall UINT32 i; 0 <= i < image_base_reloc_num ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize) ==>
          @              \let RelocOffset = image_base_reloc_offset_index ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize, i);
          @              image_reloc_correct ((char *) Context->ImageBuffer, RelocOffset, Context->SizeOfImage, Context->RelocDirRva, Context->RelocDirSize));
        */
        /*@ assert (\exists UINT32 NumRelocs; image_is_base_reloc_num ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize, NumRelocs)) ==>
          @          !image_relocs_correct ((char *) Context->ImageBuffer, Context->SizeOfImage, Context->RelocDirRva, Context->RelocDirSize, image_base_reloc_num ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize));
        */
        /*@ assert !\exists UINT32 NumRelocs; image_is_base_reloc_num ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize, NumRelocs) &&
          @          image_relocs_correct ((char *) Context->ImageBuffer, Context->SizeOfImage, Context->RelocDirRva, Context->RelocDirSize, NumRelocs);
        */
        //@ assert !image_reloc_dir_correct ((char *) Context->ImageBuffer, Context->SizeOfImage, Context->RelocDirRva, Context->RelocDirSize);
        ASSERT (FALSE);
        return Status;
      }
    }

    //@ assert image_reloc_correct ((char *) Context->ImageBuffer, RelocOffset, Context->SizeOfImage, Context->RelocDirRva, Context->RelocDirSize);

    /*@ assert \forall integer i; 0 <= i <= BaseRelocIndex && i == BaseRelocIndex ==>
      @          \let BaseRelocOffset = image_base_reloc_offset_index ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize, i);
      @          \let BaseReloc       = (EFI_IMAGE_BASE_RELOCATION_BLOCK *) ((char *) Context->ImageBuffer + BaseRelocOffset);
      @          \let NumRelocs       = image_base_reloc_num_relocs (BaseReloc);
      @          \valid (BaseReloc) &&
      @          \valid (BaseReloc->Relocations + (0 .. NumRelocs - 1)) &&
      @          (\forall integer i; 0 <= i < NumRelocs ==>
      @            \let RelocTarget = BaseReloc->VirtualAddress + image_reloc_offset (BaseReloc->Relocations[i]);
      @            \valid ((char *) Context->ImageBuffer + (RelocTarget .. RelocTarget + image_reloc_size (BaseReloc->Relocations[i]) - 1)));
    */

    /*@ requires RelocDataIndex <= (RelocOffset - Context->RelocDirRva) / sizeof (UINT16);
      @ assigns RelocDataIndex;
      @ ensures RelocDataIndex == \old(RelocDataIndex) + image_base_reloc_num_relocs (RelocWalker);
      @ ensures RelocDataIndex <= ((RelocOffset - Context->RelocDirRva) + RelocWalker->SizeOfBlock) / sizeof (UINT16);
    */
    RelocDataIndex += NumRelocs;

    /*@ requires is_aligned_32 (RelocOffset, AV_ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK)) && is_aligned_32 (RelocWalker->SizeOfBlock, AV_ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK)) ==>
      @          is_aligned_32 (RelocOffset +% RelocWalker->SizeOfBlock, AV_ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK));
      @ requires is_aligned_32 (RelocOffset, AV_ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK));
      @ requires is_aligned_32 (RelocWalker->SizeOfBlock, AV_ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK));
      @ requires RelocWalker == (EFI_IMAGE_BASE_RELOCATION_BLOCK *) ((char *) Context->ImageBuffer + RelocOffset);
      @
      @ assigns RelocOffset;
      @
      @ ensures RelocOffset == \old(RelocOffset) + RelocWalker->SizeOfBlock;
      @ ensures Context->RelocDirRva <= RelocOffset <= Context->RelocDirRva + Context->RelocDirSize;
      @ ensures RelocOffset == image_base_reloc_offset_index ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize, BaseRelocIndex + 1);
      @ ensures is_aligned_32 (RelocOffset, AV_ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK));
    */
    RelocOffset += RelocWalker->SizeOfBlock;

    //@ ghost ++BaseRelocIndex;

    //@ assert RelocOffset <= RelocMax <==> image_base_reloc_exists (RelocOffset, Context->RelocDirRva, Context->RelocDirSize);
    //@ assert RelocOffset <= RelocMax ==> !image_is_base_reloc_num ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize, BaseRelocIndex);
    /*@ assert RelocOffset <= RelocMax ==>
      @          (\forall UINT32 i; 0 <= i <= BaseRelocIndex ==>
      @            !image_is_base_reloc_num ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize, i));
    */
  }

  //@ assert image_is_base_reloc_num ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize, BaseRelocIndex);
  //@ assert BaseRelocIndex == image_base_reloc_num ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize);
  //@ assert image_relocs_correct ((char *) Context->ImageBuffer, Context->SizeOfImage, Context->RelocDirRva, Context->RelocDirSize, BaseRelocIndex);
  //@ assert image_reloc_dir_valid ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize);
  /*@ assert RelocationData != \null ==>
    @          Context->RelocDirRva == RelocationData->RelocDirRva && Context->RelocDirSize == RelocationData->RelocDirSize;
  */
  /*@ assert RelocationData != \null ==>
    @          image_reloc_dir_valid ((char *) Context->ImageBuffer, RelocationData->RelocDirRva, RelocationData->RelocDirSize);
  */
  //
  // Ensure the Relocation Directory size matches the contained data.
  //
  /*@ assigns \nothing;
    @ ensures \exists UINT32 NumBaseRelocs; NumBaseRelocs == image_base_reloc_num ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize) && NumBaseRelocs == BaseRelocIndex &&
    @           image_relocs_correct ((char *) Context->ImageBuffer, Context->SizeOfImage, Context->RelocDirRva, Context->RelocDirSize, NumBaseRelocs) &&
    @           image_base_reloc_offset_index ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize, NumBaseRelocs) == Context->RelocDirRva + Context->RelocDirSize;
    @ ensures image_reloc_dir_correct ((char *) Context->ImageBuffer, Context->SizeOfImage, Context->RelocDirRva, Context->RelocDirSize);
  */
  if (RelocOffset != RelocMax + sizeof (EFI_IMAGE_BASE_RELOCATION_BLOCK)) {
    /*@ assert \let NumBaseRelocs = image_base_reloc_num ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize);
      @        image_base_reloc_offset_index ((char *) Context->ImageBuffer, Context->RelocDirRva, Context->RelocDirSize, NumBaseRelocs) != Context->RelocDirRva + Context->RelocDirSize;
    */
    //@ assert !image_reloc_dir_correct ((char *) Context->ImageBuffer, Context->SizeOfImage, Context->RelocDirRva, Context->RelocDirSize);
    ASSERT (FALSE);
    return RETURN_UNSUPPORTED;
  }
  //
  // Initialise the still uninitialised portion of the Runtime context.
  //
  //@ assigns RelocationData->FixupData[RelocDataIndex .. (RelocationDataSize - sizeof (PE_COFF_RUNTIME_CONTEXT)) / sizeof (UINT64) - 1];
  if (RelocationData != NULL) {
    /*@ assigns RelocationData->FixupData[RelocDataIndex .. (RelocationDataSize - sizeof (PE_COFF_RUNTIME_CONTEXT)) / sizeof (UINT64) - 1];
      @ ensures \forall integer i; 0 <= i < (RelocationDataSize - sizeof (PE_COFF_RUNTIME_CONTEXT)) / sizeof (UINT64) - RelocDataIndex ==>
      @           RelocationData->FixupData[RelocDataIndex + i] == 0;
    */
    ZeroMem (
      &RelocationData->FixupData[RelocDataIndex],
      RelocationDataSize - sizeof (PE_COFF_RUNTIME_CONTEXT) - RelocDataIndex * sizeof (UINT64)
      );
  }

  return RETURN_SUCCESS;
}

/**
  Apply an Image Base Relocation for Runtime Relocation.

  Correctness has been ensured by PeCoffRelocateImage() previously.
  Fails if the Relocation target value has changed since PeCoffRelocateImage().

  @param[in]  Image       The Image destination memory. Must have been relocated
                          by PeCoffRelocateImage().
  @param[in]  RelocBlock  The Base Relocation Block to apply from.
  @param[in]  RelocIndex  The index of the Base Relocation to apply.
  @param[in]  Adjust      The delta to add to the addresses.
  @param[out] FixupData   The bookkeeping value.

  @retval RETURN_SUCCESS  The Base Relocation has been applied successfully.
  @retval other           The Base Relocation could not be applied successfully.
**/
/*@ requires \typeof(Fixup) <: \type(char *);
  @ requires image_reloc_type_supported (RelocType) && RelocType != EFI_IMAGE_REL_BASED_ABSOLUTE;
  @ requires RelocType == EFI_IMAGE_REL_BASED_ARM_MOV32T ==>
  @            pointer_aligned (Fixup, AV_ALIGNOF (UINT16));
  @ requires \valid((char *) Fixup + (0 .. image_reloc_type_size (RelocType) - 1));
  @
  @ assigns ((char *) Fixup)[0 .. image_reloc_type_size (RelocType) - 1];
  @
  @ ensures !PcdGetBool (PcdImageLoaderRtRelocAllowTargetMismatch) ==>
  @           (\result == RETURN_SUCCESS <==>
  @             image_reloc_target_value{Pre} ((char *) Fixup, RelocType) == FixupData);
  @
  @ behavior valid_highlow:
  @   assumes RelocType == EFI_IMAGE_REL_BASED_HIGHLOW;
  @   assumes uint32_from_char ((char *) Fixup) == FixupData;
  @   assigns ((char *) Fixup)[0 .. 3];
  @   ensures image_fixup_applied_highlow{Pre,Post} ((char *) Fixup, Adjust);
  @   ensures \result == RETURN_SUCCESS;
  @
  @ behavior valid_dir64:
  @   assumes RelocType == EFI_IMAGE_REL_BASED_DIR64;
  @   assumes uint64_from_char ((char *) Fixup) == FixupData;
  @   assigns ((char *) Fixup)[0 .. 7];
  @   ensures image_fixup_applied_dir64{Pre,Post} ((char *) Fixup, Adjust);
  @   ensures \result == RETURN_SUCCESS;
  @
  @ behavior valid_arm_mov32t:
  @   assumes RelocType == EFI_IMAGE_REL_BASED_ARM_MOV32T;
  @   assumes uint64_from_char ((char *) Fixup) == FixupData;
  @   assigns ((char *) Fixup)[0 .. 7];
  @   ensures \result == RETURN_SUCCESS;
  @
  @ behavior invalid_32:
  @   assumes RelocType == EFI_IMAGE_REL_BASED_HIGHLOW;
  @   assumes uint32_from_char ((char *) Fixup) != FixupData;
  @   assigns \nothing;
  @   ensures PcdGetBool (PcdImageLoaderRtRelocAllowTargetMismatch) ==>
  @             \result == RETURN_SUCCESS;
  @   ensures !PcdGetBool (PcdImageLoaderRtRelocAllowTargetMismatch) ==>
  @             \result != RETURN_SUCCESS;
  @
  @ behavior invalid_64:
  @   assumes RelocType == EFI_IMAGE_REL_BASED_DIR64 || RelocType == EFI_IMAGE_REL_BASED_ARM_MOV32T;
  @   assumes uint64_from_char ((char *) Fixup) != FixupData;
  @   assigns \nothing;
  @   ensures PcdGetBool (PcdImageLoaderRtRelocAllowTargetMismatch) ==>
  @             \result == RETURN_SUCCESS;
  @   ensures !PcdGetBool (PcdImageLoaderRtRelocAllowTargetMismatch) ==>
  @             \result != RETURN_SUCCESS;
  @
  @ complete behaviors;
  @ disjoint behaviors;
*/
STATIC
RETURN_STATUS
InternalApplyRelocationRuntime (
  IN OUT VOID    *Fixup,
  IN     UINT16  RelocType,
  IN     UINT64  Adjust,
  IN     UINT64  FixupData
  )
{
  UINT32       Fixup32;
  UINT64       Fixup64;

  ASSERT (Fixup != NULL);
  ASSERT (IMAGE_RELOC_TYPE_SUPPORTED (RelocType)
       && RelocType != EFI_IMAGE_REL_BASED_ABSOLUTE);

  /*@ assigns ((char *) Fixup)[0 .. image_reloc_type_size (RelocType) - 1];
    @ ensures RelocType == EFI_IMAGE_REL_BASED_HIGHLOW ==>
    @           image_fixup_applied_highlow{Old,Here} ((char *) Fixup, Adjust);
    @ ensures RelocType == EFI_IMAGE_REL_BASED_DIR64 ==>
    @           image_fixup_applied_dir64{Old,Here} ((char *) Fixup, Adjust);
    @ ensures !PcdGetBool (PcdImageLoaderRtRelocAllowTargetMismatch) ==>
    @           image_reloc_target_value{Pre} ((char *) Fixup, RelocType) == FixupData;
  */
  switch (RelocType) { /* LCOV_EXCL_BR_LINE */
    case EFI_IMAGE_REL_BASED_HIGHLOW:
      /*@ assigns Fixup32;
        @ ensures Fixup32 == uint32_from_char ((char *) Fixup);
      */
      Fixup32 = ReadUnaligned32 (Fixup);

      /*@ assigns \nothing;
        @ ensures FixupData == Fixup32;
      */
      if (FixupData != Fixup32) {
        /*@ assigns \nothing;
          @ ensures !PcdGetBool (PcdImageLoaderRtRelocAllowTargetMismatch);
        */
        if (PcdGetBool (PcdImageLoaderRtRelocAllowTargetMismatch)) {
          /*@ assert !PcdGetBool (PcdImageLoaderRtRelocAllowTargetMismatch) ==>
            @          image_reloc_target_value{Pre} ((char *) Fixup, RelocType) == FixupData;
          */
          return RETURN_SUCCESS;
        }

        /*@ assert !PcdGetBool (PcdImageLoaderRtRelocAllowTargetMismatch) ==>
          @          image_reloc_target_value{Pre} ((char *) Fixup, RelocType) != FixupData;
        */
        return RETURN_UNSUPPORTED;
      }

      /*@ assigns Fixup32;
        @ ensures Fixup32 == \old(Fixup32) +% (UINT32 %) Adjust;
      */
      Fixup32 +=/*@%*/ (UINT32)/*@%*/ Adjust;

      /*@ assigns ((char *) Fixup)[0 .. 3];
        @ ensures image_fixup_applied_highlow{Old,Here} ((char *) Fixup, Adjust);
      */
      WriteUnaligned32 (Fixup, Fixup32);

      break;

    case EFI_IMAGE_REL_BASED_DIR64:
      /*@ assigns Fixup64;
        @ ensures Fixup64 == uint64_from_char ((char *) Fixup) ;
      */
      Fixup64 = ReadUnaligned64 (Fixup);

      /*@ assigns \nothing;
        @ ensures FixupData == Fixup64;
      */
      if (FixupData != Fixup64) {
        /*@ assigns \nothing;
          @ ensures !PcdGetBool (PcdImageLoaderRtRelocAllowTargetMismatch);
        */
        if (PcdGetBool (PcdImageLoaderRtRelocAllowTargetMismatch)) {
          /*@ assert !PcdGetBool (PcdImageLoaderRtRelocAllowTargetMismatch) ==>
            @          image_reloc_target_value{Pre} ((char *) Fixup, RelocType) == FixupData;
          */
          return RETURN_SUCCESS;
        }

        /*@ assert !PcdGetBool (PcdImageLoaderRtRelocAllowTargetMismatch) ==>
          @          image_reloc_target_value{Pre} ((char *) Fixup, RelocType) != FixupData;
        */
        return RETURN_UNSUPPORTED;
      }

      /*@ assigns Fixup64;
        @ ensures Fixup64 == \old(Fixup64) +% Adjust;
      */
      Fixup64 +=/*@%*/ Adjust;

      /*@ assigns ((char *) Fixup)[0 .. 7];
        @ ensures image_fixup_applied_dir64{Old,Here} ((char *) Fixup, Adjust);
      */
      WriteUnaligned64 (Fixup, Fixup64);

      break;

    case EFI_IMAGE_REL_BASED_ARM_MOV32T:
      ASSERT (PcdGetBool (PcdImageLoaderSupportArmThumb));

      /*@ assigns Fixup64;
        @ ensures Fixup64 == uint64_from_char ((char *) Fixup);
      */
      Fixup64 = ReadUnaligned64 (Fixup);

      /*@ assigns \nothing;
        @ ensures FixupData == Fixup64;
      */
      if (FixupData != Fixup64) {
        /*@ assigns \nothing;
          @ ensures !PcdGetBool (PcdImageLoaderRtRelocAllowTargetMismatch);
        */
        if (PcdGetBool (PcdImageLoaderRtRelocAllowTargetMismatch)) {
          /*@ assert !PcdGetBool (PcdImageLoaderRtRelocAllowTargetMismatch) ==>
            @          image_reloc_target_value{Pre} ((char *) Fixup, RelocType) == FixupData;
          */
          return RETURN_SUCCESS;
        }

        /*@ assert !PcdGetBool (PcdImageLoaderRtRelocAllowTargetMismatch) ==>
          @          image_reloc_target_value{Pre} ((char *) Fixup, RelocType) != FixupData;
        */
        return RETURN_UNSUPPORTED;
      }

      /*@ assigns ((char *) Fixup)[0 .. 7];
      */
      ThumbMovwMovtImmediateFixup (Fixup, Adjust);

      break;

  /* LCOV_EXCL_START */
    default:
      ASSERT (FALSE);
  }
  /* LCOV_EXCL_STOP */

  return RETURN_SUCCESS;
}

RETURN_STATUS
PeCoffRelocationDataSize (
  IN  CONST PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  OUT UINT32                       *Size
  )
{
  BOOLEAN Result;

  ASSERT (Context != NULL);
  ASSERT (Size != NULL);
  //
  // Because Base Relocations have not been stripped, PeCoffInitializeContext()
  // has verified the Relocation Directory exists and is valid.
  //

  //
  // Request 64-bit of source value per 16-bit Base Relocation.
  // This allocates too many bytes because it assumes that every Base Relocation
  // refers to a 64-bit target and does not account for Base Relocation Block
  // headers.
  //
  /*@ assigns Result, *Size;
    @ ensures *Size == Context->RelocDirSize *% (UINT32) (sizeof (UINT64) / sizeof (UINT16));
    @ ensures !Result <==> *Size == Context->RelocDirSize * sizeof (UINT64) / sizeof (UINT16);
  */
  Result = BaseOverflowMulU32 (
             Context->RelocDirSize,
             sizeof (UINT64) / sizeof (UINT16),
             Size
             );
  /*@ assigns \nothing;
    @ ensures *Size == Context->RelocDirSize * sizeof (UINT64) / sizeof (UINT16);
  */
  if (Result) {
    return RETURN_UNSUPPORTED;
  }

  /*@ assigns Result, *Size;
    @ ensures !Result <==> *Size == sizeof (PE_COFF_RUNTIME_CONTEXT) + Context->RelocDirSize * sizeof (UINT64) / sizeof (UINT16);
  */
  Result = BaseOverflowAddU32 (
             *Size,
             sizeof (PE_COFF_RUNTIME_CONTEXT),
             Size
             );
  /*@ assigns \nothing;
    @ ensures *Size == image_context_runtime_fixup_size (Context);
  */
  if (Result) {
    return RETURN_UNSUPPORTED;
  }

  return RETURN_SUCCESS;
}

RETURN_STATUS
PeCoffRelocateImageForRuntime (
  IN OUT VOID                           *Image,
  IN     UINT32                         ImageSize,
  IN     UINT64                         BaseAddress,
  IN     CONST PE_COFF_RUNTIME_CONTEXT  *RelocationData
  )
{
  UINTN                                 ImageAddress;
  UINT32                                FixupDataIndex;
  CONST EFI_IMAGE_BASE_RELOCATION_BLOCK *RelocWalker;
  UINT64                                Adjust;
  RETURN_STATUS                         Status;

  UINT32                                RelocOffset;
  UINT32                                SizeOfRelocs;
  UINT32                                NumRelocs;
  UINT32                                RelocIndex;
  UINT32                                RelocTarget;
  UINT32                                RelocSuboffset;

  (VOID) ImageSize;

  ASSERT (Image != NULL);
  ASSERT (BaseAddress != 0);
  ASSERT (RelocationData != NULL);
  //
  // This function assumes the image has previously been validated by
  // PeCoffInitializeContext().
  //
  /*@ assigns ImageAddress;
    @ ensures ImageAddress == pointer_to_address (Image);
  */
  ImageAddress = PTR_TO_ADDR (Image, 0);

  /*@ assigns Adjust;
    @ ensures Adjust == BaseAddress -% ImageAddress;
  */
  Adjust = BaseAddress -/*@%*/ ImageAddress;

  /*@ assigns \nothing;
    @ ensures BaseAddress != ImageAddress;
  */
  if (Adjust == 0) {
    return RETURN_SUCCESS;
  }

  /*@ assigns FixupDataIndex;
    @ ensures FixupDataIndex == 0;
  */
  FixupDataIndex = 0;

  //@ ghost UINT32 BaseRelocIndex = 0;

  /*@ assigns RelocOffset;
    @ ensures RelocOffset == image_base_reloc_offset_index ((char *) Image, RelocationData->RelocDirRva, RelocationData->RelocDirSize, 0);
    @ ensures is_aligned_32 (RelocOffset, AV_ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK));
  */
  RelocOffset = RelocationData->RelocDirRva;

  /*@ loop assigns RelocOffset, RelocWalker, SizeOfRelocs, NumRelocs, FixupDataIndex, RelocIndex, RelocTarget, Status;
    @ loop assigns ((char *) Image)[0 .. ImageSize - 1];
    @
    @ loop invariant RelocOffset == image_base_reloc_offset_index ((char *) Image, RelocationData->RelocDirRva, RelocationData->RelocDirSize, BaseRelocIndex);
    @ loop invariant RelocationData->RelocDirRva <= RelocOffset <= RelocationData->RelocDirRva + RelocationData->RelocDirSize;
    @ loop invariant is_aligned_32 (RelocOffset, AV_ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK));
    @
    @ loop invariant 0 <= BaseRelocIndex <= image_base_reloc_num ((char *) Image, RelocationData->RelocDirRva, RelocationData->RelocDirSize);
    @ loop invariant BaseRelocIndex < image_base_reloc_num ((char *) Image, RelocationData->RelocDirRva, RelocationData->RelocDirSize) <==> RelocOffset < RelocationData->RelocDirRva + RelocationData->RelocDirSize;
    @ loop invariant 0 <= FixupDataIndex <= (RelocOffset - RelocationData->RelocDirRva) / sizeof (UINT16) <= RelocationData->RelocDirSize / sizeof (UINT16);
    @
    @ loop invariant image_reloc_dir_correct ((char *) Image, ImageSize, RelocationData->RelocDirRva, RelocationData->RelocDirSize);
    @ loop invariant image_reloc_dir_valid ((char *) Image, RelocationData->RelocDirRva, RelocationData->RelocDirSize);
    @
    @ loop variant RelocationData->RelocDirRva + RelocationData->RelocDirSize - RelocOffset;
  */
  while (RelocOffset < RelocationData->RelocDirRva + RelocationData->RelocDirSize) {
    /*@ assert image_base_reloc_exists (RelocOffset, RelocationData->RelocDirRva, RelocationData->RelocDirSize) &&
      @        image_base_reloc_sane ((char *) Image, RelocOffset, RelocationData->RelocDirRva, RelocationData->RelocDirSize);
    */

    /*@ assert \let BaseReloc = (EFI_IMAGE_BASE_RELOCATION_BLOCK *) ((char *) Image + RelocOffset);
      @        \let NumRelocs = image_base_reloc_num_relocs (BaseReloc);
      @        \valid (BaseReloc) &&
      @        \valid (BaseReloc->Relocations + (0 .. NumRelocs - 1)) &&
      @        (\forall integer j; 0 <= j < NumRelocs ==>
      @          \let RelocTarget = BaseReloc->VirtualAddress + image_reloc_offset (BaseReloc->Relocations[j]);
      @          \valid ((char *) Image + (RelocTarget .. RelocTarget + image_reloc_size (BaseReloc->Relocations[j]) - 1)));
    */

    /*@ assert \let BaseReloc = (EFI_IMAGE_BASE_RELOCATION_BLOCK *) ((char *) Image + RelocOffset);
      @        \let NumRelocs = image_base_reloc_num_relocs (BaseReloc);
      @        (\forall integer j; 0 <= j < NumRelocs ==>
      @          image_reloc_sane (BaseReloc, j, RelocationData->RelocDirRva, RelocationData->RelocDirSize, ImageSize) &&
      @          \let RelocTarget = BaseReloc->VirtualAddress + image_reloc_offset (BaseReloc->Relocations[j]);
      @          image_reloc_sane (BaseReloc, j, RelocationData->RelocDirRva, RelocationData->RelocDirSize, ImageSize) ==>
      @            (image_reloc_type (BaseReloc->Relocations[j]) == EFI_IMAGE_REL_BASED_ARM_MOV32T ==>
      @              is_aligned_32 ((UINT32) RelocTarget, AV_ALIGNOF (UINT16))));
    */

    /*@ assert \let BaseReloc = (EFI_IMAGE_BASE_RELOCATION_BLOCK *) ((char *) Image + RelocOffset);
      @        \let NumRelocs = image_base_reloc_num_relocs (BaseReloc);
      @        (\forall integer j; 0 <= j < NumRelocs ==>
      @          \let RelocTarget = BaseReloc->VirtualAddress + image_reloc_offset (BaseReloc->Relocations[j]);
      @          image_reloc_type (BaseReloc->Relocations[j]) == EFI_IMAGE_REL_BASED_ARM_MOV32T ==>
      @            is_aligned_32 ((UINT32) RelocTarget, AV_ALIGNOF (UINT16)));
    */

    /*@ requires pointer_max_aligned (Image) && is_aligned_N (RelocOffset, AV_ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK)) ==>
      @            pointer_aligned ((char *) Image + RelocOffset, AV_ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK));
      @ requires pointer_max_aligned (Image);
      @ requires is_aligned_N (RelocOffset, AV_ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK));
      @ assigns RelocWalker;
      @ ensures RelocWalker == (EFI_IMAGE_BASE_RELOCATION_BLOCK *) ((char *) Image + RelocOffset);
      @ ensures \valid(RelocWalker);
      @ ensures \valid(RelocWalker->Relocations + (0 .. image_base_reloc_num_relocs (RelocWalker) - 1));
      @ ensures \forall integer i; 0 <= i < image_base_reloc_num_relocs (RelocWalker) ==>
      @           \let RelocTarget = RelocWalker->VirtualAddress + image_reloc_offset (RelocWalker->Relocations[i]);
      @           \valid((char *) Image + (RelocTarget .. RelocTarget + image_reloc_size (RelocWalker->Relocations[i]) - 1));
      @ ensures \forall integer i; 0 <= i < image_base_reloc_num_relocs (RelocWalker) ==>
      @           image_reloc_sane (RelocWalker, i, RelocationData->RelocDirRva, RelocationData->RelocDirSize, ImageSize);
      @ ensures pointer_aligned ((char *) Image + RelocOffset, AV_ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK));
      @ ensures \valid(RelocWalker);
    */
    RelocWalker = (CONST EFI_IMAGE_BASE_RELOCATION_BLOCK *) (CONST VOID *) (
                    (CONST CHAR8 *) Image + RelocOffset
                    );

    STATIC_ASSERT (
      (sizeof (UINT32) % OC_ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK)) == 0,
      "The following accesses must be performed unaligned."
      );

    ASSERT (sizeof (EFI_IMAGE_BASE_RELOCATION_BLOCK) <= MAX_UINT32 - RelocWalker->SizeOfBlock);

    /*@ assigns SizeOfRelocs;
      @ ensures SizeOfRelocs == RelocWalker->SizeOfBlock - sizeof (EFI_IMAGE_BASE_RELOCATION_BLOCK);
    */
    SizeOfRelocs = RelocWalker->SizeOfBlock - sizeof (EFI_IMAGE_BASE_RELOCATION_BLOCK);

    ASSERT (IS_ALIGNED (RelocWalker->SizeOfBlock, OC_ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK)));
    //
    // This division is safe due to the guarantee made above.
    //
    /*@ assigns NumRelocs;
      @ ensures NumRelocs == image_base_reloc_num_relocs (RelocWalker);
      @ ensures \valid (RelocWalker->Relocations + (0 .. NumRelocs - 1));
    */
    NumRelocs = SizeOfRelocs / sizeof (*RelocWalker->Relocations);

    /*@ assert \forall integer i; 0 <= i < NumRelocs ==>
      @          image_reloc_sane (RelocWalker, i, RelocationData->RelocDirRva, RelocationData->RelocDirSize, ImageSize);
    */
    //
    // Apply all Base Relocation fixups of the current block.
    //
    /*@ loop assigns RelocIndex, RelocTarget, Status, FixupDataIndex;
      @ loop assigns ((char *) Image)[0 .. ImageSize - 1];
      @
      @ loop invariant 0 <= RelocIndex <= NumRelocs;
      @
      @ loop invariant 0 <= FixupDataIndex <= (RelocOffset - RelocationData->RelocDirRva) / sizeof (UINT16) + RelocIndex;
      @ loop invariant 0 <= FixupDataIndex <= (RelocOffset - RelocationData->RelocDirRva + RelocWalker->SizeOfBlock) / sizeof (UINT16);
      @
      @ loop invariant RelocIndex < NumRelocs ==>
      @                  image_reloc_supported (RelocWalker->Relocations[RelocIndex]) &&
      @                  \let RelocTarget = RelocWalker->VirtualAddress + image_reloc_offset (RelocWalker->Relocations[RelocIndex]);
      @                  (image_reloc_type (RelocWalker->Relocations[RelocIndex]) != EFI_IMAGE_REL_BASED_ABSOLUTE ==>
      @                    RelocTarget + image_reloc_size (RelocWalker->Relocations[RelocIndex]) <= ImageSize &&
      @                    \valid ((char *) Image + (RelocTarget .. RelocTarget + image_reloc_size (RelocWalker->Relocations[RelocIndex]) - 1))) &&
      @                  (image_reloc_type (RelocWalker->Relocations[RelocIndex]) == EFI_IMAGE_REL_BASED_ARM_MOV32T ==>
      @                    is_aligned_32 ((UINT32) RelocTarget, AV_ALIGNOF (UINT16)));
      @
      @ loop variant NumRelocs - RelocIndex;
    */
    for (RelocIndex = 0; RelocIndex < NumRelocs; ++RelocIndex) {
      /*@ assigns \nothing;
        @ ensures image_reloc_type (RelocWalker->Relocations[RelocIndex]) != EFI_IMAGE_REL_BASED_ABSOLUTE;
      */
      if (IMAGE_RELOC_TYPE (RelocWalker->Relocations[RelocIndex]) == EFI_IMAGE_REL_BASED_ABSOLUTE) {
        continue;
      }
      //
      // Determine the Base Relocation target address.
      //
      /*@ assigns RelocSuboffset;
        @ ensures RelocSuboffset == image_reloc_offset (RelocWalker->Relocations[RelocIndex]);
      */
      RelocSuboffset = IMAGE_RELOC_OFFSET (RelocWalker->Relocations[RelocIndex]);
      ASSERT (RelocSuboffset <= MAX_UINT32 - RelocWalker->VirtualAddress);

      /*@ assigns RelocTarget;
        @ ensures RelocTarget == RelocWalker->VirtualAddress + image_reloc_offset (RelocWalker->Relocations[RelocIndex]);
      */
      RelocTarget = RelocWalker->VirtualAddress + RelocSuboffset;

      /*@ requires pointer_max_aligned (Image) && is_aligned_N (RelocTarget, AV_ALIGNOF (UINT16)) ==>
        @            pointer_aligned ((char *) Image + RelocTarget, AV_ALIGNOF (UINT16));
        @ assigns ((char *) Image)[0 .. ImageSize - 1];
        @ ensures PcdGetBool (PcdImageLoaderRtRelocAllowTargetMismatch) ==>
        @           Status == RETURN_SUCCESS;
        @ ensures !PcdGetBool (PcdImageLoaderRtRelocAllowTargetMismatch) ==>
        @           (Status == RETURN_SUCCESS <==>
        @             image_reloc_target_value{Old} ((char *) Image + RelocTarget, image_reloc_type (RelocWalker->Relocations[RelocIndex])) == RelocationData->FixupData[FixupDataIndex]);
      */
      Status = InternalApplyRelocationRuntime (
                 (CHAR8 *) Image + RelocTarget,
                 IMAGE_RELOC_TYPE (RelocWalker->Relocations[RelocIndex]),
                 Adjust,
                 RelocationData->FixupData[FixupDataIndex]
                 );

      /*@ assigns \nothing;
      */
      if (!PcdGetBool (PcdImageLoaderRtRelocAllowTargetMismatch) && Status != RETURN_SUCCESS) {
        return Status;
      }

      /*@ requires FixupDataIndex <= (RelocOffset - RelocationData->RelocDirRva) / sizeof (UINT16) + RelocIndex;
        @ assigns FixupDataIndex;
        @ ensures FixupDataIndex <= (RelocOffset - RelocationData->RelocDirRva) / sizeof (UINT16) + RelocIndex + 1;
        @ ensures FixupDataIndex == \old(FixupDataIndex) + 1;
      */
      ++FixupDataIndex;
    }

    /*@ requires is_aligned_32 (RelocOffset, AV_ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK));
      @ requires is_aligned_32 (RelocWalker->SizeOfBlock, AV_ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK));
      @ requires is_aligned_32 (RelocOffset, AV_ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK)) && is_aligned_32 (RelocWalker->SizeOfBlock, AV_ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK)) ==>
      @            is_aligned_32 (RelocOffset +% RelocWalker->SizeOfBlock, AV_ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK));
      @
      @ assigns RelocOffset;
      @
      @ ensures RelocOffset == image_base_reloc_offset_index ((char *) Image, RelocationData->RelocDirRva, RelocationData->RelocDirSize, BaseRelocIndex + 1);
      @ ensures is_aligned_32 (RelocOffset, AV_ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK));
    */
    RelocOffset += RelocWalker->SizeOfBlock;

    //@ ghost ++BaseRelocIndex;
  }

  ASSERT (RelocOffset == RelocationData->RelocDirRva + RelocationData->RelocDirSize);

  return RETURN_SUCCESS;
}
