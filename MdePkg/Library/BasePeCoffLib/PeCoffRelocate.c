/** @file
  Implements APIs to relocate PE/COFF Images.

  Portions copyright (c) 2006 - 2019, Intel Corporation. All rights reserved.<BR>
  Portions copyright (c) 2008 - 2010, Apple Inc. All rights reserved.<BR>
  Portions Copyright (c) 2020, Hewlett Packard Enterprise Development LP. All rights reserved.<BR>
  Copyright (c) 2020 - 2021, Marvin Häuser. All rights reserved.<BR>
  Copyright (c) 2020, Vitaly Cheptsov. All rights reserved.<BR>
  Copyright (c) 2020, ISP RAS. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-3-Clause
**/

#include <Base.h>

#include <IndustryStandard/PeImage.h>

#include <Library/BaseLib.h>
#include <Library/BaseMemoryLib.h>
#include <Library/DebugLib.h>
#include <Library/PcdLib.h>
#include <Library/PeCoffLib.h>

#include "BaseOverflow.h"
#include "BasePeCoffLibInternals.h"

/**
  Returns the type of a Base Relocation.

  @param[in] Relocation  The composite Base Relocation value.
**/
#define IMAGE_RELOC_TYPE(Relocation)    ((Relocation) >> 12U)

/**
  Returns the target offset of a Base Relocation.

  @param[in] Relocation  The composite Base Relocation value.
**/
#define IMAGE_RELOC_OFFSET(Relocation)  ((Relocation) & 0x0FFFU)


// FIXME: Add RISC-V support.
/**
  Returns whether the Base Relocation type is supported by this loader.

  @param[in] Type  The type of the Base Relocation.
**/
#define IMAGE_RELOC_TYPE_SUPPORTED(Type) \
  (((Type) == EFI_IMAGE_REL_BASED_ABSOLUTE) || \
  ((Type) == EFI_IMAGE_REL_BASED_HIGHLOW) || \
  ((Type) == EFI_IMAGE_REL_BASED_DIR64) || \
  ((PcdGet32 (PcdImageLoaderRelocTypePolicy) & PCD_RELOC_TYPE_POLICY_ARM) != 0 && (Type) == EFI_IMAGE_REL_BASED_ARM_MOV32T))

/**
  Returns whether the Base Relocation is supported by this loader.

  @param[in] Relocation  The composite Base Relocation value.
**/
#define IMAGE_RELOC_SUPPORTED(Relocation) \
  IMAGE_RELOC_TYPE_SUPPORTED (IMAGE_RELOC_TYPE (Reloc))

/**
  Retrieve the immediate data encoded in an ARM MOVT or MOVW immediate
  instruciton.

  @param[in] Instruction  Pointer to an ARM MOVT or MOVW immediate instruction.

  @returns  The Immediate address encoded in the instruction.
**/
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
  Movt1 = *(CONST UINT16 *) (CONST VOID *) Instruction;
  Movt2 = *(CONST UINT16 *) (CONST VOID *) ((CONST CHAR8 *) Instruction + sizeof (UINT16));
  Movt  = ((UINT32) Movt1 << 16U) | (UINT32) Movt2;
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
  PatchedInstruction = *(CONST UINT16 *) (CONST VOID *) Instruction;
  *(UINT16 *) (VOID *) Instruction = (PatchedInstruction & ~(UINT16) 0x040FU) | Patch;
  //
  // Second 16-bit chunk of instruction.
  //
  Patch  = Address & 0x000000FFU;                  // imm8
  Patch |= ((UINT32) Address << 4U) & 0x00007000U; // imm3
  //
  // Mask out instruction bits and or in address.
  //
  PatchedInstruction = *(CONST UINT16 *) (CONST VOID *) ((CHAR8 *) Instruction + sizeof (UINT16));
  *(UINT16 *) (VOID *) ((CHAR8 *) Instruction + sizeof (UINT16)) =
    (PatchedInstruction & ~(UINT16) 0x70FFU) | Patch;
}

/**
  Retrieve the immediate data encoded in an ARM MOVW/MOVT instruciton pair.

  @param[in] Instructions  Pointer to an ARM MOVW/MOVT insturction pair.

  @returns  The Immediate address encoded in the instructions.
**/
STATIC
UINT32
ThumbMovwMovtImmediateAddress (
  IN CONST VOID  *Instructions
  )
{
  CONST CHAR8 *Word;
  CONST CHAR8 *Top;
  //
  // Calculate the encoded address of the instruction pair.
  //
  Word = Instructions;                                        // MOVW
  Top  = (CONST CHAR8 *) Instructions + 2 * sizeof (UINT16);  // MOVT

  return (UINT32) (((UINT32) ThumbMovtImmediateAddress (Top) << 16U) | ThumbMovtImmediateAddress (Word));
}

/**
  Update an ARM MOVW/MOVT immediate instruction instruction pair.

  @param[in,out] Instructions  Pointer to ARM MOVW/MOVT instruction pair.
  @param[in]     Address       New address to patch into the instructions.
**/
STATIC
VOID
ThumbMovwMovtImmediatePatch (
  IN OUT VOID    *Instructions,
  IN     UINT32  Address
  )
{
  CHAR8 *Word;
  CHAR8 *Top;
  //
  // Patch the instruction pair's encoded address.
  //
  Word = Instructions;                                  // MOVW
  Top  = (CHAR8 *) Instructions + 2 * sizeof (UINT16);  // MOVT

  ThumbMovtImmediatePatch (Word, (UINT16) (Address & 0x0000FFFFU));
  ThumbMovtImmediatePatch (Top, (UINT16) ((Address & 0xFFFF0000U) >> 16U));
}

/**
  Relocate an ARM MOVW/MOVT immediate instruction instruction pair.

  @param[in,out] Instructions  Pointer to ARM MOVW/MOVT instruction pair.
  @param[in]     Adjust        The delta to add to the addresses.
**/
STATIC
VOID
ThumbMovwMovtImmediateFixup (
  IN OUT VOID    *Fixup,
  IN     UINT64  Adjust
  )
{
  UINT32 Fixup32;
  //
  // Relocate the instruction pair.
  //
  Fixup32 = ThumbMovwMovtImmediateAddress (Fixup) + (UINT32) Adjust;
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
STATIC
RETURN_STATUS
InternalApplyRelocation (
  IN  CONST PE_COFF_LOADER_IMAGE_CONTEXT     *Context,
  IN  CONST EFI_IMAGE_BASE_RELOCATION_BLOCK  *RelocBlock,
  IN  UINT32                                 RelocIndex,
  IN  UINT64                                 Adjust,
  OUT UINT64                                 *FixupData OPTIONAL
  )
{
  UINT16  RelocType;
  UINT16  RelocOff;
  BOOLEAN Overflow;
  UINT32  RelocTarget;
  UINT32  RemRelocTargetSize;
  UINT32  Fixup32;
  UINT64  Fixup64;
  CHAR8   *Fixup;

  RelocType = IMAGE_RELOC_TYPE (RelocBlock->Relocations[RelocIndex]);
  RelocOff  = IMAGE_RELOC_OFFSET (RelocBlock->Relocations[RelocIndex]);
  //
  // Absolute Base Relocations are used for padding any must be skipped.
  //
  if (RelocType == EFI_IMAGE_REL_BASED_ABSOLUTE) {
    if (FixupData != NULL) {
      FixupData[RelocIndex] = 0;
    }

    return RETURN_SUCCESS;
  }
  //
  // Verify the Base Relocation target address is in bounds of the Image buffer.
  //
  Overflow = BaseOverflowAddU32 (
               RelocBlock->VirtualAddress,
               RelocOff,
               &RelocTarget
               );
  if (Overflow) {
    DEBUG_RAISE ();
    return RETURN_UNSUPPORTED;
  }

  Overflow = BaseOverflowSubU32 (
               Context->SizeOfImage,
               RelocTarget,
               &RemRelocTargetSize
               );
  if (Overflow) {
    DEBUG_RAISE ();
    return RETURN_UNSUPPORTED;
  }

  Fixup = (CHAR8 *) Context->ImageBuffer + RelocTarget;
  //
  // Apply the Base Relocation fixup per type.
  // If RuntimeContext is not NULL, store the current value of the fixup
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
  switch (RelocType) {
    case EFI_IMAGE_REL_BASED_HIGHLOW:
      //
      // Verify the Base Relocation target is in bounds of the Image buffer.
      //
      if (sizeof (UINT32) > RemRelocTargetSize) {
        DEBUG_RAISE ();
        return RETURN_UNSUPPORTED;
      }
      //
      // Verify the Base Relocation does not target the Relocation Directory.
      //
      if (RelocTarget + sizeof (UINT32) > Context->RelocDirRva
       && Context->RelocDirRva + Context->RelocDirSize > RelocTarget) {
        DEBUG_RAISE ();
        return RETURN_UNSUPPORTED;
      }
      //
      // Relocate the instruction.
      //
      Fixup32  = ReadUnaligned32 ((CONST VOID *) Fixup);
      Fixup32 += (UINT32) Adjust;
      WriteUnaligned32 ((VOID *) Fixup, Fixup32);
      //
      // Record the relocated value for Runtime Relocation.
      //
      if (FixupData != NULL) {
        FixupData[RelocIndex] = Fixup32;
      }

      break;

    case EFI_IMAGE_REL_BASED_DIR64:
      //
      // Verify the Base Relocation target is in bounds of the Image buffer.
      //
      if (sizeof (UINT64) > RemRelocTargetSize) {
        DEBUG_RAISE ();
        return RETURN_UNSUPPORTED;
      }
      //
      // Verify the Base Relocation does not target the Relocation Directory.
      //
      if (RelocTarget + sizeof (UINT64) > Context->RelocDirRva
       && Context->RelocDirRva + Context->RelocDirSize > RelocTarget) {
        DEBUG_RAISE ();
        return RETURN_UNSUPPORTED;
      }
      //
      // Relocate the instruction.
      //
      Fixup64  = ReadUnaligned64 ((CONST VOID *) Fixup);
      Fixup64 += Adjust;
      WriteUnaligned64 ((VOID *) Fixup, Fixup64);
      //
      // Record the relocated value for Runtime Relocation.
      //
      if (FixupData != NULL) {
        FixupData[RelocIndex] = Fixup64;
      }

      break;

    case EFI_IMAGE_REL_BASED_ARM_MOV32T:
      //
      // Verify ARM Thumb mode Base Relocations are supported.
      //
      if ((PcdGet32 (PcdImageLoaderRelocTypePolicy) & PCD_RELOC_TYPE_POLICY_ARM) == 0) {
        DEBUG_RAISE ();
        return RETURN_UNSUPPORTED;
      }
      //
      // Verify the Base Relocation target is in bounds of the Image buffer.
      //
      if (sizeof (UINT64) > RemRelocTargetSize) {
        DEBUG_RAISE ();
        return RETURN_UNSUPPORTED;
      }
      //
      // Verify the Base Relocation target is sufficiently aligned.
      // The ARM THunb instruction pait must start on a 32-bit boundary.
      //
      if (!IS_ALIGNED (RelocTarget, ALIGNOF (UINT32))) {
        DEBUG_RAISE ();
        return RETURN_UNSUPPORTED;
      }
      //
      // Verify the Base Relocation does not target the Relocation Directory.
      //
      if (RelocTarget + sizeof (UINT64) > Context->RelocDirRva
       && Context->RelocDirRva + Context->RelocDirSize > RelocTarget) {
        DEBUG_RAISE ();
        return RETURN_UNSUPPORTED;
      }
      //
      // Relocate the instruction.
      //
      ThumbMovwMovtImmediateFixup (Fixup, Adjust);
      //
      // Record the relocated value for Runtime Relocation.
      //
      if (FixupData != NULL) {
        FixupData[RelocIndex] = ReadUnaligned64 ((CONST VOID *) Fixup);
      }

      break;

    default:
      //
      // The Base Relocation type cannot be recognised, disallow the Image.
      //
      DEBUG_RAISE ();
      return RETURN_UNSUPPORTED;
  }

  return RETURN_SUCCESS;
}

RETURN_STATUS
PeCoffRelocateImage (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT    *Context,
  IN     UINT64                          BaseAddress,
  OUT    PE_COFF_LOADER_RUNTIME_CONTEXT  *RuntimeContext OPTIONAL,
  IN     UINT32                          RuntimeContextSize
  )
{
  BOOLEAN                               Overflow;
  RETURN_STATUS                         Status;

  UINT64                                Adjust;
  CONST EFI_IMAGE_BASE_RELOCATION_BLOCK *RelocWalker;

  UINT32                                SizeOfRelocs;
  UINT32                                NumRelocs;

  UINT32                                RelocDataIndex;

  UINT32                                RelocOffset;
  UINT32                                RelocMax;
  UINT32                                RelocBlockSize;
  UINT32                                TopOfRelocDir;

  UINT32                                RelocIndex;

  UINT64                                *WalkerFixupData;

  ASSERT (Context != NULL);
  ASSERT (!Context->RelocsStripped);
  ASSERT (RuntimeContext != NULL || RuntimeContextSize == 0);
  ASSERT (RuntimeContext == NULL || RuntimeContextSize >= sizeof (PE_COFF_LOADER_RUNTIME_CONTEXT) + Context->RelocDirSize * (sizeof (UINT64) / sizeof (UINT16)));
//
  // Verify the Relocation Directory is not empty.
  //
  if (Context->RelocDirSize == 0) {
    return RETURN_SUCCESS;
  }
  //
  // Calculate the Image displacement from its prefered load address.
  //
  Adjust = BaseAddress - Context->ImageBase;
  //
  // Runtime drivers should unconditionally go through the full Relocation
  // procedure early to eliminate the possibility of errors later at runtime.
  // Runtime drivers don't have their Base Relocations stripped, this is
  // verified during context creation.
  // Skip explicit Relocation when the Image is already loaded at its
  // prefered location.
  //
  if (RuntimeContext == NULL && Adjust == 0) {
    return RETURN_SUCCESS;
  }
  //
  // Initialise the Runtime context header.
  //
  if (RuntimeContext != NULL) {
    RuntimeContext->RelocDirRva  = Context->RelocDirRva;
    RuntimeContext->RelocDirSize = Context->RelocDirSize;
  }
  //
  // Apply Base Relocation fixups to the image.
  //
  RelocOffset    = Context->RelocDirRva;
  TopOfRelocDir  = Context->RelocDirRva + Context->RelocDirSize;
  RelocMax       = TopOfRelocDir - sizeof (EFI_IMAGE_BASE_RELOCATION_BLOCK);
  RelocDataIndex = 0;
  //
  // Align TopOfRelocDir because, if the policy does not demand Relocation Block
  // sizes to be aligned, the code below will manually align them. Thus, the
  // end offset of the last Relocation Block must be compared to a manually
  // aligned Relocation Directoriy end offset.
  //
  if ((PcdGet32 (PcdImageLoaderAlignmentPolicy) & PCD_ALIGNMENT_POLICY_RELOCATION_BLOCK_SIZES) != 0) {
    Overflow = BaseOverflowAlignUpU32 (
                 TopOfRelocDir,
                 ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK),
                 &TopOfRelocDir
                 );
    if (Overflow) {
      DEBUG_RAISE ();
      return RETURN_UNSUPPORTED;
    }
  }
  //
  // Apply all Base Relocations of the Image.
  //
  while (RelocOffset <= RelocMax) {
    RelocWalker = (CONST EFI_IMAGE_BASE_RELOCATION_BLOCK *) (CONST VOID *) (
                    (CONST CHAR8 *) Context->ImageBuffer + RelocOffset
                    );
    //
    // Verify the Base Relocation Block size is well-formed.
    //
    Overflow = BaseOverflowSubU32 (
                 RelocWalker->SizeOfBlock,
                 sizeof (EFI_IMAGE_BASE_RELOCATION_BLOCK),
                 &SizeOfRelocs
                 );
    if (Overflow) {
      DEBUG_RAISE ();
      return RETURN_UNSUPPORTED;
    }
    //
    // Verify the Base Relocation Block is in bounds of the Relocation
    // Directory.
    //
    if (SizeOfRelocs > RelocMax - RelocOffset) {
      DEBUG_RAISE ();
      return RETURN_UNSUPPORTED;
    }
    //
    // Advance to the next Base Relocation Block offset based on the alignment
    // policy.
    //
    if ((PcdGet32 (PcdImageLoaderAlignmentPolicy) & PCD_ALIGNMENT_POLICY_RELOCATION_BLOCK_SIZES) == 0) {
      RelocBlockSize = RelocWalker->SizeOfBlock;
      //
      // Verify the next Base Relocation Block offset is sufficiently aligned.
      //
      if (!IS_ALIGNED (RelocBlockSize, ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK))) {
        DEBUG_RAISE ();
        return RETURN_UNSUPPORTED;
      }
    } else {
      //
      // This arithmetics cannot overflow because we know
      //   1) RelocWalker->SizeOfBlock <= RelocMax <= TopOfRelocDir
      //   2) IS_ALIGNED (TopOfRelocDir, ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK)).
      //
      RelocBlockSize = ALIGN_VALUE (
                         RelocWalker->SizeOfBlock,
                         ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK)
                         );
    }
    //
    // This division is safe due to the guarantee made above.
    //
    NumRelocs = SizeOfRelocs / sizeof (*RelocWalker->Relocations);

    if (RuntimeContext != NULL) {
      WalkerFixupData = &RuntimeContext->FixupData[RelocDataIndex];
    } else {
      WalkerFixupData = NULL;
    }
    //
    // Process all Base Relocations of the current Block.
    //
    for (RelocIndex = 0; RelocIndex < NumRelocs; ++RelocIndex) {
      //
      // Apply the Base Relocation fixup per type.
      // If RuntimeContext is not NULL, store the current value of the fixup
      // target to determine whether it has been changed during runtime
      // execution.
      //
      // It is not clear how EFI_IMAGE_REL_BASED_HIGH and
      // EFI_IMAGE_REL_BASED_LOW are supposed to be handled. While PE reference
      // suggests to just add the high or low part of the displacement, there
      // are concerns about how it's supposed to deal with wraparounds.
      // As neither LLD,
      //

      Status = InternalApplyRelocation (
                 Context,
                 RelocWalker,
                 RelocIndex,
                 Adjust,
                 WalkerFixupData
                 );
      if (Status != RETURN_SUCCESS) {
        DEBUG_RAISE ();
        return Status;
      }
    }

    RelocDataIndex += NumRelocs;
    RelocOffset    += RelocBlockSize;
  }
  //
  // Verify the Relocation Directory size matches the contained data.
  //
  if (RelocOffset != TopOfRelocDir) {
    DEBUG_RAISE ();
    return RETURN_UNSUPPORTED;
  }
  //
  // Initialise the still uninitialised portion of the Runtime context.
  //
  if (RuntimeContext != NULL) {
    ZeroMem (
      &RuntimeContext->FixupData[RelocDataIndex],
      RuntimeContextSize - sizeof (PE_COFF_LOADER_RUNTIME_CONTEXT) - RelocDataIndex * sizeof (UINT64)
      );
  }

  return RETURN_SUCCESS;
}

/**
  Apply an Image Base Relocation for Runtime Relocation.

  Well-formedness has been verified by PeCoffRelocateImage() previously.
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
STATIC
RETURN_STATUS
InternalApplyRelocationRuntime (
  IN OUT VOID    *Fixup,
  IN     UINT16  RelocType,
  IN     UINT64  Adjust,
  IN     UINT64  FixupData
  )
{
  UINT32 Fixup32;
  UINT64 Fixup64;

  ASSERT (Fixup != NULL);
  ASSERT (IMAGE_RELOC_TYPE_SUPPORTED (RelocType)
       && RelocType != EFI_IMAGE_REL_BASED_ABSOLUTE);

  //
  // This function assumes the image has previously been validated by
  // PeCoffInitializeContext().
  //

  //
  // Apply the Base Relocation fixup per type.
  //
  switch (RelocType) {
    case EFI_IMAGE_REL_BASED_HIGHLOW:
      Fixup32 = ReadUnaligned32 ((CONST VOID *) Fixup);

      if (FixupData != Fixup32) {
        if (PcdGetBool (PcdImageLoaderRtRelocAllowTargetMismatch)) {
          return RETURN_SUCCESS;
        }

        return RETURN_UNSUPPORTED;
      }

      Fixup32 += (UINT32) Adjust;
      WriteUnaligned32 (Fixup, Fixup32);

      break;

    case EFI_IMAGE_REL_BASED_DIR64:
      Fixup64 = ReadUnaligned64 (Fixup);

      if (FixupData != Fixup64) {
        if (PcdGetBool (PcdImageLoaderRtRelocAllowTargetMismatch)) {
          return RETURN_SUCCESS;
        }

        return RETURN_UNSUPPORTED;
      }

      Fixup64 += Adjust;
      WriteUnaligned64 (Fixup, Fixup64);

      break;

    case EFI_IMAGE_REL_BASED_ARM_MOV32T:
      ASSERT ((PcdGet32 (PcdImageLoaderRelocTypePolicy) & PCD_RELOC_TYPE_POLICY_ARM) != 0);

      Fixup64 = ReadUnaligned64 (Fixup);

      if (FixupData != Fixup64) {
        if (PcdGetBool (PcdImageLoaderRtRelocAllowTargetMismatch)) {
          return RETURN_SUCCESS;
        }

        return RETURN_UNSUPPORTED;
      }

      ThumbMovwMovtImmediateFixup (Fixup, Adjust);

      break;

    default:
      //
      // Invalid Base Relocation types would have caused the Image to not be
      // loaded relocated successfully earlier.
      //
      ASSERT (FALSE);
  }

  return RETURN_SUCCESS;
}

RETURN_STATUS
PeCoffLoaderGetRuntimeContextSize (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  OUT    UINT32                        *Size
  )
{
  BOOLEAN Overflow;
  UINT32  FixupDataSize;

  ASSERT (Context != NULL);
  ASSERT (!Context->RelocsStripped);
  ASSERT (Size != NULL);

  //
  // Because Base Relocations have not been stripped, PeCoffInitializeContext()
  // has verified the Relocation Directory exists and is valid.
  //

  //
  // Request 64-bit of source value per 16-bit Base Relocation.
  // This allocates too many Bytes because it assumes that every Base Relocation
  // refers to a 64-bit target and does not account for Base Relocation Block
  // headers.
  //
  Overflow = BaseOverflowMulU32 (
               Context->RelocDirSize,
               sizeof (UINT64) / sizeof (UINT16),
               &FixupDataSize
               );
  if (Overflow) {
    return RETURN_UNSUPPORTED;
  }

  Overflow = BaseOverflowAddU32 (
               FixupDataSize,
               sizeof (PE_COFF_LOADER_RUNTIME_CONTEXT),
               Size
               );
  if (Overflow) {
    return RETURN_UNSUPPORTED;
  }

  return RETURN_SUCCESS;
}

RETURN_STATUS
PeCoffRelocateImageForRuntime (
  IN OUT VOID                                  *Image,
  IN     UINT32                                ImageSize,
  IN     UINT64                                BaseAddress,
  IN     CONST PE_COFF_LOADER_RUNTIME_CONTEXT  *RuntimeContext
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
  UINT32                                RelocBlockSize;

  (VOID) ImageSize;

  ASSERT (Image != NULL);
  ASSERT (BaseAddress != 0);
  ASSERT (RuntimeContext != NULL);

  //
  // This function assumes the image has previously been validated by
  // PeCoffInitializeContext(). The arithmetics in this function generally
  // cannot overflow because they follow those of PeCoffRelocateImage().
  //

  ImageAddress = (UINTN) Image;
  Adjust       = BaseAddress - ImageAddress;
  //
  // If the Image remains at the current address, skip relocation.
  //
  if (Adjust == 0) {
    return RETURN_SUCCESS;
  }
  //
  // Apply all Base Relocations of the Image.
  //
  FixupDataIndex = 0;
  RelocOffset    = RuntimeContext->RelocDirRva;
  while (RelocOffset < RuntimeContext->RelocDirRva + RuntimeContext->RelocDirSize) {
    ASSERT (IS_ALIGNED (RelocOffset, ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK)));

    RelocWalker = (CONST EFI_IMAGE_BASE_RELOCATION_BLOCK *) (CONST VOID *) (
                    (CONST CHAR8 *) Image + RelocOffset
                    );

    STATIC_ASSERT (
      (sizeof (UINT32) % ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK)) == 0,
      "The following accesses must be performed unaligned."
      );

    ASSERT (sizeof (EFI_IMAGE_BASE_RELOCATION_BLOCK) <= RelocWalker->SizeOfBlock);
    //
    // Determine the number of Base Relocations in this Block.
    //
    SizeOfRelocs = RelocWalker->SizeOfBlock - sizeof (EFI_IMAGE_BASE_RELOCATION_BLOCK);
    NumRelocs    = SizeOfRelocs / sizeof (*RelocWalker->Relocations);
    //
    // Apply all Base Relocation fixups of the current block.
    //
    for (RelocIndex = 0; RelocIndex < NumRelocs; ++RelocIndex) {
      //
      // Skip Absolute Base Relocations.
      //
      if (IMAGE_RELOC_TYPE (RelocWalker->Relocations[RelocIndex]) == EFI_IMAGE_REL_BASED_ABSOLUTE) {
        continue;
      }
      //
      // Determine the Base Relocation target address.
      //
      RelocSuboffset = IMAGE_RELOC_OFFSET (RelocWalker->Relocations[RelocIndex]);
      ASSERT (RelocSuboffset <= MAX_UINT32 - RelocWalker->VirtualAddress);
      //
      // Apply the Base Relocation.
      //
      RelocTarget = RelocWalker->VirtualAddress + RelocSuboffset;
      Status = InternalApplyRelocationRuntime (
                 (CHAR8 *) Image + RelocTarget,
                 IMAGE_RELOC_TYPE (RelocWalker->Relocations[RelocIndex]),
                 Adjust,
                 RuntimeContext->FixupData[FixupDataIndex]
                 );
      //
      // If the original Relocation target value mismatches the expected value,
      // and the policy demands it, report an error.
      //
      if (!PcdGetBool (PcdImageLoaderRtRelocAllowTargetMismatch)) {
        if (Status != RETURN_SUCCESS) {
          return Status;
        }
      }

      ++FixupDataIndex;
    }
    //
    // Advance to the next Base Relocation Block based on the alignment policy.
    //
    if ((PcdGet32 (PcdImageLoaderAlignmentPolicy) & PCD_ALIGNMENT_POLICY_RELOCATION_BLOCK_SIZES) == 0) {
      RelocBlockSize = RelocWalker->SizeOfBlock;
      ASSERT (IS_ALIGNED (RelocBlockSize, ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK)));
    } else {
      RelocBlockSize = ALIGN_VALUE (
                         RelocWalker->SizeOfBlock,
                         ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK)
                         );
    }

    RelocOffset += RelocBlockSize;
  }

  ASSERT (RelocOffset == RuntimeContext->RelocDirRva + RuntimeContext->RelocDirSize);

  return RETURN_SUCCESS;
}
