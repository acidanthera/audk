/** @file
  Copyright (c) 2022, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause
**/

#include "ImageTool.h"

static Elf_Ehdr  *mEhdr       = NULL;
static Elf_Size  mPeAlignment = 0x0;

#if defined (_MSC_EXTENSIONS)
#define EFI_IMAGE_MACHINE_IA32            0x014C
#define EFI_IMAGE_MACHINE_X64             0x8664
#define EFI_IMAGE_MACHINE_ARMTHUMB_MIXED  0x01C2
#define EFI_IMAGE_MACHINE_AARCH64         0xAA64
#endif

extern image_tool_image_info_t mImageInfo;

static
Elf_Shdr *
GetShdrByIndex (
  IN UINT32 Index
  )
{
  UINTN Offset;

  assert (Index < mEhdr->e_shnum);

  Offset = (UINTN)mEhdr->e_shoff + Index * mEhdr->e_shentsize;

  return (Elf_Shdr *)((UINT8 *)mEhdr + Offset);
}

Elf_Sym *
GetSymbol (
  IN UINT32 TableIndex,
  IN UINT32 SymbolIndex
  )
{
  const Elf_Shdr *TableShdr;
  UINT8          *Symtab;

  TableShdr = GetShdrByIndex (TableIndex);
  Symtab    = (UINT8 *)mEhdr + TableShdr->sh_offset;

  return (Elf_Sym *)(Symtab + SymbolIndex * TableShdr->sh_entsize);
}

static
char *
GetString (
  IN UINT32 Offset,
  IN UINT32 Index
  )
{
  const Elf_Shdr *Shdr;
  char           *String;

  if (Index == 0) {
    Shdr = GetShdrByIndex (mEhdr->e_shstrndx);
  } else {
    Shdr = GetShdrByIndex (Index);
  }

  if (Offset >= Shdr->sh_size) {
    fprintf (stderr, "ImageTool: Invalid ELF string offset\n");
    return NULL;
  }

  String = (char *)((UINT8 *)mEhdr + Shdr->sh_offset + Offset);

  return String;
}

static
BOOLEAN
IsTextShdr (
  IN const Elf_Shdr *Shdr
  )
{
  assert (Shdr != NULL);

  return ((((Shdr->sh_flags & (SHF_EXECINSTR | SHF_ALLOC)) == (SHF_EXECINSTR | SHF_ALLOC)) ||
          ((Shdr->sh_flags & (SHF_WRITE | SHF_ALLOC)) == SHF_ALLOC))
           && (Shdr->sh_type == SHT_PROGBITS));
}

static
BOOLEAN
IsHiiRsrcShdr (
  IN const Elf_Shdr *Shdr
  )
{
  assert (Shdr != NULL);

  Elf_Shdr *Namedr = GetShdrByIndex (mEhdr->e_shstrndx);

  return (BOOLEAN) (strcmp ((CHAR8*)mEhdr + Namedr->sh_offset + Shdr->sh_name, ELF_HII_SECTION_NAME) == 0);
}

static
BOOLEAN
IsDataShdr (
  IN const Elf_Shdr *Shdr
  )
{
  assert (Shdr != NULL);

  if (IsHiiRsrcShdr (Shdr)) {
    return FALSE;
  }

  return (((Shdr->sh_flags & (SHF_EXECINSTR | SHF_WRITE | SHF_ALLOC)) == (SHF_ALLOC | SHF_WRITE))
           && ((Shdr->sh_type == SHT_PROGBITS) || (Shdr->sh_type == SHT_NOBITS)));
}

static
VOID
SetHiiResourceHeader (
  IN OUT UINT8  *Hii,
  IN     UINT32 Offset
  )
{
  UINT32                              Index;
  EFI_IMAGE_RESOURCE_DIRECTORY        *RDir;
  EFI_IMAGE_RESOURCE_DIRECTORY_ENTRY  *RDirEntry;
  EFI_IMAGE_RESOURCE_DIRECTORY_STRING *RDirString;
  EFI_IMAGE_RESOURCE_DATA_ENTRY       *RDataEntry;

  assert (Hii != NULL);

  //
  // Fill Resource section entry
  //
  RDir      = (EFI_IMAGE_RESOURCE_DIRECTORY *)Hii;
  RDirEntry = (EFI_IMAGE_RESOURCE_DIRECTORY_ENTRY *)(RDir + 1);
  for (Index = 0; Index < RDir->NumberOfNamedEntries; ++Index) {
    if (RDirEntry->u1.s.NameIsString) {
      RDirString = (EFI_IMAGE_RESOURCE_DIRECTORY_STRING *)(Hii + RDirEntry->u1.s.NameOffset);

      if ((RDirString->Length == 3)
        && (RDirString->String[0] == L'H')
        && (RDirString->String[1] == L'I')
        && (RDirString->String[2] == L'I')) {
        //
        // Resource Type "HII" found
        //
        if (RDirEntry->u2.s.DataIsDirectory) {
          //
          // Move to next level - resource Name
          //
          RDir      = (EFI_IMAGE_RESOURCE_DIRECTORY *)(Hii + RDirEntry->u2.s.OffsetToDirectory);
          RDirEntry = (EFI_IMAGE_RESOURCE_DIRECTORY_ENTRY *)(RDir + 1);

          if (RDirEntry->u2.s.DataIsDirectory) {
            //
            // Move to next level - resource Language
            //
            RDir      = (EFI_IMAGE_RESOURCE_DIRECTORY *)(Hii + RDirEntry->u2.s.OffsetToDirectory);
            RDirEntry = (EFI_IMAGE_RESOURCE_DIRECTORY_ENTRY *)(RDir + 1);
          }
        }

        //
        // Now it ought to be resource Data. Update its OffsetToData value
        //
        if (!RDirEntry->u2.s.DataIsDirectory) {
          RDataEntry = (EFI_IMAGE_RESOURCE_DATA_ENTRY *)(Hii + RDirEntry->u2.OffsetToData);
          RDataEntry->OffsetToData = RDataEntry->OffsetToData + Offset;
          break;
        }
      }
    }
    RDirEntry++;
  }

  return;
}

static
RETURN_STATUS
ReadElfFile (
  IN const char *Name
  )
{
  static const unsigned char Ident[] = {
    ELFMAG0, ELFMAG1, ELFMAG2, ELFMAG3, ELFCLASS, ELFDATA2LSB
  };
  const Elf_Shdr *Shdr;
  UINTN          Offset;
  UINT32         Index;
  UINT32         FileSize;
  char           *Last;

  assert (Name != NULL);

  mEhdr = (Elf_Ehdr *)UserReadFile (Name, &FileSize);
  if (mEhdr == NULL) {
    fprintf (stderr, "ImageTool: Could not open %s: %s\n", Name, strerror (errno));
    return RETURN_VOLUME_CORRUPTED;
  }

  //
  // Check header
  //
  if ((FileSize < sizeof (*mEhdr))
    || (memcmp (Ident, mEhdr->e_ident, sizeof (Ident)) != 0)) {
    fprintf (stderr, "ImageTool: Invalid ELF header in file %s\n", Name);
    fprintf (stderr, "ImageTool: mEhdr->e_ident[0] = 0x%x expected 0x%x\n", mEhdr->e_ident[0], Ident[0]);
    fprintf (stderr, "ImageTool: mEhdr->e_ident[1] = 0x%x expected 0x%x\n", mEhdr->e_ident[1], Ident[1]);
    fprintf (stderr, "ImageTool: mEhdr->e_ident[2] = 0x%x expected 0x%x\n", mEhdr->e_ident[2], Ident[2]);
    fprintf (stderr, "ImageTool: mEhdr->e_ident[3] = 0x%x expected 0x%x\n", mEhdr->e_ident[3], Ident[3]);
    fprintf (stderr, "ImageTool: mEhdr->e_ident[4] = 0x%x expected 0x%x\n", mEhdr->e_ident[4], Ident[4]);
    fprintf (stderr, "ImageTool: mEhdr->e_ident[5] = 0x%x expected 0x%x\n", mEhdr->e_ident[5], Ident[5]);
    fprintf (stderr, "ImageTool: FileSize = 0x%x  sizeof(*mEhdr) = 0x%lx\n", FileSize, sizeof (*mEhdr));
    return RETURN_VOLUME_CORRUPTED;
  }

  if ((mEhdr->e_type != ET_EXEC) && (mEhdr->e_type != ET_DYN)) {
    fprintf (stderr, "ImageTool: ELF e_type not ET_EXEC or ET_DYN\n");
    return RETURN_UNSUPPORTED;
  }

#if defined(EFI_TARGET64)
  if ((mEhdr->e_machine != EM_X86_64) && (mEhdr->e_machine != EM_AARCH64)) {
    fprintf (stderr, "ImageTool: Unsupported ELF e_machine\n");
    return RETURN_UNSUPPORTED;
  }
#elif defined(EFI_TARGET32)
  if ((mEhdr->e_machine != EM_386) && (mEhdr->e_machine != EM_ARM)) {
    fprintf (stderr, "ImageTool: Unsupported ELF e_machine\n");
    return RETURN_UNSUPPORTED;
  }
#endif

  //
  // Check section headers
  //
  for (Index = 0; Index < mEhdr->e_shnum; ++Index) {
    Offset = (UINTN)mEhdr->e_shoff + Index * mEhdr->e_shentsize;

    if (FileSize < (Offset + sizeof (*Shdr))) {
      fprintf (stderr, "ImageTool: ELF section header is outside file %s\n", Name);
      return RETURN_VOLUME_CORRUPTED;
    }

    Shdr = (Elf_Shdr *)((UINT8 *)mEhdr + Offset);

    if ((Shdr->sh_type != SHT_NOBITS)
      && ((FileSize < Shdr->sh_offset) || ((FileSize - Shdr->sh_offset) < Shdr->sh_size))) {
      fprintf (stderr, "ImageTool: ELF section %d points outside file %s\n", Index, Name);
      return RETURN_VOLUME_CORRUPTED;
    }

    if (Shdr->sh_link >= mEhdr->e_shnum) {
      fprintf (stderr, "ImageTool: ELF %d-th section's sh_link is out of range\n", Index);
      return RETURN_VOLUME_CORRUPTED;
    }

    if (((Shdr->sh_type == SHT_RELA) || (Shdr->sh_type == SHT_REL))
      && (Shdr->sh_info >= mEhdr->e_shnum)) {
      fprintf (stderr, "ImageTool: ELF %d-th section's sh_info is out of range\n", Index);
      return RETURN_VOLUME_CORRUPTED;
    }

    if (Shdr->sh_addralign <= mPeAlignment) {
      continue;
    }

    if ((IsTextShdr (Shdr)) || (IsDataShdr (Shdr)) || (IsHiiRsrcShdr (Shdr))) {
      mPeAlignment = Shdr->sh_addralign;
    }
  }

  if (mEhdr->e_shstrndx >= mEhdr->e_shnum) {
    fprintf (stderr, "ImageTool: Invalid section name string table\n");
    return RETURN_VOLUME_CORRUPTED;
  }
  Shdr = GetShdrByIndex (mEhdr->e_shstrndx);

  if (Shdr->sh_type != SHT_STRTAB) {
    fprintf (stderr, "ImageTool: ELF string table section has wrong type\n");
    return RETURN_VOLUME_CORRUPTED;
  }

  Last = (char *)((UINT8 *)mEhdr + Shdr->sh_offset + Shdr->sh_size - 1);
  if (*Last != '\0') {
    fprintf (stderr, "ImageTool: ELF string table section is not NUL-terminated\n");
    return RETURN_VOLUME_CORRUPTED;
  }

  if ((!IS_POW2(mPeAlignment)) || (mPeAlignment > MAX_PE_ALIGNMENT)) {
    fprintf (stderr, "ImageTool: Invalid section alignment\n");
    return RETURN_VOLUME_CORRUPTED;
  }

  return RETURN_SUCCESS;
}

UINT32
GetValue (
  IN UINT64 Offset
  )
{
  UINT32 Index;

  for (Index = 0; Index < mImageInfo.SegmentInfo.NumSegments; ++Index) {
    if ((Offset >= mImageInfo.SegmentInfo.Segments[Index].ImageAddress)
      && (Offset - mImageInfo.SegmentInfo.Segments[Index].ImageAddress < mImageInfo.SegmentInfo.Segments[Index].ImageSize)) {
      return ReadUnaligned32 (
        (UINT32 *)(mImageInfo.SegmentInfo.Segments[Index].Data + (Offset - mImageInfo.SegmentInfo.Segments[Index].ImageAddress))
        );
    }
  }

  return 0;
}

static
RETURN_STATUS
SetRelocs (
  VOID
  )
{
  UINT32         Index;
  const Elf_Shdr *RelShdr;
  UINTN          RelIdx;
  const Elf_Rela *Rel;
  UINT32         RelNum;
#if defined(EFI_TARGET64)
  UINT32         Index2;
  BOOLEAN        New;
  INT64          Offset;
  Elf_Sym        *Sym;
  UINT32         Value;
#elif defined(EFI_TARGET32)
  UINT32         MovwOffset;

  MovwOffset = 0;
#endif
  RelNum = 0;

  for (Index = 0; Index < mEhdr->e_shnum; Index++) {
    RelShdr = GetShdrByIndex (Index);

    if ((RelShdr->sh_type != SHT_REL) && (RelShdr->sh_type != SHT_RELA)) {
      continue;
    }

    for (RelIdx = 0; RelIdx < RelShdr->sh_size; RelIdx += (UINTN)RelShdr->sh_entsize) {
      Rel = (Elf_Rela *)((UINT8 *)mEhdr + RelShdr->sh_offset + RelIdx);
      //
      // Assume ELF virtual addresses match corresponding PE virtual adresses one to one,
      // so we don't need to recalculate relocations computed by the linker at all r_offset's.
      // We only need to transform ELF relocations' format into PE one.
      //
#if defined(EFI_TARGET64)
      if (mEhdr->e_machine == EM_X86_64) {
        switch (ELF_R_TYPE(Rel->r_info)) {
          case R_X86_64_NONE:
            break;
          case R_X86_64_RELATIVE:
          case R_X86_64_64:
            //
            // If this is a ET_DYN (PIE) executable, we will encounter a dynamic SHT_RELA
            // section that applies to the entire binary, and which will have its section
            // index set to #0 (which is a NULL section with the SHF_ALLOC bit cleared).
            //
            // This RELA section will contain redundant R_xxx_RELATIVE relocations, one
            // for every R_xxx_xx64 relocation appearing in the per-section RELA sections.
            // (i.e., .rela.text and .rela.data) and .got entries' addresses (G + GOT).
            //
            New = TRUE;

            for (Index2 = 0; Index2 < RelNum; ++Index2) {
              if (((uint32_t)Rel->r_offset) == mImageInfo.RelocInfo.Relocs[Index2].Target) {
                New = FALSE;
              }
            }

            if (New) {
              mImageInfo.RelocInfo.Relocs[RelNum].Type   = EFI_IMAGE_REL_BASED_DIR64;
              mImageInfo.RelocInfo.Relocs[RelNum].Target = (uint32_t)Rel->r_offset;
              ++RelNum;
            }

            break;
          case R_X86_64_32:

            mImageInfo.RelocInfo.Relocs[RelNum].Type   = EFI_IMAGE_REL_BASED_HIGHLOW;
            mImageInfo.RelocInfo.Relocs[RelNum].Target = (uint32_t)Rel->r_offset;
            ++RelNum;

            break;
          case R_X86_64_32S:
          case R_X86_64_PLT32:
          case R_X86_64_PC32:
            break;
          case R_X86_64_GOTPCREL:
          case R_X86_64_GOTPCRELX:
          case R_X86_64_REX_GOTPCRELX:
            //
            // Relocations of these types point to instructions' arguments containing
            // offsets relative to RIP leading to .got entries. As sections' virtual
            // addresses do not change during ELF->PE transform, we don't need to
            // add them to relocations' list. But .got entries contain virtual
            // addresses which must be updated.
            //
            // At r_offset the following value is stored: G + GOT + A - P.
            // To derive .got entry address (G + GOT) compute: value - A + P.
            //
            // Such a method of finding relocatable .got entries can not be used,
            // due to a BUG in clang compiler, which sometimes generates
            // R_X86_64_REX_GOTPCRELX relocations instead of R_X86_64_PC32.
            //
            break;
          default:
            fprintf (stderr, "ImageTool: Unsupported ELF EM_X86_64 relocation 0x%llx\n", ELF_R_TYPE(Rel->r_info));
            return RETURN_UNSUPPORTED;
        }
      } else if (mEhdr->e_machine == EM_AARCH64) {
        Sym = GetSymbol (RelShdr->sh_link, ELF_R_SYM(Rel->r_info));

        switch (ELF_R_TYPE(Rel->r_info)) {
          case R_AARCH64_LD64_GOTOFF_LO15:
          case R_AARCH64_LD64_GOTPAGE_LO15:
            //
            // Convert into an ADR instruction that refers to the symbol directly.
            //
            Offset = Sym->st_value - Rel->r_offset;

            Value  = (GetValue (Rel->r_offset) & 0x1000001f);
            Value |= ((Offset & 0x1ffffc) << (5 - 2)) | ((Offset & 0x3) << 29);
            // WriteValue (Value, Rel->r_offset);

            if (Offset < -0x100000 || Offset > 0xfffff) {
              fprintf (stderr, "ImageTool: Failed to relax GOT based symbol reference - image is too big (>1 MiB)\n");
              return RETURN_UNSUPPORTED;
            }
            break;
          case R_AARCH64_LD64_GOT_LO12_NC:
            //
            // Convert into an ADD instruction - see R_AARCH64_ADR_GOT_PAGE below.
            //
            Value  = (GetValue (Rel->r_offset) & 0x3ff);
            Value |= 0x91000000 | ((Sym->st_value & 0xfff) << 10);
            // WriteValue (Value, Rel->r_offset);
            break;
          case R_AARCH64_ADR_GOT_PAGE:
            //
            // This relocation points to the GOT entry that contains the absolute
            // address of the symbol we are referring to. Since EDK2 only uses
            // fully linked binaries, we can avoid the indirection, and simply
            // refer to the symbol directly. This implies having to patch the
            // subsequent LDR instruction (covered by a R_AARCH64_LD64_GOT_LO12_NC
            // relocation) into an ADD instruction - this is handled above.
            //
            Offset = (Sym->st_value - (Rel->r_offset & ~0xfff)) >> 12;

            Value  = (GetValue (Rel->r_offset) & 0x9000001f);
            Value |= ((Offset & 0x1ffffc) << (5 - 2)) | ((Offset & 0x3) << 29);
            // WriteValue (Value, Rel->r_offset);
            /* fall through */

          case R_AARCH64_ADR_PREL_PG_HI21:
            //
            // In order to handle Cortex-A53 erratum #843419, the LD linker may
            // convert ADRP instructions into ADR instructions, but without
            // updating the static relocation type, and so we may end up here
            // while the instruction in question is actually ADR. So let's
            // just disregard it: the section offset check we apply below to
            // ADR instructions will trigger for its R_AARCH64_xxx_ABS_LO12_NC
            // companion instruction as well, so it is safe to omit it here.
            //
            if ((Value & BIT31) == 0) {
              break;
            }

            //
            // AArch64 PG_H21 relocations are typically paired with ABS_LO12
            // relocations, where a PC-relative reference with +/- 4 GB range is
            // split into a relative high part and an absolute low part. Since
            // the absolute low part represents the offset into a 4 KB page, we
            // either have to convert the ADRP into an ADR instruction, or we
            // need to use a section alignment of at least 4 KB, so that the
            // binary appears at a correct offset at runtime. In any case, we
            // have to make sure that the 4 KB relative offsets of both the
            // section containing the reference as well as the section to which
            // it refers have not been changed during PE/COFF conversion (i.e.,
            // in ScanSections64() above).
            //
            if (mPeAlignment < 0x1000) {
              //
              // Attempt to convert the ADRP into an ADR instruction.
              // This is only possible if the symbol is within +/- 1 MB.
              //

              // Decode the ADRP instruction
              Offset = (INT32)((Value & 0xffffe0) << 8);
              Offset = (Offset << (6 - 5)) | ((Value & 0x60000000) >> (29 - 12));

              //
              // ADRP offset is relative to the previous page boundary,
              // whereas ADR offset is relative to the instruction itself.
              // So fix up the offset so it points to the page containing
              // the symbol.
              //
              Offset -= (UINTN)(Rel->r_offset) & 0xfff;

              if (Offset < -0x100000 || Offset > 0xfffff) {
                fprintf (stderr, "ImageTool: Due to its size (> 1 MB), this module requires 4 KB section alignment\n");
                return RETURN_UNSUPPORTED;
              }

              // Re-encode the offset as an ADR instruction
              Value &= 0x1000001f;
              Value |= ((Offset & 0x1ffffc) << (5 - 2)) | ((Offset & 0x3) << 29);
              // WriteValue (Value, Rel->r_offset);
            }
            /* fall through */

          case R_AARCH64_ADD_ABS_LO12_NC:
          case R_AARCH64_LDST8_ABS_LO12_NC:
          case R_AARCH64_LDST16_ABS_LO12_NC:
          case R_AARCH64_LDST32_ABS_LO12_NC:
          case R_AARCH64_LDST64_ABS_LO12_NC:
          case R_AARCH64_LDST128_ABS_LO12_NC:
            if (mPeAlignment != 0x1000) {
              fprintf (stderr, "ImageTool: AARCH64 small code model requires identical ELF and PE/COFF section offsets modulo 4 KB\n");
              return RETURN_UNSUPPORTED;
            }
            /* fall through */

          case R_AARCH64_ADR_PREL_LO21:
          case R_AARCH64_CONDBR19:
          case R_AARCH64_LD_PREL_LO19:
          case R_AARCH64_CALL26:
          case R_AARCH64_JUMP26:
          case R_AARCH64_PREL64:
          case R_AARCH64_PREL32:
          case R_AARCH64_PREL16:
            //
            // The GCC toolchains (i.e., binutils) may corrupt section relative
            // relocations when emitting relocation sections into fully linked
            // binaries. More specifically, they tend to fail to take into
            // account the fact that a '.rodata + XXX' relocation needs to have
            // its addend recalculated once .rodata is merged into the .text
            // section, and the relocation emitted into the .rela.text section.
            //
            // We cannot really recover from this loss of information, so the
            // only workaround is to prevent having to recalculate any relative
            // relocations at all, by using a linker script that ensures that
            // the offset between the Place and the Symbol is the same in both
            // the ELF and the PE/COFF versions of the binary.
            //
            break;

            // Absolute relocations.
          case R_AARCH64_ABS64:

            mImageInfo.RelocInfo.Relocs[RelNum].Type   = EFI_IMAGE_REL_BASED_DIR64;
            mImageInfo.RelocInfo.Relocs[RelNum].Target = (uint32_t)Rel->r_offset;
            ++RelNum;
            break;
          case R_AARCH64_ABS32:

            mImageInfo.RelocInfo.Relocs[RelNum].Type   = EFI_IMAGE_REL_BASED_HIGHLOW;
            mImageInfo.RelocInfo.Relocs[RelNum].Target = (uint32_t)Rel->r_offset;
            ++RelNum;
            break;
          default:
            fprintf (stderr, "ImageTool: Unsupported ELF EM_AARCH64 relocation 0x%llx\n", ELF_R_TYPE(Rel->r_info));
            return RETURN_UNSUPPORTED;
        }
      }
#elif defined(EFI_TARGET32)
      if (mEhdr->e_machine == EM_386) {
        switch (ELF_R_TYPE(Rel->r_info)) {
          case R_386_NONE:
            break;
          case R_386_32:

            mImageInfo.RelocInfo.Relocs[RelNum].Type   = EFI_IMAGE_REL_BASED_HIGHLOW;
            mImageInfo.RelocInfo.Relocs[RelNum].Target = Rel->r_offset;
            ++RelNum;

            break;
          case R_386_PLT32:
          case R_386_PC32:
            break;
          default:
            fprintf (stderr, "ImageTool: Unsupported ELF EM_386 relocation 0x%x\n", ELF_R_TYPE(Rel->r_info));
            return RETURN_UNSUPPORTED;
        }
      } else if (mEhdr->e_machine == EM_ARM) {
        switch (ELF32_R_TYPE(Rel->r_info)) {
          case R_ARM_RBASE:
            // No relocation - no action required
            // break skipped

          case R_ARM_PC24:
          case R_ARM_REL32:
          case R_ARM_XPC25:
          case R_ARM_THM_PC22:
          case R_ARM_THM_JUMP19:
          case R_ARM_CALL:
          case R_ARM_JMP24:
          case R_ARM_THM_JUMP24:
          case R_ARM_PREL31:
          case R_ARM_MOVW_PREL_NC:
          case R_ARM_MOVT_PREL:
          case R_ARM_THM_MOVW_PREL_NC:
          case R_ARM_THM_MOVT_PREL:
          case R_ARM_THM_JMP6:
          case R_ARM_THM_ALU_PREL_11_0:
          case R_ARM_THM_PC12:
          case R_ARM_REL32_NOI:
          case R_ARM_ALU_PC_G0_NC:
          case R_ARM_ALU_PC_G0:
          case R_ARM_ALU_PC_G1_NC:
          case R_ARM_ALU_PC_G1:
          case R_ARM_ALU_PC_G2:
          case R_ARM_LDR_PC_G1:
          case R_ARM_LDR_PC_G2:
          case R_ARM_LDRS_PC_G0:
          case R_ARM_LDRS_PC_G1:
          case R_ARM_LDRS_PC_G2:
          case R_ARM_LDC_PC_G0:
          case R_ARM_LDC_PC_G1:
          case R_ARM_LDC_PC_G2:
          case R_ARM_THM_JUMP11:
          case R_ARM_THM_JUMP8:
          case R_ARM_TLS_GD32:
          case R_ARM_TLS_LDM32:
          case R_ARM_TLS_IE32:
            // Thease are all PC-relative relocations and don't require modification
            // GCC does not seem to have the concept of a application that just needs to get relocated.
            break;
          case R_ARM_THM_MOVW_ABS_NC:
            // MOVW is only lower 16-bits of the addres
            // ThumbMovtImmediatePatch ((UINT16 *)Targ, (UINT16)Sym->st_value);

            mImageInfo.RelocInfo.Relocs[RelNum].Type   = EFI_IMAGE_REL_BASED_ARM_MOV32T;
            mImageInfo.RelocInfo.Relocs[RelNum].Target = Rel->r_offset;
            ++RelNum;
            // PE/COFF treats MOVW/MOVT relocation as single 64-bit instruction
            // Track this address so we can log an error for unsupported sequence of MOVW/MOVT
            MovwOffset = Rel->r_offset;

            break;
          case R_ARM_THM_MOVT_ABS:
            // MOVT is only upper 16-bits of the addres
            // ThumbMovtImmediatePatch ((UINT16 *)Targ, (UINT16)(Sym->st_value >> 16));

            if ((MovwOffset + 4) != Rel->r_offset) {
              fprintf (stderr, "ImageTool: PE/COFF requires MOVW+MOVT instruction sequence (%x + 4) != %x\n", MovwOffset, Rel->r_offset);
              return RETURN_UNSUPPORTED;
            }

            break;
          case R_ARM_ABS32:
          case R_ARM_RABS32:

            mImageInfo.RelocInfo.Relocs[RelNum].Type   = EFI_IMAGE_REL_BASED_HIGHLOW;
            mImageInfo.RelocInfo.Relocs[RelNum].Target = Rel->r_offset;
            ++RelNum;

            break;
          default:
            fprintf (stderr, "ImageTool: Unsupported ELF EM_ARM relocation 0x%x\n", ELF_R_TYPE(Rel->r_info));
            return RETURN_UNSUPPORTED;
        }
      }
#endif
    }
  }

  mImageInfo.RelocInfo.NumRelocs = RelNum;

  return RETURN_SUCCESS;
}

static
RETURN_STATUS
CreateIntermediate (
  VOID
  )
{
  const Elf_Shdr       *Shdr;
  UINT32               Index;
  image_tool_segment_t *Segments;
  image_tool_reloc_t   *Relocs;
  UINT32               SIndex;
  const Elf_Rel        *Rel;
  UINTN                RIndex;
  char                 *Name;
  UINT32               NumRelocs;

  Segments  = NULL;
  SIndex    = 0;
  Relocs    = NULL;
  NumRelocs = 0;

  for (Index = 0; Index < mEhdr->e_shnum; ++Index) {
    Shdr = GetShdrByIndex (Index);

    if ((IsTextShdr (Shdr)) || (IsDataShdr (Shdr))) {
      ++mImageInfo.SegmentInfo.NumSegments;
      continue;
    }

    if ((Shdr->sh_type == SHT_REL) || (Shdr->sh_type == SHT_RELA)) {
      if (Shdr->sh_info == 0) {
        continue;
      }

      for (RIndex = 0; RIndex < Shdr->sh_size; RIndex += (UINTN)Shdr->sh_entsize) {
        Rel = (Elf_Rel *)((UINT8 *)mEhdr + Shdr->sh_offset + RIndex);
#if defined(EFI_TARGET64)
        if (mEhdr->e_machine == EM_X86_64) {
          if ((ELF_R_TYPE(Rel->r_info) == R_X86_64_64)
            || (ELF_R_TYPE(Rel->r_info) == R_X86_64_32)
            || (ELF_R_TYPE(Rel->r_info) == R_X86_64_GOTPCREL)
            || (ELF_R_TYPE(Rel->r_info) == R_X86_64_GOTPCRELX)
            || (ELF_R_TYPE(Rel->r_info) == R_X86_64_REX_GOTPCRELX)) {
            ++NumRelocs;
          }
        } else if (mEhdr->e_machine == EM_AARCH64) {

        }
#elif defined(EFI_TARGET32)
        if (mEhdr->e_machine == EM_386) {
          if (ELF_R_TYPE(Rel->r_info) == R_386_32) {
            ++NumRelocs;
          }
        } else if (mEhdr->e_machine == EM_ARM) {

        }
#endif
      }
    }
  }

  if (mImageInfo.SegmentInfo.NumSegments == 0) {
    fprintf (stderr, "ImageTool: No .text or .data sections\n");
    return RETURN_VOLUME_CORRUPTED;
  }

  Segments = calloc (1, sizeof (*Segments) * mImageInfo.SegmentInfo.NumSegments);
  if (Segments == NULL) {
    fprintf (stderr, "ImageTool: Could not allocate memory for Segments\n");
    return RETURN_OUT_OF_RESOURCES;
  };

  mImageInfo.SegmentInfo.Segments = Segments;

  if (NumRelocs != 0) {
    Relocs = calloc (1, sizeof (*Relocs) * NumRelocs);
    if (Relocs == NULL) {
      fprintf (stderr, "ImageTool: Could not allocate memory for Relocs\n");
      return RETURN_OUT_OF_RESOURCES;
    };

    mImageInfo.RelocInfo.Relocs = Relocs;
  }

  for (Index = 0; Index < mEhdr->e_shnum; ++Index) {
    Shdr = GetShdrByIndex (Index);

    if (IsTextShdr (Shdr)) {
      Name = GetString (Shdr->sh_name, 0);
      if (Name == NULL) {
        return RETURN_VOLUME_CORRUPTED;
      }

      Segments[SIndex].Name = calloc (1, strlen (Name) + 1);
      if (Segments[SIndex].Name == NULL) {
        fprintf (stderr, "ImageTool: Could not allocate memory for Segment #%d Name\n", SIndex);
        return RETURN_OUT_OF_RESOURCES;
      };

      memcpy (Segments[SIndex].Name, Name, strlen (Name));

      Segments[SIndex].DataSize = (uint32_t)ALIGN_VALUE (Shdr->sh_size, mPeAlignment);

      Segments[SIndex].Data = calloc (1, Segments[SIndex].DataSize);
      if (Segments[SIndex].Data == NULL) {
        fprintf (stderr, "ImageTool: Could not allocate memory for Segment #%d Data\n", SIndex);
        return RETURN_OUT_OF_RESOURCES;
      };

      memcpy (Segments[SIndex].Data, (UINT8 *)mEhdr + Shdr->sh_offset, (size_t)Shdr->sh_size);

      Segments[SIndex].ImageAddress = Shdr->sh_addr;
      Segments[SIndex].ImageSize    = Segments[SIndex].DataSize;
      Segments[SIndex].Read         = true;
      Segments[SIndex].Write        = false;
      Segments[SIndex].Execute      = true;
      Segments[SIndex].Type         = ToolImageSectionTypeCode;
      ++SIndex;
      continue;
    }

    if (IsDataShdr (Shdr)) {
      Name = GetString (Shdr->sh_name, 0);
      if (Name == NULL) {
        return RETURN_VOLUME_CORRUPTED;
      }

      Segments[SIndex].Name = calloc (1, strlen (Name) + 1);
      if (Segments[SIndex].Name == NULL) {
        fprintf (stderr, "ImageTool: Could not allocate memory for Segment #%d Name\n", SIndex);
        return RETURN_OUT_OF_RESOURCES;
      };

      memcpy (Segments[SIndex].Name, Name, strlen (Name));

      Segments[SIndex].DataSize = (uint32_t)ALIGN_VALUE (Shdr->sh_size, mPeAlignment);

      Segments[SIndex].Data = calloc (1, Segments[SIndex].DataSize);
      if (Segments[SIndex].Data == NULL) {
        fprintf (stderr, "ImageTool: Could not allocate memory for Segment #%d Data\n", SIndex);
        return RETURN_OUT_OF_RESOURCES;
      };

      if (Shdr->sh_type == SHT_PROGBITS) {
        memcpy (Segments[SIndex].Data, (UINT8 *)mEhdr + Shdr->sh_offset, (size_t)Shdr->sh_size);
      }

      Segments[SIndex].ImageAddress = Shdr->sh_addr;
      Segments[SIndex].ImageSize    = Segments[SIndex].DataSize;
      Segments[SIndex].Read         = true;
      Segments[SIndex].Write        = true;
      Segments[SIndex].Execute      = false;
      Segments[SIndex].Type         = ToolImageSectionTypeInitialisedData;
      ++SIndex;
      continue;
    }

    if (IsHiiRsrcShdr (Shdr)) {
      mImageInfo.HiiInfo.DataSize = (uint32_t)ALIGN_VALUE (Shdr->sh_size, mPeAlignment);

      mImageInfo.HiiInfo.Data = calloc (1, mImageInfo.HiiInfo.DataSize);
      if (mImageInfo.HiiInfo.Data == NULL) {
        fprintf (stderr, "ImageTool: Could not allocate memory for Hii Data\n");
        return RETURN_OUT_OF_RESOURCES;
      };

      if (Shdr->sh_type == SHT_PROGBITS) {
        memcpy (mImageInfo.HiiInfo.Data, (UINT8 *)mEhdr + Shdr->sh_offset, (size_t)Shdr->sh_size);
        SetHiiResourceHeader (mImageInfo.HiiInfo.Data, (UINT32)Shdr->sh_addr);
      }
    }
  }

  assert (SIndex == mImageInfo.SegmentInfo.NumSegments);

  return SetRelocs();
}

RETURN_STATUS
ScanElf (
  IN const char *ElfName,
  IN const char *ModuleType
  )
{
  RETURN_STATUS Status;

  assert (ElfName    != NULL);
  assert (ModuleType != NULL);

  Status = ReadElfFile (ElfName);
  if (RETURN_ERROR (Status)) {
    if (mEhdr != NULL) {
      free (mEhdr);
    }
    return Status;
  }

  memset (&mImageInfo, 0, sizeof (mImageInfo));

  mImageInfo.HeaderInfo.PreferredAddress  = 0;
  mImageInfo.HeaderInfo.EntryPointAddress = (uint32_t)mEhdr->e_entry;
  mImageInfo.HeaderInfo.IsXip             = true;
  mImageInfo.SegmentInfo.SegmentAlignment = (uint32_t)mPeAlignment;
  mImageInfo.RelocInfo.RelocsStripped     = false;
  mImageInfo.DebugInfo.SymbolsPathLen     = strlen (ElfName) + 1;

  switch (mEhdr->e_machine) {
    case EM_386:
      mImageInfo.HeaderInfo.Machine = EFI_IMAGE_MACHINE_IA32;
      break;
    case EM_X86_64:
      mImageInfo.HeaderInfo.Machine = EFI_IMAGE_MACHINE_X64;
      break;
    case EM_ARM:
      mImageInfo.HeaderInfo.Machine = EFI_IMAGE_MACHINE_ARMTHUMB_MIXED;
      break;
    case EM_AARCH64:
      mImageInfo.HeaderInfo.Machine = EFI_IMAGE_MACHINE_AARCH64;
      break;
    default:
      fprintf (stderr, "ImageTool: Unknown ELF architecture %d\n", mEhdr->e_machine);
      free (mEhdr);
      return RETURN_UNSUPPORTED;
  }

  mImageInfo.DebugInfo.SymbolsPath = calloc (1, mImageInfo.DebugInfo.SymbolsPathLen);
  if (mImageInfo.DebugInfo.SymbolsPath == NULL) {
    fprintf (stderr, "ImageTool: Could not allocate memory for Debug Data\n");
    free (mEhdr);
    return RETURN_OUT_OF_RESOURCES;
  };

  memcpy (mImageInfo.DebugInfo.SymbolsPath, ElfName, mImageInfo.DebugInfo.SymbolsPathLen);

  if ((strcmp (ModuleType, "BASE") == 0)
    || (strcmp (ModuleType, "SEC") == 0)
    || (strcmp (ModuleType, "SECURITY_CORE") == 0)
    || (strcmp (ModuleType, "PEI_CORE") == 0)
    || (strcmp (ModuleType, "PEIM") == 0)
    || (strcmp (ModuleType, "COMBINED_PEIM_DRIVER") == 0)
    || (strcmp (ModuleType, "PIC_PEIM") == 0)
    || (strcmp (ModuleType, "RELOCATABLE_PEIM") == 0)
    || (strcmp (ModuleType, "DXE_CORE") == 0)
    || (strcmp (ModuleType, "BS_DRIVER") == 0)
    || (strcmp (ModuleType, "DXE_DRIVER") == 0)
    || (strcmp (ModuleType, "DXE_SMM_DRIVER") == 0)
    || (strcmp (ModuleType, "UEFI_DRIVER") == 0)
    || (strcmp (ModuleType, "SMM_CORE") == 0)
    || (strcmp (ModuleType, "MM_STANDALONE") == 0)
    || (strcmp (ModuleType, "MM_CORE_STANDALONE") == 0)) {
      mImageInfo.HeaderInfo.Subsystem = EFI_IMAGE_SUBSYSTEM_EFI_BOOT_SERVICE_DRIVER;
  } else if ((strcmp (ModuleType, "UEFI_APPLICATION") == 0)
    || (strcmp (ModuleType, "APPLICATION") == 0)) {
      mImageInfo.HeaderInfo.Subsystem = EFI_IMAGE_SUBSYSTEM_EFI_APPLICATION;
  } else if ((strcmp (ModuleType, "DXE_RUNTIME_DRIVER") == 0)
    || (strcmp (ModuleType, "RT_DRIVER") == 0)) {
      mImageInfo.HeaderInfo.Subsystem = EFI_IMAGE_SUBSYSTEM_EFI_RUNTIME_DRIVER;
  } else if ((strcmp (ModuleType, "DXE_SAL_DRIVER") == 0)
    || (strcmp (ModuleType, "SAL_RT_DRIVER") == 0)) {
      mImageInfo.HeaderInfo.Subsystem = EFI_IMAGE_SUBSYSTEM_SAL_RUNTIME_DRIVER;
  } else {
    fprintf (stderr, "ImageTool: Unknown EFI_FILETYPE = %s\n", ModuleType);
    free (mImageInfo.DebugInfo.SymbolsPath);
    free (mEhdr);
    return RETURN_UNSUPPORTED;
  }

  Status = CreateIntermediate ();
  if (RETURN_ERROR (Status)) {
    ToolImageDestruct (&mImageInfo);
  }

  free (mEhdr);

  return Status;
}
