/*
 * Copyright (C) 2009 Michael Brown <mbrown@fensystems.co.uk>.
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License as
 * published by the Free Software Foundation; either version 2 of the
 * License, or any later version.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301, USA.
 */

#include "ImageTool.h"

static Elf_Ehdr *mEhdr             = NULL;
static Elf_Size mPeAlignment       = 0x200;
static PeOffset *mPeSectionOffsets = NULL;

static
BOOLEAN
IsTextShdr (
  IN const Elf_Shdr *Shdr
  )
{
  assert (Shdr != NULL);

  return (((Shdr->sh_flags & (SHF_EXECINSTR | SHF_ALLOC)) == (SHF_EXECINSTR | SHF_ALLOC)) ||
          ((Shdr->sh_flags & (SHF_WRITE | SHF_ALLOC)) == SHF_ALLOC));
}

static
BOOLEAN
IsDataShdr (
  IN const Elf_Shdr *Shdr
  )
{
  assert (Shdr != NULL);

  return ((Shdr->sh_flags & (SHF_EXECINSTR | SHF_WRITE | SHF_ALLOC)) == (SHF_ALLOC | SHF_WRITE));
}

static
Elf_Shdr *
GetShdrByIndex (
  IN UINT32 Index
  )
{
  UINTN Offset;

  assert (Index < mEhdr->e_shnum);

  Offset = mEhdr->e_shoff + Index * mEhdr->e_shentsize;

  return (Elf_Shdr *)((UINT8 *)mEhdr + Offset);
}

static
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
VOID
FreeRelocs (
	 IN PeRelocs *PeRel
  )
{
  assert (PeRel != NULL);

	if (PeRel->Next != NULL) {
		FreeRelocs (PeRel->Next);
	}

	if (PeRel->TypeOffsets != NULL) {
		free (PeRel->TypeOffsets);
	}

	free (PeRel);
}

static
VOID
FreeSections (
	IN PeSection *PeSections
  )
{
	assert (PeSections != NULL);

	if (PeSections->Next != NULL) {
		FreeSections (PeSections->Next);
	}

	free (PeSections);
}

static
PeSection *
CreateSection (
  IN     const char *Name,
  IN 	   BOOLEAN    (*Filter)(const Elf_Shdr *),
  IN     UINT32     Flags,
  IN     UINT8      Type,
	IN OUT PeHeader   *PeH
  )
{
  const Elf_Shdr *Shdr;
	PeSection      *PeS;
	UINT32         PeSectionSize;
  UINT32         Index;
  UINTN          NameLength;
  UINT32         Pointer;

	assert (Name   != NULL);
  assert (Filter != NULL);
	assert (PeH    != NULL);

	PeSectionSize = 0;
  Pointer       = 0;

  for (Index = 0; Index < mEhdr->e_shnum; ++Index) {
    Shdr = GetShdrByIndex (Index);

    if (Filter (Shdr)) {
      if ((Shdr->sh_addralign != 0) && (Shdr->sh_addralign != 1)) {
        //
        // The alignment field is valid
        //
        if (!IS_ALIGNED(Shdr->sh_addr, Shdr->sh_addralign)) {
          fprintf (stderr, "ImageTool: Section address not aligned to its own alignment\n");
          return NULL;
        }
      }

      if ((Shdr->sh_type == SHT_PROGBITS) || (Shdr->sh_type == SHT_NOBITS)) {
        PeSectionSize += ALIGN_VALUE (Shdr->sh_size, Shdr->sh_addralign);
      }
    }
	}

  PeSectionSize = ALIGN_VALUE (PeSectionSize, PeH->Nt->FileAlignment);

	PeS = calloc (1, sizeof (*PeS) + PeSectionSize);
	if (PeS == NULL) {
		fprintf (stderr, "ImageTool: Could not allocate memory for Pe section\n");
		return NULL;
	}

	//
	// Fill in section header details
	//
  PeS->Type = Type;

	NameLength = strlen (Name);
	if (NameLength > sizeof (PeS->PeShdr.Name)) {
		NameLength = sizeof (PeS->PeShdr.Name);
	}
	memcpy (PeS->PeShdr.Name, Name, NameLength);

	PeS->PeShdr.VirtualSize     = PeSectionSize;
	PeS->PeShdr.SizeOfRawData   = PeSectionSize;
	PeS->PeShdr.Characteristics = Flags;

  //
  // Copy necessary sections, set AddressOfEntryPoint in PE section.
  //
  for (Index = 0; Index < mEhdr->e_shnum; ++Index) {
    Shdr = GetShdrByIndex (Index);

    if ((mEhdr->e_entry >= Shdr->sh_addr)
  	  && ((mEhdr->e_entry - Shdr->sh_addr) < Shdr->sh_size)) {
  		PeH->Nt->AddressOfEntryPoint = Pointer + (mEhdr->e_entry - Shdr->sh_addr);
  	}

    if (Filter (Shdr)) {
      mPeSectionOffsets[Index].Type   = Type;
      mPeSectionOffsets[Index].Offset = Pointer;

      if (Shdr->sh_type == SHT_PROGBITS) {
        memcpy (PeS->Data + Pointer, (UINT8 *)mEhdr + Shdr->sh_offset, Shdr->sh_size);
        Pointer += ALIGN_VALUE (Shdr->sh_size, Shdr->sh_addralign);
      }

      if (Shdr->sh_type == SHT_NOBITS) {
        Pointer += ALIGN_VALUE (Shdr->sh_size, Shdr->sh_addralign);
      }
    }
	}

	//
	// Update remaining file header fields
	//
	++PeH->Nt->CommonHeader.FileHeader.NumberOfSections;
	PeH->Nt->SizeOfHeaders += sizeof (PeS->PeShdr);
	PeH->Nt->SizeOfImage   +=	ALIGN_VALUE (PeSectionSize, PeH->Nt->SectionAlignment);

	return PeS;
}

static
EFI_STATUS
GeneratePeReloc (
	IN OUT PeRelocs **PeRelTab,
	IN     UINTN    Rva,
	IN     UINT32   RelocType
  )
{
	UINTN    PageRva;
	UINT16   TypeOffset;
	PeRelocs *PeRel;
	UINT16   *Copy;

	assert (PeRelTab != NULL);

	PageRva = Rva & ~0xfff;
	//
	// Get Offset
	//
	TypeOffset = Rva & 0xfff;
	//
	// Get Type
	//
	switch (RelocType) {
		case 8:
			TypeOffset |= EFI_IMAGE_REL_BASED_DIR64 << 12;
			break;
		case 4:
			TypeOffset |= EFI_IMAGE_REL_BASED_HIGHLOW << 12;
			break;
		case 2:
			TypeOffset |= EFI_IMAGE_REL_BASED_LOW << 12;
			break;
		default:
			fprintf (stderr, "ImageTool: Unsupported relocation type\n");
			if (*PeRelTab != NULL) {
				FreeRelocs (*PeRelTab);
				*PeRelTab = NULL;
			}
	    return EFI_INVALID_PARAMETER;
	}

  //
	// Locate or create PE relocation table
	//
	for (PeRel = *PeRelTab; PeRel != NULL; PeRel = PeRel->Next) {
		if (PeRel->PageRva == PageRva) {
			break;
		}
	}

	if (PeRel == NULL) {
		PeRel = calloc (1, sizeof (*PeRel));
		if (PeRel == NULL) {
			fprintf (stderr, "ImageTool: Could not allocate memory for PeRel\n");
			if (*PeRelTab != NULL) {
				FreeRelocs (*PeRelTab);
				*PeRelTab = NULL;
			}
	    return EFI_OUT_OF_RESOURCES;
		}

		PeRel->Next    = *PeRelTab;
		*PeRelTab      = PeRel;
		PeRel->PageRva = PageRva;
	}

	//
	// Expand relocation list if necessary
	//
	if (PeRel->Used == PeRel->Total) {
		PeRel->Total = (PeRel->Total != 0) ? (PeRel->Total * 2) : 256;

		Copy = calloc (1, PeRel->Total * sizeof (TypeOffset));
		if (Copy == NULL) {
			fprintf (stderr, "ImageTool: Could not reallocate memory for TypeOffset array\n");
			FreeRelocs (*PeRelTab);
			*PeRelTab = NULL;
	    return EFI_OUT_OF_RESOURCES;
		}

		if (PeRel->TypeOffsets != NULL) {
			memcpy (Copy, PeRel->TypeOffsets, PeRel->Used * sizeof (TypeOffset));
			free (PeRel->TypeOffsets);
		}

		PeRel->TypeOffsets = Copy;
	}

	//
	// Store relocation
	//
	PeRel->TypeOffsets[PeRel->Used] = TypeOffset;
	++PeRel->Used;

	return EFI_SUCCESS;
}

static
EFI_STATUS
ProcessReloc (
	IN     const Elf_Shdr *RelShdr,
	IN     const Elf_Rel  *Rel,
	IN OUT PeRelocs       **PeRelTab
  )
{
	UINT32     Type;
	UINT32     MachineRelocType;
	UINTN      Offset;
	EFI_STATUS Status;
  Elf_Sym    *Sym;
  UINT32     SymTotal;
  Elf_Shdr   *TableShdr;

	assert (RelShdr  != NULL);
	assert (Rel      != NULL);
	assert (PeRelTab != NULL);

	Type             = ELF_R_TYPE (Rel->r_info);
	MachineRelocType = ELF_MREL (mEhdr->e_machine, Type);
	Offset           = RelShdr->sh_addr + Rel->r_offset;

  //
  // Identify symbol table
  //
  TableShdr = GetShdrByIndex (RelShdr->sh_link);
  Sym       = GetSymbol (RelShdr->sh_link, ELF_R_SYM(Rel->r_info));
  SymTotal  = TableShdr->sh_size / sizeof (*Sym);
  if (SymTotal == 0) {
    return EFI_SUCCESS;
  }

	//
	// Look up symbol and process relocation
	//
	if (ELF_R_SYM (Rel->r_info) >= SymTotal) {
		fprintf (stderr, "ImageTool: Symbol is out of range\n");
		return EFI_INVALID_PARAMETER;
	}

	if (Sym->st_shndx == SHN_ABS) {
		//
		// Skip absolute symbols;
		// the symbol value won't change when the object is loaded.
		//
		return EFI_SUCCESS;
	}

	switch (MachineRelocType) {
		case ELF_MREL (EM_386, R_386_NONE) :
		case ELF_MREL (EM_ARM, R_ARM_NONE) :
		case ELF_MREL (EM_X86_64, R_X86_64_NONE) :
		case ELF_MREL (EM_AARCH64, R_AARCH64_NONE) :
		case ELF_MREL (EM_AARCH64, R_AARCH64_NULL) :
			//
			// Ignore dummy relocations used by REQUIRE_SYMBOL()
			//
			break;
		case ELF_MREL (EM_386, R_386_32) :
		case ELF_MREL (EM_ARM, R_ARM_ABS32) :
			//
			// Generate a 4-byte PE relocation
			//
			Status = GeneratePeReloc (PeRelTab, Offset, 4);
			if (EFI_ERROR (Status)) {
				return Status;
			}
			break;
		case ELF_MREL (EM_X86_64, R_X86_64_64) :
		case ELF_MREL (EM_AARCH64, R_AARCH64_ABS64) :
			//
			// Generate an 8-byte PE relocation
			//
			Status = GeneratePeReloc (PeRelTab, Offset, 8);
			if (EFI_ERROR (Status)) {
				return Status;
			}
			break;
		case ELF_MREL (EM_386, R_386_PC32) :
		case ELF_MREL (EM_ARM, R_ARM_CALL) :
		case ELF_MREL (EM_ARM, R_ARM_REL32) :
		case ELF_MREL (EM_ARM, R_ARM_THM_PC22) :
		case ELF_MREL (EM_ARM, R_ARM_THM_JUMP24) :
		case ELF_MREL (EM_ARM, R_ARM_V4BX) :
		case ELF_MREL (EM_X86_64, R_X86_64_PC32) :
		case ELF_MREL (EM_X86_64, R_X86_64_PLT32) :
		case ELF_MREL (EM_AARCH64, R_AARCH64_CALL26) :
		case ELF_MREL (EM_AARCH64, R_AARCH64_JUMP26) :
		case ELF_MREL (EM_AARCH64, R_AARCH64_ADR_PREL_LO21) :
		case ELF_MREL (EM_AARCH64, R_AARCH64_ADR_PREL_PG_HI21) :
		case ELF_MREL (EM_AARCH64, R_AARCH64_ADD_ABS_LO12_NC) :
		case ELF_MREL (EM_AARCH64, R_AARCH64_LDST8_ABS_LO12_NC) :
		case ELF_MREL (EM_AARCH64, R_AARCH64_LDST16_ABS_LO12_NC) :
		case ELF_MREL (EM_AARCH64, R_AARCH64_LDST32_ABS_LO12_NC) :
		case ELF_MREL (EM_AARCH64, R_AARCH64_LDST64_ABS_LO12_NC) :
			//
			// Skip PC-relative relocations;
			// all relative offsets remain unaltered when the object is loaded.
			//
			break;
		default:
			fprintf (stderr, "ImageTool: Unrecognised relocation type %d\n", Type);
			return EFI_INVALID_PARAMETER;
	}

	return EFI_SUCCESS;
}

static
EFI_STATUS
ProcessRelocs (
	IN OUT PeRelocs **PeRelTab
  )
{
  const Elf_Shdr *RelShdr;
	const Elf_Rel  *Rel;
  UINT32         SIndex;
  UINTN          RIndex;
	EFI_STATUS     Status;

	assert (PeRelTab != NULL);

  for (SIndex = 0; SIndex < mEhdr->e_shnum; ++SIndex) {
    RelShdr = GetShdrByIndex (SIndex);

		if ((RelShdr->sh_type != SHT_REL) && (RelShdr->sh_type != SHT_RELA)) {
      continue;
    }

    //
    // Process each relocation
    //
    for (RIndex = 0; RIndex < RelShdr->sh_size; RIndex += RelShdr->sh_entsize) {
      Rel    = (Elf_Rel *)((UINT8 *)mEhdr + RelShdr->sh_offset + RIndex);
      Status = ProcessReloc (RelShdr, Rel, PeRelTab);
      if (EFI_ERROR (Status)) {
        return Status;
      }
    }
	}

	return EFI_SUCCESS;
}

static
UINT32
OutputPeReltab (
	IN  PeRelocs *PeRelTab,
	OUT VOID     *Buffer  OPTIONAL
  )
{
	PeRelocs *PeRel;
	UINT32   Used;
	UINT32   BlockSize;
	UINT32   SectionSize;

	assert (PeRelTab != NULL);

	SectionSize = 0;

	for (PeRel = PeRelTab; PeRel != NULL; PeRel = PeRel->Next) {
		//
		// Each block must start on a 32-bit boundary.
		//
		Used = ((PeRel->Used + 1U) & ~1U);
		BlockSize = sizeof (EFI_IMAGE_BASE_RELOCATION_BLOCK) + sizeof (*PeRel->TypeOffsets) * Used;

		if (Buffer != NULL) {
			*(UINT32 *)(Buffer + SectionSize) = PeRel->PageRva;
			*(UINT32 *)(Buffer + SectionSize + sizeof (UINT32)) = BlockSize;

			memcpy (
				Buffer + SectionSize + 2 * sizeof (UINT32),
				PeRel->TypeOffsets,
				Used * sizeof (*PeRel->TypeOffsets)
			  );
		}

		SectionSize += BlockSize;
	}

	return SectionSize;
}

static
PeSection *
CreateRelocSection (
	IN OUT PeHeader *PeH,
	IN     PeRelocs *PeRelTab
  )
{
	PeSection *PeS;
	UINT32    SectionSize;
	UINT32    RawDataSize;

  assert (PeH      != NULL);
	assert (PeRelTab != NULL);

	//
	// Allocate PE section
	//
	SectionSize = OutputPeReltab (PeRelTab, NULL);
	RawDataSize = ALIGN_VALUE (SectionSize, PeH->Nt->FileAlignment);
	PeS         = calloc (1, sizeof (*PeS) + RawDataSize);
	if (PeS == NULL) {
		fprintf (stderr, "ImageTool: Could not allocate memory for Pe .reloc section\n");
		return NULL;
	}

	//
	// Fill in section header details
	//
	strncpy ((char *)PeS->PeShdr.Name, ".reloc", sizeof (PeS->PeShdr.Name));
	PeS->PeShdr.VirtualSize     = SectionSize;
	PeS->PeShdr.SizeOfRawData   = RawDataSize;
	PeS->PeShdr.Characteristics =
	  EFI_IMAGE_SCN_CNT_INITIALIZED_DATA | EFI_IMAGE_SCN_MEM_DISCARDABLE |
		EFI_IMAGE_SCN_MEM_NOT_PAGED | EFI_IMAGE_SCN_MEM_READ;

	//
	// Copy section contents
	//
	OutputPeReltab (PeRelTab, PeS->Data);

	//
	// Update file header details
	//
	++PeH->Nt->CommonHeader.FileHeader.NumberOfSections;
	PeH->Nt->SizeOfHeaders += sizeof (PeS->PeShdr);
	PeH->Nt->SizeOfImage   += ALIGN_VALUE (SectionSize, PeH->Nt->SectionAlignment);

	PeH->Nt->DataDirectory[DIR_BASERELOC].Size = SectionSize;

	return PeS;
}

static
PeSection *
FindSection (
	IN PeSection *PeSections,
	IN UINT8    Type
  )
{
  PeSection *PeS;

	assert (PeSections != NULL);

  for (PeS = PeSections; PeS != NULL; PeS = PeS->Next) {
    if (PeS->Type == Type) {
      return PeS;
    }
	}

	return NULL;
}

static
EFI_STATUS
ApplyRelocs (
	IN PeSection *PeSections
  )
{
	UINT32         Index;
	const Elf_Shdr *RelShdr;
	const Elf_Shdr *SecShdr;
  UINT32         SecOffset;
	PeSection      *PeSRel;
	UINTN          RelIdx;
	const Elf_Rela *Rel;
	const Elf_Sym  *Sym;
	const Elf_Shdr *SymShdr;
  UINT32         SymOffset;
	UINT8          *Targ;
  // UINT64         GOTEntryRva;

	assert (PeSections != NULL);

	for (Index = 0; Index < mEhdr->e_shnum; Index++) {
    RelShdr = GetShdrByIndex (Index);

    if (RelShdr->sh_type != SHT_RELA) {
      continue;
    }

		if (RelShdr->sh_info == 0) {
			continue;
		}

    SecShdr   = GetShdrByIndex (RelShdr->sh_info);
    SecOffset = mPeSectionOffsets[RelShdr->sh_info].Offset;
    PeSRel    = FindSection (PeSections, mPeSectionOffsets[RelShdr->sh_info].Type);
		if (PeSRel == NULL) {
			return EFI_NOT_FOUND;
		}

		//
		// Process all relocation entries for this section.
		//
		for (RelIdx = 0; RelIdx < RelShdr->sh_size; RelIdx += RelShdr->sh_entsize) {
			Rel = (Elf_Rela *)((UINT8 *)mEhdr + RelShdr->sh_offset + RelIdx);

			//
			// Set pointer to symbol table entry associated with the relocation entry.
			//
      Sym = GetSymbol (RelShdr->sh_link, ELF_R_SYM(Rel->r_info));
			if ((Sym->st_shndx == SHN_UNDEF) || (Sym->st_shndx >= mEhdr->e_shnum)) {
				continue;
			}

      SymShdr   = GetShdrByIndex (Sym->st_shndx);
      SymOffset = mPeSectionOffsets[Sym->st_shndx].Offset;

			Targ = PeSRel->Data + SecOffset + (Rel->r_offset - SecShdr->sh_addr);

			if (mEhdr->e_machine == EM_X86_64) {
				switch (ELF_R_TYPE(Rel->r_info)) {
					case R_X86_64_NONE:
						break;
					case R_X86_64_64:
						*(UINT64 *)Targ = *(UINT64 *)Targ - SymShdr->sh_addr + SymOffset;
						break;
					case R_X86_64_32:
						*(UINT32 *)Targ = (UINT32)((UINT64)(*(UINT32 *)Targ) - SymShdr->sh_addr + SymOffset);
						break;
					case R_X86_64_32S:
						*(INT32 *)Targ = (INT32)((INT64)(*(INT32 *)Targ) - SymShdr->sh_addr + SymOffset);
						break;
					case R_X86_64_PLT32:
					case R_X86_64_PC32:
						*(UINT32 *)Targ = (UINT32)(*(UINT32 *)Targ + (SymOffset - SymShdr->sh_addr)
							- (SecOffset - SecShdr->sh_addr));
						break;
					case R_X86_64_GOTPCREL:
					case R_X86_64_GOTPCRELX:
					case R_X86_64_REX_GOTPCRELX:
						// GOTEntryRva = Rel->r_offset - Rel->r_addend + *(INT32 *)Targ;
						// FindElfGOTSectionFromGOTEntryElfRva(GOTEntryRva);
						// *(UINT32 *)Targ = (UINT32) (*(UINT32 *)Targ
						// 	+ (mPeSectionOffsets[mGOTShindex] - mGOTShdr->sh_addr)
						// 	- (PeSRel->Data - SecShdr->sh_addr));
						//
						// GOTEntryRva += (mPeSectionOffsets[mGOTShindex] - mGOTShdr->sh_addr);  // ELF Rva -> COFF Rva
						// if (AccumulateCoffGOTEntries((UINT32)GOTEntryRva)) {
						// 	//
						// 	// Relocate GOT entry if it's the first time we run into it
						// 	//
						// 	Targ = mCoffFile + GOTEntryRva;
						// 	*(UINT64 *)Targ = *(UINT64 *)Targ - SymShdr->sh_addr + SymOffset;
						// }
						break;
					default:
						fprintf (stderr, "ImageTool: Unsupported ELF EM_X86_64 relocation 0x%llx\n", ELF_R_TYPE(Rel->r_info));
						return EFI_UNSUPPORTED;
				}
			}
		}
	}

	return EFI_SUCCESS;
}

static
EFI_STATUS
WritePeFile (
	IN OUT PeHeader  *PeH,
	IN     UINT32    NtSize,
  IN     PeSection *PeSections,
	   OUT FILE      *Pe
  )
{
	EFI_STATUS Status;
	PeSection  *PeS;
	UINT32     Position;

	assert (PeH        != NULL);
	assert (PeSections != NULL);
	assert (Pe         != NULL);

	PeH->Nt->SizeOfHeaders = ALIGN_VALUE (PeH->Nt->SizeOfHeaders, PeH->Nt->FileAlignment);
  Position               = PeH->Nt->SizeOfHeaders;

	PeH->Nt->SizeOfImage         += ALIGN_VALUE (PeH->Nt->SizeOfHeaders, PeH->Nt->SectionAlignment);
	PeH->Nt->AddressOfEntryPoint += PeH->Nt->SizeOfHeaders;

	//
	// Assign raw data pointers
	//
	for (PeS = PeSections; PeS != NULL; PeS = PeS->Next) {
		if (PeS->PeShdr.SizeOfRawData != 0) {
			PeS->PeShdr.PointerToRawData = Position;
			PeS->PeShdr.VirtualAddress   = Position;

      if (PeS->Type == TEXT_SECTION) {
        PeH->Nt->BaseOfCode = Position;
				PeH->Nt->SizeOfCode = PeS->PeShdr.SizeOfRawData;
			}

#if defined(EFI_TARGET32)
      if (PeS->Type == DATA_SECTION) {
        PeH->Nt->BaseOfData = Position;
			}
#endif

			if (PeS->Type == RELOC_SECTION) {
				PeH->Nt->DataDirectory[DIR_BASERELOC].VirtualAddress = Position;
			}

			Position += PeS->PeShdr.SizeOfRawData;
		}
	}

	Status = ApplyRelocs (PeSections);
	if (EFI_ERROR (Status)) {
		return Status;
	}

	//
	// Write DOS header
	//
	if (fwrite (PeH, sizeof (PeH->Dos), 1, Pe) != 1) {
		fprintf (stderr, "ImageTool: Could not write PE DOS header\n");
		return EFI_ABORTED;
	}

	//
	// Write NT header
	//
	if (fwrite (PeH->Nt, NtSize, 1, Pe) != 1) {
		fprintf (stderr, "ImageTool: Could not write PE NT header\n");
		return EFI_ABORTED;
	}

	//
	// Write section headers
	//
	for (PeS = PeSections; PeS != NULL; PeS = PeS->Next) {
		if (fwrite (&PeS->PeShdr, sizeof (PeS->PeShdr), 1, Pe) != 1) {
			fprintf (stderr, "ImageTool: Could not write section header\n");
			return EFI_ABORTED;
		}
	}

	//
	// Write sections
	//
	for (PeS = PeSections; PeS != NULL; PeS = PeS->Next) {
		if (fseek (Pe, PeS->PeShdr.PointerToRawData, SEEK_SET) != 0) {
			fprintf (stderr, "ImageTool: Could not seek to %x: %s\n", PeS->PeShdr.PointerToRawData, strerror (errno));
			return EFI_ABORTED;
		}

		if ((PeS->PeShdr.SizeOfRawData != 0)
		  && (fwrite (PeS->Data, PeS->PeShdr.SizeOfRawData, 1, Pe) != 1)) {
			fprintf (stderr, "ImageTool: Could not write section %.8s: %s\n", PeS->PeShdr.Name, strerror (errno));
			return EFI_ABORTED;
		}
	}

	return EFI_SUCCESS;
}

static
EFI_STATUS
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
    return EFI_VOLUME_CORRUPTED;
  }

	//
	// Check header
	//
	if ((FileSize < sizeof (*mEhdr))
	  || (memcmp (Ident, mEhdr->e_ident, sizeof (Ident)) != 0)) {
		fprintf (stderr, "ImageTool: Invalid ELF header in file %s\n", Name);
		free (mEhdr);
    return EFI_VOLUME_CORRUPTED;
	}

	//
	// Check section headers
	//
	for (Index = 0; Index < mEhdr->e_shnum; ++Index) {
		Offset = mEhdr->e_shoff + Index * mEhdr->e_shentsize;

		if (FileSize < (Offset + sizeof (*Shdr))) {
			fprintf (stderr, "ImageTool: ELF section header is outside file %s\n", Name);
			free (mEhdr);
			return EFI_VOLUME_CORRUPTED;
		}

		Shdr = (Elf_Shdr *)((UINT8 *)mEhdr + Offset);

		if ((Shdr->sh_type != SHT_NOBITS)
		  && ((FileSize < Shdr->sh_offset) || ((FileSize - Shdr->sh_offset) < Shdr->sh_size))) {
			fprintf (stderr, "ImageTool: ELF section %d points outside file %s\n", Index, Name);
			free (mEhdr);
			return EFI_VOLUME_CORRUPTED;
		}

		if (Shdr->sh_link >= mEhdr->e_shnum) {
			fprintf (stderr, "ImageTool: ELF %d-th section's sh_link is out of range\n", Index);
			free (mEhdr);
			return EFI_VOLUME_CORRUPTED;
		}

    if (((Shdr->sh_type == SHT_RELA) || (Shdr->sh_type == SHT_REL))
      && (Shdr->sh_info >= mEhdr->e_shnum)) {
			fprintf (stderr, "ImageTool: ELF %d-th section's sh_info is out of range\n", Index);
			free (mEhdr);
			return EFI_VOLUME_CORRUPTED;
		}

		if (Shdr->sh_addralign <= mPeAlignment) {
      continue;
    }
    if (IsTextShdr(Shdr) || IsDataShdr(Shdr)) {
      mPeAlignment = Shdr->sh_addralign;
    }
	}

  if (mEhdr->e_shstrndx >= mEhdr->e_shnum) {
		fprintf (stderr, "ImageTool: Invalid section name string table\n");
    free (mEhdr);
    return EFI_VOLUME_CORRUPTED;
	}
  Shdr = GetShdrByIndex (mEhdr->e_shstrndx);

	if (Shdr->sh_type != SHT_STRTAB) {
		fprintf (stderr, "ImageTool: ELF string table section has wrong type\n");
    free (mEhdr);
    return EFI_VOLUME_CORRUPTED;
	}

	Last = (char *)((UINT8 *)mEhdr + Shdr->sh_offset + Shdr->sh_size - 1);
	if (*Last != '\0') {
		fprintf (stderr, "ImageTool: ELF string table section is not NUL-terminated\n");
    free (mEhdr);
    return EFI_VOLUME_CORRUPTED;
	}

	if ((!IS_POW2(mPeAlignment)) || (mPeAlignment > MAX_PE_ALIGNMENT)) {
    fprintf (stderr, "ImageTool: Invalid section alignment\n");
		free (mEhdr);
		return EFI_VOLUME_CORRUPTED;
  }

  mPeSectionOffsets = calloc (1, mEhdr->e_shnum * sizeof (PeOffset));
  if (mPeSectionOffsets == NULL) {
		fprintf (stderr, "ImageTool: Could not allocate memory for mPeSectionOffsets\n");
		free (mEhdr);
		return EFI_OUT_OF_RESOURCES;
	}

	return EFI_SUCCESS;
}

EFI_STATUS
ElfToPe (
	IN const char *ElfName,
	IN const char *PeName
  )
{
	PeRelocs   *PeRelTab;
	PeSection  *PeSections;
	PeSection  **NextPeSection;
	PeHeader   PeH;
	FILE       *Pe;
	EFI_STATUS Status;
	UINT32     DataDirSize;
	UINT32     NtSize;

	assert (ElfName != NULL);
	assert (PeName  != NULL);

	PeRelTab      = NULL;
	PeSections    = NULL;
	NextPeSection = &PeSections;

	Status = ReadElfFile (ElfName);
	if (EFI_ERROR (Status)) {
		return Status;
	}

	//
	// Initialise PE header
	//
	ZeroMem (&PeH, sizeof (PeH));
	PeH.Dos.e_magic  = EFI_IMAGE_DOS_SIGNATURE;
	PeH.Dos.e_lfanew = sizeof (EFI_IMAGE_DOS_HEADER);

	//
  // Only base relocation directory
	//
	NtSize = sizeof (EFI_IMAGE_NT_HEADERS) + sizeof (EFI_IMAGE_DATA_DIRECTORY);
	PeH.Nt = calloc (1, NtSize);
	if (PeH.Nt == NULL) {
		fprintf (stderr, "ImageTool: Could not allocate memory for EFI_IMAGE_NT_HEADERS\n");
		free (mEhdr);
		return EFI_OUT_OF_RESOURCES;
	}

	PeH.Nt->CommonHeader.Signature = EFI_IMAGE_NT_SIGNATURE;
	PeH.Nt->NumberOfRvaAndSizes = 1;
	DataDirSize = sizeof (EFI_IMAGE_DATA_DIRECTORY) * PeH.Nt->NumberOfRvaAndSizes;

  PeH.Nt->CommonHeader.FileHeader.SizeOfOptionalHeader = DataDirSize +
	  sizeof (EFI_IMAGE_NT_HEADERS) - sizeof (EFI_IMAGE_NT_HEADERS_COMMON_HDR);

	PeH.Nt->CommonHeader.FileHeader.Characteristics =
	  EFI_IMAGE_FILE_DLL | EFI_IMAGE_FILE_MACHINE | EFI_IMAGE_FILE_EXECUTABLE_IMAGE;

	PeH.Nt->Magic                   = EFI_IMAGE_NT_OPTIONAL_HDR_MAGIC;
	PeH.Nt->SectionAlignment        = mPeAlignment;
	PeH.Nt->FileAlignment           = mPeAlignment;
	PeH.Nt->SizeOfHeaders           = sizeof (PeH.Dos) + NtSize;
	PeH.Nt->Subsystem               = EFI_IMAGE_SUBSYSTEM_EFI_APPLICATION;
  PeH.Nt->SizeOfUninitializedData = 0;

	switch (mEhdr->e_machine) {
		case EM_386:
			PeH.Nt->CommonHeader.FileHeader.Machine = EFI_IMAGE_MACHINE_IA32;
			break;
		case EM_X86_64:
			PeH.Nt->CommonHeader.FileHeader.Machine = EFI_IMAGE_MACHINE_X64;
			break;
		case EM_ARM:
			PeH.Nt->CommonHeader.FileHeader.Machine = EFI_IMAGE_MACHINE_ARMTHUMB_MIXED;
			break;
		case EM_AARCH64:
			PeH.Nt->CommonHeader.FileHeader.Machine = EFI_IMAGE_MACHINE_AARCH64;
			break;
		default:
			fprintf (stderr, "ImageTool: Unknown ELF architecture %d\n", mEhdr->e_machine);
			Status = EFI_UNSUPPORTED;
			goto exit;
	}

	//
	// Process Elf sections
	//
  *NextPeSection = CreateSection (
    ".text",
    IsTextShdr,
    EFI_IMAGE_SCN_CNT_CODE | EFI_IMAGE_SCN_MEM_EXECUTE | EFI_IMAGE_SCN_MEM_READ,
    TEXT_SECTION,
    &PeH
    );
  if (*NextPeSection == NULL) {
    Status = EFI_ABORTED;
    goto exit;
  }

  NextPeSection = &(*NextPeSection)->Next;

  *NextPeSection = CreateSection (
    ".data",
    IsDataShdr,
    EFI_IMAGE_SCN_CNT_INITIALIZED_DATA | EFI_IMAGE_SCN_MEM_WRITE | EFI_IMAGE_SCN_MEM_READ,
    DATA_SECTION,
    &PeH
    );
  if (*NextPeSection == NULL) {
    Status = EFI_ABORTED;
    goto exit;
  }

  PeH.Nt->SizeOfInitializedData = (*NextPeSection)->PeShdr.SizeOfRawData;

  NextPeSection = &(*NextPeSection)->Next;

  Status = ProcessRelocs (&PeRelTab);
  if (EFI_ERROR (Status)) {
    goto exit;
  }

  if (PeRelTab != NULL) {
  	*NextPeSection = CreateRelocSection (&PeH, PeRelTab);
  	if (*NextPeSection == NULL) {
  		Status = EFI_ABORTED;
  		goto exit;
  	}
  }

	//
	// Write out PE file
	//
	Pe = fopen (PeName, "w");
	if (Pe == NULL) {
		fprintf (stderr, "ImageTool: Could not open %s for writing: %s\n", PeName, strerror (errno));
		Status = EFI_ABORTED;
		goto exit;
	}

	Status = WritePeFile (&PeH, NtSize, PeSections, Pe);
	fclose (Pe);

exit:
	if (PeRelTab != NULL) {
		FreeRelocs (PeRelTab);
	}
	if (PeSections != NULL) {
		FreeSections (PeSections);
	}
	free (PeH.Nt);
	free (mEhdr);

	return Status;
}
