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

static PeHeader  mPeH;
static Elf_Ehdr  *mEhdr              = NULL;
static Elf_Size  mPeAlignment        = 0x200;
static UINT32    mPeSectionsNumber   = 0;
static PeSection **mPeSections       = NULL;
static PeOffset  *mPeSectionOffsets  = NULL;
static BOOLEAN   mRelocSectionExists = FALSE;

static Elf_Shdr *mGOTShdr          = NULL;
static UINT32   mGOTShIndex        = 0;
static UINT32   *mGOTCoffEntries   = NULL;
static UINT32   mGOTMaxCoffEntries = 0;
static UINT32   mGOTNumCoffEntries = 0;

EFI_STATUS
ApplyRelocs (
  IN BOOLEAN (*Filter)(const Elf_Shdr *)
  );

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
UINT32
FindAddress (
	IN  UINT32 ElfIndex,
  OUT UINT8  **SectionData,
  OUT UINT32 *WOffset
  )
{
  UINT32    ROffset;
  PeSection *PeS;
  UINT32    PeIndex;

  assert (SectionData != NULL);
  assert (WOffset     != NULL);

  ROffset  = mPeSectionOffsets[ElfIndex].Offset;
  *WOffset = mPeH.Nt->SizeOfHeaders + ROffset;

  for (PeIndex = 0; (PeIndex < mPeSectionsNumber) && (mPeSections[PeIndex] != NULL); ++PeIndex) {
    PeS = mPeSections[PeIndex];

    if (mPeSectionOffsets[ElfIndex].Type == PeS->Type) {
      *SectionData = PeS->Data;
      break;
    }

    *WOffset += PeS->PeShdr.SizeOfRawData;
  }

	return ROffset;
}

//
// Find the ELF section hosting the GOT from an ELF Rva of a single GOT entry.
// Normally, GOT is placed in ELF .text section, so assume once we find,
// in which section the GOT is, all GOT entries are there, and just verify this.
//
static
EFI_STATUS
FindElfGOTSectionFromGOTEntryElfRva (
  IN Elf_Addr GOTEntryElfRva
  )
{
  UINT32   Index;
  Elf_Shdr *Shdr;

  if (mGOTShdr != NULL) {
    if ((GOTEntryElfRva >= mGOTShdr->sh_addr)
      && ((GOTEntryElfRva - mGOTShdr->sh_addr) < mGOTShdr->sh_size)) {
      return EFI_SUCCESS;
    }

    fprintf (stderr, "ImageTool: GOT entries found in multiple sections\n");

    return EFI_UNSUPPORTED;
  }

  for (Index = 0; Index < mEhdr->e_shnum; ++Index) {
    Shdr = GetShdrByIndex(Index);

    if ((GOTEntryElfRva >= Shdr->sh_addr)
      && ((GOTEntryElfRva - Shdr->sh_addr) < Shdr->sh_size)) {
      mGOTShdr    = Shdr;
      mGOTShIndex = Index;

      return EFI_SUCCESS;
    }
  }

  fprintf (stderr, "ImageTool: ElfRva 0x%016LX for GOT entry not found in any section\n", GOTEntryElfRva);

  return EFI_NOT_FOUND;
}

//
// Stores locations of GOT entries in COFF image. Returns TRUE if GOT entry is new.
// Simple implementation as number of GOT entries is expected to be low.
//
static
EFI_STATUS
AccumulateCoffGOTEntries (
  IN UINT32  GOTCoffEntry,
  IN BOOLEAN *New
  )
{
  UINT32 Index;

  if (mGOTCoffEntries != NULL) {
    for (Index = 0; Index < mGOTNumCoffEntries; ++Index) {
      if (mGOTCoffEntries[Index] == GOTCoffEntry) {
        *New = FALSE;
        return EFI_SUCCESS;
      }
    }

    if (mGOTNumCoffEntries == mGOTMaxCoffEntries) {
      mGOTCoffEntries = (UINT32*)realloc (mGOTCoffEntries, 2 * mGOTMaxCoffEntries * sizeof (*mGOTCoffEntries));
      if (mGOTCoffEntries == NULL) {
        fprintf (stderr, "ImageTool: Could not reallocate memory for mGOTCoffEntries\n");
    		return EFI_OUT_OF_RESOURCES;
      }

      mGOTMaxCoffEntries *= 2;
    }
  }

  if (mGOTCoffEntries == NULL) {

    mGOTCoffEntries = (UINT32*)calloc (1, 5 * sizeof (*mGOTCoffEntries));
    if (mGOTCoffEntries == NULL) {
      fprintf (stderr, "ImageTool: Could not allocate memory for mGOTCoffEntries\n");
  		return EFI_OUT_OF_RESOURCES;
    }

    mGOTMaxCoffEntries = 5;
    mGOTNumCoffEntries = 0;
  }

  mGOTCoffEntries[mGOTNumCoffEntries] = GOTCoffEntry;
  ++mGOTNumCoffEntries;

  *New = TRUE;
  return EFI_SUCCESS;
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
  VOID
  )
{
  UINT32 Index;

	if (mPeSections != NULL) {
    for (Index = 0; (Index < mPeSectionsNumber) && (mPeSections[Index] != NULL); ++Index) {
      free (mPeSections[Index]);
    }

    free (mPeSections);
	}
}

static
EFI_STATUS
CreateSection (
  IN     const char *Name,
  IN 	   BOOLEAN    (*Filter)(const Elf_Shdr *),
  IN     UINT32     Flags,
  IN     UINT8      Type
  )
{
  EFI_STATUS     Status;
  const Elf_Shdr *Shdr;
	PeSection      *PeS;
	UINT32         PeSectionSize;
  UINT32         Index;
  UINTN          NameLength;
  UINT32         Pointer;

	assert (Name   != NULL);
  assert (Filter != NULL);

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
          return EFI_VOLUME_CORRUPTED;
        }
      }

      if ((Shdr->sh_type == SHT_PROGBITS) || (Shdr->sh_type == SHT_NOBITS)) {
        PeSectionSize += ALIGN_VALUE (Shdr->sh_size, Shdr->sh_addralign);
      }
    }
	}

  PeSectionSize = ALIGN_VALUE (PeSectionSize, mPeH.Nt->FileAlignment);

	PeS = calloc (1, sizeof (*PeS) + PeSectionSize);
	if (PeS == NULL) {
		fprintf (stderr, "ImageTool: Could not allocate memory for Pe section\n");
		return EFI_OUT_OF_RESOURCES;
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
  		mPeH.Nt->AddressOfEntryPoint = Pointer + (mEhdr->e_entry - Shdr->sh_addr);
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
	++mPeH.Nt->CommonHeader.FileHeader.NumberOfSections;
	mPeH.Nt->SizeOfImage += ALIGN_VALUE (PeSectionSize, mPeH.Nt->SectionAlignment);

  mPeSections[Type] = PeS;

  Status = ApplyRelocs (Filter);

	return Status;
}

static
EFI_STATUS
GeneratePeReloc (
	IN OUT PeRelocs **PeRelTab,
	IN     UINTN    Offset,
	IN     UINT16   RelocType
  )
{
	UINTN    PageRva;
	UINT16   TypeOffset;
	PeRelocs *PeRel;

	assert (PeRelTab != NULL);

	PageRva = Offset & ~0xfffULL;

	TypeOffset = Offset & 0xfffULL;
  TypeOffset |= RelocType << 12;

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

		PeRel->TypeOffsets = realloc (PeRel->TypeOffsets, PeRel->Total * sizeof (TypeOffset));
		if (PeRel->TypeOffsets == NULL) {
			fprintf (stderr, "ImageTool: Could not reallocate memory for TypeOffset array\n");
			FreeRelocs (*PeRelTab);
			*PeRelTab = NULL;
	    return EFI_OUT_OF_RESOURCES;
		}
	}

	//
	// Store relocation
	//
	PeRel->TypeOffsets[PeRel->Used] = TypeOffset;
	++PeRel->Used;

	return EFI_SUCCESS;
}

static
VOID
EmitGOTRelocations (
  IN OUT PeRelocs **PeRelTab
  )
{
  UINT32 Index;

  if (mGOTCoffEntries == NULL) {
    return;
  }

  for (Index = 0; Index < mGOTNumCoffEntries; ++Index) {
    GeneratePeReloc (PeRelTab, mGOTCoffEntries[Index], EFI_IMAGE_REL_BASED_DIR64);
  }

  free (mGOTCoffEntries);

  mGOTCoffEntries = NULL;
  mGOTMaxCoffEntries = 0;
  mGOTNumCoffEntries = 0;
}

static
EFI_STATUS
ProcessRelocs (
	IN OUT PeRelocs **PeRelTab
  )
{
  const Elf_Shdr *RelShdr;
  const Elf_Shdr *SecShdr;
	const Elf_Rel  *Rel;
  UINT32         SIndex;
  UINTN          RIndex;
	EFI_STATUS     Status;
  UINT8          *SecData;
  UINT32         WSecOffset;
  UINTN          Offset;

  assert (PeRelTab != NULL);

  for (SIndex = 0; SIndex < mEhdr->e_shnum; ++SIndex) {
    RelShdr = GetShdrByIndex (SIndex);

		if ((RelShdr->sh_type != SHT_REL) && (RelShdr->sh_type != SHT_RELA)) {
      continue;
    }

    SecShdr = GetShdrByIndex (RelShdr->sh_info);

    if ((!IsTextShdr (SecShdr)) && (!IsDataShdr (SecShdr))) {
      continue;
    }

    //
    // Process each relocation
    //
    for (RIndex = 0; RIndex < RelShdr->sh_size; RIndex += RelShdr->sh_entsize) {
      Rel = (Elf_Rel *)((UINT8 *)mEhdr + RelShdr->sh_offset + RIndex);

      FindAddress (RelShdr->sh_info, &SecData, &WSecOffset);
      Offset = (Elf_Addr) WSecOffset + (Rel->r_offset - SecShdr->sh_addr);

#if defined(EFI_TARGET64)
      switch (ELF_R_TYPE(Rel->r_info)) {
        case R_X86_64_NONE:
        case R_X86_64_PC32:
        case R_X86_64_PLT32:
        case R_X86_64_GOTPCREL:
        case R_X86_64_GOTPCRELX:
        case R_X86_64_REX_GOTPCRELX:
          break;
        case R_X86_64_64:
          Status = GeneratePeReloc (PeRelTab, Offset, EFI_IMAGE_REL_BASED_DIR64);
          break;
        case R_X86_64_32:
          Status = GeneratePeReloc (PeRelTab, Offset, EFI_IMAGE_REL_BASED_HIGHLOW);
          break;
        default:
          fprintf (stderr, "ImageTool: Unrecognised relocation type %lld\n", ELF_R_TYPE (Rel->r_info));
          return EFI_INVALID_PARAMETER;
      }
#endif
#if defined(EFI_TARGET32)
      switch (ELF_R_TYPE(Rel->r_info)) {
        case R_386_NONE:
        case R_386_PLT32:
        case R_386_PC32:
          break;
        case R_386_32:
          Status = GeneratePeReloc (PeRelTab, Offset, EFI_IMAGE_REL_BASED_HIGHLOW);
          break;
        default:
          fprintf (stderr, "ImageTool: Unrecognised relocation type %d\n", ELF_R_TYPE (Rel->r_info));
          return EFI_INVALID_PARAMETER;
      }
#endif
    }

#if defined(EFI_TARGET64)
    if (RelShdr->sh_info == mGOTShIndex) {
      EmitGOTRelocations (PeRelTab);
    }
#endif
	}

	return Status;
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
EFI_STATUS
CreateRelocSection (
	IN PeRelocs *PeRelTab
  )
{
	PeSection *PeS;
	UINT32    SectionSize;
	UINT32    RawDataSize;

	assert (PeRelTab != NULL);

	//
	// Allocate PE section
	//
	SectionSize = OutputPeReltab (PeRelTab, NULL);
	RawDataSize = ALIGN_VALUE (SectionSize, mPeH.Nt->FileAlignment);
	PeS         = calloc (1, sizeof (*PeS) + RawDataSize);
	if (PeS == NULL) {
		fprintf (stderr, "ImageTool: Could not allocate memory for Pe .reloc section\n");
		return EFI_OUT_OF_RESOURCES;
	}

	//
	// Fill in section header details
	//
	strncpy ((char *)PeS->PeShdr.Name, ".reloc", sizeof (PeS->PeShdr.Name));
	PeS->PeShdr.VirtualSize     = SectionSize;
	PeS->PeShdr.SizeOfRawData   = RawDataSize;
	PeS->PeShdr.Characteristics = EFI_IMAGE_SCN_CNT_INITIALIZED_DATA
    | EFI_IMAGE_SCN_MEM_DISCARDABLE | EFI_IMAGE_SCN_MEM_READ;

	//
	// Copy section contents
	//
	OutputPeReltab (PeRelTab, PeS->Data);

	//
	// Update file header details
	//
	++mPeH.Nt->CommonHeader.FileHeader.NumberOfSections;
	mPeH.Nt->SizeOfImage   += ALIGN_VALUE (SectionSize, mPeH.Nt->SectionAlignment);

	mPeH.Nt->DataDirectory[DIR_BASERELOC].Size = SectionSize;

  mPeSections[RELOC_SECTION] = PeS;

	return EFI_SUCCESS;
}


EFI_STATUS
ApplyRelocs (
  IN BOOLEAN (*Filter)(const Elf_Shdr *)
  )
{
	UINT32         Index;
	const Elf_Shdr *RelShdr;
	const Elf_Shdr *SecShdr;
  UINT8          *SecData;
  UINT32         SecOffset;
  UINT32         WSecOffset;
	UINTN          RelIdx;
	const Elf_Rela *Rel;
	const Elf_Sym  *Sym;
	const Elf_Shdr *SymShdr;
  UINT8          *SymData;
  UINT32         WSymOffset;
	UINT8          *Targ;
  UINT64         GOTEntryRva;
  UINT8          *GOTData;
  UINT32         GOTOffset;
  UINT32         WGOTOffset;
  EFI_STATUS     Status;
  BOOLEAN        NewGOTEntry;

	for (Index = 0; Index < mEhdr->e_shnum; Index++) {
    RelShdr = GetShdrByIndex (Index);

    if ((RelShdr->sh_type != SHT_REL) && (RelShdr->sh_type != SHT_RELA)) {
      continue;
    }

		if (RelShdr->sh_info == 0) {
			continue;
		}

    SecShdr   = GetShdrByIndex (RelShdr->sh_info);
    SecOffset = FindAddress (RelShdr->sh_info, &SecData, &WSecOffset);

#if defined(EFI_TARGET64)
    if ((RelShdr->sh_type != SHT_RELA) || (!(*Filter)(SecShdr))) {
      continue;
    }
#endif
#if defined(EFI_TARGET32)
    if ((RelShdr->sh_type != SHT_REL) || (!(*Filter)(SecShdr))) {
      continue;
    }
#endif

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
      FindAddress (Sym->st_shndx, &SymData, &WSymOffset);

			Targ = SecData + SecOffset + (Rel->r_offset - SecShdr->sh_addr);

#if defined(EFI_TARGET64)
			switch (ELF_R_TYPE(Rel->r_info)) {
				case R_X86_64_NONE:
					break;
				case R_X86_64_64:
					*(UINT64 *)Targ = *(UINT64 *)Targ - SymShdr->sh_addr + WSymOffset;
					break;
				case R_X86_64_32:
					*(UINT32 *)Targ = (UINT32)((UINT64)(*(UINT32 *)Targ) - SymShdr->sh_addr + WSymOffset);
					break;
				case R_X86_64_32S:
					*(INT32 *)Targ = (INT32)((INT64)(*(INT32 *)Targ) - SymShdr->sh_addr + WSymOffset);
					break;
				case R_X86_64_PLT32:
				case R_X86_64_PC32:
          *(UINT32 *)Targ = (UINT32)(*(UINT32 *)Targ + (WSymOffset - WSecOffset) - (SymShdr->sh_addr - SecShdr->sh_addr));
					break;
				case R_X86_64_GOTPCREL:
				case R_X86_64_GOTPCRELX:
				case R_X86_64_REX_GOTPCRELX:
					GOTEntryRva = Rel->r_offset - Rel->r_addend + *(INT32 *)Targ;
					Status = FindElfGOTSectionFromGOTEntryElfRva (GOTEntryRva);
          if (EFI_ERROR (Status)) {
            return Status;
          }

          GOTOffset = FindAddress (mGOTShIndex, &GOTData, &WGOTOffset);
					*(UINT32 *)Targ = (UINT32) (*(UINT32 *)Targ	+ (WGOTOffset - WSecOffset) - (mGOTShdr->sh_addr - SecShdr->sh_addr));
          //
          // ELF Rva -> PE Rva
          //
					GOTEntryRva += (GOTOffset - mGOTShdr->sh_addr);
          Status = AccumulateCoffGOTEntries((UINT32)GOTEntryRva, &NewGOTEntry);
          if (EFI_ERROR (Status)) {
            return Status;
          }

          if (NewGOTEntry) {
            Targ = GOTData + GOTEntryRva;
            *(UINT64 *)Targ = *(UINT64 *)Targ - SymShdr->sh_addr + WSymOffset;
          }

					break;
				default:
					fprintf (stderr, "ImageTool: Unsupported ELF EM_X86_64 relocation 0x%llx\n", ELF_R_TYPE(Rel->r_info));
					return EFI_UNSUPPORTED;
			}
#endif
#if defined(EFI_TARGET32)
      switch (ELF_R_TYPE(Rel->r_info)) {
        case R_386_NONE:
          break;
        case R_386_32:
          *(UINT32 *)Targ = *(UINT32 *)Targ - SymShdr->sh_addr + WSymOffset;
          break;
        case R_386_PLT32:
        case R_386_PC32:
          *(UINT32 *)Targ = (UINT32)(*(UINT32 *)Targ + (WSymOffset - WSecOffset) - (SymShdr->sh_addr - SecShdr->sh_addr));
          break;
        default:
          fprintf (stderr, "ImageTool: Unsupported ELF EM_386 relocation 0x%x\n", ELF_R_TYPE(Rel->r_info));
          return EFI_UNSUPPORTED;
      }
#endif
		}
	}

	return EFI_SUCCESS;
}

static
EFI_STATUS
WritePeFile (
	IN  UINT32 NtSize,
  OUT FILE   *Pe
  )
{
	PeSection  *PeS;
	UINT32     Position;
  UINT32     Index;

	assert (Pe != NULL);

  Position = mPeH.Nt->SizeOfHeaders;

	mPeH.Nt->SizeOfImage         += ALIGN_VALUE (mPeH.Nt->SizeOfHeaders, mPeH.Nt->SectionAlignment);
	mPeH.Nt->AddressOfEntryPoint += mPeH.Nt->SizeOfHeaders;

	//
	// Assign raw data pointers
	//
  for (Index = 0; Index < mPeSectionsNumber; ++Index) {
    PeS = mPeSections[Index];

		if (PeS->PeShdr.SizeOfRawData != 0) {
			PeS->PeShdr.PointerToRawData = Position;
			PeS->PeShdr.VirtualAddress   = Position;

      if (PeS->Type == TEXT_SECTION) {
        mPeH.Nt->BaseOfCode = Position;
				mPeH.Nt->SizeOfCode = PeS->PeShdr.SizeOfRawData;
			}

#if defined(EFI_TARGET32)
      if (PeS->Type == DATA_SECTION) {
        mPeH.Nt->BaseOfData = Position;
			}
#endif

			if (PeS->Type == RELOC_SECTION) {
				mPeH.Nt->DataDirectory[DIR_BASERELOC].VirtualAddress = Position;
			}

			Position += PeS->PeShdr.SizeOfRawData;
		}
	}

	//
	// Write DOS header
	//
	if (fwrite (&mPeH, sizeof (mPeH.Dos), 1, Pe) != 1) {
		fprintf (stderr, "ImageTool: Could not write PE DOS header\n");
		return EFI_ABORTED;
	}

	//
	// Write NT header
	//
	if (fwrite (mPeH.Nt, NtSize, 1, Pe) != 1) {
		fprintf (stderr, "ImageTool: Could not write PE NT header\n");
		return EFI_ABORTED;
	}

	//
	// Write section headers
	//
  for (Index = 0; Index < mPeSectionsNumber; ++Index) {
    PeS = mPeSections[Index];
		if (fwrite (&PeS->PeShdr, sizeof (PeS->PeShdr), 1, Pe) != 1) {
			fprintf (stderr, "ImageTool: Could not write section header\n");
			return EFI_ABORTED;
		}
	}

	//
	// Write sections
	//
  for (Index = 0; Index < mPeSectionsNumber; ++Index) {
    PeS = mPeSections[Index];
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

  const Elf_Shdr *RelShdr;
  const Elf_Shdr *SecShdr;
	const Elf_Rel  *Rel;
  UINT32         SIndex;
  UINTN          RIndex;

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

  if ((mEhdr->e_type != ET_EXEC) && (mEhdr->e_type != ET_DYN)) {
    fprintf (stderr, "ImageTool: ELF e_type not ET_EXEC or ET_DYN\n");
		free (mEhdr);
    return EFI_UNSUPPORTED;
  }

#if defined(EFI_TARGET64)
  if (mEhdr->e_machine != EM_X86_64) {
    fprintf (stderr, "ImageTool: Unsupported ELF e_machine\n");
    free (mEhdr);
    return EFI_UNSUPPORTED;
  }
#endif
#if defined(EFI_TARGET32)
  if (mEhdr->e_machine != EM_386) {
    fprintf (stderr, "ImageTool: Unsupported ELF e_machine\n");
    free (mEhdr);
    return EFI_UNSUPPORTED;
  }
#endif

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

  for (SIndex = 0; SIndex < mEhdr->e_shnum; ++SIndex) {
    RelShdr = GetShdrByIndex (SIndex);

    if ((RelShdr->sh_type != SHT_REL) && (RelShdr->sh_type != SHT_RELA)) {
      continue;
    }

    SecShdr = GetShdrByIndex (RelShdr->sh_info);

    if ((!IsTextShdr (SecShdr)) && (!IsDataShdr (SecShdr))) {
      continue;
    }

    for (RIndex = 0; RIndex < RelShdr->sh_size; RIndex += RelShdr->sh_entsize) {
      Rel = (Elf_Rel *)((UINT8 *)mEhdr + RelShdr->sh_offset + RIndex);
#if defined(EFI_TARGET64)
      if ((ELF_R_TYPE(Rel->r_info) == R_X86_64_64)
        || (ELF_R_TYPE(Rel->r_info) == R_X86_64_32)) {
        mRelocSectionExists = TRUE;
      }
#endif
#if defined(EFI_TARGET32)
      if (ELF_R_TYPE(Rel->r_info) == R_386_32) {
        mRelocSectionExists = TRUE;
      }
#endif
    }
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
	FILE       *Pe;
	EFI_STATUS Status;
	UINT32     DataDirSize;
	UINT32     NtSize;

	assert (ElfName != NULL);
	assert (PeName  != NULL);

	PeRelTab   = NULL;

	Status = ReadElfFile (ElfName);
	if (EFI_ERROR (Status)) {
		return Status;
	}

  mPeSectionsNumber = 2;

	//
	// Initialise PE header
	//
	ZeroMem (&mPeH, sizeof (mPeH));
	mPeH.Dos.e_magic  = EFI_IMAGE_DOS_SIGNATURE;
	mPeH.Dos.e_lfanew = sizeof (EFI_IMAGE_DOS_HEADER);

	//
  // Only base relocation directory
	//
	NtSize = sizeof (EFI_IMAGE_NT_HEADERS) + sizeof (EFI_IMAGE_DATA_DIRECTORY);
	mPeH.Nt = calloc (1, NtSize);
	if (mPeH.Nt == NULL) {
		fprintf (stderr, "ImageTool: Could not allocate memory for EFI_IMAGE_NT_HEADERS\n");
		free (mEhdr);
		return EFI_OUT_OF_RESOURCES;
	}

	mPeH.Nt->CommonHeader.Signature = EFI_IMAGE_NT_SIGNATURE;
	mPeH.Nt->NumberOfRvaAndSizes = 1;
	DataDirSize = sizeof (EFI_IMAGE_DATA_DIRECTORY) * mPeH.Nt->NumberOfRvaAndSizes;

  mPeH.Nt->CommonHeader.FileHeader.SizeOfOptionalHeader = DataDirSize +
	  sizeof (EFI_IMAGE_NT_HEADERS) - sizeof (EFI_IMAGE_NT_HEADERS_COMMON_HDR);

	mPeH.Nt->CommonHeader.FileHeader.Characteristics =
	  EFI_IMAGE_FILE_DLL | EFI_IMAGE_FILE_MACHINE | EFI_IMAGE_FILE_EXECUTABLE_IMAGE;

	mPeH.Nt->Magic            = EFI_IMAGE_NT_OPTIONAL_HDR_MAGIC;
	mPeH.Nt->SectionAlignment = mPeAlignment;
	mPeH.Nt->FileAlignment    = mPeAlignment;
	mPeH.Nt->SizeOfHeaders    = sizeof (mPeH.Dos) + NtSize;

  if (mRelocSectionExists) {
    ++mPeSectionsNumber;
  }
  mPeH.Nt->SizeOfHeaders += mPeSectionsNumber * sizeof (EFI_IMAGE_SECTION_HEADER);
  mPeH.Nt->SizeOfHeaders = ALIGN_VALUE (mPeH.Nt->SizeOfHeaders, mPeH.Nt->FileAlignment);

	mPeH.Nt->Subsystem               = EFI_IMAGE_SUBSYSTEM_EFI_APPLICATION;
  mPeH.Nt->SizeOfUninitializedData = 0;

	switch (mEhdr->e_machine) {
		case EM_386:
			mPeH.Nt->CommonHeader.FileHeader.Machine = EFI_IMAGE_MACHINE_IA32;
			break;
		case EM_X86_64:
			mPeH.Nt->CommonHeader.FileHeader.Machine = EFI_IMAGE_MACHINE_X64;
			break;
		case EM_ARM:
			mPeH.Nt->CommonHeader.FileHeader.Machine = EFI_IMAGE_MACHINE_ARMTHUMB_MIXED;
			break;
		case EM_AARCH64:
			mPeH.Nt->CommonHeader.FileHeader.Machine = EFI_IMAGE_MACHINE_AARCH64;
			break;
		default:
			fprintf (stderr, "ImageTool: Unknown ELF architecture %d\n", mEhdr->e_machine);
			Status = EFI_UNSUPPORTED;
			goto exit;
	}

  mPeSections = calloc (1, mPeSectionsNumber * sizeof (*mPeSections));
	if (mPeSections == NULL) {
		fprintf (stderr, "ImageTool: Could not allocate memory for PeSections array\n");
		free (mEhdr);
		return EFI_OUT_OF_RESOURCES;
	}

  Status = CreateSection (
    ".text",
    IsTextShdr,
    EFI_IMAGE_SCN_CNT_CODE | EFI_IMAGE_SCN_MEM_EXECUTE | EFI_IMAGE_SCN_MEM_READ,
    TEXT_SECTION
    );
  if (EFI_ERROR (Status)) {
    goto exit;
  }

  Status = CreateSection (
    ".data",
    IsDataShdr,
    EFI_IMAGE_SCN_CNT_INITIALIZED_DATA | EFI_IMAGE_SCN_MEM_WRITE | EFI_IMAGE_SCN_MEM_READ,
    DATA_SECTION
    );
  if (EFI_ERROR (Status)) {
    goto exit;
  }

  mPeH.Nt->SizeOfInitializedData = mPeSections[DATA_SECTION]->PeShdr.SizeOfRawData;

  if (mRelocSectionExists) {
    Status = ProcessRelocs (&PeRelTab);
    if (EFI_ERROR (Status)) {
      goto exit;
    }

    Status = CreateRelocSection (PeRelTab);
    if (EFI_ERROR (Status)) {
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

	Status = WritePeFile (NtSize, Pe);
	fclose (Pe);

exit:
	if (PeRelTab != NULL) {
		FreeRelocs (PeRelTab);
	}
	FreeSections ();
	free (mPeH.Nt);
	free (mEhdr);

	return Status;
}
