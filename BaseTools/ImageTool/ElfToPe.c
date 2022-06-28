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

static Elf_Size mPeAlignment = 0x200;

static
BOOLEAN
IsTextShdr (
  IN const Elf_Shdr *Shdr
  )
{
  return (((Shdr->sh_flags & (SHF_EXECINSTR | SHF_ALLOC)) == (SHF_EXECINSTR | SHF_ALLOC)) ||
          ((Shdr->sh_flags & (SHF_WRITE | SHF_ALLOC)) == SHF_ALLOC));
}

static
BOOLEAN
IsDataShdr (
  IN const Elf_Shdr *Shdr
  )
{
  return ((Shdr->sh_flags & (SHF_EXECINSTR | SHF_WRITE | SHF_ALLOC)) == (SHF_ALLOC | SHF_WRITE));
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
ReadElfFile (
	IN  const char *Name,
	OUT Elf_Ehdr   **Ehdr
  )
{
	static const unsigned char Ident[] = {
		ELFMAG0, ELFMAG1, ELFMAG2, ELFMAG3, ELFCLASS, ELFDATA2LSB
	};
	const Elf_Shdr *Shdr;
	UINTN          Offset;
	UINT32         Index;
	UINT32         FileSize;

	assert (Ehdr != NULL);

	*Ehdr = (Elf_Ehdr *)UserReadFile (Name, &FileSize);
  if (*Ehdr == NULL) {
		fprintf (stderr, "ImageTool: Could not open %s: %s\n", Name, strerror (errno));
    return EFI_VOLUME_CORRUPTED;
  }

	//
	// Check header
	//
	if ((FileSize < sizeof (**Ehdr))
	  || (memcmp (Ident, (*Ehdr)->e_ident, sizeof (Ident)) != 0)) {
		fprintf (stderr, "ImageTool: Invalid ELF header in file %s\n", Name);
		free (*Ehdr);
    return EFI_VOLUME_CORRUPTED;
	}

	//
	// Check section headers
	//
	for (Index = 0; Index < (*Ehdr)->e_shnum; ++Index) {
		Offset = (*Ehdr)->e_shoff + Index * (*Ehdr)->e_shentsize;

		if (FileSize < (Offset + sizeof (*Shdr))) {
			fprintf (stderr, "ImageTool: ELF section header is outside file %s\n", Name);
			free (*Ehdr);
			return EFI_VOLUME_CORRUPTED;
		}

		Shdr = (Elf_Shdr *)((UINT8 *)(*Ehdr) + Offset);

		if ((Shdr->sh_type != SHT_NOBITS)
		  && ((FileSize < Shdr->sh_offset) || ((FileSize - Shdr->sh_offset) < Shdr->sh_size))) {
			fprintf (stderr, "ImageTool: ELF section %d points outside file %s\n", Index, Name);
			free (*Ehdr);
			return EFI_VOLUME_CORRUPTED;
		}

		if (Shdr->sh_link >= (*Ehdr)->e_shnum) {
			fprintf (stderr, "ImageTool: ELF %d-th section's sh_link is out of range\n", Index);
			free (*Ehdr);
			return EFI_VOLUME_CORRUPTED;
		}

		if (Shdr->sh_addralign <= mPeAlignment) {
      continue;
    }
    if (IsTextShdr(Shdr) || IsDataShdr(Shdr)) {
      mPeAlignment = Shdr->sh_addralign;
    }
	}

	if ((!IS_POW2(mPeAlignment)) || (mPeAlignment > MAX_PE_ALIGNMENT)) {
    fprintf (stderr, "ImageTool: Invalid section alignment\n");
		free (*Ehdr);
		return EFI_VOLUME_CORRUPTED;
  }

	return EFI_SUCCESS;
}

static
const char *
GetElfString (
	IN const Elf_Ehdr *Ehdr,
	IN UINT32         Section,
	IN UINT32         Offset
  )
{
	const Elf_Shdr *Shdr;
	char           *Last;

	//
	// Locate section header
	//
	if (Section >= Ehdr->e_shnum) {
		fprintf (stderr, "ImageTool: Invalid ELF string section %d\n", Section);
    return NULL;
	}
	Shdr = (Elf_Shdr *)((UINT8 *)Ehdr + Ehdr->e_shoff + Section * Ehdr->e_shentsize);

	//
	// Sanity check section
	//
	if (Shdr->sh_type != SHT_STRTAB) {
		fprintf (stderr, "ImageTool: ELF section %d (type %d) is not a string table\n", Section, Shdr->sh_type);
    return NULL;
	}

	Last = (char *)((UINT8 *)Ehdr + Shdr->sh_offset + Shdr->sh_size - 1);
	if (*Last != '\0') {
		fprintf (stderr, "ImageTool: ELF section %d is not NUL-terminated\n", Section);
    return NULL;
	}

	//
	// Locate string
	//
	if (Offset >= Shdr->sh_size) {
		fprintf (stderr, "ImageTool: Invalid ELF string offset %d in section %d\n", Offset, Section);
    return NULL;
	}

	return (char *)((UINT8 *)Ehdr + Shdr->sh_offset + Offset);
}

static
PeSection *
ProcessSection (
	IN     const Elf_Ehdr *Ehdr,
	IN     const Elf_Shdr *Shdr,
	IN OUT PeHeader       *PeH
  )
{
	PeSection  *PeS;
	const char *Name;
	UINTN      NameLength;
	UINT32     PeSectionSize;

	assert (Ehdr != NULL);
	assert (Shdr != NULL);
	assert (PeH  != NULL);

	PeSectionSize = 0;

	Name = GetElfString (Ehdr, Ehdr->e_shstrndx, Shdr->sh_name);
	if (Name == NULL) {
		return NULL;
	}

	if ((Shdr->sh_addralign != 0) && (Shdr->sh_addralign != 1)) {
		//
		// The alignment field is valid
		//
		if (!IS_ALIGNED(Shdr->sh_addr, Shdr->sh_addralign)) {
			fprintf (stderr, "ImageTool: Section address not aligned to its own alignment\n");
			return NULL;
		}
	}

	//
	// Allocate PE section
	//
	if (Shdr->sh_type == SHT_PROGBITS) {
		PeSectionSize = ALIGN_VALUE (Shdr->sh_size, PeH->Nt->FileAlignment);
	}

	PeS = calloc (1, sizeof (*PeS) + PeSectionSize);
	if (PeS == NULL) {
		fprintf (stderr, "ImageTool: Could not allocate memory for Pe section\n");
		return NULL;
	}

	//
	// Fill in section header details
	//
	NameLength = strlen (Name);
	if (NameLength > sizeof (PeS->PeShdr.Name)) {
		NameLength = sizeof (PeS->PeShdr.Name);
	}
	memcpy (PeS->PeShdr.Name, Name, NameLength);

	PeS->PeShdr.VirtualSize    = Shdr->sh_size;
	PeS->PeShdr.SizeOfRawData  = PeSectionSize;

	//
	// Fill in section characteristics
	//
	if ((Shdr->sh_type == SHT_PROGBITS) && ((Shdr->sh_flags & SHF_EXECINSTR) != 0)) {
		//
		// .text section
		//
		PeS->PeShdr.Characteristics =
		  EFI_IMAGE_SCN_CNT_CODE | EFI_IMAGE_SCN_MEM_NOT_PAGED |
			EFI_IMAGE_SCN_MEM_EXECUTE | EFI_IMAGE_SCN_MEM_READ;
	} else if ((Shdr->sh_type == SHT_PROGBITS) && ((Shdr->sh_flags & SHF_WRITE) != 0)) {
		//
		// .data section
		//
		PeS->PeShdr.Characteristics =
			EFI_IMAGE_SCN_CNT_INITIALIZED_DATA | EFI_IMAGE_SCN_MEM_NOT_PAGED |
			EFI_IMAGE_SCN_MEM_READ | EFI_IMAGE_SCN_MEM_WRITE;
	} else if (Shdr->sh_type == SHT_PROGBITS) {
		//
		// .rodata section
		//
		PeS->PeShdr.Characteristics =
			EFI_IMAGE_SCN_CNT_INITIALIZED_DATA |
			EFI_IMAGE_SCN_MEM_NOT_PAGED | EFI_IMAGE_SCN_MEM_READ;
	} else if (Shdr->sh_type == SHT_NOBITS) {
		//
		// .bss section
		//
		PeS->PeShdr.Characteristics =
			EFI_IMAGE_SCN_CNT_UNINITIALIZED_DATA | EFI_IMAGE_SCN_MEM_NOT_PAGED |
			EFI_IMAGE_SCN_MEM_READ | EFI_IMAGE_SCN_MEM_WRITE;
	} else {
		fprintf (stderr, "ImageTool: Unrecognised characteristics for section %s\n", Name);
		free (PeS);
		return NULL;
	}

	if (Shdr->sh_type == SHT_PROGBITS) {
		memcpy (PeS->Data, (UINT8 *)Ehdr + Shdr->sh_offset, Shdr->sh_size);
	}

	//
	// Update remaining file header fields
	//
	if ((Ehdr->e_entry >= Shdr->sh_addr)
	  && ((Ehdr->e_entry - Shdr->sh_addr) < Shdr->sh_size)) {
		PeH->Nt->AddressOfEntryPoint = Ehdr->e_entry - Shdr->sh_addr + PeH->Nt->SizeOfImage;
	}

	++PeH->Nt->CommonHeader.FileHeader.NumberOfSections;
	PeH->Nt->SizeOfHeaders += sizeof (PeS->PeShdr);
	PeH->Nt->SizeOfImage   +=	ALIGN_VALUE (PeSectionSize, PeH->Nt->SectionAlignment);

	return PeS;
}

static
EFI_STATUS
ProcessReloc (
	IN     const Elf_Ehdr *Ehdr,
	IN     const Elf_Shdr *Shdr,
	IN     const Elf_Sym  *SymTable,
	IN     UINT32         SymNumber,
	IN     const Elf_Rel  *Rel,
	IN OUT PeRelocs       **PeRelTab
  )
{
	UINT32     Type;
	UINT32     SymIndex;
	UINT32     MachineRelocType;
	UINTN      Offset;
	EFI_STATUS Status;

	assert (Ehdr     != NULL);
	assert (Shdr     != NULL);
	assert (SymTable != NULL);
	assert (Rel      != NULL);
	assert (PeRelTab != NULL);

	Type             = ELF_R_TYPE (Rel->r_info);
	SymIndex         = ELF_R_SYM (Rel->r_info);
	MachineRelocType = ELF_MREL (Ehdr->e_machine, Type);
	Offset           = Shdr->sh_addr + Rel->r_offset;

	//
	// Look up symbol and process relocation
	//
	if (SymIndex >= SymNumber) {
		fprintf (stderr, "ImageTool: Symbol is out of range\n");
		return EFI_INVALID_PARAMETER;
	}

	if (SymTable[SymIndex].st_shndx == SHN_ABS) {
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
	IN     const Elf_Ehdr *Ehdr,
	IN     const Elf_Shdr *Shdr,
	IN     UINT32         EntrySize,
	IN OUT PeRelocs       **PeRelTab
  )
{
	const Elf_Shdr *SymSec;
	const Elf_Sym  *SymTable;
	const Elf_Rel  *Rel;
	UINT32         SymNumber;
	UINT32         RelNumber;
	UINT32         Index;
	EFI_STATUS     Status;

	assert (Ehdr     != NULL);
	assert (Shdr     != NULL);
	assert (PeRelTab != NULL);

	//
	// Identify symbol table
	//
	SymSec    = (Elf_Shdr *)((UINT8 *)Ehdr + Ehdr->e_shoff + Shdr->sh_link * Ehdr->e_shentsize);
	SymTable  = (Elf_Sym *)((UINT8 *)Ehdr + SymSec->sh_offset);
	SymNumber = SymSec->sh_size / sizeof (*SymTable);

	if (SymNumber == 0) {
		return EFI_SUCCESS;
	}

	//
	// Process each relocation
	//
	Rel       = (Elf_Rel *)((UINT8 *)Ehdr + Shdr->sh_offset);
	RelNumber = Shdr->sh_size / EntrySize;
	for (Index = 0; Index < RelNumber; ++Index) {
		Status = ProcessReloc (Ehdr, Shdr, SymTable, SymNumber, Rel, PeRelTab);
		if (EFI_ERROR (Status)) {
			return Status;
		}

		Rel = (Elf_Rel *)((UINT8 *)Rel + EntrySize);
	}

	return EFI_SUCCESS;
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
VOID
FixupDebugSection (
	PeSection *PeS
  )
{
	DebugData *Data;

	assert (PeS != NULL);

	Data = (DebugData *)PeS->Data;
	Data->Dir.FileOffset += PeS->PeShdr.PointerToRawData - PeS->PeShdr.VirtualAddress;
}

static
PeSection *
CreateDebugSection (
	IN OUT PeHeader   *PeH,
	IN     const char *FileName
  )
{
	PeSection *PeS;
	UINT32    SectionSize;
	UINT32    RawDataSize;
	DebugData *Data;

	assert (PeH      != NULL);
	assert (FileName != NULL);

	//
	// Allocate PE section
	//
	SectionSize = sizeof (*Data) + strlen (FileName) + 1;
	RawDataSize = ALIGN_VALUE (SectionSize, PeH->Nt->FileAlignment);
	PeS         = calloc (1, sizeof (*PeS) + RawDataSize);
	if (PeS == NULL) {
		fprintf (stderr, "ImageTool: Could not allocate memory for Pe .debug section\n");
		return NULL;
	}

	Data = (DebugData *)PeS->Data;

	//
	// Fill in section header details
	//
	strncpy ((char *)PeS->PeShdr.Name, ".debug", sizeof (PeS->PeShdr.Name));

	PeS->PeShdr.VirtualSize     = SectionSize;
	PeS->PeShdr.SizeOfRawData   = RawDataSize;
	PeS->PeShdr.Characteristics =
	  EFI_IMAGE_SCN_CNT_INITIALIZED_DATA | EFI_IMAGE_SCN_MEM_DISCARDABLE |
		EFI_IMAGE_SCN_MEM_NOT_PAGED | EFI_IMAGE_SCN_MEM_READ;
	PeS->Fixup                  = FixupDebugSection;

	//
	// Create section contents
	//
	Data->Dir.Type       = EFI_IMAGE_DEBUG_TYPE_CODEVIEW;
	Data->Dir.SizeOfData = SectionSize - sizeof (Data->Dir);
	Data->Dir.RVA        = sizeof (Data->Dir);
	Data->Dir.FileOffset = Data->Dir.RVA;

	Data->Rsds.Signature = CODEVIEW_SIGNATURE_RSDS;
	snprintf (Data->Name, strlen (FileName) + 1, "%s", FileName);

	//
	// Update file header details
	//
	++PeH->Nt->CommonHeader.FileHeader.NumberOfSections;
	PeH->Nt->SizeOfHeaders += sizeof (PeS->PeShdr);
	PeH->Nt->SizeOfImage   += ALIGN_VALUE (SectionSize, PeH->Nt->SectionAlignment);

	PeH->Nt->DataDirectory[DIR_DEBUG].Size = SectionSize;

	return PeS;
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
	PeSection *PeS;
	UINT32    Position;

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

			if (strncmp ((char *)PeS->PeShdr.Name, ".reloc", sizeof (PeS->PeShdr.Name)) == 0) {
				PeH->Nt->DataDirectory[DIR_BASERELOC].VirtualAddress = Position;
			}

			if (strncmp ((char *)PeS->PeShdr.Name, ".debug", sizeof (PeS->PeShdr.Name)) == 0) {
				PeH->Nt->DataDirectory[DIR_DEBUG].VirtualAddress = Position;
				((DebugData *)PeS->Data)->Dir.RVA += Position;
			}

			if ((PeS->PeShdr.Characteristics & EFI_IMAGE_SCN_CNT_CODE) != 0) {
				if (PeH->Nt->BaseOfCode == 0) {
					PeH->Nt->BaseOfCode = Position;
				}
				PeH->Nt->SizeOfCode += PeS->PeShdr.VirtualSize;
			}

#if defined(EFI_TARGET32)
			if ((PeS->PeShdr.Characteristics & (EFI_IMAGE_SCN_CNT_INITIALIZED_DATA | EFI_IMAGE_SCN_CNT_UNINITIALIZED_DATA)) != 0) {
				if (PeH->Nt->BaseOfData == 0) {
					PeH->Nt->BaseOfData = Position;
				}
			}
#endif
			if ((PeS->PeShdr.Characteristics & EFI_IMAGE_SCN_CNT_INITIALIZED_DATA) != 0) {
				PeH->Nt->SizeOfInitializedData += PeS->PeShdr.VirtualSize;
			}

			if ((PeS->PeShdr.Characteristics & EFI_IMAGE_SCN_CNT_UNINITIALIZED_DATA) != 0) {
				PeH->Nt->SizeOfUninitializedData += PeS->PeShdr.VirtualSize;
			}

			Position += PeS->PeShdr.SizeOfRawData;
		}

		if (PeS->Fixup != NULL) {
			PeS->Fixup (PeS);
		}
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
const char *
BaseName (
	IN const char *Path
  )
{
	char *BaseName;

	assert (Path != NULL);

	BaseName = strrchr (Path, '/');

	return (BaseName != NULL) ? (BaseName + 1) : Path;
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

EFI_STATUS
ElfToPe (
	IN const char *ElfName,
	IN const char *PeName
  )
{
	PeRelocs       *PeRelTab;
	PeSection      *PeSections;
	PeSection      **NextPeSection;
	PeHeader       PeH;
	Elf_Ehdr       *Ehdr;
	const Elf_Shdr *Shdr;
	UINTN          Offset;
	UINT32         Index;
	FILE           *Pe;
	EFI_STATUS     Status;
	UINT32         DataDirSize;
	UINT32         NtSize;

	assert (ElfName != NULL);
	assert (PeName  != NULL);

	PeRelTab      = NULL;
	PeSections    = NULL;
	NextPeSection = &PeSections;

	Status = ReadElfFile (ElfName, &Ehdr);
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
  // Only base relocation and debug directory
	//
	NtSize = sizeof (EFI_IMAGE_NT_HEADERS) + sizeof (EFI_IMAGE_DATA_DIRECTORY) * 2;
	PeH.Nt = calloc (1, NtSize);
	if (PeH.Nt == NULL) {
		fprintf (stderr, "ImageTool: Could not allocate memory for EFI_IMAGE_NT_HEADERS\n");
		free (Ehdr);
		return EFI_OUT_OF_RESOURCES;
	}

	PeH.Nt->CommonHeader.Signature = EFI_IMAGE_NT_SIGNATURE;
	PeH.Nt->NumberOfRvaAndSizes = 2;
	DataDirSize = sizeof (EFI_IMAGE_DATA_DIRECTORY) * PeH.Nt->NumberOfRvaAndSizes;

  PeH.Nt->CommonHeader.FileHeader.SizeOfOptionalHeader = DataDirSize +
	  sizeof (EFI_IMAGE_NT_HEADERS) - sizeof (EFI_IMAGE_NT_HEADERS_COMMON_HDR);

	PeH.Nt->CommonHeader.FileHeader.Characteristics =
	  EFI_IMAGE_FILE_DLL | EFI_IMAGE_FILE_MACHINE | EFI_IMAGE_FILE_EXECUTABLE_IMAGE;

	PeH.Nt->Magic               = EFI_IMAGE_NT_OPTIONAL_HDR_MAGIC;
	PeH.Nt->SectionAlignment    = mPeAlignment;
	PeH.Nt->FileAlignment       = mPeAlignment;
	PeH.Nt->SizeOfHeaders       = sizeof (PeH.Dos) + NtSize;
	PeH.Nt->Subsystem           = EFI_IMAGE_SUBSYSTEM_EFI_APPLICATION;

	switch (Ehdr->e_machine) {
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
			fprintf (stderr, "ImageTool: Unknown ELF architecture %d\n", Ehdr->e_machine);
			Status = EFI_UNSUPPORTED;
			goto exit;
	}

	//
	// Process Elf sections
	//
	for (Index = 0; Index < Ehdr->e_shnum; ++Index) {
		Offset = Ehdr->e_shoff + Index * Ehdr->e_shentsize;
		Shdr   = (Elf_Shdr *)((UINT8 *)Ehdr + Offset);

		if ((Shdr->sh_flags & SHF_ALLOC) != 0) {
      //
			// Create output section
			//
			*NextPeSection = ProcessSection (Ehdr, Shdr, &PeH);
			if (*NextPeSection == NULL) {
				Status = EFI_ABORTED;
				goto exit;
			}

			NextPeSection = &(*NextPeSection)->Next;
			continue;
		}

		if (Shdr->sh_type == SHT_REL) {
      //
			// Process .rel relocations
			//
			Status = ProcessRelocs (Ehdr, Shdr, sizeof (Elf_Rel), &PeRelTab);
			if (EFI_ERROR (Status)) {
				goto exit;
			}

			continue;
		}

		if (Shdr->sh_type == SHT_RELA) {
      //
			// Process .rela relocations
			//
			Status = ProcessRelocs (Ehdr, Shdr, sizeof (Elf_Rela), &PeRelTab);
			if (EFI_ERROR (Status)) {
				goto exit;
			}
		}
	}

  if (PeRelTab != NULL) {
		*NextPeSection = CreateRelocSection (&PeH, PeRelTab);
		if (*NextPeSection == NULL) {
			Status = EFI_ABORTED;
			goto exit;
		}

		NextPeSection = &(*NextPeSection)->Next;
	}

	*NextPeSection = CreateDebugSection (&PeH, BaseName (PeName));
	if (*NextPeSection == NULL) {
		Status = EFI_ABORTED;
		goto exit;
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
	free (Ehdr);

	return Status;
}
