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

static
EFI_STATUS
GeneratePeReloc (
	PeRelocs      **PeRelTab,
	unsigned long rva,
	size_t        size
  )
{
	unsigned long start_rva;
	uint16_t      reloc;
	PeRelocs      *pe_rel;
	uint16_t      *relocs;

	//
	// Construct
	//
	start_rva = rva & ~0xfff;
	reloc     = rva & 0xfff;
	switch (size) {
		case 8:
			reloc |= 0xa000;
			break;
		case 4:
			reloc |= 0x3000;
			break;
		case 2:
			reloc |= 0x2000;
			break;
		default:
			printf ("Unsupported relocation size %zd\n", size);
	    return EFI_INVALID_PARAMETER;
	}

  //
	// Locate or create PE relocation table
	//
	for (pe_rel = *PeRelTab; pe_rel != NULL; pe_rel = pe_rel->next) {
		if (pe_rel->start_rva == start_rva) {
			break;
		}
	}

	if (pe_rel == NULL) {
		pe_rel = calloc (1, sizeof (*pe_rel));
		if (pe_rel == NULL) {
			printf ("Could not allocate memory for pe_rel\n");
	    return EFI_OUT_OF_RESOURCES;
		}

		pe_rel->next      = *PeRelTab;
		*PeRelTab         = pe_rel;
		pe_rel->start_rva = start_rva;
	}

	//
	// Expand relocation list if necessary
	//
	if (pe_rel->used_relocs < pe_rel->total_relocs) {
		relocs = pe_rel->relocs;
	} else {
		pe_rel->total_relocs = pe_rel->total_relocs ? (pe_rel->total_relocs * 2) : 256;

		relocs = calloc (1, pe_rel->total_relocs * sizeof (pe_rel->relocs[0]));
		if (relocs == NULL) {
			printf ("Could not allocate memory for relocs\n");
	    return EFI_OUT_OF_RESOURCES;
		}

		memcpy (relocs, pe_rel->relocs, pe_rel->used_relocs * sizeof (pe_rel->relocs[0]));

		free (pe_rel->relocs);
		pe_rel->relocs = relocs;
	}

	//
	// Store relocation
	//
	pe_rel->relocs[pe_rel->used_relocs] = reloc;
	++pe_rel->used_relocs;

	return EFI_SUCCESS;
}

static
size_t
OutputPeReltab (
	PeRelocs *PeRelTab,
	void     *buffer
  )
{
	PeRelocs     *pe_rel;
	unsigned int num_relocs;
	size_t       size;
	size_t       total_size;

	total_size = 0;

	for (pe_rel = PeRelTab; pe_rel != NULL; pe_rel = pe_rel->next) {
		num_relocs = ((pe_rel->used_relocs + 1) & ~1);

		//
		// VirtualAddress + SizeOfBlock + num_relocs
		//
		size = sizeof (uint32_t) + sizeof (uint32_t)  + num_relocs * sizeof (uint16_t);
		if (buffer != NULL) {
			*((uint32_t *)(buffer + total_size)) = pe_rel->start_rva;

			*((uint32_t *)(buffer + total_size + sizeof (uint32_t))) = size;

			memcpy (
				buffer + total_size + 2 * sizeof (uint32_t),
				pe_rel->relocs,
				num_relocs * sizeof (uint16_t)
			  );
		}

		total_size += size;
	}

	return total_size;
}

static
EFI_STATUS
ReadElfFile (
	const char *Name,
	Elf_Ehdr   **Ehdr
  )
{
	static const unsigned char Ident[] = {
		ELFMAG0, ELFMAG1, ELFMAG2, ELFMAG3, ELFCLASS, ELFDATA2LSB
	};
	const Elf_Shdr *Shdr;
	size_t         Offset;
	UINT32         Index;
	UINT32         FileSize;

	*Ehdr = (Elf_Ehdr *)UserReadFile (Name, &FileSize);
  if (*Ehdr == NULL) {
		printf ("Could not open %s: %s\n", Name, strerror (errno));
    return EFI_VOLUME_CORRUPTED;
  }

	//
	// Check header
	//
	if ((FileSize < sizeof (**Ehdr))
	  || (memcmp (Ident, (*Ehdr)->e_ident, sizeof (Ident)) != 0)) {
		printf ("Invalid ELF header in file %s\n", Name);
		free (*Ehdr);
    return EFI_VOLUME_CORRUPTED;
	}

	//
	// Check section headers
	//
	for (Index = 0; Index < (*Ehdr)->e_shnum; ++Index) {
		Offset = (*Ehdr)->e_shoff + Index * (*Ehdr)->e_shentsize;

		if (FileSize < (Offset + sizeof (*Shdr))) {
			printf ("ELF section header is outside file %s\n", Name);
			free (*Ehdr);
			return EFI_VOLUME_CORRUPTED;
		}

		Shdr = (Elf_Shdr *)((UINT8 *)(*Ehdr) + Offset);

		if ((Shdr->sh_type != SHT_NOBITS)
		  && ((FileSize < Shdr->sh_offset) || ((FileSize - Shdr->sh_offset) < Shdr->sh_size))) {
			printf ("ELF section %d points outside file %s\n", Index, Name);
			free (*Ehdr);
			return EFI_VOLUME_CORRUPTED;
		}

		if (Shdr->sh_link >= (*Ehdr)->e_shnum) {
			printf ("ELF %d-th section's sh_link is out of range\n", Index);
			free (*Ehdr);
			return EFI_VOLUME_CORRUPTED;
		}
	}

	return EFI_SUCCESS;
}

static
const char *
GetElfString (
	const Elf_Ehdr *Ehdr,
	unsigned int   section,
	size_t         Offset
  )
{
	const Elf_Shdr *Shdr;
	char           *last;

	//
	// Locate section header
	//
	if (section >= Ehdr->e_shnum) {
		printf ("Invalid ELF string section %d\n", section);
    return NULL;
	}
	Shdr = (Elf_Shdr *)((UINT8 *)Ehdr + Ehdr->e_shoff + section * Ehdr->e_shentsize);

	//
	// Sanity check section
	//
	if (Shdr->sh_type != SHT_STRTAB) {
		printf ("ELF section %d (type %d) is not a string table\n", section, Shdr->sh_type);
    return NULL;
	}

	last = (char *)((UINT8 *)Ehdr + Shdr->sh_offset + Shdr->sh_size - 1);
	if (*last != '\0') {
		printf ("ELF section %d is not NUL-terminated\n", section);
    return NULL;
	}

	//
	// Locate string
	//
	if (Offset >= Shdr->sh_size) {
		printf ("Invalid ELF string offset %zd in section %d\n", Offset, section);
    return NULL;
	}

	return (char *)((UINT8 *)Ehdr + Shdr->sh_offset + Offset);
}

static
PeSection *
ProcessSection (
	const Elf_Ehdr *Ehdr,
	const Elf_Shdr *Shdr,
	PeHeader       *PeH
  )
{
	PeSection  *PeS;
	const char *Name;
	UINTN      NameLength;
	UINT32     PeSectionSize;
	UINT32     CodeStart;
	UINT32     CodeEnd;
	UINT32     DataStart;
	UINT32     DataMid;
	UINT32     DataEnd;
	UINT32     Start;
	UINT32     End;
	UINT32     *PeSectionStart;
	UINT32     *PeSectionEnd;

	PeSectionSize = 0;

	Name = GetElfString (Ehdr, Ehdr->e_shstrndx, Shdr->sh_name);
	if (Name == NULL) {
		return NULL;
	}

	//
	// Extract current RVA limits from file header
	//
	CodeStart = PeH->Nt.BaseOfCode;
	CodeEnd   = CodeStart + PeH->Nt.SizeOfCode;

#if defined(EFI_TARGET32)
	DataStart = PeH->Nt.BaseOfData;
#elif defined(EFI_TARGET64)
	DataStart = CodeEnd;
#endif

	DataMid   = DataStart + PeH->Nt.SizeOfInitializedData;
	DataEnd   = DataMid + PeH->Nt.SizeOfUninitializedData;

	//
	// Allocate PE section
	//
	if (Shdr->sh_type == SHT_PROGBITS) {
		PeSectionSize = ALIGN_VALUE (Shdr->sh_size, PeH->Nt.FileAlignment);
	}

	PeS = calloc (1, sizeof (*PeS) + PeSectionSize);
	if (PeS == NULL) {
		printf ("Could not allocate memory for Pe section\n");
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
	PeS->PeShdr.VirtualAddress = Shdr->sh_addr;
	PeS->PeShdr.SizeOfRawData  = PeSectionSize;

	//
	// Fill in section characteristics and update RVA limits
	//
	if ((Shdr->sh_type == SHT_PROGBITS) && ((Shdr->sh_flags & SHF_EXECINSTR) != 0)) {
		//
		// .text section
		//
		PeSectionStart         = &CodeStart;
		PeSectionEnd           = &CodeEnd;
		PeS->PeShdr.Characteristics =
		  EFI_IMAGE_SCN_CNT_CODE | EFI_IMAGE_SCN_MEM_NOT_PAGED |
			EFI_IMAGE_SCN_MEM_EXECUTE | EFI_IMAGE_SCN_MEM_READ;
	} else if ((Shdr->sh_type == SHT_PROGBITS) && ((Shdr->sh_flags & SHF_WRITE) != 0)) {
		//
		// .data section
		//
		PeSectionStart         = &DataStart;
		PeSectionEnd           = &DataMid;
		PeS->PeShdr.Characteristics =
			EFI_IMAGE_SCN_CNT_INITIALIZED_DATA | EFI_IMAGE_SCN_MEM_NOT_PAGED |
			EFI_IMAGE_SCN_MEM_READ | EFI_IMAGE_SCN_MEM_WRITE;
	} else if (Shdr->sh_type == SHT_PROGBITS) {
		//
		// .rodata section
		//
		PeSectionStart         = &DataStart;
		PeSectionEnd           = &DataMid;
		PeS->PeShdr.Characteristics =
			EFI_IMAGE_SCN_CNT_INITIALIZED_DATA |
			EFI_IMAGE_SCN_MEM_NOT_PAGED | EFI_IMAGE_SCN_MEM_READ;
	} else if (Shdr->sh_type == SHT_NOBITS) {
		//
		// .bss section
		//
		PeSectionStart         = &DataMid;
		PeSectionEnd           = &DataEnd;
		PeS->PeShdr.Characteristics =
			EFI_IMAGE_SCN_CNT_UNINITIALIZED_DATA | EFI_IMAGE_SCN_MEM_NOT_PAGED |
			EFI_IMAGE_SCN_MEM_READ | EFI_IMAGE_SCN_MEM_WRITE;
	} else {
		printf ("Unrecognised characteristics for section %s\n", Name);
		free (PeS);
		return NULL;
	}

	if (Shdr->sh_type == SHT_PROGBITS) {
		memcpy (PeS->contents, (UINT8 *)Ehdr + Shdr->sh_offset, Shdr->sh_size);
	}

	//
	// Update RVA limits
	//
	Start = PeS->PeShdr.VirtualAddress;
	End   = Start + PeS->PeShdr.VirtualSize;
	if ( (*PeSectionStart == 0) || (*PeSectionStart >= Start)) {
		*PeSectionStart = Start;
	}

	if (*PeSectionEnd < End) {
		*PeSectionEnd = End;
	}

	if (DataStart < CodeEnd) {
		DataStart = CodeEnd;
	}

	if (DataMid < DataStart) {
		DataMid = DataStart;
	}

	if (DataEnd < DataMid) {
		DataEnd = DataMid;
	}

	//
	// Write RVA limits back to file header
	//
	PeH->Nt.BaseOfCode              = CodeStart;
	PeH->Nt.SizeOfCode              = CodeEnd - CodeStart;
#if defined(EFI_TARGET32)
	PeH->Nt.BaseOfData              = DataStart;
#endif
	PeH->Nt.SizeOfInitializedData   = DataMid - DataStart;
	PeH->Nt.SizeOfUninitializedData = DataEnd - DataMid;

	//
	// Update remaining file header fields
	//
	++PeH->Nt.CommonHeader.FileHeader.NumberOfSections;
	PeH->Nt.SizeOfHeaders += sizeof (PeS->PeShdr);
	PeH->Nt.SizeOfImage =	ALIGN_VALUE (DataEnd, PeH->Nt.SectionAlignment);

	return PeS;
}

static
EFI_STATUS
ProcessReloc (
	const Elf_Ehdr *Ehdr,
	const Elf_Shdr *Shdr,
	const Elf_Sym  *syms,
	unsigned int   nsyms,
	const Elf_Rel  *rel,
	PeRelocs       **PeRelTab
  )
{
	unsigned int type;
	unsigned int sym;
	unsigned int mrel;
	size_t       Offset;
	EFI_STATUS   Status;

	type   = ELF_R_TYPE (rel->r_info);
	sym    = ELF_R_SYM (rel->r_info);
	mrel   = ELF_MREL (Ehdr->e_machine, type);
	Offset = Shdr->sh_addr + rel->r_offset;

	//
	// Look up symbol and process relocation
	//
	if (sym >= nsyms) {
		printf ("Symbol out of range\n");
		return EFI_INVALID_PARAMETER;
	}

	if (syms[sym].st_shndx == SHN_ABS) {
		//
		// Skip absolute symbols;
		// the symbol value won't change when the object is loaded.
		//
		return EFI_SUCCESS;
	}

	switch (mrel) {
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
			/* Generate an 8-byte PE relocation */
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
			printf ("Unrecognised relocation type %d\n", type);
			return EFI_INVALID_PARAMETER;
	}

	return EFI_SUCCESS;
}

static
EFI_STATUS
ProcessRelocs (
	const Elf_Ehdr *Ehdr,
	const Elf_Shdr *Shdr,
	size_t         stride,
	PeRelocs       **PeRelTab
  )
{
	const Elf_Shdr *symtab;
	const Elf_Sym  *syms;
	const Elf_Rel  *rel;
	unsigned int   nsyms;
	unsigned int   nrels;
	unsigned int   i;
	EFI_STATUS     Status;

	//
	// Identify symbol table
	//
	symtab = (Elf_Shdr *)((UINT8 *)Ehdr + Ehdr->e_shoff + Shdr->sh_link * Ehdr->e_shentsize);
	syms   = (Elf_Sym *)((UINT8 *)Ehdr + symtab->sh_offset);
	nsyms  = symtab->sh_size / sizeof (syms[0]);

	//
	// Process each relocation
	//
	rel   = (Elf_Rel *)((UINT8 *)Ehdr + Shdr->sh_offset);
	nrels = Shdr->sh_size / stride;
	for (i = 0; i < nrels; ++i) {
		Status = ProcessReloc (Ehdr, Shdr, syms, nsyms, rel, PeRelTab);
		if (EFI_ERROR (Status)) {
			return Status;
		}

		rel = (const void * )rel + stride;
	}

	return EFI_SUCCESS;
}

static
PeSection *
CreateRelocSection (
	PeHeader *PeH,
	PeRelocs *PeRelTab
  )
{
	PeSection                *reloc;
	size_t                   section_memsz;
	size_t                   section_filesz;
	EFI_IMAGE_DATA_DIRECTORY *relocdir;

	//
	// Allocate PE section
	//
	section_memsz  = OutputPeReltab (PeRelTab, NULL);
	section_filesz = ALIGN_VALUE (section_memsz, EFI_FILE_ALIGN);
	reloc          = calloc (1, sizeof (*reloc) + section_filesz);
	if (reloc == NULL) {
		printf ("Could not allocate memory for reloc\n");
		return NULL;
	}

	//
	// Fill in section header details
	//
	strncpy ((char *)reloc->PeShdr.Name, ".reloc", sizeof (reloc->PeShdr.Name));
	reloc->PeShdr.VirtualSize     = section_memsz;
	reloc->PeShdr.VirtualAddress  = PeH->Nt.SizeOfImage;
	reloc->PeShdr.SizeOfRawData   = section_filesz;
	reloc->PeShdr.Characteristics =
	  EFI_IMAGE_SCN_CNT_INITIALIZED_DATA | EFI_IMAGE_SCN_MEM_DISCARDABLE |
		EFI_IMAGE_SCN_MEM_NOT_PAGED | EFI_IMAGE_SCN_MEM_READ;

	//
	// Copy section contents
	//
	OutputPeReltab (PeRelTab, reloc->contents);

	//
	// Update file header details
	//
	++PeH->Nt.CommonHeader.FileHeader.NumberOfSections;
	PeH->Nt.SizeOfHeaders += sizeof (reloc->PeShdr);
	PeH->Nt.SizeOfImage   += ALIGN_VALUE (section_memsz, EFI_IMAGE_ALIGN);

	relocdir = &PeH->Nt.DataDirectory[EFI_IMAGE_DIRECTORY_ENTRY_BASERELOC];

	relocdir->VirtualAddress = reloc->PeShdr.VirtualAddress;
	relocdir->Size           = section_memsz;

	return reloc;
}

static
void
FixupDebugSection (
	PeSection *debug
  )
{
	EFI_IMAGE_DEBUG_DIRECTORY_ENTRY *contents;

	contents = (void *)debug->contents;
	contents->FileOffset += debug->PeShdr.PointerToRawData - debug->PeShdr.VirtualAddress;
}

static
PeSection *
CreateDebugSection (
	PeHeader   *PeH,
	const char *filename
  )
{
	PeSection                *debug;
	size_t                   section_memsz;
	size_t                   section_filesz;
	EFI_IMAGE_DATA_DIRECTORY *debugdir;
	struct {
		EFI_IMAGE_DEBUG_DIRECTORY_ENTRY     debug;
		EFI_IMAGE_DEBUG_CODEVIEW_RSDS_ENTRY rsds;
		char                                name[strlen (filename) + 1];
	} *contents;

	//
	// Allocate PE section
	//
	section_memsz  = sizeof (*contents);
	section_filesz = ALIGN_VALUE (section_memsz, EFI_FILE_ALIGN);
	debug          = calloc (1, sizeof (*debug) + section_filesz);
	if (debug == NULL) {
		printf ("Could not allocate memory for debug\n");
		return NULL;
	}
	contents       = (void *)debug->contents;

	//
	// Fill in section header details
	//
	strncpy ((char *)debug->PeShdr.Name, ".debug", sizeof (debug->PeShdr.Name));

	debug->PeShdr.VirtualSize     = section_memsz;
	debug->PeShdr.VirtualAddress  = PeH->Nt.SizeOfImage;
	debug->PeShdr.SizeOfRawData   = section_filesz;
	debug->PeShdr.Characteristics =
	  EFI_IMAGE_SCN_CNT_INITIALIZED_DATA | EFI_IMAGE_SCN_MEM_DISCARDABLE |
		EFI_IMAGE_SCN_MEM_NOT_PAGED | EFI_IMAGE_SCN_MEM_READ;
	debug->fixup               = FixupDebugSection;

	//
	// Create section contents
	//
	contents->debug.TimeDateStamp = 0x10d1a884;
	contents->debug.Type          = EFI_IMAGE_DEBUG_TYPE_CODEVIEW;
	contents->debug.SizeOfData    = sizeof (*contents) - sizeof (contents->debug);
	contents->debug.RVA           = debug->PeShdr.VirtualAddress +	offsetof (typeof (*contents), rsds);
	contents->debug.FileOffset    = contents->debug.RVA;
	contents->rsds.Signature      = CODEVIEW_SIGNATURE_RSDS;
	snprintf (contents->name, sizeof (contents->name), "%s", filename);

	//
	// Update file header details
	//
	++PeH->Nt.CommonHeader.FileHeader.NumberOfSections;
	PeH->Nt.SizeOfHeaders += sizeof (debug->PeShdr);
	PeH->Nt.SizeOfImage   += ALIGN_VALUE (section_memsz, EFI_IMAGE_ALIGN);

	debugdir = &PeH->Nt.DataDirectory[EFI_IMAGE_DIRECTORY_ENTRY_DEBUG];

	debugdir->VirtualAddress = debug->PeShdr.VirtualAddress;
	debugdir->Size           = sizeof (contents->debug);

	return debug;
}

static
void
WritePeFile (
	PeHeader  *PeH,
  PeSection *PeSections,
	FILE      *pe
  )
{
	PeSection     *section;
	unsigned long fpos;

	PeH->Nt.SizeOfHeaders =	ALIGN_VALUE (PeH->Nt.SizeOfHeaders, EFI_FILE_ALIGN);
  fpos                        = PeH->Nt.SizeOfHeaders;

	//
	// Assign raw data pointers
	//
	for (section = PeSections; section != NULL; section = section->next) {
		if (section->PeShdr.SizeOfRawData != 0) {
			section->PeShdr.PointerToRawData = fpos;
			fpos                          += section->PeShdr.SizeOfRawData;
			fpos                          = ALIGN_VALUE (fpos, EFI_FILE_ALIGN);
		}

		if (section->fixup != NULL) {
			section->fixup (section);
		}
	}

	//
	// Write file header
	//
	if (fwrite (PeH, sizeof (*PeH), 1, pe) != 1) {
		printf ("Could not write PE header\n");
		return;
	}

	//
	// Write section headers
	//
	for (section = PeSections; section != NULL; section = section->next) {
		if (fwrite (&section->PeShdr, sizeof (section->PeShdr), 1, pe) != 1) {
			printf ("Could not write section header\n");
			return;
		}
	}

	//
	// Write sections
	//
	for (section = PeSections; section != NULL; section = section->next) {
		if (fseek (pe, section->PeShdr.PointerToRawData, SEEK_SET) != 0) {
			printf ("Could not seek to %x: %s\n", section->PeShdr.PointerToRawData, strerror (errno));
			return;
		}

		if ((section->PeShdr.SizeOfRawData != 0)
		  && (fwrite (section->contents, section->PeShdr.SizeOfRawData, 1, pe) != 1)) {
			printf ("Could not write section %.8s: %s\n", section->PeShdr.Name, strerror (errno));
			return;
		}
	}
}

static
const char *
BaseName (
	const char *Path
  )
{
	char *BaseName;

	BaseName = strrchr (Path, '/');
	return (BaseName != NULL) ? (BaseName + 1) : Path;
}

static
void
FreeSections (
	PeSection *PeSections
  )
{
	assert (PeSections != NULL);

	if (PeSections->next != NULL) {
		FreeSections (PeSections->next);
	}

	free (PeSections);
}

VOID
ElfToPe (
	const char *ElfName,
	const char *PeName
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

	PeRelTab      = NULL;
	PeSections    = NULL;
	NextPeSection = &PeSections;

	Status = ReadElfFile (ElfName, &Ehdr);
	if (EFI_ERROR (Status)) {
		return;
	}

	//
	// Initialise PE header
	//
	ZeroMem (&PeH, sizeof (PeH));
	PeH.Dos.e_magic               = EFI_IMAGE_DOS_SIGNATURE;
	PeH.Dos.e_lfanew              = sizeof (EFI_IMAGE_DOS_HEADER);
	PeH.Nt.CommonHeader.Signature = EFI_IMAGE_NT_SIGNATURE;
	//
  // Only base relocation and debug directory
	//
	PeH.Nt.NumberOfRvaAndSizes = 2;
	PeH.Nt.CommonHeader.FileHeader.SizeOfOptionalHeader =
	  sizeof (EFI_IMAGE_NT_HEADERS) - sizeof (EFI_IMAGE_NT_HEADERS_COMMON_HDR) +
		sizeof (EFI_IMAGE_DATA_DIRECTORY) * PeH.Nt.NumberOfRvaAndSizes;

	PeH.Nt.CommonHeader.FileHeader.Characteristics =
	  EFI_IMAGE_FILE_DLL | EFI_IMAGE_FILE_MACHINE | EFI_IMAGE_FILE_EXECUTABLE_IMAGE;

	PeH.Nt.Magic               = EFI_IMAGE_NT_OPTIONAL_HDR_MAGIC;
	PeH.Nt.SectionAlignment    = EFI_IMAGE_ALIGN;
	PeH.Nt.FileAlignment       = EFI_FILE_ALIGN;
	PeH.Nt.SizeOfHeaders       = sizeof (PeH) +
	  sizeof (EFI_IMAGE_DATA_DIRECTORY) * PeH.Nt.NumberOfRvaAndSizes;
	PeH.Nt.AddressOfEntryPoint = Ehdr->e_entry;
	PeH.Nt.Subsystem           = EFI_IMAGE_SUBSYSTEM_EFI_APPLICATION;

	switch (Ehdr->e_machine) {
		case EM_386:
			PeH.Nt.CommonHeader.FileHeader.Machine = EFI_IMAGE_MACHINE_IA32;
			break;
		case EM_X86_64:
			PeH.Nt.CommonHeader.FileHeader.Machine = EFI_IMAGE_MACHINE_X64;
			break;
		case EM_ARM:
			PeH.Nt.CommonHeader.FileHeader.Machine = EFI_IMAGE_MACHINE_ARMTHUMB_MIXED;
			break;
		case EM_AARCH64:
			PeH.Nt.CommonHeader.FileHeader.Machine = EFI_IMAGE_MACHINE_AARCH64;
			break;
		default:
			printf ("Unknown ELF architecture %d\n", Ehdr->e_machine);
			free (Ehdr);
			return;
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
				if (PeSections != NULL) {
					FreeSections (PeSections);
				}
				free (Ehdr);
				return;
			}

			NextPeSection = &(*NextPeSection)->next;
			continue;
		}

		if (Shdr->sh_type == SHT_REL) {
      //
			// Process .rel relocations
			//
			Status = ProcessRelocs (Ehdr, Shdr, sizeof (Elf_Rel), &PeRelTab);
			if (EFI_ERROR (Status)) {
				if (PeSections != NULL) {
					FreeSections (PeSections);
				}
				free (Ehdr);
				return;
			}

			continue;
		}

		if (Shdr->sh_type == SHT_RELA) {
      //
			// Process .rela relocations
			//
			Status = ProcessRelocs (Ehdr, Shdr, sizeof (Elf_Rela), &PeRelTab);
			if (EFI_ERROR (Status)) {
				if (PeSections != NULL) {
					FreeSections (PeSections);
				}
				free (Ehdr);
				return;
			}
		}
	}

	*(NextPeSection) = CreateRelocSection (&PeH, PeRelTab);
	NextPeSection    = &(*NextPeSection)->next;

	*(NextPeSection) = CreateDebugSection (&PeH, BaseName (PeName));
	NextPeSection    = &(*NextPeSection)->next;

	//
	// Write out PE file
	//
	Pe = fopen (PeName, "w");
	if (Pe == NULL) {
		printf ("Could not open %s for writing: %s\n", PeName, strerror (errno));
		FreeSections (PeSections);
		free (Ehdr);
		return;
	}

	WritePeFile (&PeH, PeSections, Pe);
	fclose (Pe);

	FreeSections (PeSections);
	free (Ehdr);
}
