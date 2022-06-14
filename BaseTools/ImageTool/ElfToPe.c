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
	PeRelocs      **pe_reltab,
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
	for (pe_rel = *pe_reltab; pe_rel != NULL; pe_rel = pe_rel->next) {
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

		pe_rel->next      = *pe_reltab;
		*pe_reltab        = pe_rel;
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
	PeRelocs *pe_reltab,
	void     *buffer
  )
{
	PeRelocs     *pe_rel;
	unsigned int num_relocs;
	size_t       size;
	size_t       total_size;

	total_size = 0;

	for (pe_rel = pe_reltab; pe_rel != NULL; pe_rel = pe_rel->next) {
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
	const char *name,
	Elf_Ehdr   **ehdr
  )
{
	static const unsigned char ident[] = {
		ELFMAG0, ELFMAG1, ELFMAG2, ELFMAG3, ELFCLASS, ELFDATA2LSB
	};
	const Elf_Shdr *shdr;
	size_t         offset;
	unsigned int   i;
	UINT32         len;

	*ehdr = (Elf_Ehdr *)UserReadFile (name, &len);
  if (*ehdr == NULL) {
		printf ("Could not open %s: %s\n", name, strerror (errno));
    return EFI_VOLUME_CORRUPTED;
  }

	//
	// Check header
	//
	if ((len < sizeof (**ehdr))
	  || (memcmp (ident, (*ehdr)->e_ident, sizeof (ident)) != 0)) {
		printf ("Invalid ELF header in file %s\n", name);
		free (*ehdr);
    return EFI_VOLUME_CORRUPTED;
	}

	//
	// Check section headers
	//
	for (i = 0; i < (*ehdr)->e_shnum; ++i) {
		offset = (*ehdr)->e_shoff + i * (*ehdr)->e_shentsize;

		if (len < (offset + sizeof (*shdr))) {
			printf ("ELF section header is outside file %s\n", name);
			free (*ehdr);
			return EFI_VOLUME_CORRUPTED;
		}

		shdr = (Elf_Shdr *)((UINT8 *)(*ehdr) + offset);

		if ((shdr->sh_type != SHT_NOBITS)
		  && ((len < shdr->sh_offset) || ((len - shdr->sh_offset) < shdr->sh_size))) {
			printf ("ELF section %d points outside file %s\n", i, name);
			free (*ehdr);
			return EFI_VOLUME_CORRUPTED;
		}

		if (shdr->sh_link >= (*ehdr)->e_shnum) {
			printf ("ELF %d-th section's sh_link is out of range\n", i);
			free (*ehdr);
			return EFI_VOLUME_CORRUPTED;
		}
	}

	return EFI_SUCCESS;
}

static
const char *
GetElfString (
	const Elf_Ehdr *ehdr,
	unsigned int   section,
	size_t         offset
  )
{
	const Elf_Shdr *shdr;
	char           *last;

	//
	// Locate section header
	//
	if (section >= ehdr->e_shnum) {
		printf ("Invalid ELF string section %d\n", section);
    return NULL;
	}
	shdr = (Elf_Shdr *)((UINT8 *)ehdr + ehdr->e_shoff + section * ehdr->e_shentsize);

	//
	// Sanity check section
	//
	if (shdr->sh_type != SHT_STRTAB) {
		printf ("ELF section %d (type %d) is not a string table\n", section, shdr->sh_type);
    return NULL;
	}

	last = (char *)((UINT8 *)ehdr + shdr->sh_offset + shdr->sh_size - 1);
	if (*last != '\0') {
		printf ("ELF section %d is not NUL-terminated\n", section);
    return NULL;
	}

	//
	// Locate string
	//
	if (offset >= shdr->sh_size) {
		printf ("Invalid ELF string offset %zd in section %d\n", offset, section);
    return NULL;
	}

	return (char *)((UINT8 *)ehdr + shdr->sh_offset + offset);
}

static
PeSection *
ProcessSection (
	const Elf_Ehdr *ehdr,
	const Elf_Shdr *shdr,
	PeHeader       *pe_header
  )
{
	PeSection     *new;
	const char    *name;
	size_t        name_len;
	size_t        section_memsz;
	size_t        section_filesz;
	unsigned long code_start;
	unsigned long code_end;
	unsigned long data_start;
	unsigned long data_mid;
	unsigned long data_end;
	unsigned long start;
	unsigned long end;
	unsigned long *applicable_start;
	unsigned long *applicable_end;

	name = GetElfString (ehdr, ehdr->e_shstrndx, shdr->sh_name);
	if (name == NULL) {
		return NULL;
	}

	//
	// Extract current RVA limits from file header
	//
	code_start = pe_header->nt.BaseOfCode;
	code_end   = code_start + pe_header->nt.SizeOfCode;
#if defined(EFI_TARGET32)
	data_start = pe_header->nt.BaseOfData;
#elif defined(EFI_TARGET64)
	data_start = code_end;
#endif
	data_mid   = data_start + pe_header->nt.SizeOfInitializedData;
	data_end   = data_mid + pe_header->nt.SizeOfUninitializedData;

	//
	// Allocate PE section
	//
	section_memsz  = shdr->sh_size;
	section_filesz = (shdr->sh_type == SHT_PROGBITS) ? ALIGN_VALUE (section_memsz, EFI_FILE_ALIGN) : 0;
	new            = calloc (1, sizeof (*new) + section_filesz);
	if (new == NULL) {
		printf ("Could not allocate memory for new\n");
		return NULL;
	}

	//
	// Fill in section header details
	//
	name_len = strlen (name);
	if (name_len > sizeof (new->hdr.Name)) {
		name_len = sizeof (new->hdr.Name);
	}
	memcpy (new->hdr.Name, name, name_len);

	new->hdr.VirtualSize    = section_memsz;
	new->hdr.VirtualAddress = shdr->sh_addr;
	new->hdr.SizeOfRawData  = section_filesz;

	//
	// Fill in section characteristics and update RVA limits
	//
	if ((shdr->sh_type == SHT_PROGBITS) && ((shdr->sh_flags & SHF_EXECINSTR) != 0)) {
		//
		// .text section
		//
		applicable_start         = &code_start;
		applicable_end           = &code_end;
		new->hdr.Characteristics =
		  EFI_IMAGE_SCN_CNT_CODE | EFI_IMAGE_SCN_MEM_NOT_PAGED |
			EFI_IMAGE_SCN_MEM_EXECUTE | EFI_IMAGE_SCN_MEM_READ;
	} else if ((shdr->sh_type == SHT_PROGBITS) && ((shdr->sh_flags & SHF_WRITE) != 0)) {
		//
		// .data section
		//
		applicable_start         = &data_start;
		applicable_end           = &data_mid;
		new->hdr.Characteristics =
			EFI_IMAGE_SCN_CNT_INITIALIZED_DATA | EFI_IMAGE_SCN_MEM_NOT_PAGED |
			EFI_IMAGE_SCN_MEM_READ | EFI_IMAGE_SCN_MEM_WRITE;
	} else if (shdr->sh_type == SHT_PROGBITS) {
		//
		// .rodata section
		//
		applicable_start         = &data_start;
		applicable_end           = &data_mid;
		new->hdr.Characteristics =
			EFI_IMAGE_SCN_CNT_INITIALIZED_DATA |
			EFI_IMAGE_SCN_MEM_NOT_PAGED | EFI_IMAGE_SCN_MEM_READ;
	} else if (shdr->sh_type == SHT_NOBITS) {
		//
		// .bss section
		//
		applicable_start         = &data_mid;
		applicable_end           = &data_end;
		new->hdr.Characteristics =
			EFI_IMAGE_SCN_CNT_UNINITIALIZED_DATA | EFI_IMAGE_SCN_MEM_NOT_PAGED |
			EFI_IMAGE_SCN_MEM_READ | EFI_IMAGE_SCN_MEM_WRITE;
	} else {
		printf ("Unrecognised characteristics for section %s\n", name);
		return NULL;
	}

	if (shdr->sh_type == SHT_PROGBITS) {
		memcpy (new->contents, (UINT8 *)ehdr + shdr->sh_offset, shdr->sh_size);
	}

	//
	// Update RVA limits
	//
	start = new->hdr.VirtualAddress;
	end   = start + new->hdr.VirtualSize;
	if ( (*applicable_start == 0) || (*applicable_start >= start)) {
		*applicable_start = start;
	}

	if (*applicable_end < end) {
		*applicable_end = end;
	}

	if (data_start < code_end) {
		data_start = code_end;
	}

	if (data_mid < data_start) {
		data_mid = data_start;
	}

	if (data_end < data_mid) {
		data_end = data_mid;
	}

	//
	// Write RVA limits back to file header
	//
	pe_header->nt.BaseOfCode              = code_start;
	pe_header->nt.SizeOfCode              = code_end - code_start;
#if defined(EFI_TARGET32)
	pe_header->nt.BaseOfData              = data_start;
#endif
	pe_header->nt.SizeOfInitializedData   = data_mid - data_start;
	pe_header->nt.SizeOfUninitializedData = data_end - data_mid;

	//
	// Update remaining file header fields
	//
	++pe_header->nt.CommonHeader.FileHeader.NumberOfSections;
	pe_header->nt.SizeOfHeaders += sizeof (new->hdr);
	pe_header->nt.SizeOfImage =	ALIGN_VALUE (data_end, EFI_IMAGE_ALIGN);

	return new;
}

static
EFI_STATUS
ProcessReloc (
	const Elf_Ehdr *ehdr,
	const Elf_Shdr *shdr,
	const Elf_Sym  *syms,
	unsigned int   nsyms,
	const Elf_Rel  *rel,
	PeRelocs       **pe_reltab
  )
{
	unsigned int type;
	unsigned int sym;
	unsigned int mrel;
	size_t       offset;
	EFI_STATUS   Status;

	type   = ELF_R_TYPE (rel->r_info);
	sym    = ELF_R_SYM (rel->r_info);
	mrel   = ELF_MREL (ehdr->e_machine, type);
	offset = shdr->sh_addr + rel->r_offset;

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
			Status = GeneratePeReloc (pe_reltab, offset, 4);
			if (EFI_ERROR (Status)) {
				return Status;
			}
			break;
		case ELF_MREL (EM_X86_64, R_X86_64_64) :
		case ELF_MREL (EM_AARCH64, R_AARCH64_ABS64) :
			/* Generate an 8-byte PE relocation */
			Status = GeneratePeReloc (pe_reltab, offset, 8);
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
	const Elf_Ehdr *ehdr,
	const Elf_Shdr *shdr,
	size_t         stride,
	PeRelocs       **pe_reltab
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
	symtab = (Elf_Shdr *)((UINT8 *)ehdr + ehdr->e_shoff + shdr->sh_link * ehdr->e_shentsize);
	syms   = (Elf_Sym *)((UINT8 *)ehdr + symtab->sh_offset);
	nsyms  = symtab->sh_size / sizeof (syms[0]);

	//
	// Process each relocation
	//
	rel   = (Elf_Rel *)((UINT8 *)ehdr + shdr->sh_offset);
	nrels = shdr->sh_size / stride;
	for (i = 0; i < nrels; ++i) {
		Status = ProcessReloc (ehdr, shdr, syms, nsyms, rel, pe_reltab);
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
	PeHeader *pe_header,
	PeRelocs *pe_reltab
  )
{
	PeSection                *reloc;
	size_t                   section_memsz;
	size_t                   section_filesz;
	EFI_IMAGE_DATA_DIRECTORY *relocdir;

	//
	// Allocate PE section
	//
	section_memsz  = OutputPeReltab (pe_reltab, NULL);
	section_filesz = ALIGN_VALUE (section_memsz, EFI_FILE_ALIGN);
	reloc          = calloc (1, sizeof (*reloc) + section_filesz);
	if (reloc == NULL) {
		printf ("Could not allocate memory for reloc\n");
		return NULL;
	}

	//
	// Fill in section header details
	//
	strncpy ((char *)reloc->hdr.Name, ".reloc", sizeof (reloc->hdr.Name));
	reloc->hdr.VirtualSize     = section_memsz;
	reloc->hdr.VirtualAddress  = pe_header->nt.SizeOfImage;
	reloc->hdr.SizeOfRawData   = section_filesz;
	reloc->hdr.Characteristics =
	  EFI_IMAGE_SCN_CNT_INITIALIZED_DATA | EFI_IMAGE_SCN_MEM_DISCARDABLE |
		EFI_IMAGE_SCN_MEM_NOT_PAGED | EFI_IMAGE_SCN_MEM_READ;

	//
	// Copy section contents
	//
	OutputPeReltab (pe_reltab, reloc->contents);

	//
	// Update file header details
	//
	++pe_header->nt.CommonHeader.FileHeader.NumberOfSections;
	pe_header->nt.SizeOfHeaders += sizeof (reloc->hdr);
	pe_header->nt.SizeOfImage   += ALIGN_VALUE (section_memsz, EFI_IMAGE_ALIGN);

	relocdir = &pe_header->nt.DataDirectory[EFI_IMAGE_DIRECTORY_ENTRY_BASERELOC];

	relocdir->VirtualAddress = reloc->hdr.VirtualAddress;
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
	contents->FileOffset += debug->hdr.PointerToRawData - debug->hdr.VirtualAddress;
}

static
PeSection *
CreateDebugSection (
	PeHeader   *pe_header,
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
	strncpy ((char *)debug->hdr.Name, ".debug", sizeof (debug->hdr.Name));

	debug->hdr.VirtualSize     = section_memsz;
	debug->hdr.VirtualAddress  = pe_header->nt.SizeOfImage;
	debug->hdr.SizeOfRawData   = section_filesz;
	debug->hdr.Characteristics =
	  EFI_IMAGE_SCN_CNT_INITIALIZED_DATA | EFI_IMAGE_SCN_MEM_DISCARDABLE |
		EFI_IMAGE_SCN_MEM_NOT_PAGED | EFI_IMAGE_SCN_MEM_READ;
	debug->fixup               = FixupDebugSection;

	//
	// Create section contents
	//
	contents->debug.TimeDateStamp = 0x10d1a884;
	contents->debug.Type          = EFI_IMAGE_DEBUG_TYPE_CODEVIEW;
	contents->debug.SizeOfData    = sizeof (*contents) - sizeof (contents->debug);
	contents->debug.RVA           = debug->hdr.VirtualAddress +	offsetof (typeof (*contents), rsds);
	contents->debug.FileOffset    = contents->debug.RVA;
	contents->rsds.Signature      = CODEVIEW_SIGNATURE_RSDS;
	snprintf (contents->name, sizeof (contents->name), "%s", filename);

	//
	// Update file header details
	//
	++pe_header->nt.CommonHeader.FileHeader.NumberOfSections;
	pe_header->nt.SizeOfHeaders += sizeof (debug->hdr);
	pe_header->nt.SizeOfImage   += ALIGN_VALUE (section_memsz, EFI_IMAGE_ALIGN);

	debugdir = &pe_header->nt.DataDirectory[EFI_IMAGE_DIRECTORY_ENTRY_DEBUG];

	debugdir->VirtualAddress = debug->hdr.VirtualAddress;
	debugdir->Size           = sizeof (contents->debug);

	return debug;
}

static
void
WritePeFile (
	PeHeader  *pe_header,
  PeSection *pe_sections,
	FILE      *pe
  )
{
	PeSection     *section;
	unsigned long fpos;

	pe_header->nt.SizeOfHeaders =	ALIGN_VALUE (pe_header->nt.SizeOfHeaders, EFI_FILE_ALIGN);
  fpos                        = pe_header->nt.SizeOfHeaders;

	//
	// Assign raw data pointers
	//
	for (section = pe_sections; section != NULL; section = section->next) {
		if (section->hdr.SizeOfRawData != 0) {
			section->hdr.PointerToRawData = fpos;
			fpos                          += section->hdr.SizeOfRawData;
			fpos                          = ALIGN_VALUE (fpos, EFI_FILE_ALIGN);
		}

		if (section->fixup != NULL) {
			section->fixup (section);
		}
	}

	//
	// Write file header
	//
	if (fwrite (pe_header, sizeof (*pe_header), 1, pe) != 1) {
		printf ("Could not write PE header\n");
		return;
	}

	//
	// Write section headers
	//
	for (section = pe_sections; section != NULL; section = section->next) {
		if (fwrite (&section->hdr, sizeof (section->hdr), 1, pe) != 1) {
			printf ("Could not write section header\n");
			return;
		}
	}

	//
	// Write sections
	//
	for (section = pe_sections; section != NULL; section = section->next) {
		if (fseek (pe, section->hdr.PointerToRawData, SEEK_SET) != 0) {
			printf ("Could not seek to %x: %s\n", section->hdr.PointerToRawData, strerror (errno));
			return;
		}

		if ((section->hdr.SizeOfRawData != 0)
		  && (fwrite (section->contents, section->hdr.SizeOfRawData, 1, pe) != 1)) {
			printf ("Could not write section %.8s: %s\n", section->hdr.Name, strerror (errno));
			return;
		}
	}
}

static
char *
basename (
	char *path
  )
{
	char *basename;

	basename = strrchr (path, '/');
	return (basename != NULL) ? (basename + 1) : path;
}

VOID
ElfToPe (
	const char *elf_name,
	const char *pe_name
  )
{
	char pe_name_tmp[strlen (pe_name) + 1];
	PeRelocs       *pe_reltab;
	PeSection      *pe_sections;
	PeSection      **next_pe_section;
	PeHeader       pe_header;
	Elf_Ehdr       *ehdr;
	const Elf_Shdr *shdr;
	size_t         offset;
	unsigned int   i;
	FILE           *pe;
	EFI_STATUS     Status;

	pe_reltab       = NULL;
	pe_sections     = NULL;
	next_pe_section = &pe_sections;

	memcpy (pe_name_tmp, pe_name, sizeof (pe_name_tmp));

	Status = ReadElfFile (elf_name, &ehdr);
	if (EFI_ERROR (Status)) {
		return;
	}

	//
	// Initialise the PE header
	//
	ZeroMem (&pe_header, sizeof (pe_header));
	pe_header.dos.e_magic  = EFI_IMAGE_DOS_SIGNATURE;
	pe_header.dos.e_lfanew = sizeof (EFI_IMAGE_DOS_HEADER);

	pe_header.nt.CommonHeader.Signature = EFI_IMAGE_NT_SIGNATURE;
	//
  // Only base relocation and debug directory
	//
	pe_header.nt.CommonHeader.FileHeader.SizeOfOptionalHeader =
	  sizeof (EFI_IMAGE_NT_HEADERS) - sizeof (EFI_IMAGE_NT_HEADERS_COMMON_HDR) + sizeof (EFI_IMAGE_DATA_DIRECTORY) * 2;

	pe_header.nt.CommonHeader.FileHeader.Characteristics =
	  EFI_IMAGE_FILE_DLL | EFI_IMAGE_FILE_MACHINE | EFI_IMAGE_FILE_EXECUTABLE_IMAGE;

	pe_header.nt.Magic               = EFI_IMAGE_NT_OPTIONAL_HDR_MAGIC;
	pe_header.nt.SectionAlignment    = EFI_IMAGE_ALIGN;
	pe_header.nt.FileAlignment       = EFI_FILE_ALIGN;
	pe_header.nt.SizeOfHeaders       = sizeof (pe_header) + sizeof (EFI_IMAGE_DATA_DIRECTORY) * 2;
	pe_header.nt.NumberOfRvaAndSizes = 2; // EFI_IMAGE_NUMBER_OF_DIRECTORY_ENTRIES ?

	pe_header.nt.AddressOfEntryPoint = ehdr->e_entry;
	pe_header.nt.Subsystem           = EFI_IMAGE_SUBSYSTEM_EFI_APPLICATION;
	switch (ehdr->e_machine) {
		case EM_386:
			pe_header.nt.CommonHeader.FileHeader.Machine = EFI_IMAGE_MACHINE_IA32;
			break;
		case EM_X86_64:
			pe_header.nt.CommonHeader.FileHeader.Machine = EFI_IMAGE_MACHINE_X64;
			break;
		case EM_ARM:
			pe_header.nt.CommonHeader.FileHeader.Machine = EFI_IMAGE_MACHINE_ARMTHUMB_MIXED;
			break;
		case EM_AARCH64:
			pe_header.nt.CommonHeader.FileHeader.Machine = EFI_IMAGE_MACHINE_AARCH64;
			break;
		default:
			printf ("Unknown ELF architecture %d\n", ehdr->e_machine);
			free (ehdr);
			return;
	}

	//
	// Process input sections
	//
	for (i = 0; i < ehdr->e_shnum; ++i) {
		offset = ehdr->e_shoff + i * ehdr->e_shentsize;
		shdr   = (Elf_Shdr *)((UINT8 *)ehdr + offset);

		//
		// Process section
		//
		if ((shdr->sh_flags & SHF_ALLOC) != 0) {
      //
			// Create output section
			//
			*next_pe_section = ProcessSection (ehdr, shdr, &pe_header);
			if (*next_pe_section == NULL) {
				free (ehdr);
				return;
			}

			next_pe_section    = &(*next_pe_section)->next;
		} else if (shdr->sh_type == SHT_REL) {
      //
			// Process .rel relocations
			//
			Status = ProcessRelocs (ehdr, shdr, sizeof (Elf_Rel), &pe_reltab);
			if (EFI_ERROR (Status)) {
				free (ehdr);
				return;
			}
		} else if (shdr->sh_type == SHT_RELA) {
      //
			// Process .rela relocations
			//
			Status = ProcessRelocs (ehdr, shdr, sizeof (Elf_Rela), &pe_reltab);
			if (EFI_ERROR (Status)) {
				free (ehdr);
				return;
			}
		}
	}

	*(next_pe_section) = CreateRelocSection (&pe_header, pe_reltab);
	next_pe_section    = &(*next_pe_section)->next;

	*(next_pe_section) = CreateDebugSection (&pe_header, basename (pe_name_tmp));
	next_pe_section    = &(*next_pe_section)->next;

	//
	// Write out PE file
	//
	pe = fopen (pe_name, "w");
	if (pe == NULL) {
		printf ("Could not open %s for writing: %s\n", pe_name, strerror (errno));
		free (ehdr);
		return;
	}

	WritePeFile (&pe_header, pe_sections, pe);
	fclose (pe);

	free (ehdr);
}
