/** @file
  Copyright (c) 2022, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause
**/

#include "ImageTool.h"

static Elf_Ehdr  *mEhdr         = NULL;
static Elf_Size  mPeAlignment   = 0x0;
static UINT32    mSizeOfHeaders = 0x0;

extern image_tool_image_info_t mImageInfo;

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
char *
GetString (
  IN UINT32 Offset
  )
{
	const Elf_Shdr *Shdr;
	char           *String;

  Shdr = GetShdrByIndex (mEhdr->e_shstrndx);

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
BOOLEAN
IsRelocShdr (
  IN const Elf_Shdr *Shdr
  )
{
  const Elf_Shdr *SecShdr;
  const Elf_Rel  *Rel;
  UINTN          Index;

  assert (Shdr != NULL);

  if ((Shdr->sh_type != SHT_REL) && (Shdr->sh_type != SHT_RELA)) {
    return FALSE;
  }

  SecShdr = GetShdrByIndex (Shdr->sh_info);

  if ((!IsTextShdr (SecShdr)) && (!IsDataShdr (SecShdr))) {
    return FALSE;
  }

  for (Index = 0; Index < Shdr->sh_size; Index += Shdr->sh_entsize) {
    Rel = (Elf_Rel *)((UINT8 *)mEhdr + Shdr->sh_offset + Index);
#if defined(EFI_TARGET64)
    if ((ELF_R_TYPE(Rel->r_info) == R_X86_64_64)
      || (ELF_R_TYPE(Rel->r_info) == R_X86_64_32)) {
      return TRUE;
    }
#elif defined(EFI_TARGET32)
    if (ELF_R_TYPE(Rel->r_info) == R_386_32) {
      return TRUE;
    }
#endif
  }

  return FALSE;
}

static
VOID
FindAddress (
	IN  UINT32 ElfIndex,
  OUT UINT8  **SectionData,
  OUT UINT32 *WOffset
  )
{
  UINT32 Index;

  assert (SectionData != NULL);
  assert (WOffset     != NULL);

  *WOffset = mSizeOfHeaders;

  for (Index = 0; Index < mImageInfo.SegmentInfo.NumSegments; ++Index) {
    if (mImageInfo.SegmentInfo.Segments[Index].ImageSize == ElfIndex) {
      *SectionData = mImageInfo.SegmentInfo.Segments[Index].Data;
      break;
    }

    *WOffset += mImageInfo.SegmentInfo.Segments[Index].DataSize;
  }

	return;
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
    return EFI_VOLUME_CORRUPTED;
	}

  if ((mEhdr->e_type != ET_EXEC) && (mEhdr->e_type != ET_DYN)) {
    fprintf (stderr, "ImageTool: ELF e_type not ET_EXEC or ET_DYN\n");
    return EFI_UNSUPPORTED;
  }

#if defined(EFI_TARGET64)
  if (mEhdr->e_machine != EM_X86_64) {
    fprintf (stderr, "ImageTool: Unsupported ELF e_machine\n");
    return EFI_UNSUPPORTED;
  }
#elif defined(EFI_TARGET32)
  if (mEhdr->e_machine != EM_386) {
    fprintf (stderr, "ImageTool: Unsupported ELF e_machine\n");
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
			return EFI_VOLUME_CORRUPTED;
		}

		Shdr = (Elf_Shdr *)((UINT8 *)mEhdr + Offset);

		if ((Shdr->sh_type != SHT_NOBITS)
		  && ((FileSize < Shdr->sh_offset) || ((FileSize - Shdr->sh_offset) < Shdr->sh_size))) {
			fprintf (stderr, "ImageTool: ELF section %d points outside file %s\n", Index, Name);
			return EFI_VOLUME_CORRUPTED;
		}

		if (Shdr->sh_link >= mEhdr->e_shnum) {
			fprintf (stderr, "ImageTool: ELF %d-th section's sh_link is out of range\n", Index);
			return EFI_VOLUME_CORRUPTED;
		}

    if (((Shdr->sh_type == SHT_RELA) || (Shdr->sh_type == SHT_REL))
      && (Shdr->sh_info >= mEhdr->e_shnum)) {
			fprintf (stderr, "ImageTool: ELF %d-th section's sh_info is out of range\n", Index);
			return EFI_VOLUME_CORRUPTED;
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
    return EFI_VOLUME_CORRUPTED;
	}
  Shdr = GetShdrByIndex (mEhdr->e_shstrndx);

	if (Shdr->sh_type != SHT_STRTAB) {
		fprintf (stderr, "ImageTool: ELF string table section has wrong type\n");
    return EFI_VOLUME_CORRUPTED;
	}

	Last = (char *)((UINT8 *)mEhdr + Shdr->sh_offset + Shdr->sh_size - 1);
	if (*Last != '\0') {
		fprintf (stderr, "ImageTool: ELF string table section is not NUL-terminated\n");
    return EFI_VOLUME_CORRUPTED;
	}

	if ((!IS_POW2(mPeAlignment)) || (mPeAlignment > MAX_PE_ALIGNMENT)) {
    fprintf (stderr, "ImageTool: Invalid section alignment\n");
		return EFI_VOLUME_CORRUPTED;
  }

	return EFI_SUCCESS;
}

static
EFI_STATUS
FixSegmentsSetRelocs (
  VOID
  )
{
	UINT32         Index;
	const Elf_Shdr *RelShdr;
	const Elf_Shdr *SecShdr;
  UINT8          *SecData;
  UINT32         WSecOffset;
	UINTN          RelIdx;
	const Elf_Rela *Rel;
	const Elf_Sym  *Sym;
	const Elf_Shdr *SymShdr;
  UINT8          *SymData;
  UINT32         WSymOffset;
	UINT8          *Targ;
  UINT32         RelNum;
  UINTN          Offset;

  RelNum = 0;

	for (Index = 0; Index < mEhdr->e_shnum; Index++) {
    RelShdr = GetShdrByIndex (Index);

    if ((RelShdr->sh_type != SHT_REL) && (RelShdr->sh_type != SHT_RELA)) {
      continue;
    }

		if (RelShdr->sh_info == 0) {
			continue;
		}

    SecShdr = GetShdrByIndex (RelShdr->sh_info);
    FindAddress (RelShdr->sh_info, &SecData, &WSecOffset);

#if defined(EFI_TARGET64)
    if ((RelShdr->sh_type != SHT_RELA) || (!((IsTextShdr (SecShdr)) || (IsDataShdr (SecShdr))))) {
      continue;
    }
#elif defined(EFI_TARGET32)
    if ((RelShdr->sh_type != SHT_REL) || (!((IsTextShdr (SecShdr)) || (IsDataShdr (SecShdr))))) {
      continue;
    }
#endif

		//
		// Process all relocation entries for this section.
		//
		for (RelIdx = 0; RelIdx < RelShdr->sh_size; RelIdx += RelShdr->sh_entsize) {
			Rel = (Elf_Rela *)((UINT8 *)mEhdr + RelShdr->sh_offset + RelIdx);

      Offset = (Elf_Addr) WSecOffset + (Rel->r_offset - SecShdr->sh_addr);

			//
			// Set pointer to symbol table entry associated with the relocation entry.
			//
      Sym = GetSymbol (RelShdr->sh_link, ELF_R_SYM(Rel->r_info));
			if ((Sym->st_shndx == SHN_UNDEF) || (Sym->st_shndx >= mEhdr->e_shnum)) {
				continue;
			}

      SymShdr = GetShdrByIndex (Sym->st_shndx);
      FindAddress (Sym->st_shndx, &SymData, &WSymOffset);

			Targ = SecData + (Rel->r_offset - SecShdr->sh_addr);

#if defined(EFI_TARGET64)
			switch (ELF_R_TYPE(Rel->r_info)) {
				case R_X86_64_NONE:
					break;
				case R_X86_64_64:
					*(UINT64 *)Targ = *(UINT64 *)Targ - SymShdr->sh_addr + WSymOffset;

          mImageInfo.RelocInfo.Relocs[RelNum].Type   = EFI_IMAGE_REL_BASED_DIR64;
          mImageInfo.RelocInfo.Relocs[RelNum].Target = Offset;
          ++RelNum;

					break;
				case R_X86_64_32:
					*(UINT32 *)Targ = (UINT32)((UINT64)(*(UINT32 *)Targ) - SymShdr->sh_addr + WSymOffset);

          mImageInfo.RelocInfo.Relocs[RelNum].Type   = EFI_IMAGE_REL_BASED_HIGHLOW;
          mImageInfo.RelocInfo.Relocs[RelNum].Target = Offset;
          ++RelNum;

					break;
				case R_X86_64_32S:
					*(INT32 *)Targ = (INT32)((INT64)(*(INT32 *)Targ) - SymShdr->sh_addr + WSymOffset);
					break;
				case R_X86_64_PLT32:
				case R_X86_64_PC32:
          *(UINT32 *)Targ = (UINT32)(*(UINT32 *)Targ + (WSymOffset - WSecOffset) - (SymShdr->sh_addr - SecShdr->sh_addr));
					break;
				default:
					fprintf (stderr, "ImageTool: Unsupported ELF EM_X86_64 relocation 0x%llx\n", ELF_R_TYPE(Rel->r_info));
					return EFI_UNSUPPORTED;
			}
#elif defined(EFI_TARGET32)
      switch (ELF_R_TYPE(Rel->r_info)) {
        case R_386_NONE:
          break;
        case R_386_32:
          *(UINT32 *)Targ = *(UINT32 *)Targ - SymShdr->sh_addr + WSymOffset;

          mImageInfo.RelocInfo.Relocs[RelNum].Type   = EFI_IMAGE_REL_BASED_HIGHLOW;
          mImageInfo.RelocInfo.Relocs[RelNum].Target = Offset;
          ++RelNum;

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

  assert (RelNum == mImageInfo.RelocInfo.NumRelocs);

	return EFI_SUCCESS;
}

static
EFI_STATUS
FixAddresses (
  VOID
  )
{
  EFI_STATUS     Status;
  UINT32         Index;
  const Elf_Shdr *Shdr;
  UINT32         Pointer;

  mSizeOfHeaders = sizeof (EFI_IMAGE_DOS_HEADER) + sizeof (EFI_IMAGE_NT_HEADERS) +
    EFI_IMAGE_NUMBER_OF_DIRECTORY_ENTRIES * sizeof (EFI_IMAGE_DATA_DIRECTORY) +
    mImageInfo.SegmentInfo.NumSegments * sizeof (EFI_IMAGE_SECTION_HEADER);

  if (mImageInfo.RelocInfo.Relocs != NULL) {
    mSizeOfHeaders += sizeof (EFI_IMAGE_SECTION_HEADER);
  }

  if (mImageInfo.DebugInfo.SymbolsPath != NULL) {
    mSizeOfHeaders += sizeof (EFI_IMAGE_SECTION_HEADER);
  }

  if (mImageInfo.HiiInfo.Data != NULL) {
    mSizeOfHeaders += sizeof (EFI_IMAGE_SECTION_HEADER);
  }

  mSizeOfHeaders = ALIGN_VALUE (mSizeOfHeaders, mPeAlignment);

  Status = FixSegmentsSetRelocs ();
  if (EFI_ERROR (Status)) {
		return Status;
	}

  Pointer = mSizeOfHeaders;

  for (Index = 0; Index < mImageInfo.SegmentInfo.NumSegments; ++Index) {
    Shdr = GetShdrByIndex (mImageInfo.SegmentInfo.Segments[Index].ImageSize);

    if ((mEhdr->e_entry >= Shdr->sh_addr)
    && ((mEhdr->e_entry - Shdr->sh_addr) < Shdr->sh_size)) {
      mImageInfo.HeaderInfo.EntryPointAddress = Pointer + (mEhdr->e_entry - Shdr->sh_addr);
    }

    mImageInfo.SegmentInfo.Segments[Index].ImageAddress = Pointer;
    mImageInfo.SegmentInfo.Segments[Index].ImageSize    = mImageInfo.SegmentInfo.Segments[Index].DataSize;

    Pointer += mImageInfo.SegmentInfo.Segments[Index].DataSize;
  }

  if (mImageInfo.HiiInfo.Data != NULL) {
    SetHiiResourceHeader (mImageInfo.HiiInfo.Data, Pointer);
  }

  return EFI_SUCCESS;
}

static
EFI_STATUS
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

  Segments = NULL;
  SIndex   = 0;
  Relocs   = NULL;

  for (Index = 0; Index < mEhdr->e_shnum; ++Index) {
    Shdr = GetShdrByIndex (Index);

    if ((IsTextShdr (Shdr)) || (IsDataShdr (Shdr)) || (IsHiiRsrcShdr (Shdr))) {
      if ((Shdr->sh_addralign == 0) || (Shdr->sh_addralign == 1)) {
        fprintf (stderr, "ImageTool: Alignment field is invalid\n");
        return EFI_VOLUME_CORRUPTED;
      }

      if (!IS_ALIGNED(Shdr->sh_addr, Shdr->sh_addralign)) {
        fprintf (stderr, "ImageTool: Section address not aligned to its own alignment\n");
        return EFI_VOLUME_CORRUPTED;
      }
    }

    if ((IsTextShdr (Shdr)) || (IsDataShdr (Shdr))) {
      ++mImageInfo.SegmentInfo.NumSegments;
    }

    if (IsRelocShdr (Shdr)) {
      for (RIndex = 0; RIndex < Shdr->sh_size; RIndex += Shdr->sh_entsize) {
        Rel = (Elf_Rel *)((UINT8 *)mEhdr + Shdr->sh_offset + RIndex);
#if defined(EFI_TARGET64)
        if ((ELF_R_TYPE(Rel->r_info) == R_X86_64_64)
          || (ELF_R_TYPE(Rel->r_info) == R_X86_64_32)) {
          ++mImageInfo.RelocInfo.NumRelocs;
        }
#elif defined(EFI_TARGET32)
        if (ELF_R_TYPE(Rel->r_info) == R_386_32) {
          ++mImageInfo.RelocInfo.NumRelocs;
        }
#endif
      }
    }
	}

  if (mImageInfo.SegmentInfo.NumSegments == 0) {
    fprintf (stderr, "ImageTool: No .text or .data sections\n");
    return EFI_VOLUME_CORRUPTED;
  }

  Segments = calloc (1, sizeof (*Segments) * mImageInfo.SegmentInfo.NumSegments);
	if (Segments == NULL) {
		fprintf (stderr, "ImageTool: Could not allocate memory for Segments\n");
		return EFI_OUT_OF_RESOURCES;
	};

  mImageInfo.SegmentInfo.Segments = Segments;

  if (mImageInfo.RelocInfo.NumRelocs != 0) {
    Relocs = calloc (1, sizeof (*Relocs) * mImageInfo.RelocInfo.NumRelocs);
  	if (Relocs == NULL) {
  		fprintf (stderr, "ImageTool: Could not allocate memory for Relocs\n");
  		return EFI_OUT_OF_RESOURCES;
  	};

    mImageInfo.RelocInfo.Relocs = Relocs;
  }

  for (Index = 0; Index < mEhdr->e_shnum; ++Index) {
    Shdr = GetShdrByIndex (Index);

    if (IsTextShdr (Shdr)) {
      Name = GetString (Shdr->sh_name);
      if (Name == NULL) {
        return EFI_VOLUME_CORRUPTED;
      }

      Segments[SIndex].Name = calloc (1, strlen (Name) + 1);
      if (Segments[SIndex].Name == NULL) {
    		fprintf (stderr, "ImageTool: Could not allocate memory for Segment #%d Name\n", SIndex);
    		return EFI_OUT_OF_RESOURCES;
    	};

      memcpy (Segments[SIndex].Name, Name, strlen (Name));

      Segments[SIndex].DataSize = ALIGN_VALUE (Shdr->sh_size, mPeAlignment);

      Segments[SIndex].Data = calloc (1, Segments[SIndex].DataSize);
    	if (Segments[SIndex].Data == NULL) {
    		fprintf (stderr, "ImageTool: Could not allocate memory for Segment #%d Data\n", SIndex);
    		return EFI_OUT_OF_RESOURCES;
    	};

      memcpy (Segments[SIndex].Data, (UINT8 *)mEhdr + Shdr->sh_offset, Shdr->sh_size);

      Segments[SIndex].ImageAddress = 0;
      Segments[SIndex].ImageSize    = Index; // Will be needed by FindAddress()
      Segments[SIndex].Read         = true;
      Segments[SIndex].Write        = false;
      Segments[SIndex].Execute      = true;
      Segments[SIndex].Type         = ToolImageSectionTypeCode;
      ++SIndex;
      continue;
    }

    if (IsDataShdr (Shdr)) {
      Name = GetString (Shdr->sh_name);
      if (Name == NULL) {
        return EFI_VOLUME_CORRUPTED;
      }

      Segments[SIndex].Name = calloc (1, strlen (Name) + 1);
      if (Segments[SIndex].Name == NULL) {
    		fprintf (stderr, "ImageTool: Could not allocate memory for Segment #%d Name\n", SIndex);
    		return EFI_OUT_OF_RESOURCES;
    	};

      memcpy (Segments[SIndex].Name, Name, strlen (Name));

      Segments[SIndex].DataSize = ALIGN_VALUE (Shdr->sh_size, mPeAlignment);

      Segments[SIndex].Data = calloc (1, Segments[SIndex].DataSize);
    	if (Segments[SIndex].Data == NULL) {
    		fprintf (stderr, "ImageTool: Could not allocate memory for Segment #%d Data\n", SIndex);
    		return EFI_OUT_OF_RESOURCES;
    	};

      if (Shdr->sh_type == SHT_PROGBITS) {
        memcpy (Segments[SIndex].Data, (UINT8 *)mEhdr + Shdr->sh_offset, Shdr->sh_size);
      }

      Segments[SIndex].ImageAddress = 0;
      Segments[SIndex].ImageSize    = Index; // Will be needed by FindAddress()
      Segments[SIndex].Read         = true;
      Segments[SIndex].Write        = true;
      Segments[SIndex].Execute      = false;
      Segments[SIndex].Type         = ToolImageSectionTypeInitialisedData;
      ++SIndex;
      continue;
    }

    if (IsHiiRsrcShdr (Shdr)) {
      mImageInfo.HiiInfo.DataSize = ALIGN_VALUE (Shdr->sh_size, mPeAlignment);

      mImageInfo.HiiInfo.Data = calloc (1, mImageInfo.HiiInfo.DataSize);
    	if (mImageInfo.HiiInfo.Data == NULL) {
    		fprintf (stderr, "ImageTool: Could not allocate memory for Hii Data\n");
    		return EFI_OUT_OF_RESOURCES;
    	};

      if (Shdr->sh_type == SHT_PROGBITS) {
        memcpy (mImageInfo.HiiInfo.Data, (UINT8 *)mEhdr + Shdr->sh_offset, Shdr->sh_size);
      }
    }
	}

  assert (SIndex == mImageInfo.SegmentInfo.NumSegments);

  return FixAddresses();
}

EFI_STATUS
ElfToIntermediate (
	IN const char *ElfName,
  IN const char *ModuleType
  )
{
	EFI_STATUS Status;
  
  assert (ElfName    != NULL);
	assert (ModuleType != NULL);

	Status = ReadElfFile (ElfName);
	if (EFI_ERROR (Status)) {
    if (mEhdr != NULL) {
      free (mEhdr);
    }
		return Status;
	}

  memset (&mImageInfo, 0, sizeof (mImageInfo));

  mImageInfo.HeaderInfo.PreferredAddress  = 0;
  mImageInfo.HeaderInfo.EntryPointAddress = 0;
  mImageInfo.HeaderInfo.Machine           = mEhdr->e_machine;
  mImageInfo.HeaderInfo.IsXip             = true;
  mImageInfo.SegmentInfo.SegmentAlignment = mPeAlignment;
  mImageInfo.RelocInfo.RelocsStripped     = false;
  mImageInfo.DebugInfo.SymbolsPathLen     = strlen (ElfName) + 1;

  mImageInfo.DebugInfo.SymbolsPath = calloc (1, mImageInfo.DebugInfo.SymbolsPathLen);
  if (mImageInfo.DebugInfo.SymbolsPath == NULL) {
    fprintf (stderr, "ImageTool: Could not allocate memory for Debug Data\n");
    free (mEhdr);
    return EFI_OUT_OF_RESOURCES;
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
    return EFI_UNSUPPORTED;
  }

  Status = CreateIntermediate ();
  if (EFI_ERROR (Status)) {
    ToolImageDestruct (&mImageInfo);
	}

	free (mEhdr);

	return Status;
}
