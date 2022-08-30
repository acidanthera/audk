/** @file
  Copyright (c) 2022, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause
**/

#include "ImageTool.h"

static Elf_Ehdr  *mEhdr       = NULL;
static Elf_Size  mPeAlignment = 0x0;

static image_tool_image_info_t mImageInfo;

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

    mPeAlignment = Shdr->sh_addralign;
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
ApplyRelocs (
  VOID
  )
{
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
  UINT32               RelNum;

  Segments = NULL;
  SIndex   = 0;
  Relocs   = NULL;
  RelNum   = 0;

  for (Index = 0; Index < mEhdr->e_shnum; ++Index) {
    Shdr = GetShdrByIndex (Index);

    if ((Shdr->sh_addralign == 0) || (Shdr->sh_addralign == 1)) {
      fprintf (stderr, "ImageTool: Alignment field is invalid\n");
      return EFI_VOLUME_CORRUPTED;
    }

    if (!IS_ALIGNED(Shdr->sh_addr, Shdr->sh_addralign)) {
      fprintf (stderr, "ImageTool: Section address not aligned to its own alignment\n");
      return EFI_VOLUME_CORRUPTED;
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
      Segments[SIndex].Name     = ".text";
      Segments[SIndex].DataSize = ALIGN_VALUE (Shdr->sh_size, mPeAlignment);

      Segments[SIndex].Data = calloc (1, Segments[SIndex].DataSize);
    	if (Segments[SIndex].Data == NULL) {
    		fprintf (stderr, "ImageTool: Could not allocate memory for Segment #%d Data\n", SIndex);
    		return EFI_OUT_OF_RESOURCES;
    	};

      memcpy (Segments[SIndex].Data, (UINT8 *)mEhdr + Shdr->sh_offset, Shdr->sh_size);

      Segments[SIndex].ImageAddress = Shdr->sh_addr;
      Segments[SIndex].ImageSize    = Shdr->sh_size;
      Segments[SIndex].Read         = true;
      Segments[SIndex].Write        = false;
      Segments[SIndex].Execute      = true;
      Segments[SIndex].Type         = ToolImageSectionTypeCode;
      ++SIndex;
      continue;
    }

    if (IsDataShdr (Shdr)) {
      Segments[SIndex].Name = ".data";
      Segments[SIndex].DataSize = ALIGN_VALUE (Shdr->sh_size, mPeAlignment);

      Segments[SIndex].Data = calloc (1, Segments[SIndex].DataSize);
    	if (Segments[SIndex].Data == NULL) {
    		fprintf (stderr, "ImageTool: Could not allocate memory for Segment #%d Data\n", SIndex);
    		return EFI_OUT_OF_RESOURCES;
    	};

      if (Shdr->sh_type == SHT_PROGBITS) {
        memcpy (Segments[SIndex].Data, (UINT8 *)mEhdr + Shdr->sh_offset, Shdr->sh_size);
      }

      Segments[SIndex].ImageAddress = Shdr->sh_addr;
      Segments[SIndex].ImageSize    = Shdr->sh_size;
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

      continue;
    }

    if (IsRelocShdr (Shdr)) {
      for (RIndex = 0; RIndex < Shdr->sh_size; RIndex += Shdr->sh_entsize) {
        Rel = (Elf_Rel *)((UINT8 *)mEhdr + Shdr->sh_offset + RIndex);
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
            Relocs[RelNum].Type   = EFI_IMAGE_REL_BASED_DIR64;
            Relocs[RelNum].Target = Rel->r_offset;
            ++RelNum;
            break;
          case R_X86_64_32:
            Relocs[RelNum].Type   = EFI_IMAGE_REL_BASED_HIGHLOW;
            Relocs[RelNum].Target = Rel->r_offset;
            ++RelNum;
            break;
          default:
            fprintf (stderr, "ImageTool: Unrecognised relocation type %lld\n", ELF_R_TYPE (Rel->r_info));
            return EFI_INVALID_PARAMETER;
        }
#elif defined(EFI_TARGET32)
        switch (ELF_R_TYPE(Rel->r_info)) {
          case R_386_NONE:
          case R_386_PLT32:
          case R_386_PC32:
            break;
          case R_386_32:
            Relocs[RelNum].Type   = EFI_IMAGE_REL_BASED_HIGHLOW;
            Relocs[RelNum].Target = Rel->r_offset;
            ++RelNum;
            break;
          default:
            fprintf (stderr, "ImageTool: Unrecognised relocation type %d\n", ELF_R_TYPE (Rel->r_info));
            return EFI_INVALID_PARAMETER;
        }
#endif
      }
    }
	}

  assert (SIndex == mImageInfo.SegmentInfo.NumSegments);
  assert (RelNum == mImageInfo.RelocInfo.NumRelocs);

  mImageInfo.HeaderInfo.EntryPointAddress = mEhdr->e_entry;

  return ApplyRelocs();
}

EFI_STATUS
ElfToIntermediate (
	IN const char *ElfName,
  IN const char *ModuleType
  )
{
	EFI_STATUS Status;
  UINT32     SIndex;

  assert (ElfName    != NULL);
	assert (ModuleType != NULL);

	Status = ReadElfFile (ElfName);
	if (EFI_ERROR (Status)) {
    if (mEhdr != NULL) {
      free (mEhdr);
    }
		return Status;
	}

  memset (&mImageInfo, 0, sizeof(mImageInfo));

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
    if (mImageInfo.SegmentInfo.Segments != NULL) {
      for (SIndex = 0; SIndex < mImageInfo.SegmentInfo.NumSegments; ++SIndex) {
        if (mImageInfo.SegmentInfo.Segments[SIndex].Data != NULL) {
          free (mImageInfo.SegmentInfo.Segments[SIndex].Data);
        }
      }
      free (mImageInfo.SegmentInfo.Segments);
    }

    if (mImageInfo.HiiInfo.Data != NULL) {
      free (mImageInfo.HiiInfo.Data);
    }

    if (mImageInfo.RelocInfo.Relocs != NULL) {
      free (mImageInfo.RelocInfo.Relocs);
    }

    free (mImageInfo.DebugInfo.SymbolsPath);
	}

	free (mEhdr);

	return Status;
}
