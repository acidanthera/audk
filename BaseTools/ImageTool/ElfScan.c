/** @file
  Copyright (c) 2022, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause
**/

#include "ImageTool.h"

static Elf_Ehdr  *mEhdr         = NULL;
static Elf_Size  mPeAlignment   = 0x0;

#if defined(EFI_TARGET64)
// static UINT8           *mGotData      = NULL;
static UINT32          mWGotOffset    = 0x0;
static const Elf_Shdr  *mGOTShdr      = NULL;
static UINT32          *mGOTPeEntries = NULL;
static UINT32          mGOTMaxEntries = 0;
static UINT32          mGOTNumEntries = 0;
#endif

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

  for (Index = 0; Index < Shdr->sh_size; Index += (UINTN)Shdr->sh_entsize) {
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

#if defined(EFI_TARGET64)
RETURN_STATUS
FindElfGOTSectionFromGOTEntryElfRva (
  IN Elf_Addr GOTEntryElfRva
  )
{
  UINT32         Index;
  const Elf_Shdr *Shdr;

  if (mGOTShdr != NULL) {
    if ((GOTEntryElfRva >= mGOTShdr->sh_addr)
      && (GOTEntryElfRva < (mGOTShdr->sh_addr + mGOTShdr->sh_size))) {
      return RETURN_SUCCESS;
    }

    fprintf (stderr, "ImageTool: GOT entries found in multiple sections\n");
    return RETURN_UNSUPPORTED;
  }

  for (Index = 0; Index < mEhdr->e_shnum; ++Index) {
    Shdr = GetShdrByIndex(Index);
    if ((GOTEntryElfRva >= Shdr->sh_addr)
      && (GOTEntryElfRva < (Shdr->sh_addr + Shdr->sh_size))) {
      mGOTShdr = Shdr;
      // FindAddress (Index, &mGotData, &mWGotOffset);
      return RETURN_SUCCESS;
    }
  }

  fprintf (stderr, "ImageTool: ElfRva 0x%016llx for GOT entry not found in any section\n", GOTEntryElfRva);
  return RETURN_VOLUME_CORRUPTED;
}

RETURN_STATUS
AccumulatePeGOTEntries (
  IN  UINT32  GOTPeEntry,
  OUT BOOLEAN *IsNew
  )
{
  UINT32 Index;

  assert (IsNew != NULL);

  if (mGOTPeEntries != NULL) {
    for (Index = 0; Index < mGOTNumEntries; ++Index) {
      if (mGOTPeEntries[Index] == GOTPeEntry) {
        *IsNew = FALSE;
        return RETURN_SUCCESS;
      }
    }
  }

  if (mGOTPeEntries == NULL) {
    mGOTMaxEntries = 5;
    mGOTNumEntries = 0;
    mGOTPeEntries  = calloc (1, mGOTMaxEntries * sizeof (*mGOTPeEntries));
    if (mGOTPeEntries == NULL) {
      fprintf (stderr, "ImageTool: Could not allocate memory for mGOTPeEntries\n");
      return RETURN_OUT_OF_RESOURCES;
    }
  } else if (mGOTNumEntries == mGOTMaxEntries) {
    mGOTMaxEntries *= 2;
    mGOTPeEntries   = realloc (mGOTPeEntries, mGOTMaxEntries * sizeof (*mGOTPeEntries));
    if (mGOTPeEntries == NULL) {
      fprintf (stderr, "ImageTool: Could not reallocate memory for mGOTPeEntries\n");
      return RETURN_OUT_OF_RESOURCES;
    }
  }

  mGOTPeEntries[mGOTNumEntries] = mWGotOffset + GOTPeEntry;
  ++mGOTNumEntries;
  *IsNew = TRUE;

  return RETURN_SUCCESS;
}
#endif

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
  if (mEhdr->e_machine != EM_X86_64) {
    fprintf (stderr, "ImageTool: Unsupported ELF e_machine\n");
    return RETURN_UNSUPPORTED;
  }
#elif defined(EFI_TARGET32)
  if (mEhdr->e_machine != EM_386) {
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

static
RETURN_STATUS
FixSegmentsSetRelocs (
  VOID
  )
{
  UINT32         Index;
  const Elf_Shdr *RelShdr;
  const Elf_Shdr *SecShdr;
  UINTN          RelIdx;
  const Elf_Rela *Rel;
  const Elf_Sym  *Sym;
  UINT32         RelNum;
  UINTN          Offset;
#if defined(EFI_TARGET64)
  // Elf_Addr       GOTEntryRva;
  // RETURN_STATUS  Status;
  // BOOLEAN        IsNew;
#endif
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
    for (RelIdx = 0; RelIdx < RelShdr->sh_size; RelIdx += (UINTN)RelShdr->sh_entsize) {
      Rel    = (Elf_Rela *)((UINT8 *)mEhdr + RelShdr->sh_offset + RelIdx);
      Offset = (UINTN)Rel->r_offset;

      //
      // Set pointer to symbol table entry associated with the relocation entry.
      //
      Sym = GetSymbol (RelShdr->sh_link, ELF_R_SYM(Rel->r_info));
      if ((Sym->st_shndx == SHN_UNDEF) || (Sym->st_shndx >= mEhdr->e_shnum)) {
        continue;
      }

#if defined(EFI_TARGET64)
      switch (ELF_R_TYPE(Rel->r_info)) {
        case R_X86_64_NONE:
          break;
        case R_X86_64_64:

          mImageInfo.RelocInfo.Relocs[RelNum].Type   = EFI_IMAGE_REL_BASED_DIR64;
          mImageInfo.RelocInfo.Relocs[RelNum].Target = (uint32_t)Offset;
          ++RelNum;

          break;
        case R_X86_64_32:

          mImageInfo.RelocInfo.Relocs[RelNum].Type   = EFI_IMAGE_REL_BASED_HIGHLOW;
          mImageInfo.RelocInfo.Relocs[RelNum].Target = (uint32_t)Offset;
          ++RelNum;

          break;
        case R_X86_64_32S:
        case R_X86_64_PLT32:
        case R_X86_64_PC32:
          break;
        case R_X86_64_GOTPCREL:
        case R_X86_64_GOTPCRELX:
        case R_X86_64_REX_GOTPCRELX:
          // GOTEntryRva = Rel->r_offset - Rel->r_addend + *(INT32 *)Targ;
          //
          // Status = FindElfGOTSectionFromGOTEntryElfRva (GOTEntryRva);
          // if (RETURN_ERROR (Status)) {
          //   return Status;
          // }
          //
          // WriteUnaligned32 ((UINT32 *)Targ, (UINT32)(ReadUnaligned32((UINT32 *)Targ) + (mWGotOffset - mGOTShdr->sh_addr) - (WSecOffset - SecShdr->sh_addr)));
          // //
          // // ELF Rva -> Offset in PE GOT
          // //
          // GOTEntryRva -= mGOTShdr->sh_addr;
          //
          // Status = AccumulatePeGOTEntries ((UINT32)GOTEntryRva, &IsNew);
          // if (RETURN_ERROR (Status)) {
          //   return Status;
          // }
          //
          // if (IsNew) {
          //   //
          //   // Relocate GOT entry if it's the first time we run into it
          //   //
          //   Targ = mGotData + GOTEntryRva;
          //
          //   WriteUnaligned64 ((UINT64 *)Targ, ReadUnaligned64((UINT64 *)Targ) - SymShdr->sh_addr + WSymOffset);
          // }
          break;
        default:
          fprintf (stderr, "ImageTool: Unsupported ELF EM_X86_64 relocation 0x%llx\n", ELF_R_TYPE(Rel->r_info));
          return RETURN_UNSUPPORTED;
      }
#elif defined(EFI_TARGET32)
      switch (ELF_R_TYPE(Rel->r_info)) {
        case R_386_NONE:
          break;
        case R_386_32:

          mImageInfo.RelocInfo.Relocs[RelNum].Type   = EFI_IMAGE_REL_BASED_HIGHLOW;
          mImageInfo.RelocInfo.Relocs[RelNum].Target = Offset;
          ++RelNum;

          break;
        case R_386_PLT32:
        case R_386_PC32:
          break;
        default:
          fprintf (stderr, "ImageTool: Unsupported ELF EM_386 relocation 0x%x\n", ELF_R_TYPE(Rel->r_info));
          return RETURN_UNSUPPORTED;
      }
#endif
    }
  }

  assert (RelNum == mImageInfo.RelocInfo.NumRelocs);

  return RETURN_SUCCESS;
}

static
RETURN_STATUS
FixAddresses (
  VOID
  )
{
  RETURN_STATUS  Status;
#if defined(EFI_TARGET64)
  UINT32         Index;
  UINT32         NewSize;
#endif

  Status = FixSegmentsSetRelocs ();
  if (RETURN_ERROR (Status)) {
    return Status;
  }

#if defined(EFI_TARGET64)
  if (mGOTPeEntries != NULL) {
    NewSize = (mImageInfo.RelocInfo.NumRelocs + mGOTNumEntries) * sizeof (*mImageInfo.RelocInfo.Relocs);

    mImageInfo.RelocInfo.Relocs = realloc (mImageInfo.RelocInfo.Relocs, NewSize);
    if (mImageInfo.RelocInfo.Relocs == NULL) {
      fprintf (stderr, "ImageTool: Could not reallocate memory for Relocs\n");
      return RETURN_OUT_OF_RESOURCES;
    }

    for (Index = 0; Index < mGOTNumEntries; ++Index) {
      mImageInfo.RelocInfo.Relocs[mImageInfo.RelocInfo.NumRelocs + Index].Type   = EFI_IMAGE_REL_BASED_DIR64;
      mImageInfo.RelocInfo.Relocs[mImageInfo.RelocInfo.NumRelocs + Index].Target = mGOTPeEntries[Index];
    }
  }
#endif
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
  UINT64               Pointer;

  Segments = NULL;
  SIndex   = 0;
  Relocs   = NULL;

  for (Index = 0; Index < mEhdr->e_shnum; ++Index) {
    Shdr = GetShdrByIndex (Index);

    if ((IsTextShdr (Shdr)) || (IsDataShdr (Shdr)) || (IsHiiRsrcShdr (Shdr))) {
      if ((Shdr->sh_addralign == 0) || (Shdr->sh_addralign == 1)) {
        fprintf (stderr, "ImageTool: Alignment field is invalid\n");
        return RETURN_VOLUME_CORRUPTED;
      }

      if (!IS_ALIGNED(Shdr->sh_addr, Shdr->sh_addralign)) {
        fprintf (stderr, "ImageTool: Section address not aligned to its own alignment\n");
        return RETURN_VOLUME_CORRUPTED;
      }
    }

    if ((IsTextShdr (Shdr)) || (IsDataShdr (Shdr))) {
      ++mImageInfo.SegmentInfo.NumSegments;
    }

    if (IsRelocShdr (Shdr)) {
      for (RIndex = 0; RIndex < Shdr->sh_size; RIndex += (UINTN)Shdr->sh_entsize) {
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
    return RETURN_VOLUME_CORRUPTED;
  }

  Segments = calloc (1, sizeof (*Segments) * mImageInfo.SegmentInfo.NumSegments);
  if (Segments == NULL) {
    fprintf (stderr, "ImageTool: Could not allocate memory for Segments\n");
    return RETURN_OUT_OF_RESOURCES;
  };

  mImageInfo.SegmentInfo.Segments = Segments;

  if (mImageInfo.RelocInfo.NumRelocs != 0) {
    Relocs = calloc (1, sizeof (*Relocs) * mImageInfo.RelocInfo.NumRelocs);
    if (Relocs == NULL) {
      fprintf (stderr, "ImageTool: Could not allocate memory for Relocs\n");
      return RETURN_OUT_OF_RESOURCES;
    };

    mImageInfo.RelocInfo.Relocs = Relocs;
  }
  //
  // Assume 4K alignment, which must be enough for all PE headers.
  //
  Pointer = mPeAlignment;

  for (Index = 0; Index < mEhdr->e_shnum; ++Index) {
    Shdr = GetShdrByIndex (Index);

    if (IsTextShdr (Shdr)) {
      Name = GetString (Shdr->sh_name);
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

      Segments[SIndex].ImageAddress = Pointer;
      Segments[SIndex].ImageSize    = Segments[SIndex].DataSize;
      Segments[SIndex].Read         = true;
      Segments[SIndex].Write        = false;
      Segments[SIndex].Execute      = true;
      Segments[SIndex].Type         = ToolImageSectionTypeCode;
      Pointer                      += Segments[SIndex].DataSize;
      ++SIndex;
      continue;
    }

    if (IsDataShdr (Shdr)) {
      Name = GetString (Shdr->sh_name);
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

      Segments[SIndex].ImageAddress = Pointer;
      Segments[SIndex].ImageSize    = Segments[SIndex].DataSize;
      Segments[SIndex].Read         = true;
      Segments[SIndex].Write        = true;
      Segments[SIndex].Execute      = false;
      Segments[SIndex].Type         = ToolImageSectionTypeInitialisedData;
      Pointer                      += Segments[SIndex].DataSize;
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
        SetHiiResourceHeader (mImageInfo.HiiInfo.Data, (UINT32)Pointer);
        Pointer += mImageInfo.HiiInfo.DataSize;
      }
    }
  }

  assert (SIndex == mImageInfo.SegmentInfo.NumSegments);

  return FixAddresses();
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

#if defined(EFI_TARGET64)
  if (mGOTPeEntries != NULL) {
    free (mGOTPeEntries);
  }
#endif
  free (mEhdr);

  return Status;
}
