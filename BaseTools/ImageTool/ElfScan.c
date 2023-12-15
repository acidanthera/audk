/** @file
  Copyright (c) 2022, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause
**/

#include "ImageTool.h"

#include "ElfScanCommon.h"

#include "../../UefiPayloadPkg/PayloadLoaderPeim/ElfLib/ElfCommon.h"

#if ELF_ARCH == 32

#include "../../UefiPayloadPkg/PayloadLoaderPeim/ElfLib/Elf32.h"

#define ELFCLASS    ELFCLASS32
#define Elf_Ehdr    Elf32_Ehdr
#define Elf_Shdr    Elf32_Shdr
#define Elf_Sym     Elf32_Sym
#define Elf_Rel     Elf32_Rel
#define Elf_Rela    Elf32_Rela
#define Elf_Size    Elf32_Size
#define Elf_Addr    Elf32_Addr
#define ELF_R_TYPE  ELF32_R_TYPE
#define ELF_R_SYM   ELF32_R_SYM

#elif ELF_ARCH == 64

#include "../../UefiPayloadPkg/PayloadLoaderPeim/ElfLib/Elf64.h"

#define ELFCLASS    ELFCLASS64
#define Elf_Ehdr    Elf64_Ehdr
#define Elf_Shdr    Elf64_Shdr
#define Elf_Sym     Elf64_Sym
#define Elf_Rel     Elf64_Rel
#define Elf_Rela    Elf64_Rela
#define Elf_Size    Elf64_Size
#define Elf_Addr    Elf64_Addr
#define ELF_R_TYPE  ELF64_R_TYPE
#define ELF_R_SYM   ELF64_R_SYM

#endif

#define ELF_SUFFIX__(Name, Arch)  Name##Arch
#define ELF_SUFFIX_(Name, Arch)   ELF_SUFFIX__ (Name, Arch)
#define ELF_SUFFIX(Name)          ELF_SUFFIX_ (Name, ELF_ARCH)

typedef struct {
  const Elf_Ehdr  *Ehdr;
  uint32_t        Alignment;
  Elf_Addr        BaseAddress;
  bool            HasPieRelocs;
} tool_elf_scan_context;


#define GetShrbyIndex  ELF_SUFFIX(GetShrbyIndex)
static
Elf_Shdr *
GetShdrByIndex (
  IN const Elf_Ehdr  *Ehdr,
  IN UINT32          Index
  )
{
  UINTN Offset;

  assert (Index < Ehdr->e_shnum);

  Offset = (UINTN)Ehdr->e_shoff + Index * Ehdr->e_shentsize;

  return (Elf_Shdr *)((UINT8 *)Ehdr + Offset);
}

#define GetString  ELF_SUFFIX(GetString)
static
const char *
GetString (
  IN const Elf_Ehdr  *Ehdr,
  IN UINT32          Offset,
  IN UINT32          Index
  )
{
  const Elf_Shdr *Shdr;

  if (Index == 0) {
    Shdr = GetShdrByIndex (Ehdr, Ehdr->e_shstrndx);
  } else {
    Shdr = GetShdrByIndex (Ehdr, Index);
  }

  if (Offset >= Shdr->sh_size) {
    fprintf (stderr, "ImageTool: Invalid ELF string offset\n");
    return NULL;
  }

  return (const char *)Ehdr + Shdr->sh_offset + Offset;
}

#define IsShdrLoadable  ELF_SUFFIX(IsShdrLoadable)
static
BOOLEAN
IsShdrLoadable (
  IN const Elf_Ehdr  *Ehdr,
  IN const Elf_Shdr  *Shdr
  )
{
  return (Shdr->sh_flags & SHF_ALLOC) != 0;
}

#define ParseElfFile  ELF_SUFFIX(ParseElfFile)
static
RETURN_STATUS
ParseElfFile (
  OUT tool_elf_scan_context  *Context,
  IN  const void             *File,
  IN  uint32_t               FileSize
  )
{
  static const unsigned char Ident[] = {
    ELFMAG0, ELFMAG1, ELFMAG2, ELFMAG3, ELFCLASS, ELFDATA2LSB
  };
  const Elf_Ehdr  *Ehdr;
  bool            AlignmentSet;
  Elf_Size        Alignment;
  bool            BaseAddressSet;
  Elf_Addr        BaseAddress;
  bool            HasPieRelocs;
  const Elf_Shdr  *Shdr;
  UINTN           Offset;
  UINT32          Index;
  char            *Last;

  assert (File != NULL || FileSize == 0);

  Ehdr = (const Elf_Ehdr *)File;

  //
  // Check header
  //
  if ((FileSize < sizeof (*Ehdr))
    || (memcmp (Ident, Ehdr->e_ident, sizeof (Ident)) != 0)) {
    return RETURN_UNSUPPORTED;
  }

  if ((Ehdr->e_type != ET_EXEC) && (Ehdr->e_type != ET_DYN)) {
    fprintf (stderr, "ImageTool: ELF e_type not ET_EXEC or ET_DYN\n");
    return RETURN_INCOMPATIBLE_VERSION;
  }

  //
  // Check section headers
  //
  BaseAddressSet = false;
  BaseAddress    = 0;
  Alignment      = 0;
  AlignmentSet   = false;
  HasPieRelocs   = false;
  for (Index = 0; Index < Ehdr->e_shnum; ++Index) {
    Offset = (UINTN)Ehdr->e_shoff + Index * Ehdr->e_shentsize;

    if (FileSize < (Offset + sizeof (*Shdr))) {
      fprintf (stderr, "ImageTool: ELF section header is outside file\n");
      return RETURN_VOLUME_CORRUPTED;
    }

    Shdr = (const Elf_Shdr *)((const char *)Ehdr + Offset);

    if ((Shdr->sh_type != SHT_NOBITS)
      && ((FileSize < Shdr->sh_offset) || ((FileSize - Shdr->sh_offset) < Shdr->sh_size))) {
      fprintf (stderr, "ImageTool: ELF section %d points outside file\n", Index);
      return RETURN_VOLUME_CORRUPTED;
    }

    if (Shdr->sh_link >= Ehdr->e_shnum) {
      fprintf (stderr, "ImageTool: ELF %d-th section's sh_link is out of range\n", Index);
      return RETURN_VOLUME_CORRUPTED;
    }

    if ((Shdr->sh_type == SHT_RELA) || (Shdr->sh_type == SHT_REL)) {
      if (Shdr->sh_info >= Ehdr->e_shnum) {
        fprintf (stderr, "ImageTool: ELF %d-th section's sh_info is out of range\n", Index);
        return RETURN_VOLUME_CORRUPTED;
      }

      if (Shdr->sh_info == 0) {
        HasPieRelocs = TRUE;
      }
    }

    if (!BaseAddressSet || Shdr->sh_addr < BaseAddress) {
      BaseAddressSet = TRUE;
      BaseAddress    = Shdr->sh_addr;
    }

    if (!IsShdrLoadable (Ehdr, Shdr)) {
      continue;
    }

    if (!AlignmentSet || Alignment < Shdr->sh_addralign) {
      AlignmentSet = TRUE;
      Alignment    = Shdr->sh_addralign;
    }
  }

  if (Ehdr->e_shstrndx >= Ehdr->e_shnum) {
    fprintf (stderr, "ImageTool: Invalid section name string table\n");
    return RETURN_VOLUME_CORRUPTED;
  }
  Shdr = GetShdrByIndex (Ehdr, Ehdr->e_shstrndx);

  if (Shdr->sh_type != SHT_STRTAB) {
    fprintf (stderr, "ImageTool: ELF string table section has wrong type\n");
    return RETURN_VOLUME_CORRUPTED;
  }

  Last = (char *)((UINT8 *)Ehdr + Shdr->sh_offset + Shdr->sh_size - 1);
  if (*Last != '\0') {
    fprintf (stderr, "ImageTool: ELF string table section is not NUL-terminated\n");
    return RETURN_VOLUME_CORRUPTED;
  }

  if (!AlignmentSet || (!IS_POW2(Alignment)) || (Alignment > MAX_PE_ALIGNMENT)) {
    fprintf (stderr, "ImageTool: Invalid section alignment\n");
    return RETURN_VOLUME_CORRUPTED;
  }

  if (!BaseAddressSet || !IS_ALIGNED (BaseAddress, Alignment)) {
    fprintf (stderr, "ImageTool: Invalid base address %llx\n", (unsigned long long)BaseAddress);
    return RETURN_VOLUME_CORRUPTED;
  }

  memset (Context, 0, sizeof (*Context));

  Context->Ehdr         = Ehdr;
  Context->Alignment    = (uint32_t)Alignment;
  Context->BaseAddress  = BaseAddress;
  Context->HasPieRelocs = HasPieRelocs;

  return RETURN_SUCCESS;
}

#define ProcessRelocSection  ELF_SUFFIX(ProcessRelocSection)
static
bool
ProcessRelocSection (
  const tool_elf_scan_context  *Context,
  const Elf_Shdr               *Shdr
  )
{
  const Elf_Ehdr  *Ehdr;
  bool            HasPieRelocs;
  const Elf_Shdr  *SecShdr;

  Ehdr         = Context->Ehdr;
  HasPieRelocs = Context->HasPieRelocs;
  //
  // PIE relocations will target dummy section 0.
  //
  if (Shdr->sh_info != 0) {
    //
    // If PIE relocations exist, prefer them.
    //
    if (HasPieRelocs) {
      return FALSE;
    }
    //
    // Only translate relocations targetting sections that are translated.
    //
    SecShdr = GetShdrByIndex (Ehdr, Shdr->sh_info);

    if (!IsShdrLoadable (Ehdr, SecShdr)) {
      return FALSE;
    }
  } else {
    assert (HasPieRelocs);
  }

  return TRUE;
}

#define SetRelocs  ELF_SUFFIX(SetRelocs)
static
RETURN_STATUS
SetRelocs (
  OUT image_tool_image_info_t      *ImageInfo,
  IN  const tool_elf_scan_context  *Context
  )
{
  const Elf_Ehdr  *Ehdr;
  Elf_Addr        BaseAddress;
  UINT32          Index;
  const Elf_Shdr  *RelShdr;
  UINTN           RelIdx;
  const Elf_Rela  *Rel;
  UINT32          RelNum;

  Ehdr        = Context->Ehdr;
  BaseAddress = Context->BaseAddress;

  RelNum = 0;

  for (Index = 0; Index < Ehdr->e_shnum; Index++) {
    RelShdr = GetShdrByIndex (Ehdr, Index);

    if ((RelShdr->sh_type != SHT_REL) && (RelShdr->sh_type != SHT_RELA)) {
      continue;
    }

    if (!ProcessRelocSection (Context, RelShdr)) {
      continue;
    }

    for (RelIdx = 0; RelIdx < RelShdr->sh_size; RelIdx += (UINTN)RelShdr->sh_entsize) {
      Rel = (const Elf_Rela *)((const char *)Ehdr + RelShdr->sh_offset + RelIdx);
      //
      // Assume ELF virtual addresses match corresponding PE virtual adresses one to one,
      // so we don't need to recalculate relocations computed by the linker at all r_offset's.
      // We only need to transform ELF relocations' format into PE one.
      //
#if ELF_ARCH == 64
      if (Ehdr->e_machine == EM_X86_64) {
        switch (ELF_R_TYPE(Rel->r_info)) {
          case R_X86_64_NONE:
            break;
          case R_X86_64_RELATIVE:
          case R_X86_64_64:
            ImageInfo->RelocInfo.Relocs[RelNum].Type   = EFI_IMAGE_REL_BASED_DIR64;
            ImageInfo->RelocInfo.Relocs[RelNum].Target = (uint32_t)(Rel->r_offset - BaseAddress);
            ++RelNum;

            break;
          case R_X86_64_32:

            ImageInfo->RelocInfo.Relocs[RelNum].Type   = EFI_IMAGE_REL_BASED_HIGHLOW;
            ImageInfo->RelocInfo.Relocs[RelNum].Target = (uint32_t)(Rel->r_offset - BaseAddress);
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
            fprintf (
              stderr,
              "ImageTool: Unsupported ELF EM_X86_64 relocation 0x%llx in %s\n",
              (unsigned long long)ELF_R_TYPE(Rel->r_info),
              ImageInfo->DebugInfo.SymbolsPath
              );
            return RETURN_INCOMPATIBLE_VERSION;
        }
      } else if (Ehdr->e_machine == EM_AARCH64) {
        switch (ELF_R_TYPE(Rel->r_info)) {
          case R_AARCH64_NONE0:
          case R_AARCH64_NONE:
          case R_AARCH64_LD64_GOTOFF_LO15:
          case R_AARCH64_LD64_GOTPAGE_LO15:
          case R_AARCH64_LD64_GOT_LO12_NC:
          case R_AARCH64_ADR_GOT_PAGE:
          case R_AARCH64_ADR_PREL_PG_HI21:
          case R_AARCH64_ADD_ABS_LO12_NC:
          case R_AARCH64_LDST8_ABS_LO12_NC:
          case R_AARCH64_LDST16_ABS_LO12_NC:
          case R_AARCH64_LDST32_ABS_LO12_NC:
          case R_AARCH64_LDST64_ABS_LO12_NC:
          case R_AARCH64_LDST128_ABS_LO12_NC:
          case R_AARCH64_ADR_PREL_LO21:
          case R_AARCH64_CONDBR19:
          case R_AARCH64_LD_PREL_LO19:
          case R_AARCH64_CALL26:
          case R_AARCH64_JUMP26:
          case R_AARCH64_PREL64:
          case R_AARCH64_PREL32:
          case R_AARCH64_PREL16:
            break;
          case R_AARCH64_ABS64:
          case R_AARCH64_RELATIVE:
            ImageInfo->RelocInfo.Relocs[RelNum].Type   = EFI_IMAGE_REL_BASED_DIR64;
            ImageInfo->RelocInfo.Relocs[RelNum].Target = (uint32_t)(Rel->r_offset - BaseAddress);
            ++RelNum;

            break;
          case R_AARCH64_ABS32:

            ImageInfo->RelocInfo.Relocs[RelNum].Type   = EFI_IMAGE_REL_BASED_HIGHLOW;
            ImageInfo->RelocInfo.Relocs[RelNum].Target = (uint32_t)(Rel->r_offset - BaseAddress);
            ++RelNum;

            break;
          default:
            fprintf (
              stderr,
              "ImageTool: Unsupported ELF EM_AARCH64 relocation 0x%llx in %s\n",
              (unsigned long long)ELF_R_TYPE(Rel->r_info),
              ImageInfo->DebugInfo.SymbolsPath
              );
            return RETURN_INCOMPATIBLE_VERSION;
        }
      }
#elif ELF_ARCH == 32
      if (Ehdr->e_machine == EM_386) {
        switch (ELF_R_TYPE(Rel->r_info)) {
          case R_386_NONE:
            break;
          case R_386_32:

            ImageInfo->RelocInfo.Relocs[RelNum].Type   = EFI_IMAGE_REL_BASED_HIGHLOW;
            ImageInfo->RelocInfo.Relocs[RelNum].Target = (Rel->r_offset - BaseAddress);
            ++RelNum;

            break;
          case R_386_PLT32:
          case R_386_PC32:
            break;
          default:
            fprintf (stderr, "ImageTool: Unsupported ELF EM_386 relocation 0x%x in %s\n", ELF_R_TYPE(Rel->r_info), ImageInfo->DebugInfo.SymbolsPath);
            return RETURN_INCOMPATIBLE_VERSION;
        }
      } else if (Ehdr->e_machine == EM_ARM) {
        switch (ELF32_R_TYPE(Rel->r_info)) {
          case R_ARM_NONE:
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
            break;
          case R_ARM_ABS32:

            ImageInfo->RelocInfo.Relocs[RelNum].Type   = EFI_IMAGE_REL_BASED_HIGHLOW;
            ImageInfo->RelocInfo.Relocs[RelNum].Target = (Rel->r_offset - BaseAddress);
            ++RelNum;

            break;
          default:
            fprintf (stderr, "ImageTool: Unsupported ELF EM_ARM relocation 0x%x in %s\n", ELF_R_TYPE(Rel->r_info), ImageInfo->DebugInfo.SymbolsPath);
            return RETURN_INCOMPATIBLE_VERSION;
        }
      }
#endif
    }
  }

  ImageInfo->RelocInfo.NumRelocs = RelNum;

  return RETURN_SUCCESS;
}

#define CreateIntermediate  ELF_SUFFIX(CreateIntermediate)
static
RETURN_STATUS
CreateIntermediate (
  OUT image_tool_image_info_t      *ImageInfo,
  IN  const tool_elf_scan_context  *Context
  )
{
  const Elf_Ehdr       *Ehdr;
  Elf_Addr             BaseAddress;
  const Elf_Shdr       *Shdr;
  UINT32               Index;
  image_tool_segment_t *Segments;
  image_tool_reloc_t   *Relocs;
  UINT32               SIndex;
  const Elf_Rel        *Rel;
  UINTN                RIndex;
  const char           *Name;
  UINT32               NumRelocs;

  Ehdr        = Context->Ehdr;
  BaseAddress = Context->BaseAddress;

  Segments  = NULL;
  SIndex    = 0;
  Relocs    = NULL;
  NumRelocs = 0;

  for (Index = 0; Index < Ehdr->e_shnum; ++Index) {
    Shdr = GetShdrByIndex (Ehdr, Index);

    if ((Shdr->sh_type == SHT_REL) || (Shdr->sh_type == SHT_RELA)) {
      if ((Shdr->sh_flags & SHF_ALLOC) != 0) {
        fprintf (stderr, "ImageTool: Loadable reloc sections are unsupported\n");
        return RETURN_VOLUME_CORRUPTED;
      }

      if (!ProcessRelocSection (Context, Shdr)) {
        continue;
      }

      for (RIndex = 0; RIndex < Shdr->sh_size; RIndex += (UINTN)Shdr->sh_entsize) {
        Rel = (Elf_Rel *)((UINT8 *)Ehdr + Shdr->sh_offset + RIndex);
#if ELF_ARCH == 64
        if (Ehdr->e_machine == EM_X86_64) {
          if ((ELF_R_TYPE(Rel->r_info) == R_X86_64_RELATIVE)
            || (ELF_R_TYPE(Rel->r_info) == R_X86_64_64)
            || (ELF_R_TYPE(Rel->r_info) == R_X86_64_32)
            || (ELF_R_TYPE(Rel->r_info) == R_X86_64_GOTPCREL)
            || (ELF_R_TYPE(Rel->r_info) == R_X86_64_GOTPCRELX)
            || (ELF_R_TYPE(Rel->r_info) == R_X86_64_REX_GOTPCRELX)) {
            ++NumRelocs;
          }
        } else if (Ehdr->e_machine == EM_AARCH64) {
          if ((ELF_R_TYPE(Rel->r_info) == R_AARCH64_ABS64)
            || (ELF_R_TYPE(Rel->r_info) == R_AARCH64_RELATIVE)
            || (ELF_R_TYPE(Rel->r_info) == R_AARCH64_ABS32)) {
            ++NumRelocs;
          }
        }
#elif ELF_ARCH == 32
        if (Ehdr->e_machine == EM_386) {
          if (ELF_R_TYPE(Rel->r_info) == R_386_32) {
            ++NumRelocs;
          }
        } else if (Ehdr->e_machine == EM_ARM) {
          if (ELF_R_TYPE(Rel->r_info) == R_ARM_ABS32) {
            ++NumRelocs;
          }
        }
#endif
      }
    }

    if (!IsShdrLoadable (Ehdr, Shdr)) {
      continue;
    }

    ++ImageInfo->SegmentInfo.NumSegments;
  }

  if (ImageInfo->SegmentInfo.NumSegments == 0) {
    fprintf (stderr, "ImageTool: No loadable sections\n");
    return RETURN_VOLUME_CORRUPTED;
  }

  Segments = AllocateZeroPool (sizeof (*Segments) * ImageInfo->SegmentInfo.NumSegments);
  if (Segments == NULL) {
    fprintf (stderr, "ImageTool: Could not allocate memory for Segments\n");
    return RETURN_OUT_OF_RESOURCES;
  };

  ImageInfo->SegmentInfo.Segments = Segments;

  if (NumRelocs != 0) {
    Relocs = AllocateZeroPool (sizeof (*Relocs) * NumRelocs);
    if (Relocs == NULL) {
      fprintf (stderr, "ImageTool: Could not allocate memory for Relocs\n");
      return RETURN_OUT_OF_RESOURCES;
    };

    ImageInfo->RelocInfo.Relocs = Relocs;
  }

  for (Index = 0; Index < Ehdr->e_shnum; ++Index) {
    Shdr = GetShdrByIndex (Ehdr, Index);

    if ((Shdr->sh_flags & SHF_ALLOC) == 0) {
      continue;
    }

    if (Shdr->sh_type != SHT_PROGBITS && Shdr->sh_type != SHT_NOBITS) {
      fprintf (stderr, "ImageTool: Segment #%d type %x unsupported\n", Index, Shdr->sh_type);
      return RETURN_VOLUME_CORRUPTED;
    }

    Name = GetString (Ehdr, Shdr->sh_name, 0);
    if (Name == NULL) {
      return RETURN_VOLUME_CORRUPTED;
    }

    Segments[SIndex].Name = AllocateZeroPool (strlen (Name) + 1);
    if (Segments[SIndex].Name == NULL) {
      fprintf (stderr, "ImageTool: Could not allocate memory for Segment #%d Name\n", Index);
      return RETURN_OUT_OF_RESOURCES;
    };

    memcpy (Segments[SIndex].Name, Name, strlen (Name));

    Segments[SIndex].ImageAddress = (uint32_t)(Shdr->sh_addr - BaseAddress);
    Segments[SIndex].ImageSize    = ALIGN_VALUE ((uint32_t)Shdr->sh_size, Context->Alignment);
    Segments[SIndex].Read         = true;
    Segments[SIndex].Write        = (Shdr->sh_flags & SHF_WRITE) != 0;
    Segments[SIndex].Execute      = (Shdr->sh_flags & SHF_EXECINSTR) != 0;

    Segments[SIndex].Data = AllocateZeroPool (Segments[SIndex].ImageSize);
    if (Segments[SIndex].Data == NULL) {
      fprintf (stderr, "ImageTool: Could not allocate memory for Segment #%d Data\n", Index);
      return RETURN_OUT_OF_RESOURCES;
    };

    if (Shdr->sh_type == SHT_PROGBITS) {
      memcpy (Segments[SIndex].Data, (const char *)Ehdr + Shdr->sh_offset, (size_t)Shdr->sh_size);
    }

    ++SIndex;
  }

  assert (SIndex == ImageInfo->SegmentInfo.NumSegments);

  return SetRelocs (ImageInfo, Context);
}

#define ScanElf  ELF_SUFFIX(ScanElf)
RETURN_STATUS
ScanElf (
  OUT image_tool_image_info_t  *ImageInfo,
  IN  const void               *File,
  IN  uint32_t                 FileSize,
  IN  const char               *SymbolsPath OPTIONAL
  )
{
  RETURN_STATUS          Status;
  tool_elf_scan_context  Context;
  const Elf_Ehdr         *Ehdr;
  Elf_Addr               BaseAddress;

  assert (File != NULL || FileSize == 0);

  Status = ParseElfFile (&Context, File, FileSize);
  if (RETURN_ERROR (Status)) {
    return Status;
  }

  Ehdr        = Context.Ehdr;
  BaseAddress = Context.BaseAddress;

  memset (ImageInfo, 0, sizeof (*ImageInfo));

  ImageInfo->HeaderInfo.BaseAddress       = BaseAddress;
  ImageInfo->HeaderInfo.EntryPointAddress = (uint32_t)(Ehdr->e_entry - BaseAddress);
  ImageInfo->SegmentInfo.SegmentAlignment = (uint32_t)Context.Alignment;
  ImageInfo->RelocInfo.RelocsStripped     = false;

  if (SymbolsPath != NULL) {
    ImageInfo->DebugInfo.SymbolsPathLen = strlen (SymbolsPath);
  } else {
    assert (ImageInfo->DebugInfo.SymbolsPathLen == 0);
  }

  switch (Ehdr->e_machine) {
#if ELF_ARCH == 64
    case EM_X86_64:
      ImageInfo->HeaderInfo.Machine = IMAGE_FILE_MACHINE_X64;
      break;
    case EM_AARCH64:
      ImageInfo->HeaderInfo.Machine = IMAGE_FILE_MACHINE_ARM64;
      break;
#elif ELF_ARCH == 32
    case EM_386:
      ImageInfo->HeaderInfo.Machine = IMAGE_FILE_MACHINE_I386;
      break;
    case EM_ARM:
      ImageInfo->HeaderInfo.Machine = IMAGE_FILE_MACHINE_ARMTHUMB_MIXED;
      break;
#endif
    default:
      fprintf (stderr, "ImageTool: Unknown ELF architecture %d\n", Ehdr->e_machine);
      return RETURN_INCOMPATIBLE_VERSION;
  }

  ImageInfo->DebugInfo.SymbolsPath = AllocatePool (ImageInfo->DebugInfo.SymbolsPathLen + 1);
  if (ImageInfo->DebugInfo.SymbolsPath == NULL) {
    fprintf (stderr, "ImageTool: Could not allocate memory for Debug Data\n");
    return RETURN_OUT_OF_RESOURCES;
  }

  if (SymbolsPath != NULL) {
    memmove (ImageInfo->DebugInfo.SymbolsPath, SymbolsPath, ImageInfo->DebugInfo.SymbolsPathLen + 1);
  } else {
    *ImageInfo->DebugInfo.SymbolsPath = '\0';
  }

  //
  // There is no corresponding ELF property.
  //
  ImageInfo->HeaderInfo.Subsystem = 0;

  Status = CreateIntermediate (ImageInfo, &Context);
  if (RETURN_ERROR (Status)) {
    ToolImageDestruct (ImageInfo);
  }

  return Status;
}
