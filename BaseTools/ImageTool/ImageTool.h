#ifndef IMAGE_TOOL_H
#define IMAGE_TOOL_H

#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <errno.h>
#include <assert.h>
#include <getopt.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/mman.h>
#include <fcntl.h>

#include <Base.h>
#include <IndustryStandard/PeImage2.h>
#include <IndustryStandard/UeImage.h>
#include <Library/PeCoffLib2.h>
#include <Library/UeImageLib.h>
#include <Library/BaseMemoryLib.h>
#include <UserFile.h>
#include "../../MdePkg/Library/BasePeCoffLib2/BaseOverflow.h"
#include "../../UefiPayloadPkg/PayloadLoaderPeim/ElfLib/ElfCommon.h"

#undef ELF_R_TYPE
#undef ELF_R_SYM

#ifdef EFI_TARGET32
#include "../../UefiPayloadPkg/PayloadLoaderPeim/ElfLib/Elf32.h"

#define EFI_IMAGE_NT_HEADERS		         EFI_IMAGE_NT_HEADERS32
#define EFI_IMAGE_NT_OPTIONAL_HDR_MAGIC	 EFI_IMAGE_NT_OPTIONAL_HDR32_MAGIC
#define EFI_IMAGE_FILE_MACHINE		       EFI_IMAGE_FILE_32BIT_MACHINE
#define ELFCLASS                         ELFCLASS32
#define Elf_Ehdr                         Elf32_Ehdr
#define Elf_Shdr                         Elf32_Shdr
#define Elf_Sym                          Elf32_Sym
#define Elf_Rel                          Elf32_Rel
#define Elf_Rela                         Elf32_Rela
#define Elf_Size                         Elf32_Size
#define Elf_Addr                         Elf32_Addr
#define ELF_R_TYPE                       ELF32_R_TYPE
#define ELF_R_SYM                        ELF32_R_SYM

#elif defined(EFI_TARGET64)
#include "../../UefiPayloadPkg/PayloadLoaderPeim/ElfLib/Elf64.h"

#define EFI_IMAGE_NT_HEADERS		         EFI_IMAGE_NT_HEADERS64
#define EFI_IMAGE_NT_OPTIONAL_HDR_MAGIC  EFI_IMAGE_NT_OPTIONAL_HDR64_MAGIC
#define EFI_IMAGE_FILE_MACHINE		       0
#define ELFCLASS                         ELFCLASS64
#define Elf_Ehdr                         Elf64_Ehdr
#define Elf_Shdr                         Elf64_Shdr
#define Elf_Sym                          Elf64_Sym
#define Elf_Rel                          Elf64_Rel
#define Elf_Rela                         Elf64_Rela
#define Elf_Size                         Elf64_Size
#define Elf_Addr                         Elf64_Addr
#define ELF_R_TYPE                       ELF64_R_TYPE
#define ELF_R_SYM                        ELF64_R_SYM
#endif

#define ELF_HII_SECTION_NAME ".hii"
#define MAX_PE_ALIGNMENT     0x10000

enum {
	TEXT_SECTION  = 1,
	DATA_SECTION  = 2,
	HII_SECTION   = 3,
	RELOC_SECTION = 4,
};

#define raise() assert(false)

typedef struct _PeRelocs PeRelocs;

typedef struct {
	EFI_IMAGE_DOS_HEADER Dos;
	EFI_IMAGE_NT_HEADERS *Nt;
} PeHeader;

typedef struct {
	EFI_IMAGE_SECTION_HEADER PeShdr;
	UINT8                    Type;
	UINT8                    Data[];
} PeSection;

typedef struct _PeOffset {
	UINT8  Type;
	UINT32 Offset;
} PeOffset;

typedef struct _PeRelocs {
	PeRelocs *Next;
	UINTN    PageRva;
	UINT32   Used;
	UINT32   Total;
	UINT16   *TypeOffsets;
} PeRelocs;

typedef struct {
	EFI_IMAGE_DEBUG_DIRECTORY_ENTRY     Dir;
	EFI_IMAGE_DEBUG_CODEVIEW_NB10_ENTRY Nb10;
	char                                Name[];
} DebugData;

#define PAGE(x)     ((x) & ~(uint64_t) 4095ULL)
#define PAGE_OFF(x) ((x) & 4095U)

typedef struct {
  uint64_t PreferredAddress;
  uint32_t EntryPointAddress;
  uint8_t  Machine;
  uint8_t  Subsystem;
  bool     IsXip;
} image_tool_header_info_t;

typedef enum {
  ToolImageSectionTypeCode,
  ToolImageSectionTypeInitialisedData,
  ToolImageSectionTypeUninitialisedData
} image_tool_type_t;

typedef struct {
  char     *Name;
  uint8_t  *Data;
  uint32_t DataSize;
  uint64_t ImageAddress;
  uint32_t ImageSize;
  bool     Read;
  bool     Write;
  bool     Execute;
  image_tool_type_t Type;
} image_tool_segment_t;

typedef struct {
  uint32_t             SegmentAlignment;
  uint64_t             NumSegments;
  image_tool_segment_t *Segments;
} image_tool_segment_info_t;

typedef struct {
  uint8_t  Type;
  uint32_t Target;
} image_tool_reloc_t;

typedef struct {
  uint32_t           NumRelocs;
  bool               RelocsStripped;
  image_tool_reloc_t *Relocs;
} image_tool_reloc_info_t;

typedef struct {
  char   *SymbolsPath;
  size_t SymbolsPathLen;
} image_tool_debug_info_t;

typedef struct {
  uint32_t DebugDirAddress;
  uint32_t DebugDirSize;
} image_tool_pe_datadir_info_t;

typedef struct {
  void     *Data;
  uint32_t DataSize;
} image_tool_hii_info_t;

typedef struct {
  image_tool_header_info_t  HeaderInfo;
  image_tool_segment_info_t SegmentInfo;
  image_tool_reloc_info_t   RelocInfo;
  image_tool_hii_info_t     HiiInfo;
  image_tool_debug_info_t   DebugInfo;
} image_tool_image_info_t;

void ToolImageDestruct (
  image_tool_image_info_t *Image
  );

bool ImageConvertToXip (
  image_tool_image_info_t *Image
  );

void *ToolImageEmitUe (
  const image_tool_image_info_t *Image,
  uint32_t                      *FileSize
  );

bool ToolContextConstructPe (
  image_tool_image_info_t *Image,
  const void              *File,
  size_t                  FileSize
  );

bool CheckToolImage (
  image_tool_image_info_t *Image
  );

void *ToolImageEmitPe (
  const image_tool_image_info_t *Image,
  uint32_t                      *FileSize
  );

EFI_STATUS
ElfToPe (
	IN const char *ElfName,
	IN const char *PeName,
	IN const char *ModuleType
  );

#endif // IMAGE_TOOL_H
