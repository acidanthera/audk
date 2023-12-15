/** @file
  Copyright (c) 2021, Marvin Häuser. All rights reserved.
  Copyright (c) 2022, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause
**/

#include "ImageTool.h"

#include "DynamicBuffer.h"
#include "PeEmitCommon.h"

#if PE_ARCH == 32

typedef UINT32                  EFI_IMAGE_NT_BASE_ADDRESS;
typedef EFI_IMAGE_NT_HEADERS32  EFI_IMAGE_NT_HEADERS;
#define EFI_IMAGE_NT_OPTIONAL_HDR_MAGIC  EFI_IMAGE_NT_OPTIONAL_HDR32_MAGIC

#elif PE_ARCH == 64

typedef UINT64                  EFI_IMAGE_NT_BASE_ADDRESS;
typedef EFI_IMAGE_NT_HEADERS64  EFI_IMAGE_NT_HEADERS;
#define EFI_IMAGE_NT_OPTIONAL_HDR_MAGIC  EFI_IMAGE_NT_OPTIONAL_HDR64_MAGIC

#endif

#define PE_SUFFIX__(Name, Arch)  Name##Arch
#define PE_SUFFIX_(Name, Arch)   PE_SUFFIX__ (Name, Arch)
#define PE_SUFFIX(Name)          PE_SUFFIX_ (Name, PE_ARCH)

typedef struct {
  EFI_IMAGE_DEBUG_DIRECTORY_ENTRY        Dir;
  EFI_IMAGE_DEBUG_CODEVIEW_NB10_ENTRY    Nb10;
} image_tool_debug_dir_t;

#define SIZE_OF_DATA_DIRECRORY  \
  EFI_IMAGE_NUMBER_OF_DIRECTORY_ENTRIES * sizeof (EFI_IMAGE_DATA_DIRECTORY)

#define SIZE_OF_OPTIONAL_HEADER                                             \
  sizeof (EFI_IMAGE_NT_HEADERS) - sizeof (EFI_IMAGE_NT_HEADERS_COMMON_HDR)  \
    + SIZE_OF_DATA_DIRECRORY

static
bool
InternalFinalizeExtraSection (
  image_tool_dynamic_buffer  *Buffer,
  EFI_IMAGE_NT_HEADERS       *PeHdr,
  EFI_IMAGE_SECTION_HEADER   *SectionHeader,
  const char                 *Name,
  uint32_t                   Size,
  uint32_t                   Offset
  )
{
  uint32_t  BufferOffset;

  assert (Size == ImageToolBufferGetSize (Buffer) - Offset);

  strncpy (
    (char *)SectionHeader->Name,
    Name,
    sizeof (SectionHeader->Name)
    );
  SectionHeader->Name[ARRAY_SIZE (SectionHeader->Name) - 1] = 0;

  SectionHeader->VirtualSize      = ALIGN_VALUE (Size, PeHdr->SectionAlignment);
  SectionHeader->VirtualAddress   = PeHdr->SizeOfImage;
  SectionHeader->SizeOfRawData    = ALIGN_VALUE (Size, PeHdr->FileAlignment);
  SectionHeader->PointerToRawData = Offset;
  SectionHeader->Characteristics  = EFI_IMAGE_SCN_CNT_INITIALIZED_DATA | EFI_IMAGE_SCN_MEM_READ;

  PeHdr->SizeOfInitializedData += SectionHeader->VirtualSize;
  PeHdr->SizeOfImage           += SectionHeader->VirtualSize;

  BufferOffset = ImageToolBufferAppendReserve (
                   Buffer,
                   SectionHeader->SizeOfRawData - Size
                   );
  return BufferOffset != MAX_UINT32;
}

#define ToolImageEmitPeHiiTable  PE_SUFFIX (ToolImageEmitPeHiiTable)
static
bool
ToolImageEmitPeHiiTable (
  image_tool_dynamic_buffer      *Buffer,
  EFI_IMAGE_NT_HEADERS           *PeHdr,
  EFI_IMAGE_SECTION_HEADER       *SectionHeader,
  const image_tool_image_info_t  *Image
  )
{
  bool      Success;
  uint32_t  HiiTableOffset;
  uint32_t  HiiTableSize;
  void      *HiiTable;
  uint32_t  Offset;

  HiiTableOffset = ImageToolBufferAppendReserve (
                     Buffer,
                     mHiiResourceSectionHeaderSize
                     );
  if (HiiTableOffset == MAX_UINT32) {
    DEBUG_RAISE ();
    return false;
  }

  assert (IS_ALIGNED (HiiTableOffset, PeHdr->FileAlignment));

  HiiTable = ImageToolBufferGetPointer (Buffer, HiiTableOffset);
  InitializeHiiResouceSectionHeader (
    HiiTable,
    SectionHeader->VirtualAddress,
    Image->HiiInfo.DataSize
    );
  HiiTable = NULL;

  Offset = ImageToolBufferAppend (
             Buffer,
             Image->HiiInfo.Data,
             Image->HiiInfo.DataSize
             );
  if (Offset == MAX_UINT32) {
    DEBUG_RAISE ();
    return false;
  }

  HiiTableSize = ImageToolBufferGetSize (Buffer) - HiiTableOffset;

  Success = InternalFinalizeExtraSection (
              Buffer,
              PeHdr,
              SectionHeader,
              ".rsrc",
              HiiTableSize,
              HiiTableOffset
              );
  if (!Success) {
    DEBUG_RAISE ();
    return false;
  }

  PeHdr->DataDirectory[EFI_IMAGE_DIRECTORY_ENTRY_RESOURCE].VirtualAddress = SectionHeader->VirtualAddress;
  PeHdr->DataDirectory[EFI_IMAGE_DIRECTORY_ENTRY_RESOURCE].Size           = HiiTableSize;

  return true;
}

#define ToolImageEmitPeRelocTable  PE_SUFFIX (ToolImageEmitPeRelocTable)
static
bool
ToolImageEmitPeRelocTable (
  image_tool_dynamic_buffer      *Buffer,
  EFI_IMAGE_NT_HEADERS           *PeHdr,
  EFI_IMAGE_SECTION_HEADER       *SectionHeader,
  const image_tool_image_info_t  *Image
  )
{
  bool                             Success;
  uint32_t                         RelocTableSize;
  EFI_IMAGE_BASE_RELOCATION_BLOCK  RelocBlock;
  uint32_t                         BlockAddress;
  uint32_t                         Index;
  uint32_t                         RelocAddress;
  uint16_t                         Relocation;
  uint32_t                         RelocTableOffset;
  uint32_t                         RelocTableEnd;
  uint32_t                         RelocBlockOffset;
  uint32_t                         NewRelocBlockOffset;
  uint32_t                         Offset;

  RelocBlockOffset = ImageToolBufferAppendReserve (Buffer, sizeof (RelocBlock));
  if (RelocBlockOffset == MAX_UINT32) {
    DEBUG_RAISE ();
    return false;
  }

  RelocTableOffset = RelocBlockOffset;

  assert (IS_ALIGNED (RelocTableOffset, PeHdr->FileAlignment));

  BlockAddress = PAGE (Image->RelocInfo.Relocs[0].Target);

  for (Index = 0; Index < Image->RelocInfo.NumRelocs; ++Index) {
    RelocAddress = PAGE (Image->RelocInfo.Relocs[Index].Target);
    if (RelocAddress != BlockAddress) {
      Offset = ImageToolBufferAppendReserveAlign (
                 Buffer,
                 ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK)
                 );
      if (Offset == MAX_UINT32) {
        DEBUG_RAISE ();
        return false;
      }

      NewRelocBlockOffset = ImageToolBufferAppendReserve (
                              Buffer,
                              sizeof (RelocBlock)
                              );
      if (NewRelocBlockOffset == MAX_UINT32) {
        DEBUG_RAISE ();
        return false;
      }

      RelocBlock.VirtualAddress = BlockAddress;
      RelocBlock.SizeOfBlock    = NewRelocBlockOffset - RelocBlockOffset;
      ImageToolBufferWrite (
        Buffer,
        RelocBlockOffset,
        &RelocBlock,
        sizeof (RelocBlock)
        );

      RelocBlockOffset = NewRelocBlockOffset;

      BlockAddress = RelocAddress;
    }

    Relocation  = PAGE_OFF (Image->RelocInfo.Relocs[Index].Target);
    Relocation |= ((uint16_t)Image->RelocInfo.Relocs[Index].Type) << 12U;

    Offset = ImageToolBufferAppend (Buffer, &Relocation, sizeof (Relocation));
    if (Offset == MAX_UINT32) {
      DEBUG_RAISE ();
      return false;
    }
  }

  Offset = ImageToolBufferAppendReserveAlign (
             Buffer,
             ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK)
             );
  if (Offset == MAX_UINT32) {
    DEBUG_RAISE ();
    return false;
  }

  RelocTableEnd = ImageToolBufferGetSize (Buffer);

  RelocBlock.VirtualAddress = BlockAddress;
  RelocBlock.SizeOfBlock    = RelocTableEnd - RelocBlockOffset;
  ImageToolBufferWrite (
    Buffer,
    RelocBlockOffset,
    &RelocBlock,
    sizeof (RelocBlock)
    );

  RelocTableSize = RelocTableEnd - RelocTableOffset;

  Success = InternalFinalizeExtraSection (
              Buffer,
              PeHdr,
              SectionHeader,
              ".reloc",
              RelocTableSize,
              RelocTableOffset
              );
  if (!Success) {
    DEBUG_RAISE ();
    return false;
  }

  SectionHeader->Characteristics |= EFI_IMAGE_SCN_MEM_DISCARDABLE;

  PeHdr->DataDirectory[EFI_IMAGE_DIRECTORY_ENTRY_BASERELOC].VirtualAddress = SectionHeader->VirtualAddress;
  PeHdr->DataDirectory[EFI_IMAGE_DIRECTORY_ENTRY_BASERELOC].Size           = RelocTableSize;

  return true;
}

#define ToolImageEmitPeDebugTable  PE_SUFFIX (ToolImageEmitPeDebugTable)
static
bool
ToolImageEmitPeDebugTable (
  image_tool_dynamic_buffer      *Buffer,
  EFI_IMAGE_NT_HEADERS           *PeHdr,
  EFI_IMAGE_SECTION_HEADER       *SectionHeader,
  const image_tool_image_info_t  *Image
  )
{
  bool                    Success;
  uint32_t                DebugDirOffset;
  uint32_t                DebugDirSize;
  image_tool_debug_dir_t  *Data;
  uint32_t                Offset;

  assert (Image->DebugInfo.SymbolsPath != NULL);

  DebugDirOffset = ImageToolBufferAppendReserve (Buffer, sizeof (*Data));
  if (DebugDirOffset == MAX_UINT32) {
    DEBUG_RAISE ();
    return false;
  }

  assert (IS_ALIGNED (DebugDirOffset, PeHdr->FileAlignment));

  Offset = ImageToolBufferAppend (
             Buffer,
             Image->DebugInfo.SymbolsPath,
             Image->DebugInfo.SymbolsPathLen + 1
             );
  if (Offset == MAX_UINT32) {
    DEBUG_RAISE ();
    return false;
  }

  DebugDirSize = ImageToolBufferGetSize (Buffer) - DebugDirOffset;

  Success = InternalFinalizeExtraSection (
              Buffer,
              PeHdr,
              SectionHeader,
              ".debug",
              DebugDirSize,
              DebugDirOffset
              );
  if (!Success) {
    DEBUG_RAISE ();
    return false;
  }

  SectionHeader->Characteristics |= EFI_IMAGE_SCN_MEM_DISCARDABLE;

  PeHdr->DataDirectory[EFI_IMAGE_DIRECTORY_ENTRY_DEBUG].VirtualAddress = SectionHeader->VirtualAddress;
  PeHdr->DataDirectory[EFI_IMAGE_DIRECTORY_ENTRY_DEBUG].Size           = sizeof (Data->Dir);

  Data = ImageToolBufferGetPointer (Buffer, DebugDirOffset);

  memset (Data, 0, sizeof (*Data));
  Data->Dir.Type       = EFI_IMAGE_DEBUG_TYPE_CODEVIEW;
  Data->Dir.SizeOfData = DebugDirSize - OFFSET_OF (image_tool_debug_dir_t, Nb10);
  Data->Dir.RVA        = SectionHeader->VirtualAddress + OFFSET_OF (image_tool_debug_dir_t, Nb10);
  Data->Dir.FileOffset = SectionHeader->PointerToRawData + OFFSET_OF (image_tool_debug_dir_t, Nb10);
  Data->Nb10.Signature = CODEVIEW_SIGNATURE_NB10;

  Data = NULL;

  return true;
}

static
bool
ToolImagePeHiiTableRequired (
  const image_tool_image_info_t  *Image
  )
{
  return Image->HiiInfo.DataSize != 0;
}

static
bool
ToolImagePeRelocTableRequired (
  const image_tool_image_info_t  *Image
  )
{
  return Image->RelocInfo.NumRelocs != 0;
}

static
bool
ToolImagePeDebugTableRequired (
  const image_tool_image_info_t  *Image
  )
{
  return Image->DebugInfo.SymbolsPath != NULL;
}

#define ToolImageEmitPeSection  PE_SUFFIX (ToolImageEmitPeSection)
static
bool
ToolImageEmitPeSection (
  image_tool_dynamic_buffer      *Buffer,
  EFI_IMAGE_NT_HEADERS           *PeHdr,
  EFI_IMAGE_SECTION_HEADER       *SectionHeader,
  const image_tool_image_info_t  *Image,
  bool                           Xip,
  const image_tool_segment_t     *Segment
  )
{
  uint32_t  SectionOffset;
  uint32_t  SizeOfRawData;
  uint32_t  Offset;

  SectionOffset = ImageToolBufferAppend (
                    Buffer,
                    Segment->Data,
                    Segment->UnpaddedSize
                    );
  if (SectionOffset == MAX_UINT32) {
    DEBUG_RAISE ();
    return false;
  }

  assert (IS_ALIGNED (SectionOffset, PeHdr->FileAlignment));

  if (!Xip) {
    SizeOfRawData = Segment->UnpaddedSize;
  } else {
    SizeOfRawData = Segment->ImageSize;
  }

  strncpy (
    (char *)SectionHeader->Name,
    Segment->Name,
    sizeof (SectionHeader->Name)
    );
  SectionHeader->Name[ARRAY_SIZE (SectionHeader->Name) - 1] = 0;

  SectionHeader->VirtualSize      = Segment->ImageSize;
  SectionHeader->VirtualAddress   = Segment->ImageAddress;
  SectionHeader->SizeOfRawData    = ALIGN_VALUE (SizeOfRawData, PeHdr->FileAlignment);
  SectionHeader->PointerToRawData = SectionOffset;

  assert (SectionHeader->Characteristics == 0);

  if (Segment->Read) {
    SectionHeader->Characteristics |= EFI_IMAGE_SCN_MEM_READ;
  }

  if (Segment->Write) {
    SectionHeader->Characteristics |= EFI_IMAGE_SCN_MEM_WRITE;
  }

  if (Segment->Execute) {
    SectionHeader->Characteristics |= EFI_IMAGE_SCN_MEM_EXECUTE | EFI_IMAGE_SCN_CNT_CODE;

    PeHdr->SizeOfCode += Segment->ImageSize;
    if (PeHdr->BaseOfCode == 0) {
      PeHdr->BaseOfCode = Segment->ImageAddress;
    }
  } else {
    SectionHeader->Characteristics |= EFI_IMAGE_SCN_CNT_INITIALIZED_DATA;

    PeHdr->SizeOfInitializedData += Segment->ImageSize;
 #if PE_ARCH == 32
    if (PeHdr->BaseOfData == 0) {
      PeHdr->BaseOfData = Segment->ImageAddress;
    }

 #endif
  }

  assert (PeHdr->SizeOfImage == SectionHeader->VirtualAddress);
  PeHdr->SizeOfImage += SectionHeader->VirtualSize;

  Offset = ImageToolBufferAppendReserve (
             Buffer,
             SectionHeader->SizeOfRawData - Segment->UnpaddedSize
             );
  return Offset != MAX_UINT32;
}

#define ToolImageEmitPeSections  PE_SUFFIX (ToolImageEmitPeSections)
static
bool
ToolImageEmitPeSections (
  image_tool_dynamic_buffer      *Buffer,
  EFI_IMAGE_NT_HEADERS           *PeHdr,
  EFI_IMAGE_SECTION_HEADER       *SectionHeaders,
  const image_tool_image_info_t  *Image,
  bool                           Xip
  )
{
  bool                        Success;
  uint16_t                    Index;
  const image_tool_segment_t  *Segment;
  EFI_IMAGE_SECTION_HEADER    *SectionHeader;

  if (PeHdr->SizeOfImage != Image->SegmentInfo.Segments[0].ImageAddress) {
    DEBUG_RAISE ();
    return false;
  }

  for (Index = 0; Index < Image->SegmentInfo.NumSegments; ++Index) {
    Segment       = &Image->SegmentInfo.Segments[Index];
    SectionHeader = &SectionHeaders[Index];

    Success = ToolImageEmitPeSection (
                Buffer,
                PeHdr,
                SectionHeader,
                Image,
                Xip,
                Segment
                );
    if (!Success) {
      DEBUG_RAISE ();
      return false;
    }
  }

  if (ToolImagePeHiiTableRequired (Image)) {
    Success = ToolImageEmitPeHiiTable (Buffer, PeHdr, &SectionHeaders[Index], Image);
    if (!Success) {
      DEBUG_RAISE ();
      return false;
    }

    ++Index;
  }

  if (ToolImagePeRelocTableRequired (Image)) {
    Success = ToolImageEmitPeRelocTable (Buffer, PeHdr, &SectionHeaders[Index], Image);
    if (!Success) {
      DEBUG_RAISE ();
      return false;
    }

    ++Index;
  }

  if (ToolImagePeDebugTableRequired (Image)) {
    Success = ToolImageEmitPeDebugTable (Buffer, PeHdr, &SectionHeaders[Index], Image);
    if (!Success) {
      DEBUG_RAISE ();
      return false;
    }

    ++Index;
  }

  assert (Index == PeHdr->CommonHeader.FileHeader.NumberOfSections);

  if (Image->HeaderInfo.FixedAddress) {
    for (Index = 0; Index < PeHdr->CommonHeader.FileHeader.NumberOfSections; ++Index) {
      if ((SectionHeaders[Index].Characteristics & EFI_IMAGE_SCN_MEM_EXECUTE) == 0) {
        WriteUnaligned64 (
          (VOID *)&SectionHeaders[Index].PointerToRelocations,
          PeHdr->ImageBase
          );
        break;
      }
    }

    if (Index == PeHdr->CommonHeader.FileHeader.NumberOfSections) {
      DEBUG_RAISE ();
      return false;
    }
  }

  return true;
}

STATIC CONST EFI_IMAGE_DOS_HEADER  mDosHdr = {
  .e_magic  = EFI_IMAGE_DOS_SIGNATURE,
  .e_lfanew = sizeof (mDosHdr)
};

#define ToolImageEmitPeFile  PE_SUFFIX (ToolImageEmitPeFile)
static
bool
ToolImageEmitPeFile (
  image_tool_dynamic_buffer      *Buffer,
  const image_tool_image_info_t  *Image,
  bool                           Xip
  )
{
  bool                      Success;
  uint32_t                  FileAlignment;
  uint32_t                  PeOffset;
  EFI_IMAGE_NT_HEADERS      *PeHdr;
  uint16_t                  NumSections;
  EFI_IMAGE_SECTION_HEADER  *SectionHeaders;
  uint32_t                  SectionHeadersOffset;
  uint32_t                  SectionHeadersSize;
  uint32_t                  SizeOfPeHeaders;
  uint32_t                  SizeOfHeaders;
  uint32_t                  AlignedSizeOfHeaders;
  void                      *BufferPeHdr;
  uint32_t                  Offset;

  if (!Xip) {
    FileAlignment = 64;
  } else {
    FileAlignment = Image->SegmentInfo.SegmentAlignment;
  }

  NumSections  = Image->SegmentInfo.NumSegments;
  NumSections += ToolImagePeHiiTableRequired (Image) ? 1 : 0;
  NumSections += ToolImagePeRelocTableRequired (Image) ? 1 : 0;
  NumSections += ToolImagePeDebugTableRequired (Image) ? 1 : 0;

  Offset = ImageToolBufferAppend (Buffer, &mDosHdr, sizeof (mDosHdr));
  if (Offset == MAX_UINT32) {
    DEBUG_RAISE ();
    return false;
  }

  SectionHeadersOffset = sizeof (*PeHdr) + SIZE_OF_DATA_DIRECRORY;
  SectionHeadersSize   = NumSections * sizeof (EFI_IMAGE_SECTION_HEADER);
  SizeOfPeHeaders      = SectionHeadersOffset + SectionHeadersSize;
  SizeOfHeaders        = sizeof (mDosHdr) + SizeOfPeHeaders;
  AlignedSizeOfHeaders = ALIGN_VALUE (SizeOfHeaders, FileAlignment);

  PeOffset = ImageToolBufferAppendReserve (
               Buffer,
               AlignedSizeOfHeaders - sizeof (mDosHdr)
               );
  if (PeOffset == MAX_UINT32) {
    DEBUG_RAISE ();
    return false;
  }

  PeHdr = AllocateZeroPool (SizeOfPeHeaders);
  if (PeHdr == NULL) {
    DEBUG_RAISE ();
    return false;
  }

  SectionHeaders = (EFI_IMAGE_SECTION_HEADER *)((UINT8 *)PeHdr + SectionHeadersOffset);

  PeHdr->CommonHeader.Signature                       = EFI_IMAGE_NT_SIGNATURE;
  PeHdr->CommonHeader.FileHeader.Machine              = Image->HeaderInfo.Machine;
  PeHdr->CommonHeader.FileHeader.NumberOfSections     = NumSections;
  PeHdr->CommonHeader.FileHeader.SizeOfOptionalHeader = SIZE_OF_OPTIONAL_HEADER;
  PeHdr->CommonHeader.FileHeader.Characteristics      =
    EFI_IMAGE_FILE_EXECUTABLE_IMAGE | EFI_IMAGE_FILE_LINE_NUMS_STRIPPED |
    EFI_IMAGE_FILE_LOCAL_SYMS_STRIPPED | EFI_IMAGE_FILE_LARGE_ADDRESS_AWARE;

  if (Image->RelocInfo.RelocsStripped) {
    PeHdr->CommonHeader.FileHeader.Characteristics |= EFI_IMAGE_FILE_RELOCS_STRIPPED;
  }

  PeHdr->Magic               = EFI_IMAGE_NT_OPTIONAL_HDR_MAGIC;
  PeHdr->AddressOfEntryPoint = Image->HeaderInfo.EntryPointAddress;
  PeHdr->ImageBase           = (EFI_IMAGE_NT_BASE_ADDRESS)Image->HeaderInfo.BaseAddress;
  PeHdr->SectionAlignment    = Image->SegmentInfo.SegmentAlignment;
  PeHdr->FileAlignment       = FileAlignment;
  PeHdr->SizeOfImage         = ALIGN_VALUE (SizeOfHeaders, PeHdr->SectionAlignment);
  PeHdr->SizeOfHeaders       = AlignedSizeOfHeaders;
  PeHdr->Subsystem           = Image->HeaderInfo.Subsystem;
  PeHdr->NumberOfRvaAndSizes = EFI_IMAGE_NUMBER_OF_DIRECTORY_ENTRIES;

  Success = ToolImageEmitPeSections (Buffer, PeHdr, SectionHeaders, Image, Xip);
  if (!Success) {
    FreePool (PeHdr);
    DEBUG_RAISE ();
    return false;
  }

  BufferPeHdr = ImageToolBufferGetPointer (Buffer, PeOffset);
  memmove (BufferPeHdr, PeHdr, SizeOfPeHeaders);
  FreePool (PeHdr);
  BufferPeHdr = NULL;

  return true;
}

#define ToolImageEmitPe  PE_SUFFIX (ToolImageEmitPe)
void *
ToolImageEmitPe (
  const image_tool_image_info_t  *Image,
  uint32_t                       *FileSize,
  bool                           Xip
  )
{
  bool                       Success;
  image_tool_dynamic_buffer  Buffer;
  void                       *FileBuffer;

  assert (Image    != NULL);
  assert (FileSize != NULL);

  ImageInitUnpaddedSize (Image);

  ImageToolBufferInit (&Buffer);

  Success = ToolImageEmitPeFile (&Buffer, Image, Xip);
  if (!Success) {
    DEBUG_RAISE ();
    ImageToolBufferFree (&Buffer);
    return NULL;
  }

  FileBuffer = ImageToolBufferDump (FileSize, &Buffer);

  ImageToolBufferFree (&Buffer);

  if (FileBuffer == NULL) {
    DEBUG_RAISE ();
    return NULL;
  }

  return FileBuffer;
}
