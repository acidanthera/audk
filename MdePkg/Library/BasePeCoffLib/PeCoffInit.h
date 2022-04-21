/** @file
  Provides APIs to verify PE/COFF Images for further processing.

  Copyright (c) 2020, Marvin Häuser. All rights reserved.<BR>
  Copyright (c) 2020, Vitaly Cheptsov. All rights reserved.<BR>
  Copyright (c) 2020, ISP RAS. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-3-Clause
**/

#ifndef PE_COFF_INIT_H_
#define PE_COFF_INIT_H_

/*@ predicate image_te_valid (char *FileBuffer, UINT32 FileSize) =
  @   \let TeHdr            = image_te_get_hdr (FileBuffer);
  @   \let Sections         = image_te_get_sections (FileBuffer);
  @   \let RelocDir         = image_te_get_reloc_dir (FileBuffer);
  @   \let SizeOfHeaders    = image_te_SizeOfHeaders (FileBuffer);
  @   \let SizeOfImage      = image_te_SizeOfImage (FileBuffer);
  @   \let TeStrippedOffset = TeHdr->StrippedSize - sizeof (EFI_TE_IMAGE_HEADER);
  @   \let StartAddress     = image_loaded_hdr_virtual_size (Sections, SizeOfHeaders, BASE_4KB);
  @   \let RelocsStripped   = (BOOLEAN) (RelocDir->Size > 0 ? TRUE : FALSE);
  @   0 <= TeStrippedOffset &&
  @   sizeof (EFI_TE_IMAGE_HEADER) <= image_hdr_raw_size (SizeOfHeaders, TeStrippedOffset) <= FileSize &&
  @   0 < TeHdr->NumberOfSections &&
  @   SizeOfHeaders <= MAX_UINT32 &&
  @   TeHdr->AddressOfEntryPoint < SizeOfImage &&
  @   image_reloc_info_sane (
  @     RelocDir->VirtualAddress,
  @     RelocDir->Size,
  @     RelocsStripped,
  @     StartAddress,
  @     SizeOfHeaders,
  @     SizeOfImage,
  @     TeHdr->ImageBase,
  @     BASE_4KB,
  @     TeHdr->Subsystem
  @     ) &&
  @   image_sects_sane (
  @     Sections,
  @     TeHdr->NumberOfSections,
  @     SizeOfHeaders,
  @     BASE_4KB,
  @     TeStrippedOffset,
  @     FileSize,
  @     ImageTypeTe
  @     );
*/

/*@ predicate image_pe32_reloc_info_valid (char *FileBuffer, UINT32 ExeHdrOffset) =
  @   \let Pe32Hdr        = image_pe32_get_hdr (FileBuffer, ExeHdrOffset);
  @   \let Sections       = image_pe32_get_sections (FileBuffer, ExeHdrOffset);
  @   \let RelocDir       = image_pe32_get_reloc_dir (FileBuffer, ExeHdrOffset);
  @   \let StartAddress   = image_loaded_hdr_virtual_size (Sections, Pe32Hdr->SizeOfHeaders, Pe32Hdr->SectionAlignment);
  @   \let RelocsStripped = (BOOLEAN) (image_pe_common_relocs_stripped (&Pe32Hdr->CommonHeader) ? TRUE : FALSE);
  @   image_reloc_info_sane (
  @     image_pe32_reloc_dir_exists (FileBuffer, ExeHdrOffset) ? RelocDir->VirtualAddress : 0,
  @     image_pe32_reloc_dir_exists (FileBuffer, ExeHdrOffset) ? RelocDir->Size : 0,
  @     RelocsStripped,
  @     StartAddress,
  @     Pe32Hdr->SizeOfHeaders,
  @     Pe32Hdr->SizeOfImage,
  @     Pe32Hdr->ImageBase,
  @     Pe32Hdr->SectionAlignment,
  @     Pe32Hdr->Subsystem
  @     );
*/

/*@ predicate image_pe32_valid (char *FileBuffer, UINT32 ExeHdrOffset, UINT32 FileSize) =
  @   \let Pe32Hdr        = image_pe32_get_hdr (FileBuffer, ExeHdrOffset);
  @   \let Sections       = image_pe32_get_sections (FileBuffer, ExeHdrOffset);
  @   \let RelocDir       = image_pe32_get_reloc_dir (FileBuffer, ExeHdrOffset);
  @   \let StartAddress   = image_loaded_hdr_virtual_size (Sections, Pe32Hdr->SizeOfHeaders, Pe32Hdr->SectionAlignment);
  @   \let RelocsStripped = (BOOLEAN) (image_pe_common_relocs_stripped (&Pe32Hdr->CommonHeader) ? TRUE : FALSE);
  @   image_pe32_get_min_SizeOfOptionalHeader (FileBuffer, ExeHdrOffset) <= Pe32Hdr->CommonHeader.FileHeader.SizeOfOptionalHeader &&
  @   image_pe32_get_min_SizeOfHeaders (FileBuffer, ExeHdrOffset) <= Pe32Hdr->SizeOfHeaders <= FileSize &&
  @   image_pe32_get_min_SizeOfImage (FileBuffer, ExeHdrOffset) <= Pe32Hdr->SizeOfImage &&
  @   is_aligned_32 ((UINT32) image_pecommon_get_sections_offset (&Pe32Hdr->CommonHeader, ExeHdrOffset), AV_ALIGNOF (EFI_IMAGE_SECTION_HEADER)) &&
  @   0 < Pe32Hdr->CommonHeader.FileHeader.NumberOfSections &&
  @   Pe32Hdr->NumberOfRvaAndSizes <= EFI_IMAGE_NUMBER_OF_DIRECTORY_ENTRIES &&
  @   is_pow2_32 (Pe32Hdr->SectionAlignment) &&
  @   Pe32Hdr->AddressOfEntryPoint < Pe32Hdr->SizeOfImage &&
  @   image_pe32_reloc_info_valid (FileBuffer, ExeHdrOffset) &&
  @   image_sects_sane (
  @     Sections,
  @     Pe32Hdr->CommonHeader.FileHeader.NumberOfSections,
  @     Pe32Hdr->SizeOfHeaders,
  @     Pe32Hdr->SectionAlignment,
  @     0,
  @     FileSize,
  @     ImageTypePe32
  @     );
*/

/*@ predicate image_pe32plus_reloc_info_valid (char *FileBuffer, UINT32 ExeHdrOffset) =
  @   \let Pe32PlusHdr    = image_pe32plus_get_hdr (FileBuffer, ExeHdrOffset);
  @   \let Sections       = image_pe32plus_get_sections (FileBuffer, ExeHdrOffset);
  @   \let RelocDir       = image_pe32plus_get_reloc_dir (FileBuffer, ExeHdrOffset);
  @   \let StartAddress   = image_loaded_hdr_virtual_size (Sections, Pe32PlusHdr->SizeOfHeaders, Pe32PlusHdr->SectionAlignment);
  @   \let RelocsStripped = (BOOLEAN) (image_pe_common_relocs_stripped (&Pe32PlusHdr->CommonHeader) ? TRUE : FALSE);
  @   image_reloc_info_sane (
  @     image_pe32plus_reloc_dir_exists (FileBuffer, ExeHdrOffset) ? RelocDir->VirtualAddress : 0,
  @     image_pe32plus_reloc_dir_exists (FileBuffer, ExeHdrOffset) ? RelocDir->Size : 0,
  @     RelocsStripped,
  @     StartAddress,
  @     Pe32PlusHdr->SizeOfHeaders,
  @     Pe32PlusHdr->SizeOfImage,
  @     Pe32PlusHdr->ImageBase,
  @     Pe32PlusHdr->SectionAlignment,
  @     Pe32PlusHdr->Subsystem
  @     );
*/

/*@ predicate image_pe32plus_valid (char *FileBuffer, UINT32 ExeHdrOffset, UINT32 FileSize) =
  @   \let Pe32PlusHdr    = image_pe32plus_get_hdr (FileBuffer, ExeHdrOffset);
  @   \let Sections       = image_pe32plus_get_sections (FileBuffer, ExeHdrOffset);
  @   \let RelocDir       = image_pe32plus_get_reloc_dir (FileBuffer, ExeHdrOffset);
  @   \let StartAddress   = image_loaded_hdr_virtual_size (Sections, Pe32PlusHdr->SizeOfHeaders, Pe32PlusHdr->SectionAlignment);
  @   \let RelocsStripped = (BOOLEAN) (image_pe_common_relocs_stripped (&Pe32PlusHdr->CommonHeader) ? TRUE : FALSE);
  @   image_pe32plus_get_min_SizeOfOptionalHeader (FileBuffer, ExeHdrOffset) <= Pe32PlusHdr->CommonHeader.FileHeader.SizeOfOptionalHeader &&
  @   image_pe32plus_get_min_SizeOfHeaders (FileBuffer, ExeHdrOffset) <= Pe32PlusHdr->SizeOfHeaders <= FileSize &&
  @   image_pe32plus_get_min_SizeOfImage (FileBuffer, ExeHdrOffset) <= Pe32PlusHdr->SizeOfImage &&
  @   is_aligned_32 ((UINT32) image_pecommon_get_sections_offset (&Pe32PlusHdr->CommonHeader, ExeHdrOffset), AV_ALIGNOF (EFI_IMAGE_SECTION_HEADER)) &&
  @   0 < Pe32PlusHdr->CommonHeader.FileHeader.NumberOfSections &&
  @   Pe32PlusHdr->NumberOfRvaAndSizes <= EFI_IMAGE_NUMBER_OF_DIRECTORY_ENTRIES &&
  @   is_pow2_32 (Pe32PlusHdr->SectionAlignment) &&
  @   Pe32PlusHdr->AddressOfEntryPoint < Pe32PlusHdr->SizeOfImage &&
  @   image_pe32plus_reloc_info_valid (FileBuffer, ExeHdrOffset) &&
  @   image_sects_sane (
  @     Sections,
  @     Pe32PlusHdr->CommonHeader.FileHeader.NumberOfSections,
  @     Pe32PlusHdr->SizeOfHeaders,
  @     Pe32PlusHdr->SectionAlignment,
  @     0,
  @     FileSize,
  @     ImageTypePe32Plus
  @     );
*/

/*@ predicate valid_pe(char *FileBuffer, UINT32 ExeHdrOffset, UINT32 FileSize) =
  @   (image_signature_pe32 (FileBuffer, ExeHdrOffset, FileSize) && image_pe32_valid (FileBuffer, ExeHdrOffset, FileSize)) ||
  @   (image_signature_pe32plus (FileBuffer, ExeHdrOffset, FileSize) && image_pe32plus_valid (FileBuffer, ExeHdrOffset, FileSize));
*/

/*@ axiomatic HdrValidity {
  @   predicate image_signature_dos (char *FileBuffer, UINT32 FileSize) =
  @     sizeof (EFI_IMAGE_DOS_HEADER) <= FileSize &&
  @     uint16_from_char (FileBuffer) == EFI_IMAGE_DOS_SIGNATURE;
  @
  @   predicate image_dos_sane (char *FileBuffer, UINT32 FileSize) =
  @     \let DosHdr = (EFI_IMAGE_DOS_HEADER *) FileBuffer;
  @     sizeof (EFI_IMAGE_DOS_HEADER) <= DosHdr->e_lfanew <= FileSize;
  @
  @   logic UINT32 image_exe_hdr_offset (char *FileBuffer, UINT32 FileSize) =
  @     image_signature_dos (FileBuffer, FileSize) ?
  @       \let DosHdr = (EFI_IMAGE_DOS_HEADER *) FileBuffer;
  @       DosHdr->e_lfanew : 0;
  @
  @   predicate image_signature_pe (char *FileBuffer, UINT32 ExeHdrOffset, integer FileSize) =
  @     pointer_max_aligned (FileBuffer) &&
  @     sizeof (EFI_IMAGE_NT_HEADERS_COMMON_HDR) + sizeof (UINT16) <= FileSize - ExeHdrOffset &&
  @     is_aligned_32 (ExeHdrOffset, AV_ALIGNOF (EFI_IMAGE_NT_HEADERS_COMMON_HDR)) &&
  @     uint32_from_char (FileBuffer + ExeHdrOffset) == EFI_IMAGE_NT_SIGNATURE;
  @ }
*/

/*@ predicate image_valid (char *FileBuffer, UINT32 FileSize) =
  @   (image_signature_dos (FileBuffer, FileSize) ==>
  @     image_dos_sane (FileBuffer, FileSize)) &&
  @   ((image_signature_te (FileBuffer, FileSize) &&
  @   image_te_valid (FileBuffer, FileSize)) ||
  @   (image_signature_pe (FileBuffer, image_exe_hdr_offset (FileBuffer, FileSize), FileSize) &&
  @   valid_pe (FileBuffer, image_exe_hdr_offset (FileBuffer, FileSize), FileSize)));
*/

/**
  Verify the TE, PE32, or PE32+ Image and initialise Context.

  Used offsets and ranges must be aligned and in the bounds of the raw file.
  Image Section Headers and basic Relocation information must be correct.

  @param[out] Context   The context describing the Image.
  @param[in]  FileSize  The size, in bytes, of Context->FileBuffer.

  @retval RETURN_SUCCESS  The file data is correct.
  @retval other           The file data is malformed.
**/
/*@ requires \valid(Context);
  @ requires \typeof(FileBuffer) <: \type(char *);
  @ requires pointer_max_aligned (FileBuffer);
  @ requires \valid((char *) FileBuffer + (0 .. FileSize - 1));
  @
  @ assigns *Context;
  @
  @ behavior dos_nvalid:
  @   assumes image_signature_dos ((char *) FileBuffer, FileSize) &&
  @           !image_dos_sane ((char *) FileBuffer, FileSize);
  @   ensures \result != RETURN_SUCCESS;
  @
  @ behavior sig_nvalid:
  @   assumes (image_signature_dos ((char *) FileBuffer, FileSize) ==>
  @             image_dos_sane ((char *) FileBuffer, FileSize)) &&
  @           !image_signature_te ((char *) FileBuffer, FileSize) &&
  @           !image_signature_pe ((char *) FileBuffer, image_exe_hdr_offset ((char *) FileBuffer, FileSize), FileSize);
  @   ensures \result != RETURN_SUCCESS;
  @
  @ behavior image_main_nvalid:
  @   assumes (image_signature_dos ((char *) FileBuffer, FileSize) ==>
  @             image_dos_sane ((char *) FileBuffer, FileSize)) &&
  @           ((image_signature_te ((char *) FileBuffer, FileSize) &&
  @           !image_te_valid ((char *) FileBuffer, FileSize)) ||
  @           (image_signature_pe ((char *) FileBuffer, image_exe_hdr_offset ((char *) FileBuffer, FileSize), FileSize) &&
  @           !valid_pe ((char *) FileBuffer, image_exe_hdr_offset ((char *) FileBuffer, FileSize), FileSize)));
  @   ensures \result != RETURN_SUCCESS;
  @
  @ behavior image_main_valid:
  @   assumes image_valid ((char *) FileBuffer, FileSize);
  @   ensures image_context_fields_correct (Context) &&
  @           image_context_hdr_valid (Context) &&
  @           image_context_file_char_valid (Context) &&
  @           image_context_reloc_info_sane (Context) &&
  @           image_context_sects_sane (Context, FileSize) &&
  @           image_sects_in_image (Context) &&
  @           image_datadirs_in_hdr (Context) &&
  @           Context->FileBuffer == FileBuffer &&
  @           image_context_FileBuffer_sane (Context) &&
  @           is_pow2_32 (Context->SectionAlignment) &&
  @           Context->AddressOfEntryPoint < Context->SizeOfImage &&
  @           0 < image_hdr_virtual_size (Context->SizeOfHeaders, Context->SectionAlignment) &&
  @           Context->SectionsOffset <= MAX_UINT32 &&
  @           0 < Context->NumberOfSections &&
  @           \let Sections         = image_context_get_sections (Context);
  @           \let NumberOfSections = Context->NumberOfSections;
  @           \valid (Sections + (0 .. NumberOfSections - 1)) &&
  @           Context->SizeOfImageDebugAdd == 0;
  @   ensures \result == RETURN_SUCCESS;
  @
  @ disjoint behaviors;
  @ complete behaviors;
*/
RETURN_STATUS
PeCoffInitializeContext (
  OUT PE_COFF_IMAGE_CONTEXT  *Context,
  IN  CONST VOID             *FileBuffer,
  IN  UINT32                 FileSize
  );

#endif // PE_COFF_INIT_H_
