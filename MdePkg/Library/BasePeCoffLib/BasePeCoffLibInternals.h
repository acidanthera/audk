/** @file
  Copyright (c) 2020, Marvin Häuser. All rights reserved.<BR>
  Copyright (c) 2020, Vitaly Cheptsov. All rights reserved.<BR>
  Copyright (c) 2020, ISP RAS. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-3-Clause
**/

#ifndef BASE_PECOFF_LIB_INTERNALS_H
#define BASE_PECOFF_LIB_INTERNALS_H

#include "Base.h"
#include <Library/DebugLib.h>
#include "AvMacros.h"
#include <IndustryStandard/PeCoffImage.h>
#include <Library/PeCoffLib.h>
#include "BaseOverflow.h"
#include "Unaligned.h"

#ifndef PRODUCTION
#include "Frama.h"
#else
#include <Library/BaseMemoryLib.h>
#endif

#define IS_ALIGNED(v, a)  (((v) & ((a) - 1U)) == 0U)
#define IS_POW2(v)        ((v) != 0 && ((v) & ((v) - 1U)) == 0)

/**
  Returns the type of a Base Relocation.

  @param[in] Relocation  The composite Base Relocation value.
**/
#define IMAGE_RELOC_TYPE(Relocation)    ((Relocation) >> 12U)

/**
  Returns the target offset of a Base Relocation.

  @param[in] Relocation  The composite Base Relocation value.
**/
#define IMAGE_RELOC_OFFSET(Relocation)  ((Relocation) & 0x0FFFU)

/**
  Returns whether the Image targets the UEFI Subsystem.

  @param[in] Subsystem  The Subsystem value from the Image Header.
**/
#define IMAGE_IS_EFI_SUBYSYSTEM(Subsystem) \
  ((Subsystem) >= EFI_IMAGE_SUBSYSTEM_EFI_APPLICATION && \
   (Subsystem) <= EFI_IMAGE_SUBSYSTEM_SAL_RUNTIME_DRIVER)

/*@ axiomatic ImageSections {
  @   logic integer image_hdr_raw_size (integer SizeOfHeaders, integer TeStrippedOffset) =
  @     SizeOfHeaders - TeStrippedOffset;
  @
  @   logic integer image_hdr_virtual_size (integer SizeOfHeaders, UINT32 SectionAlignment) =
  @     !PcdGetBool (PcdImageLoaderTolerantLoad) ?
  @       align_up (SizeOfHeaders, SectionAlignment) :
  @       SizeOfHeaders;
  @
  @   logic integer image_loaded_hdr_virtual_size (EFI_IMAGE_SECTION_HEADER *Sections, integer SizeOfHeaders, UINT32 SectionAlignment) =
  @     Sections[0].VirtualAddress == 0 ? 0 : image_hdr_virtual_size (SizeOfHeaders, SectionAlignment);
  @
  @   logic UINT32 image_sect_cpy_size (EFI_IMAGE_SECTION_HEADER *Section) =
  @     (UINT32) \min (Section->VirtualSize, Section->SizeOfRawData);
  @
  @   logic integer image_sect_cpy_top (EFI_IMAGE_SECTION_HEADER *Section) =
  @     Section->VirtualAddress + image_sect_cpy_size (Section);
  @
  @   logic integer image_sect_top (EFI_IMAGE_SECTION_HEADER *Section) =
  @     Section->VirtualAddress + Section->VirtualSize;
  @
  @   predicate image_sects_in_file_bounds (EFI_IMAGE_SECTION_HEADER *Sections, UINT16 NumberOfSections, integer TeStrippedOffset, UINT32 FileSize) =
  @     \forall integer i; 0 <= i < NumberOfSections ==>
  @       0 < Sections[i].SizeOfRawData ==>
  @         TeStrippedOffset <= Sections[i].PointerToRawData &&
  @         Sections[i].PointerToRawData + Sections[i].SizeOfRawData <= MAX_UINT32 &&
  @         (Sections[i].PointerToRawData - TeStrippedOffset) + Sections[i].SizeOfRawData <= FileSize;
  @
  @   logic integer image_sect_correct_address (EFI_IMAGE_SECTION_HEADER *Sections, integer SectIndex, integer SizeOfHeaders, UINT32 SectionAlignment) =
  @     SectIndex == 0 ?
  @       image_loaded_hdr_virtual_size (Sections, SizeOfHeaders, SectionAlignment) :
  @       align_up (image_sect_top (Sections + SectIndex - 1), SectionAlignment);
  @
  @   predicate image_sects_correct_addresses (EFI_IMAGE_SECTION_HEADER *Sections, UINT16 NumberOfSections, integer SizeOfHeaders, UINT32 SectionAlignment) =
  @     \forall integer i; 0 <= i < NumberOfSections ==>
  @       Sections[i].VirtualAddress == image_sect_correct_address (Sections, i, SizeOfHeaders, SectionAlignment);
  @
  @   predicate image_sect_disjunct_sorted (EFI_IMAGE_SECTION_HEADER *Sections, integer SectIndex) =
  @     \forall integer j; 0 <= j < SectIndex ==>
  @       image_sect_top (Sections + j) <= Sections[SectIndex].VirtualAddress;
  @
  @   predicate image_sects_disjunct_sorted (EFI_IMAGE_SECTION_HEADER *Sections, UINT16 NumberOfSections, integer SizeOfHeaders, UINT32 SectionAlignment) =
  @     (\forall integer i; 0 <= i < NumberOfSections ==>
  @       image_loaded_hdr_virtual_size (Sections, SizeOfHeaders, SectionAlignment) <= Sections[i].VirtualAddress) &&
  @     (\forall integer i; 0 <= i < NumberOfSections ==>
  @       image_sect_disjunct_sorted (Sections, i));
  @
  @   predicate image_sects_sane (EFI_IMAGE_SECTION_HEADER *Sections, UINT16 NumberOfSections, integer SizeOfHeaders, UINT32 SectionAlignment, integer TeStrippedOffset, UINT32 FileSize, integer ImageType) =
  @     image_sects_in_file_bounds (Sections, NumberOfSections, TeStrippedOffset, FileSize) &&
  @     (!PcdGetBool (PcdImageLoaderTolerantLoad) ==>
  @       image_sects_correct_addresses (Sections, NumberOfSections, SizeOfHeaders, SectionAlignment)) &&
  @     image_sects_disjunct_sorted (Sections, NumberOfSections, SizeOfHeaders, SectionAlignment) &&
  @     image_sect_top (Sections + NumberOfSections - 1) <= MAX_UINT32 &&
  @     (!PcdGetBool (PcdImageLoaderTolerantLoad) ==>
  @       align_up (image_sect_top (Sections + NumberOfSections - 1), SectionAlignment) <= MAX_UINT32) &&
  @     (ImageType == ImageTypeTe ==> Sections[0].VirtualAddress != 0);
  @ }
*/

/*@ axiomatic ImageValidty {
  @   predicate image_is_efi_subsystem (UINT16 Subsystem) =
  @     Subsystem == EFI_IMAGE_SUBSYSTEM_EFI_APPLICATION ||
  @     Subsystem == EFI_IMAGE_SUBSYSTEM_EFI_BOOT_SERVICE_DRIVER ||
  @     Subsystem == EFI_IMAGE_SUBSYSTEM_EFI_RUNTIME_DRIVER ||
  @     Subsystem == EFI_IMAGE_SUBSYSTEM_SAL_RUNTIME_DRIVER;
  @
  @   lemma image_is_efi_subsystem_eq:
  @     \forall UINT16 Subsystem;
  @       image_is_efi_subsystem (Subsystem) <==> IMAGE_IS_EFI_SUBYSYSTEM (Subsystem);
  @ }
*/

/*@ axiomatic TeImage {
  @   logic EFI_TE_IMAGE_HEADER *image_te_get_hdr{L} (char *Image) =
  @     (EFI_TE_IMAGE_HEADER *) (\at(Image, L) + 0);
  @
  @   logic integer image_te_get_sections_offset (char *Image) =
  @     sizeof (EFI_TE_IMAGE_HEADER);
  @
  @   logic EFI_IMAGE_SECTION_HEADER *image_te_get_sections{L} (char *Image) =
  @     (EFI_IMAGE_SECTION_HEADER *) (\at(Image, L) + image_te_get_sections_offset (\at(Image, L)));
  @
  @   predicate image_te_sections_validity (char *Image) =
  @     \let TeHdr    = image_te_get_hdr (Image);
  @     \let Sections = image_te_get_sections (Image);
  @     pointer_aligned (Image + image_te_get_sections_offset (Image), AV_ALIGNOF (EFI_IMAGE_SECTION_HEADER)) ==>
  @       \valid (Sections + (0 .. TeHdr->NumberOfSections - 1));
  @
  @   predicate image_te_datadirs_valid (char *Image) =
  @     \true;
  @
  @   predicate image_te_reloc_dir_exists (char *Image) =
  @     \true;
  @
  @   logic integer image_te_SizeOfHeaders (char *Image) =
  @     \let TeHdr = image_te_get_hdr (Image);
  @     TeHdr->StrippedSize + TeHdr->NumberOfSections * sizeof (EFI_IMAGE_SECTION_HEADER);
  @
  @   logic integer image_te_SizeOfImage (char *Image) =
  @     \let TeHdr    = image_te_get_hdr (Image);
  @     \let Sections = image_te_get_sections (Image);
  @     !PcdGetBool (PcdImageLoaderTolerantLoad) ?
  @       align_up (image_sect_top (Sections + TeHdr->NumberOfSections - 1), BASE_4KB) :
  @       image_sect_top (Sections + TeHdr->NumberOfSections - 1);
  @
  @   logic EFI_IMAGE_DATA_DIRECTORY *image_te_get_reloc_dir{L} (char *Image) =
  @     \let TeHdr = image_te_get_hdr (\at(Image, L));
  @     TeHdr->DataDirectory + 0;
  @
  @   predicate image_te_debug_dir_exists (char *Image) =
  @     \true;
  @
  @   logic EFI_IMAGE_DATA_DIRECTORY *image_te_get_debug_dir{L} (char *Image) =
  @     \let TeHdr = image_te_get_hdr (\at(Image, L));
  @     TeHdr->DataDirectory + 1;
  @
  @   predicate image_signature_te (char *FileBuffer, UINT32 FileSize) =
  @     pointer_max_aligned (FileBuffer) &&
  @     sizeof (EFI_TE_IMAGE_HEADER) <= FileSize &&
  @     uint16_from_char (FileBuffer) == EFI_TE_IMAGE_HEADER_SIGNATURE;
  @
  @   predicate image_te_file_hdrs_validity (char *FileBuffer, UINT32 FileSize) =
  @     \let TeHdr = image_te_get_hdr (FileBuffer);
  @     (image_signature_te (FileBuffer, FileSize) ==>
  @       \valid (TeHdr)) &&
  @     (image_signature_te (FileBuffer, FileSize) <==>
  @       (\let SectsOffset = image_te_get_sections_offset (FileBuffer);
  @       SectsOffset + TeHdr->NumberOfSections * sizeof (EFI_IMAGE_SECTION_HEADER) <= FileSize ==>
  @         image_te_sections_validity (FileBuffer)));
  @ }
*/

/*@ axiomatic PeCommonImage {
  @   logic integer image_pecommon_get_sections_offset (EFI_IMAGE_NT_HEADERS_COMMON_HDR *PeCommonHdr, UINT32 ExeHdrOffset) =
  @     ExeHdrOffset + sizeof (EFI_IMAGE_NT_HEADERS_COMMON_HDR) + PeCommonHdr->FileHeader.SizeOfOptionalHeader;
  @ }
*/

/*@ axiomatic Pe32Image {
  @   logic EFI_IMAGE_NT_HEADERS32 *image_pe32_get_hdr{L} (char *Image, UINT32 ExeHdrOffset) =
  @     (EFI_IMAGE_NT_HEADERS32 *) (\at(Image, L) + ExeHdrOffset);
  @
  @   logic EFI_IMAGE_SECTION_HEADER *image_pe32_get_sections{L} (char *Image, UINT32 ExeHdrOffset) =
  @     \let Pe32Hdr = image_pe32_get_hdr (Image, ExeHdrOffset);
  @     (EFI_IMAGE_SECTION_HEADER *) (\at(Image, L) + image_pecommon_get_sections_offset (&Pe32Hdr->CommonHeader, ExeHdrOffset));
  @
  @   predicate image_pe32_sections_validity (char *Image, UINT32 ExeHdrOffset) =
  @     \let Pe32Hdr  = image_pe32_get_hdr (Image, ExeHdrOffset);
  @     \let Sections = image_pe32_get_sections (Image, ExeHdrOffset);
  @     pointer_aligned (Image + image_pecommon_get_sections_offset (&Pe32Hdr->CommonHeader, ExeHdrOffset), AV_ALIGNOF (EFI_IMAGE_SECTION_HEADER)) ==>
  @       \valid (Sections + (0 .. Pe32Hdr->CommonHeader.FileHeader.NumberOfSections - 1));
  @
  @   logic integer image_pe32_get_min_SizeOfOptionalHeader (char *Image, UINT32 ExeHdrOffset) =
  @     \let Pe32Hdr = image_pe32_get_hdr (Image, ExeHdrOffset);
  @     sizeof (EFI_IMAGE_NT_HEADERS32) - sizeof (EFI_IMAGE_NT_HEADERS_COMMON_HDR) + Pe32Hdr->NumberOfRvaAndSizes * sizeof (EFI_IMAGE_DATA_DIRECTORY);
  @
  @   logic integer image_pe32_get_min_SizeOfHeaders (char *Image, UINT32 ExeHdrOffset) =
  @     \let Pe32Hdr = image_pe32_get_hdr (Image, ExeHdrOffset);
  @     image_pecommon_get_sections_offset (&Pe32Hdr->CommonHeader, ExeHdrOffset) + Pe32Hdr->CommonHeader.FileHeader.NumberOfSections * sizeof (EFI_IMAGE_SECTION_HEADER);
  @
  @   logic integer image_pe32_get_min_SizeOfImage (char *Image, UINT32 ExeHdrOffset) =
  @     \let Pe32Hdr  = image_pe32_get_hdr (Image, ExeHdrOffset);
  @     \let Sections = image_pe32_get_sections (Image, ExeHdrOffset);
  @     !PcdGetBool (PcdImageLoaderTolerantLoad) ?
  @       align_up (image_sect_top (Sections + Pe32Hdr->CommonHeader.FileHeader.NumberOfSections - 1), Pe32Hdr->SectionAlignment) :
  @       image_sect_top (Sections + Pe32Hdr->CommonHeader.FileHeader.NumberOfSections - 1);
  @
  @   predicate image_pe32_datadirs_valid (char *Image, UINT32 ExeHdrOffset) =
  @     \let Pe32Hdr = image_pe32_get_hdr (Image, ExeHdrOffset);
  @     \valid(Pe32Hdr->DataDirectory + (0 .. Pe32Hdr->NumberOfRvaAndSizes - 1));
  @
  @   predicate image_pe32_reloc_dir_exists (char *Image, UINT32 ExeHdrOffset) =
  @     \let Pe32Hdr = image_pe32_get_hdr (Image, ExeHdrOffset);
  @     EFI_IMAGE_DIRECTORY_ENTRY_BASERELOC < Pe32Hdr->NumberOfRvaAndSizes;
  @
  @   logic EFI_IMAGE_DATA_DIRECTORY *image_pe32_get_reloc_dir (char *Image, UINT32 ExeHdrOffset) =
  @     \let Pe32Hdr = image_pe32_get_hdr (Image, ExeHdrOffset);
  @     Pe32Hdr->DataDirectory + EFI_IMAGE_DIRECTORY_ENTRY_BASERELOC;
  @
  @   predicate image_pe32_debug_dir_exists (char *Image, UINT32 ExeHdrOffset) =
  @     \let Pe32Hdr = image_pe32_get_hdr (Image, ExeHdrOffset);
  @     EFI_IMAGE_DIRECTORY_ENTRY_DEBUG < Pe32Hdr->NumberOfRvaAndSizes;
  @
  @   logic EFI_IMAGE_DATA_DIRECTORY *image_pe32_get_debug_dir (char *Image, UINT32 ExeHdrOffset) =
  @     \let Pe32Hdr = image_pe32_get_hdr (Image, ExeHdrOffset);
  @     Pe32Hdr->DataDirectory + EFI_IMAGE_DIRECTORY_ENTRY_DEBUG;
  @
  @   predicate image_signature_pe32 (char *FileBuffer, UINT32 ExeHdrOffset, UINT32 FileSize) =
  @     pointer_max_aligned (FileBuffer) &&
  @     sizeof (EFI_IMAGE_NT_HEADERS32) <= FileSize - ExeHdrOffset &&
  @     is_aligned_32 (ExeHdrOffset, AV_ALIGNOF (EFI_IMAGE_NT_HEADERS32)) &&
  @     uint32_from_char (FileBuffer + ExeHdrOffset) == EFI_IMAGE_NT_SIGNATURE &&
  @     uint16_from_char (FileBuffer + ExeHdrOffset + sizeof (EFI_IMAGE_NT_HEADERS_COMMON_HDR)) == EFI_IMAGE_NT_OPTIONAL_HDR32_MAGIC;
  @
  @   predicate image_pe32_file_hdrs_validity (char *FileBuffer, UINT32 ExeHdrOffset, UINT32 FileSize) =
  @     \let Pe32Hdr = image_pe32_get_hdr (FileBuffer, ExeHdrOffset);
  @     (image_signature_pe32 (FileBuffer, ExeHdrOffset, FileSize) && pointer_aligned (FileBuffer + ExeHdrOffset, AV_ALIGNOF (EFI_IMAGE_NT_HEADERS32)) ==>
  @       \valid (Pe32Hdr)) &&
  @     (image_signature_pe32 (FileBuffer, ExeHdrOffset, FileSize) <==>
  @       (\let SectsOffset = image_pecommon_get_sections_offset (&Pe32Hdr->CommonHeader, ExeHdrOffset);
  @       image_pe32_get_min_SizeOfOptionalHeader (FileBuffer, ExeHdrOffset) <= Pe32Hdr->CommonHeader.FileHeader.SizeOfOptionalHeader &&
  @       SectsOffset + Pe32Hdr->CommonHeader.FileHeader.NumberOfSections * sizeof (EFI_IMAGE_SECTION_HEADER) <= FileSize ==>
  @         image_pe32_datadirs_valid (FileBuffer, ExeHdrOffset) &&
  @         image_pe32_sections_validity (FileBuffer, ExeHdrOffset)));
  @ }
*/

/*@ axiomatic Pe32PlusImage {
  @   logic EFI_IMAGE_NT_HEADERS64 *image_pe32plus_get_hdr{L} (char *Image, UINT32 ExeHdrOffset) =
  @     (EFI_IMAGE_NT_HEADERS64 *) (\at(Image, L) + ExeHdrOffset);
  @
  @   logic integer image_pe32plus_get_sections_offset (char *Image, UINT32 ExeHdrOffset) =
  @     \let Pe32PlusHdr = image_pe32plus_get_hdr (Image, ExeHdrOffset);
  @     image_pecommon_get_sections_offset (&Pe32PlusHdr->CommonHeader, ExeHdrOffset);
  @
  @   logic EFI_IMAGE_SECTION_HEADER *image_pe32plus_get_sections{L} (char *Image, UINT32 ExeHdrOffset) =
  @     (EFI_IMAGE_SECTION_HEADER *) (\at(Image, L) + image_pe32plus_get_sections_offset (Image, ExeHdrOffset));
  @
  @   predicate image_pe32plus_sections_validity (char *Image, UINT32 ExeHdrOffset) =
  @     \let Pe32PlusHdr = image_pe32plus_get_hdr (Image, ExeHdrOffset);
  @     \let Sections    = image_pe32plus_get_sections (Image, ExeHdrOffset);
  @     pointer_aligned (Image + image_pe32plus_get_sections_offset (Image, ExeHdrOffset), AV_ALIGNOF (EFI_IMAGE_SECTION_HEADER)) ==>
  @       \valid (Sections + (0 .. Pe32PlusHdr->CommonHeader.FileHeader.NumberOfSections - 1));
  @
  @   logic integer image_pe32plus_get_min_SizeOfOptionalHeader (char *Image, UINT32 ExeHdrOffset) =
  @     \let Pe32PlusHdr = image_pe32plus_get_hdr (Image, ExeHdrOffset);
  @     sizeof (EFI_IMAGE_NT_HEADERS64) - sizeof (EFI_IMAGE_NT_HEADERS_COMMON_HDR) + Pe32PlusHdr->NumberOfRvaAndSizes * sizeof (EFI_IMAGE_DATA_DIRECTORY);
  @
  @   logic integer image_pe32plus_get_min_SizeOfHeaders (char *Image, UINT32 ExeHdrOffset) =
  @     \let Pe32PlusHdr = image_pe32plus_get_hdr (Image, ExeHdrOffset);
  @     image_pe32plus_get_sections_offset (Image, ExeHdrOffset) + Pe32PlusHdr->CommonHeader.FileHeader.NumberOfSections * sizeof (EFI_IMAGE_SECTION_HEADER);
  @
  @   logic integer image_pe32plus_get_min_SizeOfImage (char *Image, UINT32 ExeHdrOffset) =
  @     \let Pe32PlusHdr = image_pe32plus_get_hdr (Image, ExeHdrOffset);
  @     \let Sections    = image_pe32plus_get_sections (Image, ExeHdrOffset);
  @     !PcdGetBool (PcdImageLoaderTolerantLoad) ?
  @       align_up (image_sect_top (Sections + Pe32PlusHdr->CommonHeader.FileHeader.NumberOfSections - 1), Pe32PlusHdr->SectionAlignment) :
  @       image_sect_top (Sections + Pe32PlusHdr->CommonHeader.FileHeader.NumberOfSections - 1);
  @
  @   predicate image_pe32plus_datadirs_valid (char *Image, UINT32 ExeHdrOffset) =
  @     \let Pe32PlusHdr = image_pe32plus_get_hdr (Image, ExeHdrOffset);
  @     \valid(Pe32PlusHdr->DataDirectory + (0 .. Pe32PlusHdr->NumberOfRvaAndSizes - 1));
  @
  @   predicate image_pe32plus_reloc_dir_exists (char *Image, UINT32 ExeHdrOffset) =
  @     \let Pe32PlusHdr = image_pe32plus_get_hdr (Image, ExeHdrOffset);
  @     EFI_IMAGE_DIRECTORY_ENTRY_BASERELOC < Pe32PlusHdr->NumberOfRvaAndSizes;
  @
  @   logic EFI_IMAGE_DATA_DIRECTORY *image_pe32plus_get_reloc_dir (char *Image, UINT32 ExeHdrOffset) =
  @     \let Pe32PlusHdr = image_pe32plus_get_hdr (Image, ExeHdrOffset);
  @     Pe32PlusHdr->DataDirectory + EFI_IMAGE_DIRECTORY_ENTRY_BASERELOC;
  @
  @   predicate image_pe32plus_debug_dir_exists (char *Image, UINT32 ExeHdrOffset) =
  @     \let Pe32PlusHdr = image_pe32plus_get_hdr (Image, ExeHdrOffset);
  @     EFI_IMAGE_DIRECTORY_ENTRY_DEBUG < Pe32PlusHdr->NumberOfRvaAndSizes;
  @
  @   logic EFI_IMAGE_DATA_DIRECTORY *image_pe32plus_get_debug_dir (char *Image, UINT32 ExeHdrOffset) =
  @     \let Pe32PlusHdr = image_pe32plus_get_hdr (Image, ExeHdrOffset);
  @     Pe32PlusHdr->DataDirectory + EFI_IMAGE_DIRECTORY_ENTRY_DEBUG;
  @
  @   predicate image_signature_pe32plus (char *FileBuffer, UINT32 ExeHdrOffset, UINT32 FileSize) =
  @     sizeof (EFI_IMAGE_NT_HEADERS64) <= FileSize - ExeHdrOffset &&
  @     uint32_from_char (FileBuffer + ExeHdrOffset) == EFI_IMAGE_NT_SIGNATURE &&
  @     uint16_from_char (FileBuffer + ExeHdrOffset + sizeof (EFI_IMAGE_NT_HEADERS_COMMON_HDR)) == EFI_IMAGE_NT_OPTIONAL_HDR64_MAGIC;
  @
  @   predicate image_pe32plus_file_hdrs_validity (char *FileBuffer, UINT32 ExeHdrOffset, UINT32 FileSize) =
  @     \let Pe32PlusHdr = image_pe32plus_get_hdr (FileBuffer, ExeHdrOffset);
  @     (image_signature_pe32plus (FileBuffer, ExeHdrOffset, FileSize) && pointer_aligned (FileBuffer + ExeHdrOffset, AV_ALIGNOF (EFI_IMAGE_NT_HEADERS64)) ==>
  @       \valid (Pe32PlusHdr)) &&
  @     (image_signature_pe32plus (FileBuffer, ExeHdrOffset, FileSize) <==>
  @       (\let SectsOffset = image_pe32plus_get_sections_offset (FileBuffer, ExeHdrOffset);
  @       image_pe32plus_get_min_SizeOfOptionalHeader (FileBuffer, ExeHdrOffset) <= Pe32PlusHdr->CommonHeader.FileHeader.SizeOfOptionalHeader &&
  @       SectsOffset + Pe32PlusHdr->CommonHeader.FileHeader.NumberOfSections * sizeof (EFI_IMAGE_SECTION_HEADER) <= FileSize ==>
  @         image_pe32plus_datadirs_valid (FileBuffer, ExeHdrOffset) &&
  @         image_pe32plus_sections_validity (FileBuffer, ExeHdrOffset)));
  @ }
*/

/*@ axiomatic ImageLoaderContextValidity {
  @   predicate image_context_type_valid (PE_COFF_IMAGE_CONTEXT *Context) =
  @     Context->ImageType == ImageTypeTe ||
  @     Context->ImageType == ImageTypePe32 ||
  @     Context->ImageType == ImageTypePe32Plus;
  @
  @   predicate image_context_hdr_valid (PE_COFF_IMAGE_CONTEXT *Context) =
  @     (Context->ImageType == ImageTypeTe ==>
  @       \let TeHdr = image_te_get_hdr ((char *) Context->FileBuffer);
  @       \valid(TeHdr)) &&
  @     (Context->ImageType == ImageTypePe32 ==>
  @       \let Pe32Hdr = image_pe32_get_hdr ((char *) Context->FileBuffer, Context->ExeHdrOffset);
  @       \valid(Pe32Hdr)) &&
  @     (Context->ImageType == ImageTypePe32Plus ==>
  @       \let Pe32PlusHdr = image_pe32plus_get_hdr ((char *) Context->FileBuffer, Context->ExeHdrOffset);
  @       \valid(Pe32PlusHdr));
  @
  @   logic integer image_context_get_sections_offset (PE_COFF_IMAGE_CONTEXT *Context) =
  @     (Context->ImageType == ImageTypeTe ?
  @       image_te_get_sections_offset ((char *) Context->FileBuffer) :
  @     (Context->ImageType == ImageTypePe32 ?
  @       \let Pe32Hdr = image_pe32_get_hdr ((char *) Context->FileBuffer, Context->ExeHdrOffset);
  @       image_pecommon_get_sections_offset (&Pe32Hdr->CommonHeader, Context->ExeHdrOffset) :
  @     (Context->ImageType == ImageTypePe32Plus ?
  @       \let Pe32PlusHdr = image_pe32plus_get_hdr ((char *) Context->FileBuffer, Context->ExeHdrOffset);
  @       image_pecommon_get_sections_offset (&Pe32PlusHdr->CommonHeader, Context->ExeHdrOffset) :
  @     0)));
  @
  @   logic EFI_IMAGE_SECTION_HEADER *image_context_get_sections (PE_COFF_IMAGE_CONTEXT *Context) =
  @     (EFI_IMAGE_SECTION_HEADER *) ((char *) Context->FileBuffer + Context->SectionsOffset);
  @
  @   logic UINT16 image_context_get_sections_num (PE_COFF_IMAGE_CONTEXT *Context) =
  @     (Context->ImageType == ImageTypeTe ?
  @       \let TeHdr = image_te_get_hdr ((char *) Context->FileBuffer);
  @       (UINT16) TeHdr->NumberOfSections :
  @     (Context->ImageType == ImageTypePe32 ?
  @       \let Pe32Hdr = image_pe32_get_hdr ((char *) Context->FileBuffer, Context->ExeHdrOffset);
  @       Pe32Hdr->CommonHeader.FileHeader.NumberOfSections :
  @     (Context->ImageType == ImageTypePe32Plus ?
  @       \let Pe32PlusHdr = image_pe32plus_get_hdr ((char *) Context->FileBuffer, Context->ExeHdrOffset);
  @       Pe32PlusHdr->CommonHeader.FileHeader.NumberOfSections :
  @     0)));
  @
  @   predicate image_context_sects_sane (PE_COFF_IMAGE_CONTEXT *Context, UINT32 FileSize) =
  @     image_sects_sane (
  @       image_context_get_sections (Context),
  @       Context->NumberOfSections,
  @       Context->SizeOfHeaders,
  @       Context->SectionAlignment,
  @       Context->TeStrippedOffset,
  @       FileSize,
  @       Context->ImageType
  @       );
  @
  @   predicate image_sects_in_image (PE_COFF_IMAGE_CONTEXT *Context) =
  @     \let Sections         = image_context_get_sections (Context);
  @     \let NumberOfSections = Context->NumberOfSections;
  @     \forall integer i; 0 <= i < NumberOfSections ==>
  @       image_sect_top (Sections + i) <= Context->SizeOfImage;
  @
  @   predicate image_datadirs_in_hdr (PE_COFF_IMAGE_CONTEXT *Context) =
  @     (Context->ImageType == ImageTypePe32 ==>
  @       \let Pe32Hdr = image_pe32_get_hdr ((char *) Context->FileBuffer, Context->ExeHdrOffset);
  @       Context->ExeHdrOffset + sizeof (EFI_IMAGE_NT_HEADERS32) + Pe32Hdr->NumberOfRvaAndSizes * sizeof (EFI_IMAGE_DATA_DIRECTORY) <= Context->SizeOfHeaders) &&
  @     (Context->ImageType == ImageTypePe32Plus ==>
  @       \let Pe32PlusHdr = image_pe32plus_get_hdr ((char *) Context->FileBuffer, Context->ExeHdrOffset);
  @       Context->ExeHdrOffset + sizeof (EFI_IMAGE_NT_HEADERS64) + Pe32PlusHdr->NumberOfRvaAndSizes * sizeof (EFI_IMAGE_DATA_DIRECTORY) <= Context->SizeOfHeaders);
  @
  @   logic integer image_context_get_loaded_hdr_raw_size (PE_COFF_IMAGE_CONTEXT *Context) =
  @     \let Sections = image_context_get_sections (Context);
  @     Sections[0].VirtualAddress != 0 && PcdGetBool (PcdImageLoaderLoadHeader) ?
  @       image_hdr_raw_size (Context->SizeOfHeaders, Context->TeStrippedOffset) :
  @       0;
  @
  @   logic integer image_context_get_loaded_hdr_virtual_size (PE_COFF_IMAGE_CONTEXT *Context) =
  @     \let Sections = image_context_get_sections (Context);
  @     image_loaded_hdr_virtual_size (Sections, Context->SizeOfHeaders, Context->SectionAlignment);
  @
  @   predicate image_context_hdr_datadirs_valid (PE_COFF_IMAGE_CONTEXT *Context) =
  @     (Context->ImageType == ImageTypeTe ==>
  @       image_te_datadirs_valid ((char *) Context->FileBuffer)) &&
  @     (Context->ImageType == ImageTypePe32 ==>
  @       image_pe32_datadirs_valid ((char *) Context->FileBuffer, Context->ExeHdrOffset)) &&
  @     (Context->ImageType == ImageTypePe32Plus ==>
  @       image_pe32plus_datadirs_valid ((char *) Context->FileBuffer, Context->ExeHdrOffset));
  @
  @   predicate image_context_reloc_dir_exists (PE_COFF_IMAGE_CONTEXT *Context) =
  @     (Context->ImageType == ImageTypeTe ==>
  @       image_te_reloc_dir_exists ((char *) Context->FileBuffer)) &&
  @     (Context->ImageType == ImageTypePe32 ==>
  @       image_pe32_reloc_dir_exists ((char *) Context->FileBuffer, Context->ExeHdrOffset)) &&
  @     (Context->ImageType == ImageTypePe32Plus ==>
  @       image_pe32plus_reloc_dir_exists ((char *) Context->FileBuffer, Context->ExeHdrOffset));
  @
  @   logic EFI_IMAGE_DATA_DIRECTORY *image_context_get_reloc_dir (PE_COFF_IMAGE_CONTEXT *Context) =
  @     Context->ImageType == ImageTypeTe ?
  @       image_te_get_reloc_dir ((char *) Context->FileBuffer) :
  @     (Context->ImageType == ImageTypePe32 ?
  @       image_pe32_get_reloc_dir ((char *) Context->FileBuffer, Context->ExeHdrOffset) :
  @     (Context->ImageType == ImageTypePe32Plus ?
  @       image_pe32plus_get_reloc_dir ((char *) Context->FileBuffer, Context->ExeHdrOffset) :
  @     (EFI_IMAGE_DATA_DIRECTORY *) \null));
  @
  @   predicate image_base_sane (UINT64 ImageBase, UINT32 SectionAlignment) =
  @     is_aligned_64 (ImageBase, SectionAlignment);
  @
  @   predicate image_reloc_dir_sane (UINT32 RelocDirRva, UINT32 RelocDirSize, BOOLEAN RelocsStripped, integer StartAddress, integer SizeOfImage) =
  @     is_aligned_32 (RelocDirRva, AV_ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK)) &&
  @     StartAddress <= RelocDirRva &&
  @     sizeof (EFI_IMAGE_BASE_RELOCATION_BLOCK) <= RelocDirSize &&
  @     RelocDirRva + RelocDirSize <= SizeOfImage;
  @
  @   predicate image_reloc_info_sane (UINT32 RelocDirRva, UINT32 RelocDirSize, BOOLEAN RelocsStripped, integer StartAddress, integer SizeOfHeaders, integer SizeOfImage, UINT64 ImageBase, UINT32 SectionAlignment, UINT16 Subsystem) =
  @     image_base_sane (ImageBase, SectionAlignment) &&
  @     (!RelocsStripped ==>
  @       image_reloc_dir_sane (RelocDirRva, RelocDirSize, RelocsStripped, StartAddress, SizeOfImage));
  @
  @   predicate image_context_reloc_info_sane (PE_COFF_IMAGE_CONTEXT *Context) =
  @     \let Sections     = image_context_get_sections (Context);
  @     \let StartAddress = image_loaded_hdr_virtual_size (Sections, Context->SizeOfHeaders, Context->SectionAlignment);
  @     image_reloc_info_sane (
  @       Context->RelocDirRva,
  @       Context->RelocDirSize,
  @       Context->RelocsStripped,
  @       StartAddress,
  @       Context->SizeOfHeaders,
  @       Context->SizeOfImage,
  @       Context->ImageBase,
  @       Context->SectionAlignment,
  @       Context->Subsystem
  @       );
  @
  @   predicate image_context_debug_dir_exists (PE_COFF_IMAGE_CONTEXT *Context) =
  @     (Context->ImageType == ImageTypeTe ==>
  @       image_te_debug_dir_exists ((char *) Context->FileBuffer)) &&
  @     (Context->ImageType == ImageTypePe32 ==>
  @       image_pe32_debug_dir_exists ((char *) Context->FileBuffer, Context->ExeHdrOffset)) &&
  @     (Context->ImageType == ImageTypePe32Plus ==>
  @       image_pe32plus_debug_dir_exists ((char *) Context->FileBuffer, Context->ExeHdrOffset));
  @
  @   logic EFI_IMAGE_DATA_DIRECTORY *image_context_get_debug_dir (PE_COFF_IMAGE_CONTEXT *Context) =
  @     Context->ImageType == ImageTypeTe ?
  @       image_te_get_debug_dir ((char *) Context->FileBuffer) :
  @     (Context->ImageType == ImageTypePe32 ?
  @       image_pe32_get_debug_dir ((char *) Context->FileBuffer, Context->ExeHdrOffset) :
  @     (Context->ImageType == ImageTypePe32Plus ?
  @       image_pe32plus_get_debug_dir ((char *) Context->FileBuffer, Context->ExeHdrOffset) :
  @     (EFI_IMAGE_DATA_DIRECTORY *) \null));
  @
  @   predicate image_pe_common_relocs_stripped (EFI_IMAGE_NT_HEADERS_COMMON_HDR *PeCommonHdr) =
  @     (PeCommonHdr->FileHeader.Characteristics & EFI_IMAGE_FILE_RELOCS_STRIPPED) != 0;
  @
  @   predicate image_context_fields_correct_pe_common (PE_COFF_IMAGE_CONTEXT *Context, EFI_IMAGE_NT_HEADERS_COMMON_HDR *PeCommonHdr) =
  @     \let RelocDir       = image_context_get_reloc_dir (Context);
  @     \let RelocsStripped = (BOOLEAN) (image_pe_common_relocs_stripped (PeCommonHdr) ? TRUE : FALSE);
  @     Context->TeStrippedOffset == 0 &&
  @     Context->SectionsOffset   == image_pecommon_get_sections_offset (PeCommonHdr, Context->ExeHdrOffset) &&
  @     Context->NumberOfSections == PeCommonHdr->FileHeader.NumberOfSections &&
  @     Context->Machine          == PeCommonHdr->FileHeader.Machine &&
  @     Context->RelocsStripped   == RelocsStripped &&
  @     Context->RelocDirRva      == (image_context_reloc_dir_exists (Context) ? RelocDir->VirtualAddress : 0) &&
  @     Context->RelocDirSize     == (image_context_reloc_dir_exists (Context) ? RelocDir->Size : 0);
  @
  @   predicate image_context_fields_correct_pe32_opt (PE_COFF_IMAGE_CONTEXT *Context) =
  @     \let Pe32Hdr  = image_pe32_get_hdr ((char *) Context->FileBuffer, Context->ExeHdrOffset);
  @     \let Sections = image_pe32_get_sections ((char *) Context->FileBuffer, Context->ExeHdrOffset);
  @     Context->AddressOfEntryPoint == Pe32Hdr->AddressOfEntryPoint &&
  @     Context->ImageBase           == Pe32Hdr->ImageBase &&
  @     Context->Subsystem           == Pe32Hdr->Subsystem &&
  @     Context->SectionAlignment    == Pe32Hdr->SectionAlignment &&
  @     Context->SizeOfHeaders       == Pe32Hdr->SizeOfHeaders &&
  @     Context->SizeOfImage         == Pe32Hdr->SizeOfImage;
  @
  @   predicate image_context_fields_correct_pe32plus_opt (PE_COFF_IMAGE_CONTEXT *Context) =
  @     \let Pe32PlusHdr = image_pe32plus_get_hdr ((char *) Context->FileBuffer, Context->ExeHdrOffset);
  @     \let Sections    = image_pe32plus_get_sections ((char *) Context->FileBuffer, Context->ExeHdrOffset);
  @     Context->AddressOfEntryPoint == Pe32PlusHdr->AddressOfEntryPoint &&
  @     Context->ImageBase           == Pe32PlusHdr->ImageBase &&
  @     Context->Subsystem           == Pe32PlusHdr->Subsystem &&
  @     Context->SectionAlignment    == Pe32PlusHdr->SectionAlignment &&
  @     Context->SizeOfHeaders       == Pe32PlusHdr->SizeOfHeaders &&
  @     Context->SizeOfImage         == Pe32PlusHdr->SizeOfImage;
  @
  @   predicate image_context_fields_correct_pe32 (PE_COFF_IMAGE_CONTEXT *Context) =
  @     \let Pe32Hdr = image_pe32_get_hdr ((char *) Context->FileBuffer, Context->ExeHdrOffset);
  @     image_context_fields_correct_pe_common (Context, &Pe32Hdr->CommonHeader) &&
  @     image_context_fields_correct_pe32_opt (Context);
  @
  @   predicate image_context_fields_correct_pe32plus (PE_COFF_IMAGE_CONTEXT *Context) =
  @     \let Pe32PlusHdr = image_pe32plus_get_hdr ((char *) Context->FileBuffer, Context->ExeHdrOffset);
  @     image_context_fields_correct_pe_common (Context, &Pe32PlusHdr->CommonHeader) &&
  @     image_context_fields_correct_pe32plus_opt (Context);
  @
  @   predicate image_context_fields_correct (PE_COFF_IMAGE_CONTEXT *Context) =
  @     image_context_type_valid (Context) &&
  @     (Context->ImageType == ImageTypeTe ==>
  @       \let TeHdr            = image_te_get_hdr ((char *) Context->FileBuffer);
  @       \let SectionsOffset   = image_te_get_sections_offset ((char *) Context->FileBuffer);
  @       \let Sections         = image_te_get_sections ((char *) Context->FileBuffer);
  @       \let SizeOfHeaders    = TeHdr->NumberOfSections * sizeof (EFI_IMAGE_SECTION_HEADER) + TeHdr->StrippedSize;
  @       \let TeStrippedOffset = TeHdr->StrippedSize - sizeof (EFI_TE_IMAGE_HEADER);
  @       \let RelocDir         = image_te_get_reloc_dir ((char *) Context->FileBuffer);
  @       Context->ExeHdrOffset        == 0 &&
  @       Context->SectionsOffset      == SectionsOffset &&
  @       Context->NumberOfSections    == TeHdr->NumberOfSections &&
  @       Context->AddressOfEntryPoint == TeHdr->AddressOfEntryPoint &&
  @       Context->ImageBase           == TeHdr->ImageBase &&
  @       Context->Subsystem           == TeHdr->Subsystem &&
  @       Context->Machine             == TeHdr->Machine &&
  @       Context->RelocsStripped      == (RelocDir->Size > 0) &&
  @       Context->SectionAlignment    == BASE_4KB &&
  @       Context->TeStrippedOffset    == TeStrippedOffset &&
  @       Context->SizeOfHeaders       == SizeOfHeaders &&
  @       Context->SizeOfImage         == image_te_SizeOfImage ((char *) Context->FileBuffer) &&
  @       Context->RelocDirRva         == RelocDir->VirtualAddress &&
  @       Context->RelocDirSize        == RelocDir->Size) &&
  @     (Context->ImageType == ImageTypePe32 ==>
  @       image_context_fields_correct_pe32 (Context)) &&
  @     (Context->ImageType == ImageTypePe32Plus ==>
  @       image_context_fields_correct_pe32plus (Context));
  @
  @   predicate image_context_FileBuffer_sane (PE_COFF_IMAGE_CONTEXT *Context) =
  @     \typeof (Context->FileBuffer) <: \type (char *) &&
  @     pointer_max_aligned (Context->FileBuffer);
  @
  @   predicate image_context_ImageBuffer_sane (PE_COFF_IMAGE_CONTEXT *Context) =
  @     \typeof (Context->ImageBuffer) <: \type (char *) &&
  @     pointer_max_aligned (Context->ImageBuffer);
  @
  @   predicate image_context_file_char_valid (PE_COFF_IMAGE_CONTEXT *Context) =
  @     \let Sections         = image_context_get_sections (Context);
  @     \let NumberOfSections = Context->NumberOfSections;
  @     \valid ((char *) Context->FileBuffer + (0 .. image_hdr_raw_size (Context->SizeOfHeaders, Context->TeStrippedOffset) - 1)) &&
  @     (\forall integer i; 0 <= i < NumberOfSections ==>
  @       \valid ((char *) Context->FileBuffer + ((Sections[i].PointerToRawData - Context->TeStrippedOffset) .. (Sections[i].PointerToRawData - Context->TeStrippedOffset) + Sections[i].SizeOfRawData - 1)));
  @
  @   logic integer image_context_runtime_fixup_num (PE_COFF_IMAGE_CONTEXT *Context) =
  @     Context->RelocDirSize / sizeof (UINT16);
  @
  @   logic integer image_context_runtime_fixup_size (PE_COFF_IMAGE_CONTEXT *Context) =
  @     sizeof (PE_COFF_RUNTIME_CONTEXT) + Context->RelocDirSize * sizeof (UINT64) / sizeof (UINT16);
  @ }
*/

#endif // BASE_PECOFF_LIB_INTERNALS_H
