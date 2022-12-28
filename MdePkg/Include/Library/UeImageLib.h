/** @file
  UEFI Image Loader library implementation for UE Images.

  Copyright (c) 2021, Marvin Häuser. All rights reserved.<BR>

  SPDX-License-Identifier: BSD-3-Clause
**/

#ifndef UE_LIB_H_
#define UE_LIB_H_

#include <IndustryStandard/UeImage.h>

// FIXME: Deduplicate?
//
// PcdImageLoaderAlignmentPolicy bits.
//

///
/// If set, unaligned Image sections are permitted.
///
#define PCD_ALIGNMENT_POLICY_CONTIGUOUS_SECTIONS     BIT0
///
/// If set, unaligned Image Relocation Block sizes are permitted.
///
#define PCD_ALIGNMENT_POLICY_RELOCATION_BLOCK_SIZES  BIT1
///
/// If set, unaligned Image certificate sizes are permitted.
///
#define PCD_ALIGNMENT_POLICY_CERTIFICATE_SIZES       BIT2

//
// PcdImageLoaderRelocTypePolicy bits.
//

///
/// If set, ARM Thumb Image relocations are supported.
///
#define PCD_RELOC_TYPE_POLICY_ARM  BIT0

// FIXME: Add RISC-V support.
/**
  Returns whether the Base Relocation type is supported by this loader.

  @param[in] Type  The type of the Base Relocation.
**/
#define UE_RELOC_TYPE_SUPPORTED(Type) \
  (((Type) == EFI_IMAGE_REL_BASED_ABSOLUTE) || \
  ((Type) == EFI_IMAGE_REL_BASED_HIGHLOW) || \
  ((Type) == EFI_IMAGE_REL_BASED_DIR64) || \
  ((PcdGet32 (PcdImageLoaderRelocTypePolicy) & PCD_RELOC_TYPE_POLICY_ARM) != 0 && (Type) == EFI_IMAGE_REL_BASED_ARM_MOV32T))

/**
  Returns whether the Base Relocation is supported by this loader.

  @param[in] Relocation  The composite Base Relocation value.
**/
#define UE_RELOC_SUPPORTED(RelocInfo) \
  UE_RELOC_TYPE_SUPPORTED (UE_RELOC_TYPE (RelocInfo))

typedef struct {
  CONST VOID       *FileBuffer;
  UINT32           SegmentAlignment;
  VOID             *ImageBuffer;
  UINT32           SegmentsFileOffset; // Unused for XIP
  CONST UE_SECTION *Sections;
  CONST VOID       *Segments;
  UINT32           SectionsFileOffset;
  UINT32           ImageSize;
  UINT32           UnsignedFileSize;
  UINT32           CertTableSize;
  UINT32           RelocTableSize;
  UINT8            ImageInfo;
  UINT8            LastSegmentIndex;
  UINT8            NumSections;
  UINT8            Subsystem;
  UINT8            Machine;
  UINT64           PreferredAddress; // Unused for XIP
  UINT32           EntryPointAddress;
  UINT8            SegmentImageInfoIterSize;
} UE_LOADER_IMAGE_CONTEXT;

typedef struct UE_LOADER_RUNTIME_CONTEXT_ UE_LOADER_RUNTIME_CONTEXT;

/**
  Adds the digest of Data to HashContext. This function can be called multiple
  times to compute the digest of discontinuous data.

  @param[in,out] HashContext  The context of the current hash.
  @param[in]     Data         The data to be hashed.
  @param[in]     DataSize     The size, in Bytes, of Data.

  @returns  Whether hashing has been successful.
**/
typedef
BOOLEAN
(EFIAPI *UE_LOADER_HASH_UPDATE)(
  IN OUT VOID        *HashContext,
  IN     CONST VOID  *Data,
  IN     UINTN       DataSize
  );

RETURN_STATUS
UeInitializeContextPreHash (
  OUT UE_LOADER_IMAGE_CONTEXT  *Context,
  IN  CONST VOID               *FileBuffer,
  IN  UINT32                   FileSize
  );

RETURN_STATUS
UeInitializeContextPostHash (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context
  );

RETURN_STATUS
UeInitializeContext (
  OUT UE_LOADER_IMAGE_CONTEXT  *Context,
  IN  CONST VOID               *FileBuffer,
  IN  UINT32                   FileSize
  );

BOOLEAN
UeHashImageDefault (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context,
  IN OUT VOID                     *HashContext,
  IN     UE_LOADER_HASH_UPDATE    HashUpdate
  );

RETURN_STATUS
UeLoadImage (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context,
  OUT    VOID                     *Destination,
  IN     UINT32                   DestinationSize
  );

RETURN_STATUS
UeLoadImageInplace (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context
  );

RETURN_STATUS
UeLoaderGetRuntimeContextSize (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context,
  OUT    UINT32                   *Size
  );

RETURN_STATUS
UeRelocateImage (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context,
  IN     UINT64                   BaseAddress
  );

RETURN_STATUS
UeRelocateImageForRuntime (
  IN OUT VOID                             *Image,
  IN     UINT32                           ImageSize,
  IN     UINT64                           BaseAddress,
  IN     CONST UE_LOADER_RUNTIME_CONTEXT  *RuntimeContext
  );

RETURN_STATUS
UeGetSymbolsPath (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context,
  OUT    CONST CHAR8              **SymbolsPath,
  OUT    UINT32                   *SymbolsPathSize
  );

RETURN_STATUS
UeGetFirstCertificate (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context,
  OUT    CONST WIN_CERTIFICATE    **Certificate
  );

RETURN_STATUS
UeGetNextCertificate (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context,
  IN OUT CONST WIN_CERTIFICATE    **Certificate
  );

RETURN_STATUS
UeGetHiiDataRva (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context,
  OUT    UINT32                   *HiiRva,
  OUT    UINT32                   *HiiSize
  );

UINT32
UeGetAddressOfEntryPoint (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context
  );

UINT16
UeGetMachine (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context
  );

UINT16
UeGetSubsystem (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context
  );

UINT32
UeGetSegmentAlignment (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context
  );

UINT32
UeGetImageSize (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context
  );

UINT32
UeGetImageSizeInplace (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context
  );

UINT64
UeGetPreferredAddress (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context
  );

BOOLEAN
UeGetRelocsStripped (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context
  );

UINTN
UeLoaderGetImageAddress (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context
  );

UINT8
UeGetSegments (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context,
  OUT    CONST UE_SEGMENT         **Segments
  );

UINT8
UeGetSegmentImageInfos (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context,
  OUT    CONST UINT32             **SegmentImageInfos,
  OUT    UINT8                    *SegmentImageInfoIterSize
  );

UINT32
UeGetSectionsFileOffset (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context
  );

#endif // UE_LIB_H_
