/** @file
  Provides APIs to load and relocate PE/COFF Images.

  Copyright (c) 2020 - 2021, Marvin Häuser. All rights reserved.<BR>
  Copyright (c) 2020, Vitaly Cheptsov. All rights reserved.<BR>
  Copyright (c) 2020, ISP RAS. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-3-Clause
**/

#ifndef PE_COFF_LIB_H_
#define PE_COFF_LIB_H_

#include <IndustryStandard/PeImage.h>

#include <Guid/WinCertificate.h>

///
/// Image type enumeration for Image format identification from the context.
///
typedef enum {
  PeCoffLoaderTypeTe,
  PeCoffLoaderTypePe32,
  PeCoffLoaderTypePe32Plus,
  PeCoffLoaderTypeMax
} PE_COFF_LOADER_IMAGE_TYPE;

///
/// Image context structure used for abstraction and bookkeeping.
/// This structure is publicly exposed for memory allocation reasons and must
/// not be accessed directly outside of the library implementation.
///
typedef struct {
  ///
  /// The preferred load address of the Image.
  ///
  UINT64     ImageBase;
  ///
  /// A pointer to the Image raw file buffer.
  ///
  CONST VOID *FileBuffer;
  ///
  /// The size, in Bytes, of FileBuffer.
  ///
  UINT32     FileSize;
  ///
  /// A pointer to the loaded Image destination.
  ///
  VOID       *ImageBuffer;
  ///
  /// The offset of the Section Headers from the beginning of the raw file.
  ///
  UINT32     SectionsOffset;
  ///
  /// The number of Sections in the Image.
  ///
  UINT16     NumberOfSections;
  ///
  /// The size, in Bytes, required to load the Image.
  ///
  UINT32     SizeOfImage;
  ///
  /// The additional size, in Bytes, required to force-load debug information.
  ///
  UINT32     SizeOfImageDebugAdd;
  ///
  /// The alignment, in Bytes, of Image Sections virtual addresses.
  ///
  UINT32     SectionAlignment;
  ///
  /// The offset of the Image Header from the beginning of the raw file.
  ///
  UINT32     ExeHdrOffset;
  ///
  /// The combined size, in Bytes, of all Image Headers.
  ///
  UINT32     SizeOfHeaders;
  ///
  /// The RVA of the Image entry point.
  ///
  UINT32     AddressOfEntryPoint;
  ///
  /// Indicates whether relocation information has been stripped from the Image.
  ///
  BOOLEAN    RelocsStripped;
  ///
  /// The file format of the Image raw file, refer to PE_COFF_LOADER_IMAGE_TYPE.
  ///
  UINT8      ImageType;
  ///
  /// The Subsystem value from the Image Header.
  ///
  UINT16     Subsystem;
  ///
  /// The Machine value from the Image Header.
  ///
  UINT16     Machine;
  ///
  /// The size, in Bytes, stripped from the beginning of the Image raw file
  /// during TE file generation. Always 0 for PE Images.
  ///
  UINT16     TeStrippedOffset;
  ///
  /// The RVA of the Relocation Directory.
  ///
  UINT32     RelocDirRva;
  ///
  /// The size, in Bytes, of the Relocation Directory.
  ///
  UINT32     RelocDirSize;
  ///
  /// The RVA of the Security Directory.
  ///
  UINT32     SecDirOffset;
  ///
  /// The size, in Bytes, of the Security Directory.
  ///
  UINT32     SecDirSize;
  ///
  /// The RVA of the CodeView debug information.
  ///
  UINT32     CodeViewRva;
} PE_COFF_LOADER_IMAGE_CONTEXT;

///
/// Runtime Image context used to relocate the Image into virtual addressing.
///
typedef struct {
  ///
  /// The RVA of the Relocation Directory.
  ///
  UINT32 RelocDirRva;
  ///
  /// The size, in Bytes, of the Relocation Directory.
  ///
  UINT32 RelocDirSize;
  ///
  /// Information bookkept during the initial Image Relocation.
  ///
  UINT64 FixupData[];
} PE_COFF_LOADER_RUNTIME_CONTEXT;

/**
  Adds the digest of Data to HashContext. This function can be called multiple
  times to compute the digest of discontinuous data.

  @param[in,out] HashContext  The context of the current hash.
  @param[in]     Data         Pointer to the data to be hashed.
  @param[in]     DataSize     The size, in Bytes, of Data.

  @returns  Whether hashing has been successful.
**/
typedef
BOOLEAN
(EFIAPI *PE_COFF_LOADER_HASH_UPDATE)(
  IN OUT VOID        *HashContext,
  IN     CONST VOID  *Data,
  IN     UINTN       DataSize
  );

/**
  Verify the TE, PE32, or PE32+ Image and initialise Context.

  Used offsets and ranges must be aligned and in the bounds of the raw file.
  Image Section Headers and basic Relocation information must be correct.

  @param[out] Context   The context describing the Image.
  @param[in]  FileSize  The size, in Bytes, of Context->FileBuffer.

  @retval RETURN_SUCCESS  The file data is correct.
  @retval other           The file data is malformed.
**/
RETURN_STATUS
PeCoffInitializeContext (
  OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  IN  CONST VOID                    *FileBuffer,
  IN  UINT32                        FileSize
  );

/**
  Load the Image into the destination memory space.

  @param[in]  Context          The context describing the Image. Must have been
                               initialised by PeCoffInitializeContext().
  @param[out] Destination      The Image destination memory. Must be allocated
                               from page memory.
  @param[in]  DestinationSize  The size, in Bytes, of Destination.
                               Must be at least
                               Context->SizeOfImage +
                               Context->SizeOfImageDebugAdd. If the Section
                               Alignment exceeds 4 KB, must be at least
                               Context->SizeOfImage +
                               Context->SizeOfImageDebugAdd
                               Context->SectionAlignment.

  @retval RETURN_SUCCESS  The Image was loaded successfully.
  @retval other           The Image could not be loaded successfully.
**/
RETURN_STATUS
PeCoffLoadImage (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  OUT    VOID                          *Destination,
  IN     UINT32                        DestinationSize
  );

RETURN_STATUS
PeCoffLoadImageForExecution (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT    *Context,
  OUT    VOID                            *Destination,
  IN     UINT32                          DestinationSize,
  OUT    PE_COFF_LOADER_RUNTIME_CONTEXT  *RuntimeContext OPTIONAL,
  IN     UINT32                          RuntimeContextSize
  );

RETURN_STATUS
PeCoffRelocateImageForRuntimeExecution (
  IN OUT VOID                                  *Image,
  IN     UINT32                                ImageSize,
  IN     UINT64                                BaseAddress,
  IN     CONST PE_COFF_LOADER_RUNTIME_CONTEXT  *RuntimeContext
  );

RETURN_STATUS
PeCoffLoadImageInplace (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  );

/**
  Discards optional Image Sections to disguise sensitive data.

  @param[in] Context  The context describing the Image. Must have been loaded by
                      PeCoffLoadImage().
**/
VOID
PeCoffDiscardSections (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  );

/**
  Retrieves the size required to bookkeep Runtime Relocation information.

  @param[in]  Context  The context describing the Image. Must have been loaded
                       by PeCoffLoadImage().
  @param[out] Size     On output, the size, in Bytes, of the bookkeeping buffer.

  @retval RETURN_SUCCESS  The Runtime context size for the Image was retrieved
                          successfully.
  @retval other           The Runtime context size for the Image could not be
                          retrieved successfully.
**/
RETURN_STATUS
PeCoffLoaderGetRuntimeContextSize (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  OUT    UINT32                        *Size
  );

/**
  Relocate Image for boot-time usage.

  @param[in]  Context             The context describing the Image. Must have
                                  been loaded by PeCoffLoadImage().
  @param[in]  BaseAddress         The address to relocate the Image to.
  @param[out] RuntimeContext      If not NULL, on output, a buffer bookkeeping
                                  data required for Runtime Relocation.
  @param[in]  RuntimeContextSize  The size, in Bytes, of RuntimeContext. Must be
                                  at least as big as
                                  PeCoffLoaderGetRuntimeContextSize().

  @retval RETURN_SUCCESS  The Image has been relocated successfully.
  @retval other           The Image could not be relocated successfully.
**/
RETURN_STATUS
PeCoffRelocateImage (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT    *Context,
  IN     UINT64                          BaseAddress,
  OUT    PE_COFF_LOADER_RUNTIME_CONTEXT  *RuntimeContext OPTIONAL,
  IN     UINT32                          RuntimeContextSize
  );

/**
  Relocate Image for Runtime usage.

  @param[in]  Image           The Image destination memory. Must have been
                              relocated by PeCoffRelocateImage().
  @param[in]  ImageSize       The size, in Bytes, of Image.
  @param[in]  BaseAddress     The address to relocate the Image to.
  @param[in]  RuntimeContext  The Relocation context obtained by
                              PeCoffRelocateImage().

  @retval RETURN_SUCCESS  The Image has been relocated successfully.
  @retval other           The Image could not be relocated successfully.
**/
RETURN_STATUS
PeCoffRelocateImageForRuntime (
  IN OUT VOID                                  *Image,
  IN     UINT32                                ImageSize,
  IN     UINT64                                BaseAddress,
  IN     CONST PE_COFF_LOADER_RUNTIME_CONTEXT  *RuntimeContext
  );

/**
  Retrieves the Image PDB path.

  @param[in,out] Context      The context describing the Image. Must have been
                              initialised by PeCoffInitializeContext().
  @param[out]    PdbPath      On output, a pointer to the Image PDB path.
  @param[out]    PdbPathSize  On output, the size, in Bytes, of *PdbPath.

  @retval RETURN_SUCCESS  The Image PDB path was retrieved successfully.
  @retval other           The Image PDB path could not be retrieved
                          successfully.
**/
RETURN_STATUS
PeCoffGetPdbPath (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  OUT    CONST CHAR8                   **PdbPath,
  OUT    UINT32                        *PdbPathSize
  );

/**
  Hashes the Image using the Authenticode (PE/COFF Specification 8.1 Appendix A)
  algorithm.

  @param[in]     Context      The context describing the Image. Must have been
                              initialised by PeCoffInitializeContext().
  @param[in]     HashUpdate   The data hashing function.
  @param[in,out] HashContext  The context of the current hash.

  @returns  Whether hashing has been successful.
**/
BOOLEAN
PeCoffHashImage (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  IN     PE_COFF_LOADER_HASH_UPDATE    HashUpdate,
  IN OUT VOID                          *HashContext
  );

RETURN_STATUS
PeCoffGetFirstCertificate (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  OUT    CONST WIN_CERTIFICATE         **Certificate
  );

RETURN_STATUS
PeCoffGetNextCertificate (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  OUT    CONST WIN_CERTIFICATE         **Certificate
  );

UINT16
PeCoffGetSections (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT    *Context,
  OUT    CONST EFI_IMAGE_SECTION_HEADER  **Sections
  );

RETURN_STATUS
PeCoffGetHiiResourceSection (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  OUT    UINT32                        *HiiRva,
  OUT    UINT32                        *HiiSize
  );

UINT32
PeCoffGetAddressOfEntryPoint (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  );

UINT16
PeCoffGetMachine (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  );

UINT16
PeCoffGetSubsystem (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  );
UINT32
PeCoffGetSectionAlignment (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  );

UINT32
PeCoffGetSizeOfImage (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  );

UINT64
PeCoffGetImageBase (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  );

UINT32
PeCoffGetSizeOfHeaders (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  );

BOOLEAN
PeCoffGetRelocsStripped (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  );

UINTN
PeCoffLoaderGetImageAddress (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  );

RETURN_STATUS
PeCoffLoaderGetDestinationSize (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  OUT    UINT32                        *Size
  );

#endif // PE_COFF_LIB_H
