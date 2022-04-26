/** @file
  Provides APIs to inspect, load, and relocate PE/COFF Images.

  Copyright (c) 2020 - 2021, Marvin Häuser. All rights reserved.<BR>
  Copyright (c) 2020, Vitaly Cheptsov. All rights reserved.<BR>
  Copyright (c) 2020, ISP RAS. All rights reserved.<BR>

  SPDX-License-Identifier: BSD-3-Clause
**/

#ifndef PE_COFF_LIB_H_
#define PE_COFF_LIB_H_

#include <IndustryStandard/PeImage.h>

#include <Guid/WinCertificate.h>

/**
  Returns whether the Image targets the UEFI Subsystem.

  @param[in] Subsystem  The Subsystem value from the Image Headers.
**/
#define IMAGE_IS_EFI_SUBYSYSTEM(Subsystem) \
  ((Subsystem) >= EFI_IMAGE_SUBSYSTEM_EFI_APPLICATION && \
   (Subsystem) <= EFI_IMAGE_SUBSYSTEM_SAL_RUNTIME_DRIVER)

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
/// Image runtime context used to relocate the Image durinf runtime.
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
  /// Information bookkept during the initial Image relocation.
  ///
  UINT64 FixupData[];
} PE_COFF_LOADER_RUNTIME_CONTEXT;

///
/// Image record section that desribes the UEFI memory permission configuration
/// for one segment of the Image.
///
typedef struct {
  ///
  /// The start address of the Image record section in memory.
  ///
  UINTN  Address;
  ///
  /// The size, in Bytes, of the Image record section.
  ///
  UINT32 Size;
  ///
  /// The UEFI memory permission attributes corresponding to this Image record
  /// section.
  ///
  UINT32 Attributes;
} PE_COFF_IMAGE_RECORD_SECTION;

///
/// The 32-bit signature that identifies a PE_COFF_IMAGE_RECORD structure.
///
#define PE_COFF_IMAGE_RECORD_SIGNATURE  SIGNATURE_32 ('P','C','I','R')

///
/// Image record that describes the UEFI memory permission configuration for
/// every segment of the Image.
///
typedef struct {
  ///
  /// The signature of the Image record structure. Must be set to
  /// PE_COFF_IMAGE_RECORD_SIGNATURE.
  ///
  UINT32                       Signature;
  ///
  /// A link to allow insertion of the Image record into a doubly-linked list.
  ///
  LIST_ENTRY                   Link;
  // FIXME: Is this needed?
  ///
  /// The end address of the Image memory space. Must be equal to
  /// Sections[NumberOfSections - 1].Address + Sections[NumberOfSections - 1].Size.
  ///
  UINTN                        EndAddress;
  ///
  /// The number of Image records. Must be at least 1.
  ///
  UINT32                       NumberOfSections;
  ///
  /// The Image record sections with their corresponding memory permission
  /// attributes. Must be contiguous and cover the entire Image memory space.
  /// The Image record sections are ordered in ascending order by Address. The
  /// start address of the Image memory space can be retrieved by
  /// Sections[0].Address.
  ///
  PE_COFF_IMAGE_RECORD_SECTION Sections[];
} PE_COFF_IMAGE_RECORD;

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
(EFIAPI *PE_COFF_LOADER_HASH_UPDATE)(
  IN OUT VOID        *HashContext,
  IN     CONST VOID  *Data,
  IN     UINTN       DataSize
  );

/**
  Verify the TE, PE32, or PE32+ Image and initialise Context.

  Used offsets and ranges must be aligned and in the bounds of the raw file.
  Image Section Headers and basic Relocation information must be well-formed.

  FileBuffer must remain valid for the entire lifetime of Context.

  @param[out] Context     The context describing the Image.
  @param[in]  FileBuffer  The file data to parse as TE or PE Image.
  @param[in]  FileSize    The size, in Bytes, of FileBuffer.

  @retval RETURN_SUCCESS  The Image context has been initialised successfully.
  @retval other           The file data is malformed.
**/
RETURN_STATUS
PeCoffInitializeContext (
  OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  IN  CONST VOID                    *FileBuffer,
  IN  UINT32                        FileSize
  );

/**
  Hashes the Image using the Authenticode (PE/COFF Specification 8.1 Appendix A)
  algorithm.

  @param[in,out] Context      The context describing the Image. Must have been
                              initialised by PeCoffInitializeContext().
  @param[in,out] HashContext  The context of the current hash. Must have been
                              initialised for usage with the HashUpdate
                              function.
  @param[in]     HashUpdate   The data hashing function.

  @returns  Whether hashing has been successful.
**/
BOOLEAN
PeCoffHashImageAuthenticode (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  IN OUT VOID                          *HashContext,
  IN     PE_COFF_LOADER_HASH_UPDATE    HashUpdate
  );

/**
  Calculate the size, in Bytes, required for the destination Image memory space
  to load into with PeCoffLoadImage(). This potentially includes additional
  space to internally align the Image within the destination buffer.

  @param[in,out] Context  The context describing the Image. Must have been
                          initialised by PeCoffInitializeContext().
  @param[out]    Size     On output, the size, in Bytes, required to allocate
                          the Image destination buffer.

  @retval RETURN_SUCCESS  The Image destination size has been calculated
                          successfully.
  @retval other           The Image destination cannot be calculated.
**/
RETURN_STATUS
PeCoffLoaderGetDestinationSize (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  OUT    UINT32                        *Size
  );

/**
  Load the Image into the destination memory space.

  @param[in,out] Context       The context describing the Image. Must have been
                               initialised by PeCoffInitializeContext().
  @param[out] Destination      The Image destination memory. Must be allocated
                               from page memory.
  @param[in]  DestinationSize  The size, in Bytes, of Destination. Must be at
                               least as large as the size returned by
                               PeCoffLoaderGetDestinationSize().

  @retval RETURN_SUCCESS  The Image was loaded successfully.
  @retval other           The Image could not be loaded successfully.
**/
RETURN_STATUS
PeCoffLoadImage (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  OUT    VOID                          *Destination,
  IN     UINT32                        DestinationSize
  );

/**
  Equivalent to the PeCoffLoadImage() function for inplace-loading. Ensures that
  all important raw file offsets match the respective RVAs.

  @param[in,out] Context  The context describing the Image. Must have been
                          initialised by PeCoffInitializeContext().

  @retval RETURN_SUCCESS  The Image has been inplace-loaded successfully.
  @retval other           The Image is not suitable for inplace-loading.
**/
RETURN_STATUS
PeCoffLoadImageInplace (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  );

// FIXME:
RETURN_STATUS
PeCoffRelocateImageInplaceForExecution (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  );

/**
  Retrieves the size required to bookkeep Image runtime relocation information.

  May only be called when PeCoffGetRelocsStripped() returns FALSE.

  @param[in,out] Context  The context describing the Image. Must have been
                          loaded by PeCoffLoadImage().
  @param[out]    Size     On output, the size, in Bytes, required for the
                          bookkeeping buffer.

  @retval RETURN_SUCCESS  The Image runtime context size for the Image was
                          retrieved successfully.
  @retval other           The Image runtime context size for the Image could not
                          be retrieved successfully.
**/
RETURN_STATUS
PeCoffLoaderGetRuntimeContextSize (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  OUT    UINT32                        *Size
  );

/**
  Relocate the Image for boot-time usage.

  May only be called when PeCoffGetRelocsStripped() returns FALSE, or with
  BaseAddress == PeCoffGetImageBase().

  @param[in,out] Context             The context describing the Image. Must have
                                     been loaded by PeCoffLoadImage().
  @param[in]     BaseAddress         The address to relocate the Image to.
  @param[out]    RuntimeContext      If not NULL, on output, a bookkeeping data
                                     required for Image runtime relocation.
  @param[in]     RuntimeContextSize  The size, in Bytes, of RuntimeContext. Must
                                     be at least as big as the size returned by
                                     PeCoffLoaderGetRuntimeContextSize().

  @retval RETURN_SUCCESS  The Image has been relocated successfully.
  @retval other           The Image Relocation Directory is malformed.
**/
RETURN_STATUS
PeCoffRelocateImage (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT    *Context,
  IN     UINT64                          BaseAddress,
  OUT    PE_COFF_LOADER_RUNTIME_CONTEXT  *RuntimeContext OPTIONAL,
  IN     UINT32                          RuntimeContextSize
  );

/**
  Load the Image into the destination memory space, relocate Image for boot-time
  usage, and perform environment-specific actions required to execute code from
  the Image.

  May only be called when PeCoffGetRelocsStripped() returns FALSE, or with
  BaseAddress == PeCoffGetImageBase().

  @param[in,out] Context             The context describing the Image. Must have
                                     been initialised by
                                     PeCoffInitializeContext().
  @param[out]    Destination         The Image destination memory. Must be
                                     allocated from page memory.
  @param[in]     DestinationSize     The size, in Bytes, of Destination. Must be
                                     at least as large as the size returned by
                                     PeCoffLoaderGetDestinationSize().
  @param[out]    RuntimeContext      If not NULL, on output, a buffer
                                     bookkeeping data required for Image runtime
                                     relocation.
  @param[in]     RuntimeContextSize  The size, in Bytes, of RuntimeContext. Must
                                     be at least as big as the size returned by
                                     PeCoffLoaderGetRuntimeContextSize().

  @retval RETURN_SUCCESS  The Image was loaded successfully.
  @retval other           The Image could not be loaded successfully.
**/
RETURN_STATUS
PeCoffLoadImageForExecution (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT    *Context,
  OUT    VOID                            *Destination,
  IN     UINT32                          DestinationSize,
  OUT    PE_COFF_LOADER_RUNTIME_CONTEXT  *RuntimeContext OPTIONAL,
  IN     UINT32                          RuntimeContextSize
  );

/**
  Relocate Image for Runtime usage.

  May only be called when PeCoffGetRelocsStripped() returns FALSE, or with
  BaseAddress == PeCoffGetImageBase().

  @param[in,out] Image           The Image destination memory. Must have been
                                 relocated by PeCoffRelocateImage().
  @param[in]     ImageSize       The size, in Bytes, of Image.
  @param[in]     BaseAddress     The address to relocate the Image to.
  @param[in]     RuntimeContext  The Relocation context obtained by
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
  Relocate Image for Runtime usage, and perform environment-specific actions
  required to execute code from the Image.

  May only be called when PeCoffGetRelocsStripped() returns FALSE, or with
  BaseAddress == PeCoffGetImageBase().

  @param[in,out] Image           The Image destination memory. Must have been
                                 relocated by PeCoffRelocateImage().
  @param[in]     ImageSize       The size, in Bytes, of Image.
  @param[in]     BaseAddress     The address to relocate the Image to.
  @param[in]     RuntimeContext  The Relocation context obtained by
                                 PeCoffRelocateImage().

  @retval RETURN_SUCCESS  The Image has been relocated successfully.
  @retval other           The Image could not be relocated successfully.
**/
RETURN_STATUS
PeCoffRelocateImageForRuntimeExecution (
  IN OUT VOID                                  *Image,
  IN     UINT32                                ImageSize,
  IN     UINT64                                BaseAddress,
  IN     CONST PE_COFF_LOADER_RUNTIME_CONTEXT  *RuntimeContext
  );

/**
  Discards optional Image Sections to disguise sensitive data.

  This may destruct the Image Relocation Directory and as such, no function that
  performs Image relocation may be called after this function has been invoked.

  @param[in,out] Context  The context describing the Image. Must have been
                          loaded by PeCoffLoadImage().
**/
VOID
PeCoffDiscardSections (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  );

/**
  Retrieves the Image PDB path.

  @param[in,out] Context      The context describing the Image. Must have been
                              initialised by PeCoffInitializeContext().
  @param[out]    PdbPath      On output, a pointer to the Image PDB path.
  @param[out]    PdbPathSize  On output, the size, in Bytes, of PdbPath.

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
  Retrieves the Image module name from the Image PDB path.

  @param[in,out] Context         The context describing the Image. Must have
                                 been initialised by PeCoffInitializeContext().
  @param[out]    ModuleName      Buffer the Image module name is written into.
                                 If the name exceeds ModuleNameSize, it will be
                                 truncated.
  @param[out]    ModuleNameSize  The size, in Bytes, of ModuleName.

  @retval RETURN_SUCCESS  The Image module name was retrieved successfully.
  @retval other           The Image module name could not be retrieved
                          successfully.
**/
RETURN_STATUS
PeCoffGetModuleNameFromPdb (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  OUT    CHAR8                         *ModuleName,
  IN     UINT32                        ModuleNameSize
  );

/**
  Retrieves the first certificate from the Image Certificate Directory.

  @param[in,out] Context      The context describing the Image. Must have been
                              initialised by PeCoffInitializeContext().
  @param[out]    Certificate  On output, the first certificate of the Image.

  @retval RETURN_SUCCESS    The certificate has been retrieved successfully.
  @retval RETURN_NOT_FOUND  There is no such certificate.
  @retval other             The Image Certificate Directory is malformed.
**/
RETURN_STATUS
PeCoffGetFirstCertificate (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  OUT    CONST WIN_CERTIFICATE         **Certificate
  );

/**
  Retrieves the next certificate from the Image Certificate Directory.

  @param[in,out] Context      The context describing the Image. Must have been
                              initialised by PeCoffInitializeContext().
  @param[out]    Certificate  On input, the current certificate of the Image.
                              Must have been retrieved by
                              PeCoffGetFirstCertificate().
                              On output, the next certificate of the Image.

  @retval RETURN_SUCCESS    The certificate has been retrieved successfully.
  @retval RETURN_NOT_FOUND  There is no such certificate.
  @retval other             The Image Certificate Directory is malformed.
**/
RETURN_STATUS
PeCoffGetNextCertificate (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  IN OUT CONST WIN_CERTIFICATE         **Certificate
  );

/**
  Retrieves the Image Section Table.

  @param[in,out] Context   The context describing the Image. Must have been
                           initialised by PeCoffInitializeContext().
  @param[out]    Sections  On output, points to the Image Section Table.

  @returns  The number of sections in the Image Section Table.
**/
UINT16
PeCoffGetSectionTable (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT    *Context,
  OUT    CONST EFI_IMAGE_SECTION_HEADER  **Sections
  );

/**
  Retrieves the Image HII data RVA.

  @param[in,out] Context  The context describing the Image. Must have been
                          initialised by PeCoffInitializeContext().
  @param[out]    HiiRva   On output, the RVA of the HII resource data.
  @param[out]    HiiSize  On output, the size, in Bytes, of HiiRva.

  @retval RETURN_SUCCESS    The Image HII data has been retrieved successfully.
  @retval RETURN_NOT_FOUND  The Image HII data could not be found.
  @retval other             The Image Resource Directory is malformed.
**/
RETURN_STATUS
PeCoffGetHiiDataRva (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  OUT    UINT32                        *HiiRva,
  OUT    UINT32                        *HiiSize
  );

/**
  Retrieve the Image entry point RVA.

  @param[in,out] Context  The context describing the Image. Must have been
                          initialised by PeCoffInitializeContext().

  @returns  The Image entry point RVA.
**/
UINT32
PeCoffGetAddressOfEntryPoint (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  );

/**
  Retrieves the Image machine type.

  @param[in,out] Context  The context describing the Image. Must have been
                          initialised by PeCoffInitializeContext().

  @returns  The Image machine type.
**/
UINT16
PeCoffGetMachine (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  );

/**
  Retrieves the Image subsystem type.

  @param[in,out] Context  The context describing the Image. Must have been
                          initialised by PeCoffInitializeContext().

  @returns  The Image subsystem type.
**/
UINT16
PeCoffGetSubsystem (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  );

/**
  Retrieves the Image section alignment.

  @param[in,out] Context  The context describing the Image. Must have been
                          initialised by PeCoffInitializeContext().

  @returns  The Image section alignment.
**/
UINT32
PeCoffGetSectionAlignment (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  );

/**
  Retrieves the size, in Bytes, of the Image memory space.

  @param[in,out] Context  The context describing the Image. Must have been
                          initialised by PeCoffInitializeContext().

  @returns  The size of the Image memory space.
**/
UINT32
PeCoffGetSizeOfImage (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  );

/**
  Retrieves the Image preferred load address.

  @param[in,out] Context  The context describing the Image. Must have been
                          initialised by PeCoffInitializeContext().

  @returns  The Image preferred load address.
**/
UINT64
PeCoffGetImageBase (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  );

/**
  Retrieves the size, in Bytes, of the Image Headers.

  @param[in,out] Context  The context describing the Image. Must have been
                          initialised by PeCoffInitializeContext().

  @returns  The size of the Image Headers.
**/
UINT32
PeCoffGetSizeOfHeaders (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  );

/**
  Returns whether the Image relocations have been stripped.

  @param[in,out] Context  The context describing the Image. Must have been
                          initialised by PeCoffInitializeContext().

  @returns  Whether the Image relocations have been stripped.
**/
BOOLEAN
PeCoffGetRelocsStripped (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  );

/**
  Retrieves the Image load address PeCoffLoadImage() has loaded the Image to.

  May be called only after PeCoffLoadImage() has succeeded.

  @param[in,out] Context  The context describing the Image. Must have been
                          initialised by PeCoffInitializeContext().

  @returns  The Image load address.
**/
UINTN
PeCoffLoaderGetImageAddress (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  );

/**
  Constructs an Image record from the Image. Any headers, gaps, or trailers are
  described as read-only data.

  May be called only after PeCoffLoadImage() has succeeded.

  @param[in,out] Context  The context describing the Image. Must have been
                          initialised by PeCoffInitializeContext().

  @retval NULL   The Image record could not constructed successfully.
  @retval other  The Image record was constructed successfully and is returned.
                 It is allocated using the AllocatePool() API and is
                 caller-owned as soon as this function returns.
**/
PE_COFF_IMAGE_RECORD *
PeCoffLoaderGetImageRecord (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  );

#endif // PE_COFF_LIB_H_
