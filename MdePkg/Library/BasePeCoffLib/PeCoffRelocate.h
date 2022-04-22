/** @file
  Provides APIs to relocate PE/COFF Images.

  Copyright (c) 2020, Marvin Häuser. All rights reserved.<BR>
  Copyright (c) 2020, Vitaly Cheptsov. All rights reserved.<BR>
  Copyright (c) 2020, ISP RAS. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-3-Clause
**/

#ifndef PE_COFF_RELOCATE_H_
#define PE_COFF_RELOCATE_H_

#define IMAGE_RELOC_TYPE_SUPPORTED(Type) \
  (((Type) == EFI_IMAGE_REL_BASED_ABSOLUTE) || \
  ((Type) == EFI_IMAGE_REL_BASED_HIGHLOW) || \
  ((Type) == EFI_IMAGE_REL_BASED_DIR64) || \
  ((Type) == EFI_IMAGE_REL_BASED_ARM_MOV32T && PcdGetBool (PcdImageLoaderSupportArmThumb)))

#define IMAGE_RELOC_SUPPORTED(Reloc) \
  IMAGE_RELOC_TYPE_SUPPORTED (IMAGE_RELOC_TYPE (Reloc))

//
// 4 byte alignment has been replaced with OC_ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK)
// for proof simplicity. This obviously was the original intention of the
// specification. Assert in case the equality is not given.
//
STATIC_ASSERT (
  sizeof (UINT32) == OC_ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK),
  "The current model violates the PE specification"
  );

/**
  Retrieves the size required to bookkeep Runtime Relocation information.

  @param[in]  Context  The context describing the Image. Must have been loaded
                       by PeCoffLoadImage().
  @param[out] Size     On output, the size, in bytes, of the bookkeeping buffer.

  @retval RETURN_SUCCESS  The Runtime context size for the Image was retrieved
                          successfully.
  @retval other           The Runtime context size for the Image could not be
                          retrieved successfully.
**/
RETURN_STATUS
PeCoffRelocationDataSize (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  OUT UINT32                       *Size
  );

/**
  Relocate Image for boot-time usage.

  @param[in]  Context             The context describing the Image. Must have
                                  been loaded by PeCoffLoadImage().
  @param[in]  BaseAddress         The address to relocate the Image to.
  @param[out] RelocationData      If not NULL, on output, a buffer bookkeeping
                                  data required for Runtime Relocation.
  @param[in]  RelocationDataSize  The size, in bytes, of RelocationData. Must be
                                  at least as big as PeCoffRelocationDataSize().

  @retval RETURN_SUCCESS  The Image has been relocated successfully.
  @retval other           The Image could not be relocated successfully.
**/
RETURN_STATUS
PeCoffRelocateImage (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  IN  UINT64                       BaseAddress,
  OUT PE_COFF_RUNTIME_CONTEXT      *RelocationData OPTIONAL,
  IN  UINT32                       RelocationDataSize
  );

/**
  Relocate Image for Runtime usage.

  @param[in]  Image           The Image destination memory. Must have been
                              relocated by PeCoffRelocateImage().
  @param[in]  ImageSize       The size, in bytes, of Image.
  @param[in]  BaseAddress     The address to relocate the Image to.
  @param[in]  RelocationData  The Relocation context obtained by
                              PeCoffRelocateImage().

  @retval RETURN_SUCCESS  The Image has been relocated successfully.
  @retval other           The Image could not be relocated successfully.
**/
RETURN_STATUS
PeCoffRelocateImageForRuntime (
  IN OUT VOID                           *Image,
  IN     UINT32                         ImageSize,
  IN     UINT64                         BaseAddress,
  IN     CONST PE_COFF_RUNTIME_CONTEXT  *RelocationData
  );

#endif // PE_COFF_RELOCATE_H_
