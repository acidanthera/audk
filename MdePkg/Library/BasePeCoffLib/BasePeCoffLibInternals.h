/** @file
  Copyright (c) 2020 - 2021, Marvin Häuser. All rights reserved.<BR>
  Copyright (c) 2020, Vitaly Cheptsov. All rights reserved.<BR>
  Copyright (c) 2020, ISP RAS. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-3-Clause
**/

#ifndef BASE_PECOFF_LIB_INTERNALS_H_
#define BASE_PECOFF_LIB_INTERNALS_H_

#define ALIGNOF           _Alignof
#define CRITIAL_ERROR     ASSERT
#define IS_ALIGNED(v, a)  (((v) & ((a) - 1U)) == 0U)
#define IS_POW2(v)        ((v) != 0 && ((v) & ((v) - 1U)) == 0)

#define IMAGE_CERTIFICATE_ALIGN  8U

//
// 4 byte alignment has been replaced with ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK)
// for proof simplicity. This obviously was the original intention of the
// specification. Assert in case the equality is not given.
//
STATIC_ASSERT (
  sizeof (UINT32) == ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK),
  "The current model violates the PE specification"
  );

/**
  Retrieves information about the Image CodeView data.

  The Image context is updated accordingly.

  @param[in,out]  Context   The context describing the Image. Must have been
                            initialised by PeCoffInitializeContext().
  @param[in]      FileSize  The size, in bytes, of Context->FileBuffer.
**/
VOID
PeCoffLoaderRetrieveCodeViewInfo (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  IN     UINT32                 FileSize
  );

/**
  Loads the Image CodeView data into memory.

  @param[in,out]  Context   The context describing the Image. Must have been
                            updated by PeCoffLoaderRetrieveCodeViewInfo().
**/
VOID
PeCoffLoaderLoadCodeView (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  );

VOID
PeCoffLoaderLoadCodeViewInplace (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  );

#endif // BASE_PECOFF_LIB_INTERNALS_H
