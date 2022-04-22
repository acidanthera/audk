/** @file
  Copyright (c) 2020 - 2021, Marvin Häuser. All rights reserved.<BR>
  Copyright (c) 2020, Vitaly Cheptsov. All rights reserved.<BR>
  Copyright (c) 2020, ISP RAS. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-3-Clause
**/

#ifndef BASE_PECOFF_LIB_INTERNALS_H_
#define BASE_PECOFF_LIB_INTERNALS_H_

#define PCD_ALIGNMENT_POLICY_SECTIONS                BIT0
#define PCD_ALIGNMENT_POLICY_RELOCATION_BLOCK_SIZES  BIT1
#define PCD_ALIGNMENT_POLICY_CERTIFICATE_SIZES       BIT2

#define PCD_RELOC_TYPE_POLICY_ARM  BIT0

#define PCD_DEBUG_SUPPORT_BASIC       1U
#define PCD_DEBUG_SUPPORT_FORCE_LOAD  2U

#define ALIGNOF           _Alignof
#define CRITICAL_ERROR(x)  ASSERT(x)
#define IS_ALIGNED(v, a)  (((v) & ((a) - 1U)) == 0U)
#define IS_POW2(v)        ((v) != 0 && ((v) & ((v) - 1U)) == 0)

#define IMAGE_CERTIFICATE_ALIGN  8U

//
// The PE specification guarantees an 8 Byte alignment for certificate sizes.
// This is larger than the alignment requirement for WIN_CERTIFICATE implied by
// the UEFI ABI. ASSERT this is holds.
//
STATIC_ASSERT (
  ALIGNOF (WIN_CERTIFICATE) <= IMAGE_CERTIFICATE_ALIGN,
  "The PE specification guarantee does not suffice."
  );

//
// The 4 Byte alignment guaranteed by the PE specification has been replaced
// with ALIGNOF (EFI_IMAGE_BASE_RELOCATION_BLOCK) for proof simplicity. This
// obviously was the original intention of the specification. Assert in case the
// equality is not given.
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
  @param[in]      FileSize  The size, in Bytes, of Context->FileBuffer.
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
