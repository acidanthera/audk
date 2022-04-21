/** @file
  Provides APIs to load PE/COFF Debug information.
  Please note that this code is not verified.

  Copyright (c) 2020, Marvin Häuser. All rights reserved.<BR>
  Copyright (c) 2020, Vitaly Cheptsov. All rights reserved.<BR>
  Copyright (c) 2020, ISP RAS. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-3-Clause
**/

#ifndef PE_COFF_DEBUG_H_
#define PE_COFF_DEBUG_H_

/**
  Retrieves information about the Image CodeView data.

  The Image context is updated accordingly.

  @param[in,out]  Context   The context describing the Image. Must have been
                            initialised by PeCoffInitializeContext().
  @param[in]      FileSize  The size, in bytes, of Context->FileBuffer.
**/
//@ assigns \nothing;
VOID
PeCoffLoaderRetrieveCodeViewInfo (
  IN OUT PE_COFF_IMAGE_CONTEXT  *Context,
  IN     UINT32                 FileSize
  );

/**
  Loads the Image CodeView data into memory.

  @param[in,out]  Context   The context describing the Image. Must have been
                            updated by PeCoffLoaderRetrieveCodeViewInfo().
**/
//@ assigns \nothing;
VOID
PeCoffLoaderLoadCodeView (
  IN OUT PE_COFF_IMAGE_CONTEXT  *Context
  );

/**
  Retrieves the Image PDB path.

  @param[in,out] Context      The context describing the Image. Must have been
                              initialised by PeCoffInitializeContext().
  @param[out]    PdbPath      On output, a pointer to the Image PDB path.
  @param[out]    PdbPathSize  On output, the size, in bytes, of *PdbPath.

  @retval RETURN_SUCCESS  The Image PDB path was retrieved successfully.
  @retval other           The Image PDB path could not be retrieved
                          successfully.
**/
/*@ assigns *PdbPathSize;
  @ ensures *PdbPathSize == 0;
*/
RETURN_STATUS
PeCoffGetPdbPath (
  IN  CONST PE_COFF_IMAGE_CONTEXT  *Context,
  OUT CHAR8                        **PdbPath,
  OUT UINT32                       *PdbPathSize
  );

#endif // PE_COFF_DEBUG_H_
