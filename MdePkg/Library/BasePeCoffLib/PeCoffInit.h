/** @file
  Provides APIs to verify PE/COFF Images for further processing.

  Copyright (c) 2020, Marvin Häuser. All rights reserved.<BR>
  Copyright (c) 2020, Vitaly Cheptsov. All rights reserved.<BR>
  Copyright (c) 2020, ISP RAS. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-3-Clause
**/

#ifndef PE_COFF_INIT_H_
#define PE_COFF_INIT_H_

/**
  Verify the TE, PE32, or PE32+ Image and initialise Context.

  Used offsets and ranges must be aligned and in the bounds of the raw file.
  Image Section Headers and basic Relocation information must be correct.

  @param[out] Context   The context describing the Image.
  @param[in]  FileSize  The size, in bytes, of Context->FileBuffer.

  @retval RETURN_SUCCESS  The file data is correct.
  @retval other           The file data is malformed.
**/
RETURN_STATUS
PeCoffInitializeContext (
  OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  IN  CONST VOID             *FileBuffer,
  IN  UINT32                 FileSize
  );

#endif // PE_COFF_INIT_H_
