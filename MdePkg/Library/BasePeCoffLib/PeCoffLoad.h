/** @file
  Provides APIs to load PE/COFF Images.

  Copyright (c) 2020, Marvin Häuser. All rights reserved.<BR>
  Copyright (c) 2020, Vitaly Cheptsov. All rights reserved.<BR>
  Copyright (c) 2020, ISP RAS. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-3-Clause
**/

#ifndef PE_COFF_LOAD_H_
#define PE_COFF_LOAD_H_

/**
  Load the Image into the destination memory space.

  @param[in]  Context          The context describing the Image. Must have been
                               initialised by PeCoffInitializeContext().
  @param[out] Destination      The Image destination memory. Must be allocated
                               from page memory.
  @param[in]  DestinationSize  The size, in bytes, of Destination.
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

/**
  Discards optional Image Sections to disguise sensitive data.

  @param[in] Context  The context describing the Image. Must have been loaded by
                      PeCoffLoadImage().
**/
VOID
PeCoffDiscardSections (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context
  );

#endif // PE_COFF_LOAD_H_
