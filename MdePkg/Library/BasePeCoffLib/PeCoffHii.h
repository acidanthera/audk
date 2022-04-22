/** @file
  Provides APIs to retrieve UEFI HII data from PE/COFF Images.

  Copyright (c) 2020, Marvin Häuser. All rights reserved.<BR>
  Copyright (c) 2020, Vitaly Cheptsov. All rights reserved.<BR>
  Copyright (c) 2020, ISP RAS. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-3-Clause
**/

#ifndef PE_COFF_HII_H
#define PE_COFF_HII_H

RETURN_STATUS
PeCoffLoaderGetHiiResourceSection (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  OUT UINT32                       *HiiOffset,
  OUT UINT32                       *MaxHiiSize
  );

#endif // PE_COFF_HII_H
