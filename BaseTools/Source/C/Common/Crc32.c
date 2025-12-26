/** @file
BtCalculateCrc32 routine.

Copyright (c) 2004 - 2018, Intel Corporation. All rights reserved.<BR>
SPDX-License-Identifier: BSD-2-Clause-Patent

**/

#include <stdlib.h>
#include <Common/BaseTypes.h>
#include <Library/BaseLib.h>
#include "Crc32.h"

EFI_STATUS
BtCalculateCrc32 (
  IN  UINT8      *Data,
  IN  UINTN      DataSize,
  IN OUT UINT32  *CrcOut
  )

/*++

Routine Description:

  The BtCalculateCrc32 routine.

Arguments:

  Data        - The buffer containing the data to be processed
  DataSize    - The size of data to be processed
  CrcOut      - A pointer to the caller allocated UINT32 that on
                contains the CRC32 checksum of Data

Returns:

  EFI_SUCCESS               - Calculation is successful.
  EFI_INVALID_PARAMETER     - Data / CrcOut = NULL, or DataSize = 0

--*/
{
  if ((DataSize == 0) || (Data == NULL) || (CrcOut == NULL)) {
    return EFI_INVALID_PARAMETER;
  }

  *CrcOut = CalculateCrc32 (Data, DataSize);

  return EFI_SUCCESS;
}
