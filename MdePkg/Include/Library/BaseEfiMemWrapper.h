/** @file
  Provide strictly specification compliant instances of SetMem and CopyMem
  for those interfaces which need it.

Copyright (c) 2025, TianoCore and contributors. All rights reserved.<BR>
SPDX-License-Identifier: BSD-2-Clause-Patent

*/

#ifndef __BASE_EFI_MEM_WRAPPER__
#define __BASE_EFI_MEM_WRAPPER__

#include "BaseMemoryLib.h"

/**
  Copies a source buffer to a destination buffer, and returns the destination buffer.

  This function copies Length bytes from SourceBuffer to DestinationBuffer, and returns
  DestinationBuffer.  The implementation must be reentrant, and it must handle the case
  where SourceBuffer overlaps DestinationBuffer.

  If Length is greater than (MAX_ADDRESS - DestinationBuffer + 1), then ASSERT().
  If Length is greater than (MAX_ADDRESS - SourceBuffer + 1), then ASSERT().

  @param  DestinationBuffer   The pointer to the destination buffer of the memory copy.
  @param  SourceBuffer        The pointer to the source buffer of the memory copy.
  @param  Length              The number of bytes to copy from SourceBuffer to DestinationBuffer.

  @return None.

**/
STATIC
VOID
EFIAPI
EfiCopyMem (
  IN VOID                       *Destination,
  IN VOID                       *Source,
  IN UINTN                      Length
  )
{
  CopyMem (
    Destination,
    Source,
    Length
  );
}

/**
  Fills a target buffer with a byte value, and returns the target buffer.

  This function fills Length bytes of Buffer with Value, and returns Buffer.

  If Length is greater than (MAX_ADDRESS - Buffer + 1), then ASSERT().

  @param  Buffer    The memory to set.
  @param  Length    The number of bytes to set.
  @param  Value     The value with which to fill Length bytes of Buffer.

  @return None.

**/
STATIC
VOID
EFIAPI
EfiSetMem (
  IN VOID                       *Buffer,
  IN UINTN                      Size,
  IN UINT8                      Value
  )
{
  SetMem (
    Buffer,
    Size,
    Value
  );
}

#endif
