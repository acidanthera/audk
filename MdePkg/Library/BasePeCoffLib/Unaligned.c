/** @file
  Unaligned access functions of BaseLib for ARM.

  volatile was added to work around optimization issues.

  Copyright (c) 2006 - 2018, Intel Corporation. All rights reserved.<BR>
  Portions copyright (c) 2008 - 2009, Apple Inc. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-2-Clause-Patent

**/

#include "Base.h"
#include "AvMacros.h"
#include "Unaligned.h"

/**
  Reads a 16-bit value from memory that may be unaligned.

  This function returns the 16-bit value pointed to by Buffer. The function
  guarantees that the read operation does not produce an alignment fault.

  If the Buffer is NULL, then ASSERT().

  @param  Buffer  The pointer to a 16-bit value that may be unaligned.

  @return The 16-bit value read from Buffer.

**/
UINT16
EFIAPI
ReadUnaligned16 (
  IN CONST VOID              *Buffer
  )
{
  volatile UINT8 LowerByte;
  volatile UINT8 HigherByte;

  ASSERT (Buffer != NULL);

  LowerByte = ((CONST UINT8*)Buffer)[0];
  HigherByte = ((CONST UINT8*)Buffer)[1];

  return (UINT16)(LowerByte | (HigherByte << 8));
}

/**
  Writes a 16-bit value to memory that may be unaligned.

  This function writes the 16-bit value specified by Value to Buffer. Value is
  returned. The function guarantees that the write operation does not produce
  an alignment fault.

  If the Buffer is NULL, then ASSERT().

  @param  Buffer  The pointer to a 16-bit value that may be unaligned.
  @param  Value   16-bit value to write to Buffer.

  @return The 16-bit value to write to Buffer.

**/
UINT16
EFIAPI
WriteUnaligned16 (
  OUT VOID                      *Buffer,
  IN  UINT16                    Value
  )
{
  ASSERT (Buffer != NULL);

  ((volatile UINT8*)Buffer)[0] = (UINT8)Value;
  ((volatile UINT8*)Buffer)[1] = (UINT8)(Value >> 8U);

  return Value;
}

/**
  Reads a 32-bit value from memory that may be unaligned.

  This function returns the 32-bit value pointed to by Buffer. The function
  guarantees that the read operation does not produce an alignment fault.

  If the Buffer is NULL, then ASSERT().

  @param  Buffer  The pointer to a 32-bit value that may be unaligned.

  @return The 32-bit value read from Buffer.

**/
UINT32
EFIAPI
ReadUnaligned32 (
  IN CONST VOID              *Buffer
  )
{
  UINT16  LowerBytes;
  UINT16  HigherBytes;

  ASSERT (Buffer != NULL);

  LowerBytes  = ReadUnaligned16 (Buffer);
  HigherBytes = ReadUnaligned16 ((CONST UINT8*) Buffer + sizeof (UINT16));

  return (UINT32) (LowerBytes | ((UINT32) HigherBytes << 16U));
}

/**
  Writes a 32-bit value to memory that may be unaligned.

  This function writes the 32-bit value specified by Value to Buffer. Value is
  returned. The function guarantees that the write operation does not produce
  an alignment fault.

  If the Buffer is NULL, then ASSERT().

  @param  Buffer  The pointer to a 32-bit value that may be unaligned.
  @param  Value   32-bit value to write to Buffer.

  @return The 32-bit value to write to Buffer.

**/
UINT32
EFIAPI
WriteUnaligned32 (
  OUT VOID                      *Buffer,
  IN  UINT32                    Value
  )
{
  ASSERT (Buffer != NULL);

  WriteUnaligned16 (Buffer, (UINT16) Value);
  WriteUnaligned16 ((UINT8 *) Buffer + sizeof (UINT16), (UINT16)(Value >> 16U));

  return Value;
}

/**
  Reads a 64-bit value from memory that may be unaligned.

  This function returns the 64-bit value pointed to by Buffer. The function
  guarantees that the read operation does not produce an alignment fault.

  If the Buffer is NULL, then ASSERT().

  @param  Buffer  The pointer to a 64-bit value that may be unaligned.

  @return The 64-bit value read from Buffer.

**/
UINT64
EFIAPI
ReadUnaligned64 (
  IN CONST VOID              *Buffer
  )
{
  UINT32  LowerBytes;
  UINT32  HigherBytes;

  ASSERT (Buffer != NULL);

  LowerBytes  = ReadUnaligned32 (Buffer);
  HigherBytes = ReadUnaligned32 ((CONST UINT8*) Buffer + sizeof (UINT32));

  return (UINT64) (LowerBytes | ((UINT64) HigherBytes << 32U));
}

/**
  Writes a 64-bit value to memory that may be unaligned.

  This function writes the 64-bit value specified by Value to Buffer. Value is
  returned. The function guarantees that the write operation does not produce
  an alignment fault.

  If the Buffer is NULL, then ASSERT().

  @param  Buffer  The pointer to a 64-bit value that may be unaligned.
  @param  Value   64-bit value to write to Buffer.

  @return The 64-bit value to write to Buffer.

**/
UINT64
EFIAPI
WriteUnaligned64 (
  OUT VOID                      *Buffer,
  IN  UINT64                    Value
  )
{
  ASSERT (Buffer != NULL);

  WriteUnaligned32 (Buffer, (UINT32)Value);
  WriteUnaligned32 ((UINT8 *)Buffer + sizeof(UINT32), (UINT32)(Value >> 32U));

  return Value;
}
