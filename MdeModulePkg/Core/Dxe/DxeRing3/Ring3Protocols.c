/** @file

  Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause

**/

#include "Ring3.h"

EFI_STATUS
EFIAPI
Ring3BlockIoReset (
  IN EFI_BLOCK_IO_PROTOCOL  *This,
  IN BOOLEAN                ExtendedVerification
  )
{
  return SysCall (
           SysCallBlockIoReset,
           This,
           ExtendedVerification
           );
}

EFI_STATUS
EFIAPI
Ring3BlockIoRead (
  IN EFI_BLOCK_IO_PROTOCOL  *This,
  IN UINT32                 MediaId,
  IN EFI_LBA                Lba,
  IN UINTN                  BufferSize,
  OUT VOID                  *Buffer
  )
{
  return SysCall (
           SysCallBlockIoRead,
           This,
           MediaId,
           BufferSize,
           Buffer,
           Lba
           );
}

EFI_STATUS
EFIAPI
Ring3BlockIoWrite (
  IN EFI_BLOCK_IO_PROTOCOL  *This,
  IN UINT32                 MediaId,
  IN EFI_LBA                Lba,
  IN UINTN                  BufferSize,
  IN VOID                   *Buffer
  )
{
  return SysCall (
           SysCallBlockIoWrite,
           This,
           MediaId,
           BufferSize,
           Buffer,
           Lba
           );
}

EFI_STATUS
EFIAPI
Ring3BlockIoFlush (
  IN EFI_BLOCK_IO_PROTOCOL  *This
  )
{
  return SysCall (
           SysCallBlockIoFlush,
           This
           );
}

EFI_STATUS
EFIAPI
Ring3DiskIoRead (
  IN EFI_DISK_IO_PROTOCOL  *This,
  IN UINT32                MediaId,
  IN UINT64                Offset,
  IN UINTN                 BufferSize,
  OUT VOID                 *Buffer
  )
{
  return SysCall (
           SysCallDiskIoRead,
           This,
           MediaId,
           BufferSize,
           Buffer,
           Offset
           );
}

EFI_STATUS
EFIAPI
Ring3DiskIoWrite (
  IN EFI_DISK_IO_PROTOCOL  *This,
  IN UINT32                MediaId,
  IN UINT64                Offset,
  IN UINTN                 BufferSize,
  IN VOID                  *Buffer
  )
{
  return SysCall (
           SysCallDiskIoWrite,
           This,
           MediaId,
           BufferSize,
           Buffer,
           Offset
           );
}

INTN
EFIAPI
Ring3UnicodeStriColl (
  IN EFI_UNICODE_COLLATION_PROTOCOL  *This,
  IN CHAR16                          *Str1,
  IN CHAR16                          *Str2
  )
{
  return (INTN)SysCall (
                 SysCallUnicodeStriColl,
                 This,
                 Str1,
                 Str2
                 );
}

BOOLEAN
EFIAPI
Ring3UnicodeMetaiMatch (
  IN EFI_UNICODE_COLLATION_PROTOCOL  *This,
  IN CHAR16                          *String,
  IN CHAR16                          *Pattern
  )
{
  return (BOOLEAN)SysCall (
                    SysCallUnicodeMetaiMatch,
                    This,
                    String,
                    Pattern
                    );
}

VOID
EFIAPI
Ring3UnicodeStrLwr (
  IN EFI_UNICODE_COLLATION_PROTOCOL  *This,
  IN OUT CHAR16                      *Str
  )
{
  SysCall (
    SysCallUnicodeStrLwr,
    This,
    Str
    );
}

VOID
EFIAPI
Ring3UnicodeStrUpr (
  IN EFI_UNICODE_COLLATION_PROTOCOL  *This,
  IN OUT CHAR16                      *Str
  )
{
  SysCall (
    SysCallUnicodeStrUpr,
    This,
    Str
    );
}

VOID
EFIAPI
Ring3UnicodeFatToStr (
  IN EFI_UNICODE_COLLATION_PROTOCOL  *This,
  IN UINTN                           FatSize,
  IN CHAR8                           *Fat,
  OUT CHAR16                         *String
  )
{
  SysCall (
    SysCallUnicodeFatToStr,
    This,
    FatSize,
    Fat,
    String
    );
}

BOOLEAN
EFIAPI
Ring3UnicodeStrToFat (
  IN EFI_UNICODE_COLLATION_PROTOCOL  *This,
  IN CHAR16                          *String,
  IN UINTN                           FatSize,
  OUT CHAR8                          *Fat
  )
{
  return (BOOLEAN)SysCall (
                    SysCallUnicodeStrToFat,
                    This,
                    String,
                    FatSize,
                    Fat
                    );
}
