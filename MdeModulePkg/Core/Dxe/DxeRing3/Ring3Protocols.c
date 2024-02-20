/** @file

  Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause

**/

#include "Ring3.h"

EFI_BLOCK_IO_PROTOCOL  mCoreBlockIo;
EFI_DISK_IO_PROTOCOL   mCoreDiskIo;

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
           Lba,
           BufferSize,
           Buffer
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
           Lba,
           BufferSize,
           Buffer
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
           Offset,
           BufferSize,
           Buffer
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
           Offset,
           BufferSize,
           Buffer
           );
}
