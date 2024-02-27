/** @file
  UEFI Memory pool management functions.

Copyright (c) 2006 - 2018, Intel Corporation. All rights reserved.<BR>
SPDX-License-Identifier: BSD-2-Clause-Patent

**/

#ifndef _MEMORY_POOL_LIB_H_
#define _MEMORY_POOL_LIB_H_

//
// +---------------------------------------------------+
// | 0..(EfiMaxMemoryType - 1)    - Normal memory type |
// +---------------------------------------------------+
// | EfiMaxMemoryType..0x6FFFFFFF - Invalid            |
// +---------------------------------------------------+
// | 0x70000000..0x7FFFFFFF       - OEM reserved       |
// +---------------------------------------------------+
// | 0x80000000..0xFFFFFFFF       - OS reserved        |
// +---------------------------------------------------+
//
#define MEMORY_TYPE_OS_RESERVED_MIN   0x80000000
#define MEMORY_TYPE_OS_RESERVED_MAX   0xFFFFFFFF
#define MEMORY_TYPE_OEM_RESERVED_MIN  0x70000000
#define MEMORY_TYPE_OEM_RESERVED_MAX  0x7FFFFFFF

/**
  Called to initialize the pool.

**/
VOID
CoreInitializePool (
  VOID
  );

/**
  Allocate pool of a particular type.

  @param  PoolType               Type of pool to allocate
  @param  Size                   The amount of pool to allocate
  @param  Buffer                 The address to return a pointer to the allocated
                                 pool

  @retval EFI_INVALID_PARAMETER  PoolType not valid or Buffer is NULL
  @retval EFI_OUT_OF_RESOURCES   Size exceeds max pool size or allocation failed.
  @retval EFI_SUCCESS            Pool successfully allocated.

**/
EFI_STATUS
EFIAPI
CoreInternalAllocatePool (
  IN EFI_MEMORY_TYPE  PoolType,
  IN UINTN            Size,
  OUT VOID            **Buffer
  );

/**
  Allocate pool of a particular type.

  @param  PoolType               Type of pool to allocate
  @param  Size                   The amount of pool to allocate
  @param  Buffer                 The address to return a pointer to the allocated
                                 pool

  @retval EFI_INVALID_PARAMETER  PoolType not valid or Buffer is NULL
  @retval EFI_OUT_OF_RESOURCES   Size exceeds max pool size or allocation failed.
  @retval EFI_SUCCESS            Pool successfully allocated.

**/
EFI_STATUS
EFIAPI
CoreAllocatePool (
  IN EFI_MEMORY_TYPE  PoolType,
  IN UINTN            Size,
  OUT VOID            **Buffer
  );

/**
  Internal function to allocate pool of a particular type.
  Caller must have the memory lock held

  @param  PoolType               Type of pool to allocate
  @param  Size                   The amount of pool to allocate
  @param  NeedGuard              Flag to indicate Guard page is needed or not

  @return The allocate pool, or NULL

**/
VOID *
CoreAllocatePoolI (
  IN EFI_MEMORY_TYPE  PoolType,
  IN UINTN            Size,
  IN BOOLEAN          NeedGuard
  );

/**
  Frees pool.

  @param  Buffer                 The allocated pool entry to free
  @param  PoolType               Pointer to pool type

  @retval EFI_INVALID_PARAMETER  Buffer is not a valid value.
  @retval EFI_SUCCESS            Pool successfully freed.

**/
EFI_STATUS
EFIAPI
CoreInternalFreePool (
  IN VOID              *Buffer,
  OUT EFI_MEMORY_TYPE  *PoolType OPTIONAL
  );

/**
  Frees pool.

  @param  Buffer                 The allocated pool entry to free

  @retval EFI_INVALID_PARAMETER  Buffer is not a valid value.
  @retval EFI_SUCCESS            Pool successfully freed.

**/
EFI_STATUS
EFIAPI
CoreFreePool (
  IN VOID  *Buffer
  );

/**
  Internal function to free a pool entry.
  Caller must have the memory lock held

  @param  Buffer                 The allocated pool entry to free
  @param  PoolType               Pointer to pool type

  @retval EFI_INVALID_PARAMETER  Buffer not valid
  @retval EFI_SUCCESS            Buffer successfully freed.

**/
EFI_STATUS
CoreFreePoolI (
  IN VOID              *Buffer,
  OUT EFI_MEMORY_TYPE  *PoolType OPTIONAL
  );

#endif
