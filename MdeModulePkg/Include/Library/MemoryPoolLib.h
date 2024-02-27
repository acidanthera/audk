/** @file
  UEFI Memory pool management functions.

Copyright (c) 2006 - 2018, Intel Corporation. All rights reserved.<BR>
SPDX-License-Identifier: BSD-2-Clause-Patent

**/

#ifndef _MEMORY_POOL_LIB_H_
#define _MEMORY_POOL_LIB_H_

#include <Library/UefiLib.h>

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

//
// Memory type to guard (matching the related PCD definition)
//
#define GUARD_HEAP_TYPE_PAGE   BIT0
#define GUARD_HEAP_TYPE_POOL   BIT1
#define GUARD_HEAP_TYPE_FREED  BIT4
#define GUARD_HEAP_TYPE_ALL         \
        (GUARD_HEAP_TYPE_PAGE|GUARD_HEAP_TYPE_POOL|GUARD_HEAP_TYPE_FREED)

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

/**
  Check to see if the heap guard is enabled for page and/or pool allocation.

  @param[in]  GuardType   Specify the sub-type(s) of Heap Guard.

  @return TRUE/FALSE.
**/
BOOLEAN
IsHeapGuardEnabled (
  UINT8  GuardType
  );

/**
  Check to see if the pool at the given address should be guarded or not.

  @param[in]  MemoryType      Pool type to check.


  @return TRUE  The given type of pool should be guarded.
  @return FALSE The given type of pool should not be guarded.
**/
BOOLEAN
IsPoolTypeToGuard (
  IN EFI_MEMORY_TYPE  MemoryType
  );

/**
  Check to see if the memory at the given address should be guarded or not.

  @param[in]  MemoryType      Memory type to check.
  @param[in]  AllocateType    Allocation type to check.
  @param[in]  PageOrPool      Indicate a page allocation or pool allocation.


  @return TRUE  The given type of memory should be guarded.
  @return FALSE The given type of memory should not be guarded.
**/
BOOLEAN
IsMemoryTypeToGuard (
  IN EFI_MEMORY_TYPE    MemoryType,
  IN EFI_ALLOCATE_TYPE  AllocateType,
  IN UINT8              PageOrPool
  );

/**
  Raising to the task priority level of the mutual exclusion
  lock, and then acquires ownership of the lock.

  @param  Lock               The lock to acquire

  @return Lock owned

**/
VOID
CoreAcquireLock (
  IN EFI_LOCK  *Lock
  );

/**
  Initialize a basic mutual exclusion lock.   Each lock
  provides mutual exclusion access at it's task priority
  level.  Since there is no-premption (at any TPL) or
  multiprocessor support, acquiring the lock only consists
  of raising to the locks TPL.

  @param  Lock               The EFI_LOCK structure to initialize

  @retval EFI_SUCCESS        Lock Owned.
  @retval EFI_ACCESS_DENIED  Reentrant Lock Acquisition, Lock not Owned.

**/
EFI_STATUS
CoreAcquireLockOrFail (
  IN EFI_LOCK  *Lock
  );

/**
  Releases ownership of the mutual exclusion lock, and
  restores the previous task priority level.

  @param  Lock               The lock to release

  @return Lock unowned

**/
VOID
CoreReleaseLock (
  IN EFI_LOCK  *Lock
  );

#endif
