/** @file
  DXE Core functions necessary for pool management functions.

  Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause

  Copyright (c) 2006 - 2018, Intel Corporation. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-2-Clause-Patent

**/

#ifndef _INTERNAL_POOL_H_
#define _INTERNAL_POOL_H_

extern BOOLEAN  mOnGuarding;

/**
  Update memory profile information.

  @param CallerAddress  Address of caller who call Allocate or Free.
  @param Action         This Allocate or Free action.
  @param MemoryType     Memory type.
                        EfiMaxMemoryType means the MemoryType is unknown.
  @param Size           Buffer size.
  @param Buffer         Buffer address.
  @param ActionString   String for memory profile action.
                        Only needed for user defined allocate action.

  @return EFI_SUCCESS           Memory profile is updated.
  @return EFI_UNSUPPORTED       Memory profile is unsupported,
                                or memory profile for the image is not required,
                                or memory profile for the memory type is not required.
  @return EFI_ACCESS_DENIED     It is during memory profile data getting.
  @return EFI_ABORTED           Memory profile recording is not enabled.
  @return EFI_OUT_OF_RESOURCES  No enough resource to update memory profile for allocate action.
  @return EFI_NOT_FOUND         No matched allocate info found for free action.

**/
EFI_STATUS
EFIAPI
CoreUpdateProfile (
  IN EFI_PHYSICAL_ADDRESS   CallerAddress,
  IN MEMORY_PROFILE_ACTION  Action,
  IN EFI_MEMORY_TYPE        MemoryType,
  IN UINTN                  Size,       // Valid for AllocatePages/FreePages/AllocatePool
  IN VOID                   *Buffer,
  IN CHAR8                  *ActionString OPTIONAL
  );

/**
  Install MemoryAttributesTable on memory allocation.

  @param[in] MemoryType EFI memory type.
**/
VOID
InstallMemoryAttributesTableOnMemoryAllocation (
  IN EFI_MEMORY_TYPE  MemoryType
  );

/**
  Internal function.  Frees guarded pool pages.

  @param  PoolType               The type of memory for the pool pages
  @param  Memory                 The base address to free
  @param  NoPages                The number of pages to free

**/
VOID
CoreFreePoolPagesWithGuard (
  IN EFI_MEMORY_TYPE       PoolType,
  IN EFI_PHYSICAL_ADDRESS  Memory,
  IN UINTN                 NoPages
  );

/**
  Check to see if the page at the given address is guarded or not.

  @param[in]  Address     The address to check for.

  @return TRUE  The page at Address is guarded.
  @return FALSE The page at Address is not guarded.
**/
BOOLEAN
EFIAPI
IsMemoryGuarded (
  IN EFI_PHYSICAL_ADDRESS  Address
  );

/**
  Internal function.  Used by the pool functions to allocate pages
  to back pool allocation requests.

  @param  PoolType               The type of memory for the new pool pages
  @param  NoPages                No of pages to allocate
  @param  Granularity            Bits to align.
  @param  NeedGuard              Flag to indicate Guard page is needed or not

  @return The allocated memory, or NULL

**/
VOID *
CoreAllocatePoolPagesI (
  IN EFI_MEMORY_TYPE  PoolType,
  IN UINTN            NoPages,
  IN UINTN            Granularity,
  IN BOOLEAN          NeedGuard
  );

/**
  Internal function.  Frees pool pages allocated via CoreAllocatePoolPagesI().

  @param  PoolType               The type of memory for the pool pages
  @param  Memory                 The base address to free
  @param  NoPages                The number of pages to free

**/
VOID
CoreFreePoolPagesI (
  IN EFI_MEMORY_TYPE       PoolType,
  IN EFI_PHYSICAL_ADDRESS  Memory,
  IN UINTN                 NoPages
  );

#endif
