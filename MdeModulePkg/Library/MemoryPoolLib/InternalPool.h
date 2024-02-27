/** @file
  DXE Core functions necessary for pool management functions.

  Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause

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
  Adjust the pool head position to make sure the Guard page is adjavent to
  pool tail or pool head.

  @param[in]  Memory    Base address of memory allocated.
  @param[in]  NoPages   Number of pages actually allocated.
  @param[in]  Size      Size of memory requested.
                        (plus pool head/tail overhead)

  @return Address of pool head.
**/
VOID *
AdjustPoolHeadA (
  IN EFI_PHYSICAL_ADDRESS  Memory,
  IN UINTN                 NoPages,
  IN UINTN                 Size
  );

/**
  Adjust the start address and number of pages to free according to Guard.

  The purpose of this function is to keep the shared Guard page with adjacent
  memory block if it's still in guard, or free it if no more sharing. Another
  is to reserve pages as Guard pages in partial page free situation.

  @param[in,out]  Memory          Base address of memory to free.
  @param[in,out]  NumberOfPages   Size of memory to free.

  @return VOID.
**/
VOID
AdjustMemoryF (
  IN OUT EFI_PHYSICAL_ADDRESS  *Memory,
  IN OUT UINTN                 *NumberOfPages
  );

/**
  Unset head Guard and tail Guard for the given memory range.

  @param[in]  Memory          Base address of memory to unset guard for.
  @param[in]  NumberOfPages   Memory size in pages.

  @return VOID.
**/
VOID
UnsetGuardForMemory (
  IN EFI_PHYSICAL_ADDRESS  Memory,
  IN UINTN                 NumberOfPages
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
  Get the page base address according to pool head address.

  @param[in]  Memory    Head address of pool to free.
  @param[in]  NoPages   Number of pages actually allocated.
  @param[in]  Size      Size of memory requested.
                        (plus pool head/tail overhead)

  @return Address of pool head.
**/
VOID *
AdjustPoolHeadF (
  IN EFI_PHYSICAL_ADDRESS  Memory,
  IN UINTN                 NoPages,
  IN UINTN                 Size
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
