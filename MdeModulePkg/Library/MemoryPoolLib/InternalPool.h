/** @file
  DXE Core functions necessary for pool management functions.

  Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause

**/

#ifndef _INTERNAL_POOL_H_
#define _INTERNAL_POOL_H_

extern BOOLEAN  mOnGuarding;
extern EFI_LOCK gMemoryLock;

#define GUARD_HEAP_TYPE_FREED  BIT4

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
  Internal function.  Used by the pool functions to allocate pages
  to back pool allocation requests.

  @param  PoolType               The type of memory for the new pool pages
  @param  NumberOfPages          No of pages to allocate
  @param  Alignment              Bits to align.
  @param  NeedGuard              Flag to indicate Guard page is needed or not

  @return The allocated memory, or NULL

**/
VOID *
CoreAllocatePoolPages (
  IN EFI_MEMORY_TYPE  PoolType,
  IN UINTN            NumberOfPages,
  IN UINTN            Alignment,
  IN BOOLEAN          NeedGuard
  );

/**
  Exit critical section by releasing lock on gMemoryLock.

**/
VOID
CoreReleaseMemoryLock (
  VOID
  );

/**
  Set head Guard and tail Guard for the given memory range.

  @param[in]  Memory          Base address of memory to set guard for.
  @param[in]  NumberOfPages   Memory size in pages.

  @return VOID.
**/
VOID
SetGuardForMemory (
  IN EFI_PHYSICAL_ADDRESS  Memory,
  IN UINTN                 NumberOfPages
  );

/**
  Manage memory permission attributes on a memory range, according to the
  configured DXE memory protection policy.

  @param  OldType           The old memory type of the range
  @param  NewType           The new memory type of the range
  @param  Memory            The base address of the range
  @param  Length            The size of the range (in bytes)

  @return EFI_SUCCESS       If the the CPU arch protocol is not installed yet
  @return EFI_SUCCESS       If no DXE memory protection policy has been configured
  @return EFI_SUCCESS       If OldType and NewType use the same permission attributes
  @return other             Return value of gCpu->SetMemoryAttributes()

**/
EFI_STATUS
EFIAPI
ApplyMemoryProtectionPolicy (
  IN  EFI_MEMORY_TYPE       OldType,
  IN  EFI_MEMORY_TYPE       NewType,
  IN  EFI_PHYSICAL_ADDRESS  Memory,
  IN  UINT64                Length
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
  Enter critical section by gaining lock on gMemoryLock.

**/
VOID
CoreAcquireMemoryLock (
  VOID
  );

/**
  Internal function.  Frees pool pages allocated via AllocatePoolPages ()

  @param  Memory                 The base address to free
  @param  NumberOfPages          The number of pages to free

**/
VOID
CoreFreePoolPages (
  IN EFI_PHYSICAL_ADDRESS  Memory,
  IN UINTN                 NumberOfPages
  );

/**
  Record freed pages as well as mark them as not-present, if enabled.

  @param[in]  BaseAddress   Base address of just freed pages.
  @param[in]  Pages         Number of freed pages.

  @return VOID.
**/
VOID
EFIAPI
GuardFreedPagesChecked (
  IN  EFI_PHYSICAL_ADDRESS  BaseAddress,
  IN  UINTN                 Pages
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

#endif
