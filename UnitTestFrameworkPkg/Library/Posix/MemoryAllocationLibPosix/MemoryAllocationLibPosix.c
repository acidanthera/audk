/** @file
  Instance of Memory Allocation Library based on POSIX APIs

  Uses POSIX APIs malloc() and free() to allocate and free memory.

  Copyright (c) 2018 - 2020, Intel Corporation. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-2-Clause-Patent
**/

#include <stdlib.h>
#include <string.h>

#include <Uefi.h>
#include <Library/PhaseMemoryAllocationLib.h>
#include <Library/DebugLib.h>

///
/// Signature for PAGE_HEAD structure
/// Used to verify that buffer being freed was allocated by this library.
///
#define PAGE_HEAD_PRIVATE_SIGNATURE  SIGNATURE_32 ('P', 'H', 'D', 'R')

///
/// Structure placed immediately before an aligned allocation to store the
/// information required to free the entire buffer allocated to support then
/// aligned allocation.
///
typedef struct {
  UINT32    Signature;
  VOID      *AllocatedBuffer;
  UINTN     TotalPages;
  VOID      *AlignedBuffer;
  UINTN     AlignedPages;
} PAGE_HEAD;

#define POOL_HEAD_PRIVATE_SIGNATURE  SIGNATURE_32 ('P', 'O', 'H', 'D')

typedef struct {
  UINT32    Signature;
  UINT32    TotalSize;
} POOL_HEAD;

GLOBAL_REMOVE_IF_UNREFERENCED CONST EFI_MEMORY_TYPE gPhaseDefaultDataType = EfiBootServicesData;
GLOBAL_REMOVE_IF_UNREFERENCED CONST EFI_MEMORY_TYPE gPhaseDefaultCodeType = EfiBootServicesCode;

/**
  Allocates one or more 4KB pages of a certain memory type.

  Allocates the number of 4KB pages of a certain memory type and returns a pointer
  to the allocated buffer.  The buffer returned is aligned on a 4KB boundary.

  @param  Type                  The type of allocation to perform.
  @param  MemoryType            The type of memory to allocate.
  @param  Pages                 The number of 4 KB pages to allocate.
  @param  Memory                The pointer to a physical address. On input, the
                                way in which the address is used depends on the
                                value of Type.

  @retval EFI_SUCCESS           The requested pages were allocated.
  @retval EFI_INVALID_PARAMETER 1) Type is not AllocateAnyPages or
                                AllocateMaxAddress or AllocateAddress.
                                2) MemoryType is in the range
                                EfiMaxMemoryType..0x6FFFFFFF.
                                3) Memory is NULL.
                                4) MemoryType is EfiPersistentMemory.
  @retval EFI_OUT_OF_RESOURCES  The pages could not be allocated.
  @retval EFI_NOT_FOUND         The requested pages could not be found.

**/
EFI_STATUS
EFIAPI
PhaseAllocatePages (
  IN     EFI_ALLOCATE_TYPE     Type,
  IN     EFI_MEMORY_TYPE       MemoryType,
  IN     UINTN                 Pages,
  IN OUT EFI_PHYSICAL_ADDRESS  *Memory
  )
{
  PAGE_HEAD  PageHead;
  PAGE_HEAD  *PageHeadPtr;
  UINTN      Alignment;
  UINTN      AlignmentMask;

  ASSERT (Type == AllocateAnyPages);

  Alignment     = SIZE_4KB;
  AlignmentMask = Alignment - 1;

  //
  // We need reserve Alignment pages for PAGE_HEAD, as meta data.
  //
  PageHead.Signature       = PAGE_HEAD_PRIVATE_SIGNATURE;
  PageHead.TotalPages      = Pages + EFI_SIZE_TO_PAGES (Alignment) * 2;
  PageHead.AlignedPages    = Pages;
  PageHead.AllocatedBuffer = malloc (EFI_PAGES_TO_SIZE (PageHead.TotalPages));
  if (PageHead.AllocatedBuffer == NULL) {
    return EFI_OUT_OF_RESOURCES;
  }

  ASSERT (PageHead.AllocatedBuffer != NULL);

  DEBUG_CLEAR_MEMORY (PageHead.AllocatedBuffer, EFI_PAGES_TO_SIZE (PageHead.TotalPages));

  PageHead.AlignedBuffer = (VOID *)(((UINTN)PageHead.AllocatedBuffer + AlignmentMask) & ~AlignmentMask);
  if ((UINTN)PageHead.AlignedBuffer - (UINTN)PageHead.AllocatedBuffer < sizeof (PAGE_HEAD)) {
    PageHead.AlignedBuffer = (VOID *)((UINTN)PageHead.AlignedBuffer + Alignment);
  }

  PageHeadPtr = (VOID *)((UINTN)PageHead.AlignedBuffer - sizeof (PAGE_HEAD));
  memcpy (PageHeadPtr, &PageHead, sizeof (PAGE_HEAD));

  *Memory = (UINTN)PageHead.AlignedBuffer;
  return EFI_SUCCESS;
}

/**
  Frees one or more 4KB pages that were previously allocated with one of the page allocation
  functions in the Memory Allocation Library.

  Frees the number of 4KB pages specified by Pages from the buffer specified by Buffer.
  Buffer must have been allocated on a previous call to the page allocation services
  of the Memory Allocation Library.  If it is not possible to free allocated pages,
  then this function will perform no actions.

  If Buffer was not allocated with a page allocation function in the Memory Allocation
  Library, then ASSERT().
  If Pages is zero, then ASSERT().

  @param  Memory                The base physical address of the pages to be freed.
  @param  Pages                 The number of 4 KB pages to free.

  @retval EFI_SUCCESS           The requested pages were freed.
  @retval EFI_NOT_FOUND         The requested memory pages were not allocated with
                                PhaseAllocatePages().

**/
EFI_STATUS
EFIAPI
PhaseFreePages (
  IN EFI_PHYSICAL_ADDRESS  Memory,
  IN UINTN                 Pages
  )
{
  PAGE_HEAD  *PageHeadPtr;
  VOID       *AllocatedBuffer;
  UINTN      Length;

  ASSERT (Memory != NULL);

  PageHeadPtr = ((PAGE_HEAD *)Memory) - 1;

  ASSERT (PageHeadPtr != NULL);
  ASSERT (PageHeadPtr->Signature == PAGE_HEAD_PRIVATE_SIGNATURE);
  ASSERT (PageHeadPtr->AlignedPages == Pages);
  ASSERT (PageHeadPtr->AllocatedBuffer != NULL);

  AllocatedBuffer = PageHeadPtr->AllocatedBuffer;
  Length          = EFI_PAGES_TO_SIZE (PageHeadPtr->TotalPages);

  DEBUG_CLEAR_MEMORY (AllocatedBuffer, Length);

  free (AllocatedBuffer);

  return EFI_SUCCESS;
}

/**
  Allocates a buffer of a certain pool type.

  Allocates the number bytes specified by AllocationSize of a certain pool type and returns a
  pointer to the allocated buffer.  If AllocationSize is 0, then a valid buffer of 0 size is
  returned.  If there is not enough memory remaining to satisfy the request, then NULL is returned.

  @param  MemoryType            The type of memory to allocate.
  @param  AllocationSize        The number of bytes to allocate.

  @return A pointer to the allocated buffer or NULL if allocation fails.

**/
VOID *
EFIAPI
PhaseAllocatePool (
  IN EFI_MEMORY_TYPE  MemoryType,
  IN UINTN            AllocationSize
  )
{
  POOL_HEAD  *PoolHead;
  UINTN      TotalSize;

  TotalSize = sizeof (POOL_HEAD) + AllocationSize;
  PoolHead  = malloc (TotalSize);
  if (PoolHead == NULL) {
    return NULL;
  }

  DEBUG_CLEAR_MEMORY (PoolHead, TotalSize);
  PoolHead->Signature = POOL_HEAD_PRIVATE_SIGNATURE;
  PoolHead->TotalSize = (UINT32)TotalSize;

  return (VOID *)(PoolHead + 1);
}

/**
  Frees a buffer that was previously allocated with one of the pool allocation functions in the
  Memory Allocation Library.

  Frees the buffer specified by Buffer.  Buffer must have been allocated on a previous call to the
  pool allocation services of the Memory Allocation Library.  If it is not possible to free pool
  resources, then this function will perform no actions.

  If Buffer was not allocated with a pool allocation function in the Memory Allocation Library,
  then ASSERT().

  @param  Buffer  The pointer to the buffer to free.

**/
VOID
EFIAPI
PhaseFreePool (
  IN VOID  *Buffer
  )
{
  POOL_HEAD  *PoolHead;

  ASSERT (Buffer != NULL);

  PoolHead = ((POOL_HEAD *)Buffer) - 1;

  ASSERT (PoolHead != NULL);
  ASSERT (PoolHead->Signature == POOL_HEAD_PRIVATE_SIGNATURE);
  ASSERT (PoolHead->TotalSize >= sizeof (POOL_HEAD));

  DEBUG_CLEAR_MEMORY (PoolHead, PoolHead->TotalSize);
  free (PoolHead);
}
