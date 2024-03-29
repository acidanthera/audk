/** @file
  Implementation of the 6 PEI Ffs (FV) APIs in library form.

  Copyright (c) 2008 - 2009, Apple Inc. All rights reserved.<BR>

  SPDX-License-Identifier: BSD-2-Clause-Patent

**/

#include <PiPei.h>
#include <Uefi/UefiSpec.h>

#include <Library/BaseLib.h>
#include <Library/BaseMemoryLib.h>
#include <Library/PrePiLib.h>
#include <Library/DebugLib.h>

GLOBAL_REMOVE_IF_UNREFERENCED CONST EFI_MEMORY_TYPE gPhaseDefaultDataType = EfiBootServicesData;
GLOBAL_REMOVE_IF_UNREFERENCED CONST EFI_MEMORY_TYPE gPhaseDefaultCodeType = EfiBootServicesCode;

EFI_STATUS
EFIAPI
PhaseAllocatePages (
  IN     EFI_ALLOCATE_TYPE     Type,
  IN     EFI_MEMORY_TYPE       MemoryType,
  IN     UINTN                 Pages,
  IN OUT EFI_PHYSICAL_ADDRESS  *Memory
  )
{
  EFI_PEI_HOB_POINTERS  Hob;
  EFI_PHYSICAL_ADDRESS  NewTop;

  ASSERT (Type == AllocateAnyPages);

  Hob.Raw = GetHobList ();

  NewTop  = Hob.HandoffInformationTable->EfiFreeMemoryTop & ~(EFI_PHYSICAL_ADDRESS)EFI_PAGE_MASK;
  NewTop -= Pages * EFI_PAGE_SIZE;

  //
  // Verify that there is sufficient memory to satisfy the allocation
  //
  if (NewTop < (Hob.HandoffInformationTable->EfiFreeMemoryBottom + sizeof (EFI_HOB_MEMORY_ALLOCATION))) {
    return EFI_OUT_OF_RESOURCES;
  }

  //
  // Update the PHIT to reflect the memory usage
  //
  Hob.HandoffInformationTable->EfiFreeMemoryTop = NewTop;

  //
  // Create a memory allocation HOB.
  //
  BuildMemoryAllocationHob (
    Hob.HandoffInformationTable->EfiFreeMemoryTop,
    Pages * EFI_PAGE_SIZE,
    MemoryType
    );

  *Memory = Hob.HandoffInformationTable->EfiFreeMemoryTop;
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
  // For now, we do not support the ability to free pages in the PrePei Memory Allocator.
  // The allocated memory is lost.
  return EFI_SUCCESS;
}

/**
  Allocates a buffer of type EfiBootServicesData.

  Allocates the number bytes specified by AllocationSize of type EfiBootServicesData and returns a
  pointer to the allocated buffer.  If AllocationSize is 0, then a valid buffer of 0 size is
  returned.  If there is not enough memory remaining to satisfy the request, then NULL is returned.

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
  EFI_HOB_MEMORY_POOL  *Hob;

  Hob = GetHobList ();

  //
  // Verify that there is sufficient memory to satisfy the allocation
  //
  if (AllocationSize > 0x10000) {
    // Please call AllocatePages for big allocations
    return 0;
  } else {
    Hob = (EFI_HOB_MEMORY_POOL *)CreateHob (
                                   EFI_HOB_TYPE_MEMORY_POOL,
                                   (UINT16)(sizeof (EFI_HOB_MEMORY_POOL) +
                                            AllocationSize)
                                   );
    return (VOID *)(Hob + 1);
  }
}

/**
  Frees a buffer that was previously allocated with one of the pool allocation functions in the
  Memory Allocation Library.

  Frees the buffer specified by Buffer.  Buffer must have been allocated on a previous call to the
  pool allocation services of the Memory Allocation Library.  If it is not possible to free pool
  resources, then this function will perform no actions.

  If Buffer was not allocated with a pool allocation function in the Memory Allocation Library,
  then ASSERT().

  @param  Buffer                Pointer to the buffer to free.

**/
VOID
EFIAPI
PhaseFreePool (
  IN VOID  *Buffer
  )
{
  // Not implemented yet
}
