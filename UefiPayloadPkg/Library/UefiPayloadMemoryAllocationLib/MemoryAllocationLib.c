/** @file


  Copyright (c) 2008 - 2009, Apple Inc. All rights reserved.<BR>
  Copyright (c) 2020, Intel Corporation. All rights reserved.<BR>

  SPDX-License-Identifier: BSD-2-Clause-Patent

**/

#include <PiPei.h>
#include <Uefi/UefiSpec.h>

#include <Library/BaseLib.h>
#include <Library/BaseMemoryLib.h>
#include <Library/PhaseMemoryAllocationLib.h>
#include <Library/DebugLib.h>
#include <Library/HobLib.h>
#include <Guid/MemoryAllocationHob.h>

GLOBAL_REMOVE_IF_UNREFERENCED CONST EFI_MEMORY_TYPE gPhaseDefaultDataType = EfiBootServicesData;
GLOBAL_REMOVE_IF_UNREFERENCED CONST EFI_MEMORY_TYPE gPhaseDefaultCodeType = EfiBootServicesCode;

/**
  Add a new HOB to the HOB List.

  @param HobType            Type of the new HOB.
  @param HobLength          Length of the new HOB to allocate.

  @return  NULL if there is no space to create a hob.
  @return  The address point to the new created hob.

**/
VOID *
EFIAPI
CreateHob (
  IN  UINT16  HobType,
  IN  UINT16  HobLength
  );

/**
  Allocates one or more pages .

  Allocates the number of pages of MemoryType and returns a pointer to the
  allocated buffer.  The buffer returned is aligned on a 4KB boundary.
  If Pages is 0, then NULL is returned.
  If there is not enough memory availble to satisfy the request, then NULL
  is returned.

  @param   Pages                 The number of 4 KB pages to allocate.
  @param   MemoryType            The MemoryType
  @return  A pointer to the allocated buffer or NULL if allocation fails.
**/
VOID *
EFIAPI
PayloadAllocatePages (
  IN UINTN            Pages,
  IN EFI_MEMORY_TYPE  MemoryType
  )
{
  EFI_PEI_HOB_POINTERS        Hob;
  EFI_PHYSICAL_ADDRESS        Offset;
  EFI_HOB_HANDOFF_INFO_TABLE  *HobTable;

  Hob.Raw  = GetHobList ();
  HobTable = Hob.HandoffInformationTable;

  if (Pages == 0) {
    return NULL;
  }

  // Make sure allocation address is page alligned.
  Offset = HobTable->EfiFreeMemoryTop & EFI_PAGE_MASK;
  if (Offset != 0) {
    HobTable->EfiFreeMemoryTop -= Offset;
  }

  //
  // Check available memory for the allocation
  //
  if (HobTable->EfiFreeMemoryTop - ((Pages * EFI_PAGE_SIZE) + sizeof (EFI_HOB_MEMORY_ALLOCATION)) < HobTable->EfiFreeMemoryBottom) {
    return NULL;
  }

  HobTable->EfiFreeMemoryTop -= Pages * EFI_PAGE_SIZE;
  BuildMemoryAllocationHob (HobTable->EfiFreeMemoryTop, Pages * EFI_PAGE_SIZE, MemoryType);

  return (VOID *)(UINTN)HobTable->EfiFreeMemoryTop;
}

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
  EFI_PEI_HOB_POINTERS        Hob;
  EFI_PHYSICAL_ADDRESS        Offset;
  EFI_HOB_HANDOFF_INFO_TABLE  *HobTable;

  ASSERT (Type == AllocateAnyPages);

  Hob.Raw  = GetHobList ();
  HobTable = Hob.HandoffInformationTable;

  if (Pages == 0) {
    return EFI_INVALID_PARAMETER;
  }

  // Make sure allocation address is page aligned.
  Offset = HobTable->EfiFreeMemoryTop & EFI_PAGE_MASK;
  if (Offset != 0) {
    HobTable->EfiFreeMemoryTop -= Offset;
  }

  //
  // Check available memory for the allocation
  //
  if (HobTable->EfiFreeMemoryTop - ((Pages * EFI_PAGE_SIZE) + sizeof (EFI_HOB_MEMORY_ALLOCATION)) < HobTable->EfiFreeMemoryBottom) {
    return EFI_OUT_OF_RESOURCES;
  }

  HobTable->EfiFreeMemoryTop -= Pages * EFI_PAGE_SIZE;
  BuildMemoryAllocationHob (HobTable->EfiFreeMemoryTop, Pages * EFI_PAGE_SIZE, MemoryType);

  *Memory = HobTable->EfiFreeMemoryTop;
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
  return EFI_SUCCESS;
}


/**
  Allocates a buffer of type EfiBootServicesData.

  Allocates the number bytes specified by AllocationSize of type EfiBootServicesData and returns a
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
  EFI_HOB_MEMORY_POOL  *Hob;

  if (AllocationSize > 0x4000) {
    // Please use AllocatePages for big allocations
    return NULL;
  }

  Hob = (EFI_HOB_MEMORY_POOL *)CreateHob (EFI_HOB_TYPE_MEMORY_POOL, (UINT16)(sizeof (EFI_HOB_MEMORY_POOL) + AllocationSize));
  return (VOID *)(Hob + 1);
}

/**
  Frees a buffer that was previously allocated with one of the pool allocation functions in the
  Memory Allocation Library.

  Frees the buffer specified by Buffer.  Buffer must have been allocated on a previous call to the
  pool allocation services of the Memory Allocation Library.  If it is not possible to free pool
  resources, then this function will perform no actions.

  If Buffer was not allocated with a pool allocation function in the Memory Allocation Library,
  then ASSERT().

  @param  Buffer                The pointer to the buffer to free.

**/
VOID
EFIAPI
PhaseFreePool (
  IN VOID  *Buffer
  )
{
  //
  // PEI phase does not support to free pool, so leave it as NOP.
  //
}
