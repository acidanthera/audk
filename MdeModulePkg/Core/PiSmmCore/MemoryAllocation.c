/** @file
  Support routines for memory allocation routines based on SMM Core internal functions,
  with memory profile support.

  The PI System Management Mode Core Interface Specification only allows the use
  of EfiRuntimeServicesCode and EfiRuntimeServicesData memory types for memory
  allocations as the SMRAM space should be reserved after BDS phase.  The functions
  in the Memory Allocation Library use EfiBootServicesData as the default memory
  allocation type.  For this SMM specific instance of the Memory Allocation Library,
  EfiRuntimeServicesData is used as the default memory type for all allocations.
  In addition, allocation for the Reserved memory types are not supported and will
  always return NULL.

  Copyright (c) 2006 - 2018, Intel Corporation. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-2-Clause-Patent

**/

#include <PiSmm.h>

#include <Library/PhaseMemoryAllocationLib.h>
#include <Library/UefiBootServicesTableLib.h>
#include <Library/BaseMemoryLib.h>
#include <Library/DebugLib.h>
#include "PiSmmCore.h"
#include "PiSmmCorePrivateData.h"

#include <Library/MemoryProfileLib.h>

GLOBAL_REMOVE_IF_UNREFERENCED CONST EFI_MEMORY_TYPE  gPhaseDefaultDataType = EfiRuntimeServicesData;

EFI_SMRAM_DESCRIPTOR  *mSmmCoreMemoryAllocLibSmramRanges    = NULL;
UINTN                 mSmmCoreMemoryAllocLibSmramRangeCount = 0;

/**
  Check whether the start address of buffer is within any of the SMRAM ranges.

  @param[in]  Buffer   The pointer to the buffer to be checked.

  @retval     TRUE     The buffer is in SMRAM ranges.
  @retval     FALSE    The buffer is out of SMRAM ranges.
**/
BOOLEAN
EFIAPI
BufferInSmram (
  IN EFI_PHYSICAL_ADDRESS  Buffer
  )
{
  UINTN  Index;

  for (Index = 0; Index < mSmmCoreMemoryAllocLibSmramRangeCount; Index++) {
    if ((Buffer >= mSmmCoreMemoryAllocLibSmramRanges[Index].CpuStart) &&
        (Buffer < (mSmmCoreMemoryAllocLibSmramRanges[Index].CpuStart + mSmmCoreMemoryAllocLibSmramRanges[Index].PhysicalSize)))
    {
      return TRUE;
    }
  }

  return FALSE;
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
  if (Pages == 0) {
    return EFI_INVALID_PARAMETER;
  }

  return SmmAllocatePages (Type, MemoryType, Pages, Memory);
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
  EFI_STATUS  Status;

  ASSERT (Pages != 0);
  if (BufferInSmram (Memory)) {
    //
    // When Buffer is in SMRAM range, it should be allocated by SmmAllocatePages() service.
    // So, SmmFreePages() service is used to free it.
    //
    Status = SmmFreePages (Memory, Pages);
  } else {
    //
    // When Buffer is out of SMRAM range, it should be allocated by gBS->AllocatePages() service.
    // So, gBS->FreePages() service is used to free it.
    //
    Status = gBS->FreePages (Memory, Pages);
  }

  return Status;
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
  EFI_STATUS  Status;
  VOID        *Memory;

  Memory = NULL;

  Status = SmmAllocatePool (MemoryType, AllocationSize, &Memory);
  if (EFI_ERROR (Status)) {
    Memory = NULL;
  }

  return Memory;
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
  EFI_STATUS  Status;

  if (BufferInSmram ((UINTN)Buffer)) {
    //
    // When Buffer is in SMRAM range, it should be allocated by SmmAllocatePool() service.
    // So, SmmFreePool() service is used to free it.
    //
    Status = SmmFreePool (Buffer);
  } else {
    //
    // When Buffer is out of SMRAM range, it should be allocated by gBS->AllocatePool() service.
    // So, gBS->FreePool() service is used to free it.
    //
    Status = gBS->FreePool (Buffer);
  }

  ASSERT_EFI_ERROR (Status);
}

/**
  The constructor function calls SmmInitializeMemoryServices to initialize memory in SMRAM.

  @param  ImageHandle   The firmware allocated handle for the EFI image.
  @param  SystemTable   A pointer to the EFI System Table.

  @retval EFI_SUCCESS   The constructor always returns EFI_SUCCESS.

**/
EFI_STATUS
EFIAPI
PiSmmCoreMemoryAllocationLibConstructor (
  IN EFI_HANDLE        ImageHandle,
  IN EFI_SYSTEM_TABLE  *SystemTable
  )
{
  EFI_STATUS             Status;
  SMM_CORE_PRIVATE_DATA  *SmmCorePrivate;
  UINTN                  Size;
  VOID                   *BootServicesData;

  SmmCorePrivate = (SMM_CORE_PRIVATE_DATA *)ImageHandle;

  //
  // The FreePool()/FreePages() will need use SmramRanges data to know whether
  // the buffer to free is in SMRAM range or not. And there may be FreePool()/
  // FreePages() indrectly during calling SmmInitializeMemoryServices(), but
  // no SMRAM could be allocated before calling SmmInitializeMemoryServices(),
  // so temporarily use BootServicesData to hold the SmramRanges data.
  //
  mSmmCoreMemoryAllocLibSmramRangeCount = SmmCorePrivate->SmramRangeCount;
  Size                                  = mSmmCoreMemoryAllocLibSmramRangeCount * sizeof (EFI_SMRAM_DESCRIPTOR);
  Status                                = gBS->AllocatePool (EfiBootServicesData, Size, (VOID **)&mSmmCoreMemoryAllocLibSmramRanges);
  ASSERT_EFI_ERROR (Status);
  ASSERT (mSmmCoreMemoryAllocLibSmramRanges != NULL);
  CopyMem (mSmmCoreMemoryAllocLibSmramRanges, SmmCorePrivate->SmramRanges, Size);

  //
  // Initialize memory service using free SMRAM
  //
  SmmInitializeMemoryServices (SmmCorePrivate->SmramRangeCount, SmmCorePrivate->SmramRanges);

  //
  // Move the SmramRanges data from BootServicesData to SMRAM.
  //
  BootServicesData                  = mSmmCoreMemoryAllocLibSmramRanges;
  mSmmCoreMemoryAllocLibSmramRanges = (EFI_SMRAM_DESCRIPTOR *)AllocateCopyPool (Size, (VOID *)BootServicesData);
  ASSERT (mSmmCoreMemoryAllocLibSmramRanges != NULL);

  //
  // Free the temporarily used BootServicesData.
  //
  Status = gBS->FreePool (BootServicesData);
  ASSERT_EFI_ERROR (Status);

  return EFI_SUCCESS;
}
