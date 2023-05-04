/** @file
  Support routines for memory allocation routines based
  on boot services for Dxe phase drivers using OS malloc.

  OS malloc is used so OS based malloc debugging tools can be used.
  If a single driver links against this lib protocols from other
  drivers, or EFI boot services can return a buffer that needs to
  freed using the EFI scheme. This is why the gEmuThunk->Free ()
  can detect if the memory rang is for EFI so the right free can be
  called.

  Copyright (c) 2006 - 2009, Intel Corporation. All rights reserved.<BR>
  Portions copyright (c) 2011, Apple Inc. All rights reserved.
  SPDX-License-Identifier: BSD-2-Clause-Patent

**/

#include <Uefi.h>

#include <Library/PhaseMemoryAllocationLib.h>
#include <Library/UefiBootServicesTableLib.h>
#include <Library/BaseMemoryLib.h>
#include <Library/DebugLib.h>
#include <Library/EmuThunkLib.h>

GLOBAL_REMOVE_IF_UNREFERENCED CONST EFI_MEMORY_TYPE  gPhaseDefaultDataType = EfiBootServicesData;

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
  VOID  *Buffer;

  ASSERT (Type == AllocateAnyPages);

  if (Pages == 0) {
    return EFI_INVALID_PARAMETER;
  }

  Buffer = gEmuThunk->Valloc (Pages * EFI_PAGE_SIZE);
  if (Buffer == NULL) {
    return EFI_OUT_OF_RESOURCES;
  }

  *Memory = (UINTN)Buffer;
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
  ASSERT (Pages != 0);
  if (!gEmuThunk->Free ((VOID *)(UINTN)Memory)) {
    // The Free thunk will not free memory allocated in emulated EFI memory.
    // The assmuption is this was allocated directly by EFI. We need this as some
    // times protocols or EFI BootServices can return dynamically allocated buffers.
    return gBS->FreePages (Memory, Pages);
  }

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
  return gEmuThunk->Malloc (AllocationSize);
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
  EFI_STATUS  Status;

  if (!gEmuThunk->Free (Buffer)) {
    // The Free thunk will not free memory allocated in emulated EFI memory.
    // The assmuption is this was allocated directly by EFI. We need this as some
    // times protocols or EFI BootServices can return dynamically allocated buffers.
    Status = gBS->FreePool (Buffer);
    ASSERT_EFI_ERROR (Status);
  }
}
