/** @file
  Common code for the Memory Allocation Library based on
  PhaseMemoryAllocationLib.

  Copyright (c) 2006 - 2018, Intel Corporation. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-2-Clause-Patent

**/

#include <Base.h>
#include <Uefi/UefiBaseType.h>
#include <Uefi/UefiSpec.h>

#include <Library/MemoryAllocationLib.h>
#include <Library/MemoryAllocationLibEx.h>
#include <Library/PhaseMemoryAllocationLib.h>
#include <Library/BaseMemoryLib.h>
#include <Library/DebugLib.h>

#include <Library/MemoryProfileLib.h>

#include "AlignedPages.h"

/**
  Allocates one or more 4KB pages of type EfiBootServicesData.

  Allocates the number of 4KB pages of type EfiBootServicesData and returns a pointer to the
  allocated buffer.  The buffer returned is aligned on a 4KB boundary.  If Pages is 0, then NULL
  is returned.  If there is not enough memory remaining to satisfy the request, then NULL is
  returned.

  @param  Pages                 The number of 4 KB pages to allocate.

  @return A pointer to the allocated buffer or NULL if allocation fails.

**/
VOID *
EFIAPI
AllocatePages (
  IN UINTN  Pages
  )
{
  EFI_STATUS           Status;
  EFI_PHYSICAL_ADDRESS Memory;
  VOID                 *Buffer;

  Status = PhaseAllocatePages (AllocateAnyPages, gPhaseDefaultDataType, Pages, &Memory);
  if (EFI_ERROR (Status)) {
    return NULL;
  }

  Buffer = (VOID *)(UINTN)Memory;

  MemoryProfileLibRecord (
    (PHYSICAL_ADDRESS)(UINTN)RETURN_ADDRESS (0),
    MEMORY_PROFILE_ACTION_LIB_ALLOCATE_PAGES,
    gPhaseDefaultDataType,
    Buffer,
    EFI_PAGES_TO_SIZE (Pages),
    NULL
    );

  return Buffer;
}

/**
  Allocates one or more 4KB pages of type EfiRuntimeServicesData.

  Allocates the number of 4KB pages of type EfiRuntimeServicesData and returns a pointer to the
  allocated buffer.  The buffer returned is aligned on a 4KB boundary.  If Pages is 0, then NULL
  is returned.  If there is not enough memory remaining to satisfy the request, then NULL is
  returned.

  @param  Pages                 The number of 4 KB pages to allocate.

  @return A pointer to the allocated buffer or NULL if allocation fails.

**/
VOID *
EFIAPI
AllocateRuntimePages (
  IN UINTN  Pages
  )
{
  EFI_STATUS           Status;
  EFI_PHYSICAL_ADDRESS Memory;
  VOID                 *Buffer;

  Status = PhaseAllocatePages (AllocateAnyPages, EfiRuntimeServicesData, Pages, &Memory);
  if (EFI_ERROR (Status)) {
    return NULL;
  }

  Buffer = (VOID *)(UINTN)Memory;

  MemoryProfileLibRecord (
    (PHYSICAL_ADDRESS)(UINTN)RETURN_ADDRESS (0),
    MEMORY_PROFILE_ACTION_LIB_ALLOCATE_RUNTIME_PAGES,
    EfiRuntimeServicesData,
    Buffer,
    EFI_PAGES_TO_SIZE (Pages),
    NULL
    );

  return Buffer;
}

/**
  Allocates one or more 4KB pages of type EfiReservedMemoryType.

  Allocates the number of 4KB pages of type EfiReservedMemoryType and returns a pointer to the
  allocated buffer.  The buffer returned is aligned on a 4KB boundary.  If Pages is 0, then NULL
  is returned.  If there is not enough memory remaining to satisfy the request, then NULL is
  returned.

  @param  Pages                 The number of 4 KB pages to allocate.

  @return A pointer to the allocated buffer or NULL if allocation fails.

**/
VOID *
EFIAPI
AllocateReservedPages (
  IN UINTN  Pages
  )
{
  EFI_STATUS           Status;
  EFI_PHYSICAL_ADDRESS Memory;
  VOID                 *Buffer;

  Status = PhaseAllocatePages (AllocateAnyPages, EfiReservedMemoryType, Pages, &Memory);
  if (EFI_ERROR (Status)) {
    return NULL;
  }

  Buffer = (VOID *)(UINTN)Memory;

  MemoryProfileLibRecord (
    (PHYSICAL_ADDRESS)(UINTN)RETURN_ADDRESS (0),
    MEMORY_PROFILE_ACTION_LIB_ALLOCATE_RESERVED_PAGES,
    EfiReservedMemoryType,
    Buffer,
    EFI_PAGES_TO_SIZE (Pages),
    NULL
    );

  return Buffer;
}

/**
  Allocates one or more 4KB pages of type EfiBootServicesCode.

  Allocates the number of 4KB pages of type EfiBootServicesCode and returns a pointer to the
  allocated buffer.  The buffer returned is aligned on a 4KB boundary.  If Pages is 0, then NULL
  is returned.  If there is not enough memory remaining to satisfy the request, then NULL is
  returned.

  @param  Pages                 The number of 4 KB pages to allocate.

  @return A pointer to the allocated buffer or NULL if allocation fails.

**/
VOID *
EFIAPI
AllocateCodePages (
  IN UINTN  Pages
  )
{
  EFI_STATUS           Status;
  EFI_PHYSICAL_ADDRESS Memory;

  Status = PhaseAllocatePages (AllocateAnyPages, gPhaseDefaultCodeType, Pages, &Memory);
  if (EFI_ERROR (Status)) {
    return NULL;
  }

  return (VOID *)(UINTN)Memory;
}

/**
  Frees one or more 4KB pages that were previously allocated with one of the page allocation
  functions in the Memory Allocation Library.

  Frees the number of 4KB pages specified by Pages from the buffer specified by Buffer.  Buffer
  must have been allocated on a previous call to the page allocation services of the Memory
  Allocation Library.  If it is not possible to free allocated pages, then this function will
  perform no actions.

  If Buffer was not allocated with a page allocation function in the Memory Allocation Library,
  then ASSERT().
  If Pages is zero, then ASSERT().

  @param  Buffer                Pointer to the buffer of pages to free.
  @param  Pages                 The number of 4 KB pages to free.

**/
VOID
EFIAPI
FreePages (
  IN VOID   *Buffer,
  IN UINTN  Pages
  )
{
  EFI_STATUS Status;

  Status = PhaseFreePages ((UINTN)Buffer, Pages);
  ASSERT_EFI_ERROR (Status);
}

/**
  Allocates one or more 4KB pages of type EfiBootServicesData at a specified alignment.

  Allocates the number of 4KB pages specified by Pages of type EfiBootServicesData with an
  alignment specified by Alignment.  The allocated buffer is returned.  If Pages is 0, then NULL is
  returned.  If there is not enough memory at the specified alignment remaining to satisfy the
  request, then NULL is returned.

  If Alignment is not a power of two and Alignment is not zero, then ASSERT().
  If Pages plus EFI_SIZE_TO_PAGES (Alignment) overflows, then ASSERT().

  @param  Pages                 The number of 4 KB pages to allocate.
  @param  Alignment             The requested alignment of the allocation.  Must be a power of two.
                                If Alignment is zero, then byte alignment is used.

  @return A pointer to the allocated buffer or NULL if allocation fails.

**/
VOID *
EFIAPI
AllocateAlignedPages (
  IN UINTN  Pages,
  IN UINTN  Alignment
  )
{
  VOID  *Buffer;

  Buffer = InternalAllocateAlignedPages (gPhaseDefaultDataType, Pages, Alignment);
  if (Buffer != NULL) {
    MemoryProfileLibRecord (
      (PHYSICAL_ADDRESS)(UINTN)RETURN_ADDRESS (0),
      MEMORY_PROFILE_ACTION_LIB_ALLOCATE_ALIGNED_PAGES,
      gPhaseDefaultDataType,
      Buffer,
      EFI_PAGES_TO_SIZE (Pages),
      NULL
      );
  }

  return Buffer;
}

/**
  Allocates one or more 4KB pages of type EfiRuntimeServicesData at a specified alignment.

  Allocates the number of 4KB pages specified by Pages of type EfiRuntimeServicesData with an
  alignment specified by Alignment.  The allocated buffer is returned.  If Pages is 0, then NULL is
  returned.  If there is not enough memory at the specified alignment remaining to satisfy the
  request, then NULL is returned.

  If Alignment is not a power of two and Alignment is not zero, then ASSERT().
  If Pages plus EFI_SIZE_TO_PAGES (Alignment) overflows, then ASSERT().

  @param  Pages                 The number of 4 KB pages to allocate.
  @param  Alignment             The requested alignment of the allocation.  Must be a power of two.
                                If Alignment is zero, then byte alignment is used.

  @return A pointer to the allocated buffer or NULL if allocation fails.

**/
VOID *
EFIAPI
AllocateAlignedRuntimePages (
  IN UINTN  Pages,
  IN UINTN  Alignment
  )
{
  VOID  *Buffer;

  Buffer = InternalAllocateAlignedPages (EfiRuntimeServicesData, Pages, Alignment);
  if (Buffer != NULL) {
    MemoryProfileLibRecord (
      (PHYSICAL_ADDRESS)(UINTN)RETURN_ADDRESS (0),
      MEMORY_PROFILE_ACTION_LIB_ALLOCATE_ALIGNED_RUNTIME_PAGES,
      EfiRuntimeServicesData,
      Buffer,
      EFI_PAGES_TO_SIZE (Pages),
      NULL
      );
  }

  return Buffer;
}

/**
  Allocates one or more 4KB pages of type EfiReservedMemoryType at a specified alignment.

  Allocates the number of 4KB pages specified by Pages of type EfiReservedMemoryType with an
  alignment specified by Alignment.  The allocated buffer is returned.  If Pages is 0, then NULL is
  returned.  If there is not enough memory at the specified alignment remaining to satisfy the
  request, then NULL is returned.

  If Alignment is not a power of two and Alignment is not zero, then ASSERT().
  If Pages plus EFI_SIZE_TO_PAGES (Alignment) overflows, then ASSERT().

  @param  Pages                 The number of 4 KB pages to allocate.
  @param  Alignment             The requested alignment of the allocation.  Must be a power of two.
                                If Alignment is zero, then byte alignment is used.

  @return A pointer to the allocated buffer or NULL if allocation fails.

**/
VOID *
EFIAPI
AllocateAlignedReservedPages (
  IN UINTN  Pages,
  IN UINTN  Alignment
  )
{
  VOID  *Buffer;

  Buffer = InternalAllocateAlignedPages (EfiReservedMemoryType, Pages, Alignment);
  if (Buffer != NULL) {
    MemoryProfileLibRecord (
      (PHYSICAL_ADDRESS)(UINTN)RETURN_ADDRESS (0),
      MEMORY_PROFILE_ACTION_LIB_ALLOCATE_ALIGNED_RESERVED_PAGES,
      EfiReservedMemoryType,
      Buffer,
      EFI_PAGES_TO_SIZE (Pages),
      NULL
      );
  }

  return Buffer;
}

VOID *
EFIAPI
AllocateAlignedCodePages (
  IN UINTN  Pages,
  IN UINTN  Alignment
  )
{
  return InternalAllocateAlignedPages (gPhaseDefaultCodeType, Pages, Alignment);
}

/**
  Frees one or more 4KB pages that were previously allocated with one of the aligned page
  allocation functions in the Memory Allocation Library.

  Frees the number of 4KB pages specified by Pages from the buffer specified by Buffer.  Buffer
  must have been allocated on a previous call to the aligned page allocation services of the Memory
  Allocation Library.  If it is not possible to free allocated pages, then this function will
  perform no actions.

  If Buffer was not allocated with an aligned page allocation function in the Memory Allocation
  Library, then ASSERT().
  If Pages is zero, then ASSERT().

  @param  Buffer                Pointer to the buffer of pages to free.
  @param  Pages                 The number of 4 KB pages to free.

**/
VOID
EFIAPI
FreeAlignedPages (
  IN VOID   *Buffer,
  IN UINTN  Pages
  )
{
  InternalFreeAlignedPages (Buffer, Pages);
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
AllocatePool (
  IN UINTN  AllocationSize
  )
{
  VOID  *Buffer;

  Buffer = PhaseAllocatePool (gPhaseDefaultDataType, AllocationSize);
  if (Buffer != NULL) {
    MemoryProfileLibRecord (
      (PHYSICAL_ADDRESS)(UINTN)RETURN_ADDRESS (0),
      MEMORY_PROFILE_ACTION_LIB_ALLOCATE_POOL,
      gPhaseDefaultDataType,
      Buffer,
      AllocationSize,
      NULL
      );
  }

  return Buffer;
}

/**
  Allocates a buffer of type EfiRuntimeServicesData.

  Allocates the number bytes specified by AllocationSize of type EfiRuntimeServicesData and returns
  a pointer to the allocated buffer.  If AllocationSize is 0, then a valid buffer of 0 size is
  returned.  If there is not enough memory remaining to satisfy the request, then NULL is returned.

  @param  AllocationSize        The number of bytes to allocate.

  @return A pointer to the allocated buffer or NULL if allocation fails.

**/
VOID *
EFIAPI
AllocateRuntimePool (
  IN UINTN  AllocationSize
  )
{
  VOID  *Buffer;

  Buffer = PhaseAllocatePool (EfiRuntimeServicesData, AllocationSize);
  if (Buffer != NULL) {
    MemoryProfileLibRecord (
      (PHYSICAL_ADDRESS)(UINTN)RETURN_ADDRESS (0),
      MEMORY_PROFILE_ACTION_LIB_ALLOCATE_RUNTIME_POOL,
      EfiRuntimeServicesData,
      Buffer,
      AllocationSize,
      NULL
      );
  }

  return Buffer;
}

/**
  Allocates a buffer of type EfiReservedMemoryType.

  Allocates the number bytes specified by AllocationSize of type EfiReservedMemoryType and returns
  a pointer to the allocated buffer.  If AllocationSize is 0, then a valid buffer of 0 size is
  returned.  If there is not enough memory remaining to satisfy the request, then NULL is returned.

  @param  AllocationSize        The number of bytes to allocate.

  @return A pointer to the allocated buffer or NULL if allocation fails.

**/
VOID *
EFIAPI
AllocateReservedPool (
  IN UINTN  AllocationSize
  )
{
  VOID  *Buffer;

  Buffer = PhaseAllocatePool (EfiReservedMemoryType, AllocationSize);
  if (Buffer != NULL) {
    MemoryProfileLibRecord (
      (PHYSICAL_ADDRESS)(UINTN)RETURN_ADDRESS (0),
      MEMORY_PROFILE_ACTION_LIB_ALLOCATE_RESERVED_POOL,
      EfiReservedMemoryType,
      Buffer,
      AllocationSize,
      NULL
      );
  }

  return Buffer;
}

/**
  Allocates and zeros a buffer of a certain pool type.

  Allocates the number bytes specified by AllocationSize of a certain pool type, clears the buffer
  with zeros, and returns a pointer to the allocated buffer.  If AllocationSize is 0, then a valid
  buffer of 0 size is returned.  If there is not enough memory remaining to satisfy the request,
  then NULL is returned.

  @param  PoolType              The type of memory to allocate.
  @param  AllocationSize        The number of bytes to allocate and zero.

  @return A pointer to the allocated buffer or NULL if allocation fails.

**/
STATIC
VOID *
InternalAllocateZeroPool (
  IN EFI_MEMORY_TYPE  PoolType,
  IN UINTN            AllocationSize
  )
{
  VOID  *Memory;

  Memory = PhaseAllocatePool (PoolType, AllocationSize);
  if (Memory != NULL) {
    Memory = ZeroMem (Memory, AllocationSize);
  }

  return Memory;
}

/**
  Allocates and zeros a buffer of type EfiBootServicesData.

  Allocates the number bytes specified by AllocationSize of type EfiBootServicesData, clears the
  buffer with zeros, and returns a pointer to the allocated buffer.  If AllocationSize is 0, then a
  valid buffer of 0 size is returned.  If there is not enough memory remaining to satisfy the
  request, then NULL is returned.

  @param  AllocationSize        The number of bytes to allocate and zero.

  @return A pointer to the allocated buffer or NULL if allocation fails.

**/
VOID *
EFIAPI
AllocateZeroPool (
  IN UINTN  AllocationSize
  )
{
  VOID  *Buffer;

  Buffer = InternalAllocateZeroPool (gPhaseDefaultDataType, AllocationSize);
  if (Buffer != NULL) {
    MemoryProfileLibRecord (
      (PHYSICAL_ADDRESS)(UINTN)RETURN_ADDRESS (0),
      MEMORY_PROFILE_ACTION_LIB_ALLOCATE_ZERO_POOL,
      gPhaseDefaultDataType,
      Buffer,
      AllocationSize,
      NULL
      );
  }

  return Buffer;
}

/**
  Allocates and zeros a buffer of type EfiRuntimeServicesData.

  Allocates the number bytes specified by AllocationSize of type EfiRuntimeServicesData, clears the
  buffer with zeros, and returns a pointer to the allocated buffer.  If AllocationSize is 0, then a
  valid buffer of 0 size is returned.  If there is not enough memory remaining to satisfy the
  request, then NULL is returned.

  @param  AllocationSize        The number of bytes to allocate and zero.

  @return A pointer to the allocated buffer or NULL if allocation fails.

**/
VOID *
EFIAPI
AllocateRuntimeZeroPool (
  IN UINTN  AllocationSize
  )
{
  VOID  *Buffer;

  Buffer = InternalAllocateZeroPool (EfiRuntimeServicesData, AllocationSize);
  if (Buffer != NULL) {
    MemoryProfileLibRecord (
      (PHYSICAL_ADDRESS)(UINTN)RETURN_ADDRESS (0),
      MEMORY_PROFILE_ACTION_LIB_ALLOCATE_RUNTIME_ZERO_POOL,
      EfiRuntimeServicesData,
      Buffer,
      AllocationSize,
      NULL
      );
  }

  return Buffer;
}

/**
  Allocates and zeros a buffer of type EfiReservedMemoryType.

  Allocates the number bytes specified by AllocationSize of type EfiReservedMemoryType, clears the
  buffer with zeros, and returns a pointer to the allocated buffer.  If AllocationSize is 0, then a
  valid buffer of 0 size is returned.  If there is not enough memory remaining to satisfy the
  request, then NULL is returned.

  @param  AllocationSize        The number of bytes to allocate and zero.

  @return A pointer to the allocated buffer or NULL if allocation fails.

**/
VOID *
EFIAPI
AllocateReservedZeroPool (
  IN UINTN  AllocationSize
  )
{
  VOID  *Buffer;

  Buffer = InternalAllocateZeroPool (EfiReservedMemoryType, AllocationSize);
  if (Buffer != NULL) {
    MemoryProfileLibRecord (
      (PHYSICAL_ADDRESS)(UINTN)RETURN_ADDRESS (0),
      MEMORY_PROFILE_ACTION_LIB_ALLOCATE_RESERVED_ZERO_POOL,
      EfiReservedMemoryType,
      Buffer,
      AllocationSize,
      NULL
      );
  }

  return Buffer;
}

/**
  Copies a buffer to an allocated buffer of a certain pool type.

  Allocates the number bytes specified by AllocationSize of a certain pool type, copies
  AllocationSize bytes from Buffer to the newly allocated buffer, and returns a pointer to the
  allocated buffer.  If AllocationSize is 0, then a valid buffer of 0 size is returned.  If there
  is not enough memory remaining to satisfy the request, then NULL is returned.
  If Buffer is NULL, then ASSERT().
  If AllocationSize is greater than (MAX_ADDRESS - Buffer + 1), then ASSERT().

  @param  PoolType              The type of pool to allocate.
  @param  AllocationSize        The number of bytes to allocate and zero.
  @param  Buffer                The buffer to copy to the allocated buffer.

  @return A pointer to the allocated buffer or NULL if allocation fails.

**/
STATIC
VOID *
InternalAllocateCopyPool (
  IN EFI_MEMORY_TYPE  PoolType,
  IN UINTN            AllocationSize,
  IN CONST VOID       *Buffer
  )
{
  VOID  *Memory;

  ASSERT (Buffer != NULL);
  ASSERT (AllocationSize <= (MAX_ADDRESS - (UINTN)Buffer + 1));

  Memory = PhaseAllocatePool (PoolType, AllocationSize);
  if (Memory != NULL) {
    Memory = CopyMem (Memory, Buffer, AllocationSize);
  }

  return Memory;
}

/**
  Copies a buffer to an allocated buffer of type EfiBootServicesData.

  Allocates the number bytes specified by AllocationSize of type EfiBootServicesData, copies
  AllocationSize bytes from Buffer to the newly allocated buffer, and returns a pointer to the
  allocated buffer.  If AllocationSize is 0, then a valid buffer of 0 size is returned.  If there
  is not enough memory remaining to satisfy the request, then NULL is returned.

  If Buffer is NULL, then ASSERT().
  If AllocationSize is greater than (MAX_ADDRESS - Buffer + 1), then ASSERT().

  @param  AllocationSize        The number of bytes to allocate and zero.
  @param  Buffer                The buffer to copy to the allocated buffer.

  @return A pointer to the allocated buffer or NULL if allocation fails.

**/
VOID *
EFIAPI
AllocateCopyPool (
  IN UINTN       AllocationSize,
  IN CONST VOID  *Buffer
  )
{
  VOID  *NewBuffer;

  NewBuffer = InternalAllocateCopyPool (gPhaseDefaultDataType, AllocationSize, Buffer);
  if (NewBuffer != NULL) {
    MemoryProfileLibRecord (
      (PHYSICAL_ADDRESS)(UINTN)RETURN_ADDRESS (0),
      MEMORY_PROFILE_ACTION_LIB_ALLOCATE_COPY_POOL,
      gPhaseDefaultDataType,
      NewBuffer,
      AllocationSize,
      NULL
      );
  }

  return NewBuffer;
}

/**
  Copies a buffer to an allocated buffer of type EfiRuntimeServicesData.

  Allocates the number bytes specified by AllocationSize of type EfiRuntimeServicesData, copies
  AllocationSize bytes from Buffer to the newly allocated buffer, and returns a pointer to the
  allocated buffer.  If AllocationSize is 0, then a valid buffer of 0 size is returned.  If there
  is not enough memory remaining to satisfy the request, then NULL is returned.

  If Buffer is NULL, then ASSERT().
  If AllocationSize is greater than (MAX_ADDRESS - Buffer + 1), then ASSERT().

  @param  AllocationSize        The number of bytes to allocate and zero.
  @param  Buffer                The buffer to copy to the allocated buffer.

  @return A pointer to the allocated buffer or NULL if allocation fails.

**/
VOID *
EFIAPI
AllocateRuntimeCopyPool (
  IN UINTN       AllocationSize,
  IN CONST VOID  *Buffer
  )
{
  VOID  *NewBuffer;

  NewBuffer = InternalAllocateCopyPool (EfiRuntimeServicesData, AllocationSize, Buffer);
  if (NewBuffer != NULL) {
    MemoryProfileLibRecord (
      (PHYSICAL_ADDRESS)(UINTN)RETURN_ADDRESS (0),
      MEMORY_PROFILE_ACTION_LIB_ALLOCATE_RUNTIME_COPY_POOL,
      EfiRuntimeServicesData,
      NewBuffer,
      AllocationSize,
      NULL
      );
  }

  return NewBuffer;
}

/**
  Copies a buffer to an allocated buffer of type EfiReservedMemoryType.

  Allocates the number bytes specified by AllocationSize of type EfiReservedMemoryType, copies
  AllocationSize bytes from Buffer to the newly allocated buffer, and returns a pointer to the
  allocated buffer.  If AllocationSize is 0, then a valid buffer of 0 size is returned.  If there
  is not enough memory remaining to satisfy the request, then NULL is returned.

  If Buffer is NULL, then ASSERT().
  If AllocationSize is greater than (MAX_ADDRESS - Buffer + 1), then ASSERT().

  @param  AllocationSize        The number of bytes to allocate and zero.
  @param  Buffer                The buffer to copy to the allocated buffer.

  @return A pointer to the allocated buffer or NULL if allocation fails.

**/
VOID *
EFIAPI
AllocateReservedCopyPool (
  IN UINTN       AllocationSize,
  IN CONST VOID  *Buffer
  )
{
  VOID  *NewBuffer;

  NewBuffer = InternalAllocateCopyPool (EfiReservedMemoryType, AllocationSize, Buffer);
  if (NewBuffer != NULL) {
    MemoryProfileLibRecord (
      (PHYSICAL_ADDRESS)(UINTN)RETURN_ADDRESS (0),
      MEMORY_PROFILE_ACTION_LIB_ALLOCATE_RESERVED_COPY_POOL,
      EfiRuntimeServicesData,
      NewBuffer,
      AllocationSize,
      NULL
      );
  }

  return NewBuffer;
}

/**
  Reallocates a buffer of a specified memory type.

  Allocates and zeros the number bytes specified by NewSize from memory of the type
  specified by PoolType.  If OldBuffer is not NULL, then the smaller of OldSize and
  NewSize bytes are copied from OldBuffer to the newly allocated buffer, and
  OldBuffer is freed.  A pointer to the newly allocated buffer is returned.
  If NewSize is 0, then a valid buffer of 0 size is  returned.  If there is not
  enough memory remaining to satisfy the request, then NULL is returned.

  If the allocation of the new buffer is successful and the smaller of NewSize and OldSize
  is greater than (MAX_ADDRESS - OldBuffer + 1), then ASSERT().

  @param  PoolType       The type of pool to allocate.
  @param  OldSize        The size, in bytes, of OldBuffer.
  @param  NewSize        The size, in bytes, of the buffer to reallocate.
  @param  OldBuffer      The buffer to copy to the allocated buffer.  This is an optional
                         parameter that may be NULL.

  @return A pointer to the allocated buffer or NULL if allocation fails.

**/
STATIC
VOID *
InternalReallocatePool (
  IN EFI_MEMORY_TYPE  PoolType,
  IN UINTN            OldSize,
  IN UINTN            NewSize,
  IN VOID             *OldBuffer  OPTIONAL
  )
{
  VOID  *NewBuffer;

  NewBuffer = InternalAllocateZeroPool (PoolType, NewSize);
  if ((NewBuffer != NULL) && (OldBuffer != NULL)) {
    CopyMem (NewBuffer, OldBuffer, MIN (OldSize, NewSize));
    FreePool (OldBuffer);
  }

  return NewBuffer;
}

/**
  Reallocates a buffer of type EfiBootServicesData.

  Allocates and zeros the number bytes specified by NewSize from memory of type
  EfiBootServicesData.  If OldBuffer is not NULL, then the smaller of OldSize and
  NewSize bytes are copied from OldBuffer to the newly allocated buffer, and
  OldBuffer is freed.  A pointer to the newly allocated buffer is returned.
  If NewSize is 0, then a valid buffer of 0 size is  returned.  If there is not
  enough memory remaining to satisfy the request, then NULL is returned.

  If the allocation of the new buffer is successful and the smaller of NewSize and OldSize
  is greater than (MAX_ADDRESS - OldBuffer + 1), then ASSERT().

  @param  OldSize        The size, in bytes, of OldBuffer.
  @param  NewSize        The size, in bytes, of the buffer to reallocate.
  @param  OldBuffer      The buffer to copy to the allocated buffer.  This is an optional
                         parameter that may be NULL.

  @return A pointer to the allocated buffer or NULL if allocation fails.

**/
VOID *
EFIAPI
ReallocatePool (
  IN UINTN  OldSize,
  IN UINTN  NewSize,
  IN VOID   *OldBuffer  OPTIONAL
  )
{
  VOID  *Buffer;

  Buffer = InternalReallocatePool (gPhaseDefaultDataType, OldSize, NewSize, OldBuffer);
  if (Buffer != NULL) {
    MemoryProfileLibRecord (
      (PHYSICAL_ADDRESS)(UINTN)RETURN_ADDRESS (0),
      MEMORY_PROFILE_ACTION_LIB_REALLOCATE_POOL,
      gPhaseDefaultDataType,
      Buffer,
      NewSize,
      NULL
      );
  }

  return Buffer;
}

/**
  Reallocates a buffer of type EfiRuntimeServicesData.

  Allocates and zeros the number bytes specified by NewSize from memory of type
  EfiRuntimeServicesData.  If OldBuffer is not NULL, then the smaller of OldSize and
  NewSize bytes are copied from OldBuffer to the newly allocated buffer, and
  OldBuffer is freed.  A pointer to the newly allocated buffer is returned.
  If NewSize is 0, then a valid buffer of 0 size is  returned.  If there is not
  enough memory remaining to satisfy the request, then NULL is returned.

  If the allocation of the new buffer is successful and the smaller of NewSize and OldSize
  is greater than (MAX_ADDRESS - OldBuffer + 1), then ASSERT().

  @param  OldSize        The size, in bytes, of OldBuffer.
  @param  NewSize        The size, in bytes, of the buffer to reallocate.
  @param  OldBuffer      The buffer to copy to the allocated buffer.  This is an optional
                         parameter that may be NULL.

  @return A pointer to the allocated buffer or NULL if allocation fails.

**/
VOID *
EFIAPI
ReallocateRuntimePool (
  IN UINTN  OldSize,
  IN UINTN  NewSize,
  IN VOID   *OldBuffer  OPTIONAL
  )
{
  VOID  *Buffer;

  Buffer = InternalReallocatePool (EfiRuntimeServicesData, OldSize, NewSize, OldBuffer);
  if (Buffer != NULL) {
    MemoryProfileLibRecord (
      (PHYSICAL_ADDRESS)(UINTN)RETURN_ADDRESS (0),
      MEMORY_PROFILE_ACTION_LIB_REALLOCATE_RUNTIME_POOL,
      EfiRuntimeServicesData,
      Buffer,
      NewSize,
      NULL
      );
  }

  return Buffer;
}

/**
  Reallocates a buffer of type EfiReservedMemoryType.

  Allocates and zeros the number bytes specified by NewSize from memory of type
  EfiReservedMemoryType.  If OldBuffer is not NULL, then the smaller of OldSize and
  NewSize bytes are copied from OldBuffer to the newly allocated buffer, and
  OldBuffer is freed.  A pointer to the newly allocated buffer is returned.
  If NewSize is 0, then a valid buffer of 0 size is  returned.  If there is not
  enough memory remaining to satisfy the request, then NULL is returned.

  If the allocation of the new buffer is successful and the smaller of NewSize and OldSize
  is greater than (MAX_ADDRESS - OldBuffer + 1), then ASSERT().

  @param  OldSize        The size, in bytes, of OldBuffer.
  @param  NewSize        The size, in bytes, of the buffer to reallocate.
  @param  OldBuffer      The buffer to copy to the allocated buffer.  This is an optional
                         parameter that may be NULL.

  @return A pointer to the allocated buffer or NULL if allocation fails.

**/
VOID *
EFIAPI
ReallocateReservedPool (
  IN UINTN  OldSize,
  IN UINTN  NewSize,
  IN VOID   *OldBuffer  OPTIONAL
  )
{
  VOID  *Buffer;

  Buffer = InternalReallocatePool (EfiReservedMemoryType, OldSize, NewSize, OldBuffer);
  if (Buffer != NULL) {
    MemoryProfileLibRecord (
      (PHYSICAL_ADDRESS)(UINTN)RETURN_ADDRESS (0),
      MEMORY_PROFILE_ACTION_LIB_REALLOCATE_RESERVED_POOL,
      EfiReservedMemoryType,
      Buffer,
      NewSize,
      NULL
      );
  }

  return Buffer;
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
FreePool (
  IN VOID  *Buffer
  )
{
  PhaseFreePool (Buffer);
}
