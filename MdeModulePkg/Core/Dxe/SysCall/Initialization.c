/** @file

  Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause

**/

#include "DxeMain.h"

VOID        *gCoreSysCallStackTop;
VOID        *gCoreSysCallStackBase;
VOID        *gRing3CallStackTop;
VOID        *gRing3CallStackBase;
VOID        *gRing3EntryPoint;
RING3_DATA  *gRing3Data;
VOID        *gRing3Interfaces;

VOID
EFIAPI
InitializeMsr (
  VOID
  );

EFI_STATUS
EFIAPI
InitializeRing3 (
  IN EFI_HANDLE                 ImageHandle,
  IN LOADED_IMAGE_PRIVATE_DATA  *Image
  )
{
  EFI_STATUS              Status;
  VOID                    *TopOfStack;
  UINTN                   SizeOfStack;
  EFI_PHYSICAL_ADDRESS    Physical;

  //
  // Set Ring3 EntryPoint and BootServices.
  //
  Status = CoreAllocatePages (
             AllocateAnyPages,
             EfiRing3MemoryType,
             EFI_SIZE_TO_PAGES (sizeof (RING3_DATA)),
             &Physical
             );
  if (EFI_ERROR (Status)) {
    DEBUG ((DEBUG_ERROR, "Core: Failed to allocate memory for Ring3Data.\n"));
    return Status;
  }

  gRing3Data = (RING3_DATA *)(UINTN)Physical;

  CopyMem ((VOID *)gRing3Data, (VOID *)Image->Info.SystemTable, sizeof (EFI_SYSTEM_TABLE));

  Status = Image->EntryPoint (ImageHandle, (EFI_SYSTEM_TABLE *)gRing3Data);

  gRing3EntryPoint = gRing3Data->EntryPoint;

  gRing3Data->SystemTable.BootServices    = gRing3Data->BootServices;
  gRing3Data->SystemTable.RuntimeServices = gRing3Data->RuntimeServices;

  Status = CoreAllocatePages (
             AllocateAnyPages,
             EfiRing3MemoryType,
             RING3_INTERFACES_PAGES,
             &Physical
             );
  if (EFI_ERROR (Status)) {
    DEBUG ((DEBUG_ERROR, "Core: Failed to allocate memory for Ring3Interfaces.\n"));
    CoreFreePages (
      (EFI_PHYSICAL_ADDRESS)(UINTN)gRing3Data,
      EFI_SIZE_TO_PAGES (sizeof (RING3_DATA))
      );
    return Status;
  }

  gRing3Interfaces = (VOID *)(UINTN)Physical;

  SizeOfStack = EFI_SIZE_TO_PAGES (USER_STACK_SIZE) * EFI_PAGE_SIZE;

  //
  // Allocate 128KB for the Core SysCall Stack.
  //
  gCoreSysCallStackBase = AllocatePages (EFI_SIZE_TO_PAGES (USER_STACK_SIZE));
  ASSERT (gCoreSysCallStackBase != NULL);

  //
  // Compute the top of the allocated stack. Pre-allocate a UINTN for safety.
  //
  TopOfStack = (VOID *)((UINTN)gCoreSysCallStackBase + SizeOfStack - CPU_STACK_ALIGNMENT);
  TopOfStack = ALIGN_POINTER (TopOfStack, CPU_STACK_ALIGNMENT);

  gCoreSysCallStackTop = TopOfStack;

  SetUefiImageMemoryAttributes ((UINTN)gCoreSysCallStackBase, SizeOfStack, EFI_MEMORY_XP);
  DEBUG ((DEBUG_ERROR, "Core: gCoreSysCallStackTop = %p\n", gCoreSysCallStackTop));

  //
  // Allocate 128KB for the User Stack.
  //
  gRing3CallStackBase = AllocatePages (EFI_SIZE_TO_PAGES (USER_STACK_SIZE));
  ASSERT (gRing3CallStackBase != NULL);

  //
  // Compute the top of the allocated stack. Pre-allocate a UINTN for safety.
  //
  TopOfStack = (VOID *)((UINTN)gRing3CallStackBase + SizeOfStack - CPU_STACK_ALIGNMENT);
  TopOfStack = ALIGN_POINTER (TopOfStack, CPU_STACK_ALIGNMENT);

  gRing3CallStackTop = TopOfStack;

  SetUefiImageMemoryAttributes ((UINTN)gRing3CallStackBase, SizeOfStack, EFI_MEMORY_XP | EFI_MEMORY_USER);
  DEBUG ((DEBUG_ERROR, "Core: gRing3CallStackTop = %p\n", gRing3CallStackTop));

  InitializeMsr ();

  return Status;
}
