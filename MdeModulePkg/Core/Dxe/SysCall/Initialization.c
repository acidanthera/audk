/** @file

  Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause

**/

#include "DxeMain.h"

#include <Register/Intel/ArchitecturalMsr.h>

VOID        *gCoreSysCallStackTop;
VOID        *gRing3CallStackTop;
VOID        *gRing3EntryPoint;
RING3_DATA  *gRing3Data;
VOID        *gRing3Interfaces;

EFI_STATUS
EFIAPI
InitializeRing3 (
  IN EFI_HANDLE                 ImageHandle,
  IN LOADED_IMAGE_PRIVATE_DATA  *Image
  )
{
  EFI_STATUS              Status;
  VOID                    *BaseOfStack;
  VOID                    *TopOfStack;
  UINTN                   SizeOfStack;
  UINT64                  Msr;
  IA32_CR4                Cr4;
  IA32_EFLAGS32           Eflags;
  UINT32                  Ebx;
  UINT32                  Edx;
  MSR_IA32_EFER_REGISTER  MsrEfer;

  Ebx = 0;
  Edx = 0;

  //
  // Set Ring3 EntryPoint and BootServices.
  //
  Status = CoreAllocatePages (
             AllocateAnyPages,
             EfiRing3MemoryType,
             EFI_SIZE_TO_PAGES (sizeof (RING3_DATA)),
             (EFI_PHYSICAL_ADDRESS *)&gRing3Data
             );
  if (EFI_ERROR (Status)) {
    DEBUG ((DEBUG_ERROR, "Core: Failed to allocate memory for Ring3Data.\n"));
    return Status;
  }

  CopyMem ((VOID *)gRing3Data, (VOID *)Image->Info.SystemTable, sizeof (EFI_SYSTEM_TABLE));

  Status = Image->EntryPoint (ImageHandle, (EFI_SYSTEM_TABLE *)gRing3Data);

  gRing3EntryPoint = gRing3Data->EntryPoint;

  gRing3Data->SystemTable.BootServices    = gRing3Data->BootServices;
  gRing3Data->SystemTable.RuntimeServices = gRing3Data->RuntimeServices;

  Status = CoreAllocatePages (
             AllocateAnyPages,
             EfiRing3MemoryType,
             RING3_INTERFACES_PAGES,
             (EFI_PHYSICAL_ADDRESS *)&gRing3Interfaces
             );
  if (EFI_ERROR (Status)) {
    DEBUG ((DEBUG_ERROR, "Core: Failed to allocate memory for Ring3Interfaces.\n"));
    CoreFreePages (
      (EFI_PHYSICAL_ADDRESS)gRing3Data,
      EFI_SIZE_TO_PAGES (sizeof (RING3_DATA))
      );
    return Status;
  }

  //
  // Forbid supervisor-mode accesses to any user-mode pages.
  // SMEP and SMAP must be supported.
  //
  AsmCpuidEx (0x07, 0x0, NULL, &Ebx, NULL, NULL);
  //
  // SYSCALL and SYSRET must be also supported.
  //
  AsmCpuidEx (0x80000001, 0x0, NULL, NULL, NULL, &Edx);
  if (((Ebx & BIT20) != 0) && ((Ebx & BIT7) != 0) && ((Edx & BIT11) != 0)) {
    Cr4.UintN     = AsmReadCr4 ();
    Cr4.Bits.SMAP = 1;
    Cr4.Bits.SMEP = 1;
    AsmWriteCr4 (Cr4.UintN);

    Eflags.UintN   = AsmReadEflags ();
    Eflags.Bits.AC = 0;
    AsmWriteEflags (Eflags.UintN);
    //
    // Enable SYSCALL and SYSRET.
    //
    MsrEfer.Uint64   = AsmReadMsr64 (MSR_IA32_EFER);
    MsrEfer.Bits.SCE = 1;
    AsmWriteMsr64 (MSR_IA32_EFER, MsrEfer.Uint64);
  }

  SizeOfStack = EFI_SIZE_TO_PAGES (USER_STACK_SIZE) * EFI_PAGE_SIZE;

  //
  // Allocate 128KB for the Core SysCall Stack.
  //
  BaseOfStack = AllocatePages (EFI_SIZE_TO_PAGES (USER_STACK_SIZE));
  ASSERT (BaseOfStack != NULL);

  //
  // Compute the top of the allocated stack. Pre-allocate a UINTN for safety.
  //
  TopOfStack = (VOID *)((UINTN)BaseOfStack + SizeOfStack - CPU_STACK_ALIGNMENT);
  TopOfStack = ALIGN_POINTER (TopOfStack, CPU_STACK_ALIGNMENT);

  gCoreSysCallStackTop = TopOfStack;

  SetUefiImageMemoryAttributes ((UINTN)BaseOfStack, SizeOfStack, EFI_MEMORY_XP);
  DEBUG ((DEBUG_ERROR, "Core: gCoreSysCallStackTop = %p\n", gCoreSysCallStackTop));

  //
  // Allocate 128KB for the User Stack.
  //
  BaseOfStack = AllocatePages (EFI_SIZE_TO_PAGES (USER_STACK_SIZE));
  ASSERT (BaseOfStack != NULL);

  //
  // Compute the top of the allocated stack. Pre-allocate a UINTN for safety.
  //
  TopOfStack = (VOID *)((UINTN)BaseOfStack + SizeOfStack - CPU_STACK_ALIGNMENT);
  TopOfStack = ALIGN_POINTER (TopOfStack, CPU_STACK_ALIGNMENT);

  gRing3CallStackTop = TopOfStack;

  SetUefiImageMemoryAttributes ((UINTN)BaseOfStack, SizeOfStack, EFI_MEMORY_XP | EFI_MEMORY_USER);
  DEBUG ((DEBUG_ERROR, "Core: gRing3CallStackTop = %p\n", gRing3CallStackTop));

  //
  // Initialize MSR_IA32_STAR, MSR_IA32_LSTAR and MSR_IA32_FMASK for SYSCALL and SYSRET.
  //
  Msr = (((((UINT64)RING3_CODE64_SEL - 16) | 3) << 16) | (UINT64)RING0_CODE64_SEL) << 32;
  AsmWriteMsr64 (MSR_IA32_STAR, Msr);

  Msr = (UINT64)(UINTN)CoreBootServices;
  AsmWriteMsr64 (MSR_IA32_LSTAR, Msr);
  //
  // Disable maskable interrupts at SYSCALL.
  //
  Msr = (UINT64)BIT9;
  AsmWriteMsr64 (MSR_IA32_FMASK, Msr);

  return Status;
}
