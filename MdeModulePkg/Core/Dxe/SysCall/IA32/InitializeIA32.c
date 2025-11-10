/** @file

  Copyright (c) 2024 - 2025, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause

**/

#include "DxeMain.h"

#include <Register/Intel/ArchitecturalMsr.h>
#include <IndustryStandard/PageTable.h>

extern EXCEPTION_ADDRESSES  *mExceptionAddresses;

EFI_STATUS
EFIAPI
MakeUserPageTableTemplate (
  OUT UINTN  *UserPageTableTemplate,
  OUT UINTN  *UserPageTableTemplateSize
  )
{
  UINT8                           PhysicalAddressBits;
  EFI_PHYSICAL_ADDRESS            PhysicalAddress;
  UINTN                           IndexOfPdpEntries;
  UINTN                           IndexOfPageDirectoryEntries;
  UINT32                          NumberOfPdpEntriesNeeded;
  PAGE_MAP_AND_DIRECTORY_POINTER  *PageMap;
  PAGE_MAP_AND_DIRECTORY_POINTER  *PageDirectoryPointerEntry;
  PAGE_TABLE_ENTRY                *PageDirectoryEntry;
  UINTN                           TotalPagesNum;
  UINTN                           PageAddress;
  UINT64                          AddressEncMask;

  //
  // Make sure AddressEncMask is contained to smallest supported address field
  //
  AddressEncMask = PcdGet64 (PcdPteMemoryEncryptionAddressOrMask) & PAGING_1G_ADDRESS_MASK_64;

  PhysicalAddressBits = 32;

  //
  // Calculate the table entries needed.
  //
  NumberOfPdpEntriesNeeded = (UINT32)LShiftU64 (1, (PhysicalAddressBits - 30));

  TotalPagesNum = NumberOfPdpEntriesNeeded + 1;
  PageAddress   = (UINTN)AllocatePages (TotalPagesNum);
  if (PageAddress == 0) {
    return EFI_OUT_OF_RESOURCES;
  }

  PageMap      = (VOID *)PageAddress;
  PageAddress += SIZE_4KB;

  PageDirectoryPointerEntry = PageMap;
  PhysicalAddress           = 0;

  for (IndexOfPdpEntries = 0; IndexOfPdpEntries < NumberOfPdpEntriesNeeded; IndexOfPdpEntries++, PageDirectoryPointerEntry++) {
    //
    // Each Directory Pointer entries points to a page of Page Directory entires.
    // So allocate space for them and fill them in in the IndexOfPageDirectoryEntries loop.
    //
    PageDirectoryEntry = (VOID *)PageAddress;
    PageAddress       += SIZE_4KB;

    //
    // Fill in a Page Directory Pointer Entries
    //
    PageDirectoryPointerEntry->Uint64       = (UINT64)(UINTN)PageDirectoryEntry | AddressEncMask;
    PageDirectoryPointerEntry->Bits.Present = 1;

    for (IndexOfPageDirectoryEntries = 0; IndexOfPageDirectoryEntries < 512; IndexOfPageDirectoryEntries++, PageDirectoryEntry++, PhysicalAddress += SIZE_2MB) {
      //
      // Fill in the Page Directory entries
      //
      PageDirectoryEntry->Uint64         = (UINT64)PhysicalAddress | AddressEncMask;
      PageDirectoryEntry->Bits.ReadWrite = 1;
      PageDirectoryEntry->Bits.Present   = 0;
      PageDirectoryEntry->Bits.MustBe1   = 1;
    }
  }

  for ( ; IndexOfPdpEntries < 512; IndexOfPdpEntries++, PageDirectoryPointerEntry++) {
    ZeroMem (
      PageDirectoryPointerEntry,
      sizeof (PAGE_MAP_AND_DIRECTORY_POINTER)
      );
  }

  *UserPageTableTemplate     = (UINTN)PageMap;
  *UserPageTableTemplateSize = EFI_PAGES_TO_SIZE (TotalPagesNum);

  return EFI_SUCCESS;
}

EFI_STATUS
EFIAPI
InitializePlatform (
  IN OUT EFI_SYSTEM_TABLE  *System
  )
{
  UINT64                  Msr;
  IA32_CR4                Cr4;
  IA32_EFLAGS32           Eflags;
  UINT32                  Ebx;
  UINT32                  Edx;

  Ebx = 0;
  Edx = 0;

  //
  // Forbid global pages.
  //
  Cr4.UintN    = AsmReadCr4 ();
  Cr4.Bits.PGE = 0;
  AsmWriteCr4 (Cr4.UintN);

  //
  // Forbid supervisor-mode accesses to any user-mode pages.
  //
  AsmCpuidEx (0x07, 0x0, NULL, &Ebx, NULL, NULL);
  if ((Ebx & BIT7) != 0) {
    Cr4.UintN     = AsmReadCr4 ();
    Cr4.Bits.SMEP = 1;
    AsmWriteCr4 (Cr4.UintN);

    Eflags.UintN   = AsmReadEflags ();
    Eflags.Bits.AC = 0;
    AsmWriteEflags (Eflags.UintN);
  }

  if ((Ebx & BIT20) != 0) {
    Cr4.UintN     = AsmReadCr4 ();
    Cr4.Bits.SMAP = 1;
    AsmWriteCr4 (Cr4.UintN);

    Eflags.UintN   = AsmReadEflags ();
    Eflags.Bits.AC = 0;
    AsmWriteEflags (Eflags.UintN);
  }

  //
  // SYSENTER and SYSEXIT must be supported.
  //
  AsmCpuidEx (0x01, 0x0, NULL, NULL, NULL, &Edx);
  if ((Edx & BIT11) == 0) {
    DEBUG ((DEBUG_ERROR, "Core: SYSENTER and SYSEXIT are not supported.\n"));
    return EFI_UNSUPPORTED;
  }

  //
  // Initialize MSR_IA32_SYSENTER_CS, MSR_IA32_SYSENTER_EIP for SYSENTER and SYSEXIT.
  // MSR_IA32_SYSENTER_ESP is set in CallUserSpace().
  //
  Msr = RING0_CODE32_SEL;
  AsmWriteMsr64 (MSR_IA32_SYSENTER_CS, Msr);

  Msr = (UINT64)(UINTN)CoreBootServices;
  AsmWriteMsr64 (MSR_IA32_SYSENTER_EIP, Msr);

  gCorePageTable = AsmReadCr3 ();

  return EFI_SUCCESS;
}

VOID
EFIAPI
MapPlatform (
  IN OUT UINTN  UserPageTable
  )
{
  IA32_DESCRIPTOR  IdtDescriptor;

  gCpu->SetUserMemoryAttributes (
          gCpu,
          UserPageTable,
          (UINTN)&gCorePageTable,
          SIZE_4KB,
          EFI_MEMORY_RO | EFI_MEMORY_XP
          );

  gCpu->SetUserMemoryAttributes (
          gCpu,
          UserPageTable,
          mExceptionAddresses->ExceptionStackBase,
          mExceptionAddresses->ExceptionStackSize,
          EFI_MEMORY_XP
          );

  AsmReadIdtr (&IdtDescriptor);
  gCpu->SetUserMemoryAttributes (
          gCpu,
          UserPageTable,
          IdtDescriptor.Base,
          SIZE_4KB,
          EFI_MEMORY_RO | EFI_MEMORY_XP
          );

  //
  // Necessary fix for ProcessLibraryConstructorList() -> DxeCcProbeLibConstructor()
  //
  gCpu->SetUserMemoryAttributes (
          gCpu,
          UserPageTable,
          FixedPcdGet32 (PcdOvmfWorkAreaBase),
          FixedPcdGet32 (PcdOvmfWorkAreaSize),
          EFI_MEMORY_XP | EFI_MEMORY_USER
          );

}
