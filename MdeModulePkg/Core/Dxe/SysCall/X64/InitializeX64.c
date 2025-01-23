/** @file

  Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause

**/

#include "DxeMain.h"

#include <Register/Intel/ArchitecturalMsr.h>
#include <Register/Intel/Cpuid.h>
#include <IndustryStandard/PageTable.h>

VOID
EFIAPI
MakeUserPageTableTemplate (
  OUT UINTN  *UserPageTableTemplate,
  OUT UINTN  *UserPageTableTemplateSize
  )
{
  UINT32                                       RegEax;
  CPUID_STRUCTURED_EXTENDED_FEATURE_FLAGS_ECX  EcxFlags;
  UINT32                                       RegEdx;
  UINT8                                        PhysicalAddressBits;
  UINT32                                       NumberOfPml5EntriesNeeded;
  UINT32                                       NumberOfPml4EntriesNeeded;
  UINT32                                       NumberOfPdpEntriesNeeded;
  VOID                                         *Hob;
  BOOLEAN                                      Page5LevelEnabled;
  BOOLEAN                                      Page1GSupport;
  UINT64                                       AddressEncMask;
  IA32_CR4                                     Cr4;
  UINTN                                        TotalPagesNum;
  UINTN                                        BigPageAddress;
  EFI_PHYSICAL_ADDRESS                         PageAddress;
  UINTN                                        IndexOfPml5Entries;
  UINTN                                        IndexOfPml4Entries;
  UINTN                                        IndexOfPdpEntries;
  UINTN                                        IndexOfPageDirectoryEntries;
  PAGE_MAP_AND_DIRECTORY_POINTER               *PageMapLevel5Entry;
  PAGE_MAP_AND_DIRECTORY_POINTER               *PageMapLevel4Entry;
  PAGE_MAP_AND_DIRECTORY_POINTER               *PageMap;
  PAGE_MAP_AND_DIRECTORY_POINTER               *PageDirectoryPointerEntry;
  PAGE_TABLE_ENTRY                             *PageDirectoryEntry;
  PAGE_TABLE_1G_ENTRY                          *PageDirectory1GEntry;

  //
  // Set PageMapLevel5Entry to suppress incorrect compiler/analyzer warnings
  //
  PageMapLevel5Entry = NULL;

  //
  // Make sure AddressEncMask is contained to smallest supported address field
  //
  AddressEncMask = PcdGet64 (PcdPteMemoryEncryptionAddressOrMask) & PAGING_1G_ADDRESS_MASK_64;

  Page1GSupport = FALSE;
  if (PcdGetBool (PcdUse1GPageTable)) {
    AsmCpuid (0x80000000, &RegEax, NULL, NULL, NULL);
    if (RegEax >= 0x80000001) {
      AsmCpuid (0x80000001, NULL, NULL, NULL, &RegEdx);
      if ((RegEdx & BIT26) != 0) {
        Page1GSupport = TRUE;
      }
    }
  }

  //
  // Get physical address bits supported.
  //
  Hob = GetFirstHob (EFI_HOB_TYPE_CPU);
  if (Hob != NULL) {
    PhysicalAddressBits = ((EFI_HOB_CPU *)Hob)->SizeOfMemorySpace;
  } else {
    AsmCpuid (0x80000000, &RegEax, NULL, NULL, NULL);
    if (RegEax >= 0x80000008) {
      AsmCpuid (0x80000008, &RegEax, NULL, NULL, NULL);
      PhysicalAddressBits = (UINT8)RegEax;
    } else {
      PhysicalAddressBits = 36;
    }
  }

  if (sizeof (UINTN) == sizeof (UINT64)) {
    //
    // If cpu has already run in 64bit long mode PEI, Page table Level in DXE must align with previous level.
    //
    Cr4.UintN         = AsmReadCr4 ();
    Page5LevelEnabled = (Cr4.Bits.LA57 != 0);
    if (Page5LevelEnabled) {
      ASSERT (PcdGetBool (PcdUse5LevelPageTable));
    }
  } else {
    //
    // If cpu runs in 32bit protected mode PEI, Page table Level in DXE is decided by PCD and feature capability.
    //
    Page5LevelEnabled = FALSE;
    if (PcdGetBool (PcdUse5LevelPageTable)) {
      AsmCpuidEx (
        CPUID_STRUCTURED_EXTENDED_FEATURE_FLAGS,
        CPUID_STRUCTURED_EXTENDED_FEATURE_FLAGS_SUB_LEAF_INFO,
        NULL,
        NULL,
        &EcxFlags.Uint32,
        NULL
        );
      if (EcxFlags.Bits.FiveLevelPage != 0) {
        Page5LevelEnabled = TRUE;
      }
    }
  }

  //
  // IA-32e paging translates 48-bit linear addresses to 52-bit physical addresses
  //  when 5-Level Paging is disabled,
  //  due to either unsupported by HW, or disabled by PCD.
  //
  ASSERT (PhysicalAddressBits <= 52);
  if (!Page5LevelEnabled && (PhysicalAddressBits > 48)) {
    PhysicalAddressBits = 48;
  }

  //
  // Calculate the table entries needed.
  //
  NumberOfPml5EntriesNeeded = 1;
  if (PhysicalAddressBits > 48) {
    NumberOfPml5EntriesNeeded = (UINT32)LShiftU64 (1, PhysicalAddressBits - 48);
    PhysicalAddressBits       = 48;
  }

  NumberOfPml4EntriesNeeded = 1;
  if (PhysicalAddressBits > 39) {
    NumberOfPml4EntriesNeeded = (UINT32)LShiftU64 (1, PhysicalAddressBits - 39);
    PhysicalAddressBits       = 39;
  }

  NumberOfPdpEntriesNeeded = 1;
  ASSERT (PhysicalAddressBits > 30);
  NumberOfPdpEntriesNeeded = (UINT32)LShiftU64 (1, PhysicalAddressBits - 30);

  //
  // Pre-allocate big pages to avoid later allocations.
  //
  if (!Page1GSupport) {
    TotalPagesNum = ((NumberOfPdpEntriesNeeded + 1) * NumberOfPml4EntriesNeeded + 1) * NumberOfPml5EntriesNeeded + 1;
  } else {
    TotalPagesNum = (NumberOfPml4EntriesNeeded + 1) * NumberOfPml5EntriesNeeded + 1;
  }

  //
  // Substract the one page occupied by PML5 entries if 5-Level Paging is disabled.
  //
  if (!Page5LevelEnabled) {
    TotalPagesNum--;
  }

  BigPageAddress = (UINTN)AllocatePages (TotalPagesNum);
  if (BigPageAddress == 0) {
    DEBUG ((DEBUG_ERROR, "Core: Could not allocate buffer for User page table.\n"));
    CpuDeadLoop ();
  }

  //
  // By architecture only one PageMapLevel4 exists - so lets allocate storage for it.
  //
  PageMap = (VOID *)BigPageAddress;
  if (Page5LevelEnabled) {
    //
    // By architecture only one PageMapLevel5 exists - so lets allocate storage for it.
    //
    PageMapLevel5Entry = PageMap;
    BigPageAddress    += SIZE_4KB;
  }

  PageAddress = 0;

  for ( IndexOfPml5Entries = 0
        ; IndexOfPml5Entries < NumberOfPml5EntriesNeeded
        ; IndexOfPml5Entries++)
  {
    //
    // Each PML5 entry points to a page of PML4 entires.
    // So lets allocate space for them and fill them in in the IndexOfPml4Entries loop.
    // When 5-Level Paging is disabled, below allocation happens only once.
    //
    PageMapLevel4Entry = (VOID *)BigPageAddress;
    BigPageAddress    += SIZE_4KB;

    if (Page5LevelEnabled) {
      //
      // Make a PML5 Entry
      //
      PageMapLevel5Entry->Uint64              = (UINT64)(UINTN)PageMapLevel4Entry | AddressEncMask;
      PageMapLevel5Entry->Bits.ReadWrite      = 1;
      PageMapLevel5Entry->Bits.UserSupervisor = 1;
      PageMapLevel5Entry->Bits.Present        = 1;
      PageMapLevel5Entry++;
    }

    for ( IndexOfPml4Entries = 0
          ; IndexOfPml4Entries < (NumberOfPml5EntriesNeeded == 1 ? NumberOfPml4EntriesNeeded : 512)
          ; IndexOfPml4Entries++, PageMapLevel4Entry++)
    {
      //
      // Each PML4 entry points to a page of Page Directory Pointer entires.
      // So lets allocate space for them and fill them in in the IndexOfPdpEntries loop.
      //
      PageDirectoryPointerEntry = (VOID *)BigPageAddress;
      BigPageAddress           += SIZE_4KB;

      //
      // Make a PML4 Entry
      //
      PageMapLevel4Entry->Uint64              = (UINT64)(UINTN)PageDirectoryPointerEntry | AddressEncMask;
      PageMapLevel4Entry->Bits.ReadWrite      = 1;
      PageMapLevel4Entry->Bits.UserSupervisor = 1;
      PageMapLevel4Entry->Bits.Present        = 1;

      if (Page1GSupport) {
        PageDirectory1GEntry = (VOID *)PageDirectoryPointerEntry;

        for (IndexOfPageDirectoryEntries = 0; IndexOfPageDirectoryEntries < 512; IndexOfPageDirectoryEntries++, PageDirectory1GEntry++, PageAddress += SIZE_1GB) {
          //
          // Fill in the Page Directory entries
          //
          PageDirectory1GEntry->Uint64         = (UINT64)PageAddress | AddressEncMask;
          PageDirectory1GEntry->Bits.ReadWrite = 1;
          PageDirectory1GEntry->Bits.Present   = 0;
          PageDirectory1GEntry->Bits.MustBe1   = 1;
        }
      } else {
        for ( IndexOfPdpEntries = 0
              ; IndexOfPdpEntries < (NumberOfPml4EntriesNeeded == 1 ? NumberOfPdpEntriesNeeded : 512)
              ; IndexOfPdpEntries++, PageDirectoryPointerEntry++)
        {
          //
          // Each Directory Pointer entries points to a page of Page Directory entires.
          // So allocate space for them and fill them in in the IndexOfPageDirectoryEntries loop.
          //
          PageDirectoryEntry = (VOID *)BigPageAddress;
          BigPageAddress    += SIZE_4KB;

          //
          // Fill in a Page Directory Pointer Entries
          //
          PageDirectoryPointerEntry->Uint64              = (UINT64)(UINTN)PageDirectoryEntry | AddressEncMask;
          PageDirectoryPointerEntry->Bits.ReadWrite      = 1;
          PageDirectoryPointerEntry->Bits.UserSupervisor = 1;
          PageDirectoryPointerEntry->Bits.Present        = 1;

          for (IndexOfPageDirectoryEntries = 0; IndexOfPageDirectoryEntries < 512; IndexOfPageDirectoryEntries++, PageDirectoryEntry++, PageAddress += SIZE_2MB) {
            //
            // Fill in the Page Directory entries
            //
            PageDirectoryEntry->Uint64         = (UINT64)PageAddress | AddressEncMask;
            PageDirectoryEntry->Bits.ReadWrite = 1;
            PageDirectoryEntry->Bits.Present   = 0;
            PageDirectoryEntry->Bits.MustBe1   = 1;
          }
        }

        //
        // Fill with null entry for unused PDPTE
        //
        ZeroMem (PageDirectoryPointerEntry, (512 - IndexOfPdpEntries) * sizeof (PAGE_MAP_AND_DIRECTORY_POINTER));
      }
    }

    //
    // For the PML4 entries we are not using fill in a null entry.
    //
    ZeroMem (PageMapLevel4Entry, (512 - IndexOfPml4Entries) * sizeof (PAGE_MAP_AND_DIRECTORY_POINTER));
  }

  if (Page5LevelEnabled) {
    //
    // For the PML5 entries we are not using fill in a null entry.
    //
    ZeroMem (PageMapLevel5Entry, (512 - IndexOfPml5Entries) * sizeof (PAGE_MAP_AND_DIRECTORY_POINTER));
  }

  *UserPageTableTemplate     = (UINTN)PageMap;
  *UserPageTableTemplateSize = EFI_PAGES_TO_SIZE (TotalPagesNum);
}

VOID
EFIAPI
InitializeMsr (
  IN OUT EFI_CONFIGURATION_TABLE  *Table,
  IN     UINTN                    NumberOfEntries
  )
{
  UINT64                  Msr;
  IA32_CR4                Cr4;
  IA32_EFLAGS32           Eflags;
  UINT32                  Ebx;
  UINT32                  Edx;
  MSR_IA32_EFER_REGISTER  MsrEfer;

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
  // Enable SYSCALL and SYSRET.
  //
  AsmCpuidEx (0x80000001, 0x0, NULL, NULL, NULL, &Edx);
  if ((Edx & BIT11) != 0) {
    MsrEfer.Uint64   = AsmReadMsr64 (MSR_IA32_EFER);
    MsrEfer.Bits.SCE = 1;
    AsmWriteMsr64 (MSR_IA32_EFER, MsrEfer.Uint64);
  } else {
    DEBUG ((DEBUG_ERROR, "Core: SYSCALL and SYSRET are not supported.\n"));
    CpuDeadLoop ();
  }

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

  gCorePageTable = AsmReadCr3 ();
}
