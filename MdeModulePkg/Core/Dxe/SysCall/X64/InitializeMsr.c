/** @file

  Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause

**/

#include "DxeMain.h"

#include <Register/Intel/ArchitecturalMsr.h>
#include <IndustryStandard/PageTable.h>

VOID   *gUserPageTableTemplate;
UINTN  gUserPageTableTemplateSize;

VOID
EFIAPI
MakeUserPageTableTemplate (
  VOID
  )
{
  EFI_HOB_GUID_TYPE               *GuidHob;
  EFI_PAGE_TABLE_INFO             *PageTableInfo;
  UINTN                           BigPageAddress;
  EFI_PHYSICAL_ADDRESS            PageAddress;
  UINTN                           IndexOfPml5Entries;
  UINTN                           IndexOfPml4Entries;
  UINTN                           IndexOfPdpEntries;
  UINTN                           IndexOfPageDirectoryEntries;
  PAGE_MAP_AND_DIRECTORY_POINTER  *PageMapLevel5Entry;
  PAGE_MAP_AND_DIRECTORY_POINTER  *PageMapLevel4Entry;
  PAGE_MAP_AND_DIRECTORY_POINTER  *PageMap;
  PAGE_MAP_AND_DIRECTORY_POINTER  *PageDirectoryPointerEntry;
  PAGE_TABLE_ENTRY                *PageDirectoryEntry;
  PAGE_TABLE_1G_ENTRY             *PageDirectory1GEntry;

  GuidHob  = GetFirstGuidHob (&gEfiHobPageTableInfoGuid);
  if (GuidHob == NULL) {
    DEBUG ((DEBUG_ERROR, "Core: Could not retrieve PageTableInfo HOB.\n"));
    CpuDeadLoop ();
  }

  PageTableInfo = (EFI_PAGE_TABLE_INFO *)(GET_GUID_HOB_DATA (GuidHob));

  BigPageAddress = (UINTN)AllocateAlignedPages (PageTableInfo->TotalPagesNum, PAGE_TABLE_POOL_ALIGNMENT);
  if (BigPageAddress == 0) {
    DEBUG ((DEBUG_ERROR, "Core: Could not allocate buffer for User page table.\n"));
    CpuDeadLoop ();
  }

  //
  // By architecture only one PageMapLevel4 exists - so lets allocate storage for it.
  //
  PageMap = (VOID *)BigPageAddress;
  if (PageTableInfo->Page5LevelEnabled) {
    //
    // By architecture only one PageMapLevel5 exists - so lets allocate storage for it.
    //
    PageMapLevel5Entry = PageMap;
    BigPageAddress    += SIZE_4KB;
  }

  PageAddress = 0;

  for ( IndexOfPml5Entries = 0
        ; IndexOfPml5Entries < PageTableInfo->NumberOfPml5EntriesNeeded
        ; IndexOfPml5Entries++)
  {
    //
    // Each PML5 entry points to a page of PML4 entires.
    // So lets allocate space for them and fill them in in the IndexOfPml4Entries loop.
    // When 5-Level Paging is disabled, below allocation happens only once.
    //
    PageMapLevel4Entry = (VOID *)BigPageAddress;
    BigPageAddress    += SIZE_4KB;

    if (PageTableInfo->Page5LevelEnabled) {
      //
      // Make a PML5 Entry
      //
      PageMapLevel5Entry->Uint64              = (UINT64)(UINTN)PageMapLevel4Entry | PageTableInfo->AddressEncMask;
      PageMapLevel5Entry->Bits.ReadWrite      = 1;
      PageMapLevel5Entry->Bits.UserSupervisor = 1;
      PageMapLevel5Entry->Bits.Present        = 1;
      PageMapLevel5Entry++;
    }

    for ( IndexOfPml4Entries = 0
          ; IndexOfPml4Entries < (PageTableInfo->NumberOfPml5EntriesNeeded == 1 ? PageTableInfo->NumberOfPml4EntriesNeeded : 512)
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
      PageMapLevel4Entry->Uint64              = (UINT64)(UINTN)PageDirectoryPointerEntry | PageTableInfo->AddressEncMask;
      PageMapLevel4Entry->Bits.ReadWrite      = 1;
      PageMapLevel4Entry->Bits.UserSupervisor = 1;
      PageMapLevel4Entry->Bits.Present        = 1;

      if (PageTableInfo->Page1GSupport) {
        PageDirectory1GEntry = (VOID *)PageDirectoryPointerEntry;

        for (IndexOfPageDirectoryEntries = 0; IndexOfPageDirectoryEntries < 512; IndexOfPageDirectoryEntries++, PageDirectory1GEntry++, PageAddress += SIZE_1GB) {
          //
          // Fill in the Page Directory entries
          //
          PageDirectory1GEntry->Uint64         = (UINT64)PageAddress | PageTableInfo->AddressEncMask;
          PageDirectory1GEntry->Bits.ReadWrite = 1;
          PageDirectory1GEntry->Bits.Present   = 1;
          PageDirectory1GEntry->Bits.MustBe1   = 1;
        }
      } else {
        for ( IndexOfPdpEntries = 0
              ; IndexOfPdpEntries < (PageTableInfo->NumberOfPml4EntriesNeeded == 1 ? PageTableInfo->NumberOfPdpEntriesNeeded : 512)
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
          PageDirectoryPointerEntry->Uint64              = (UINT64)(UINTN)PageDirectoryEntry | PageTableInfo->AddressEncMask;
          PageDirectoryPointerEntry->Bits.ReadWrite      = 1;
          PageDirectoryPointerEntry->Bits.UserSupervisor = 1;
          PageDirectoryPointerEntry->Bits.Present        = 1;

          for (IndexOfPageDirectoryEntries = 0; IndexOfPageDirectoryEntries < 512; IndexOfPageDirectoryEntries++, PageDirectoryEntry++, PageAddress += SIZE_2MB) {
            //
            // Fill in the Page Directory entries
            //
            PageDirectoryEntry->Uint64         = (UINT64)PageAddress | PageTableInfo->AddressEncMask;
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

  if (PageTableInfo->Page5LevelEnabled) {
    //
    // For the PML5 entries we are not using fill in a null entry.
    //
    ZeroMem (PageMapLevel5Entry, (512 - IndexOfPml5Entries) * sizeof (PAGE_MAP_AND_DIRECTORY_POINTER));
  }

  gUserPageTableTemplate     = (VOID *)PageMap;
  gUserPageTableTemplateSize = ALIGN_VALUE (EFI_PAGES_TO_SIZE (PageTableInfo->TotalPagesNum), PAGE_TABLE_POOL_ALIGNMENT);
  gUserPageTable             = (UINTN)gUserPageTableTemplate;

  SetUefiImageMemoryAttributes ((UINT64)PageMap, gUserPageTableTemplateSize, EFI_MEMORY_XP);
  //
  // Map CoreBootServices
  //
  gCpu->SetUserMemoryAttributes (
    gCpu,
    (UINTN)PageMap,
    (EFI_PHYSICAL_ADDRESS)(UINTN)CoreBootServices,
    SIZE_4KB,
    EFI_MEMORY_RO
    );

  gCpu->SetUserMemoryAttributes (
    gCpu,
    (UINTN)PageMap,
    (EFI_PHYSICAL_ADDRESS)(UINTN)&gCorePageTable,
    SIZE_4KB,
    EFI_MEMORY_RO | EFI_MEMORY_XP
    );
  //
  // Map ExceptionHandlerAsm: AsmIdtVectorBegin - AsmGetTemplateAddressMap
  //  mCorePageTable, gCoreSysCallStackTop
  //
  // gCpu->SetUserMemoryAttributes (gCpu, (UINTN)PageMap, BaseAddress, SIZE_4KB, EFI_MEMORY_RO);

  gCpu->SetUserMemoryAttributes (
    gCpu,
    (UINTN)PageMap,
    FixedPcdGet32 (PcdOvmfWorkAreaBase),
    FixedPcdGet32 (PcdOvmfWorkAreaSize),
    EFI_MEMORY_XP | EFI_MEMORY_USER
    );
}

VOID
EFIAPI
InitializeMsr (
  IN OUT EFI_CONFIGURATION_TABLE *Table,
  IN     UINTN                   NumberOfEntries
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

  // The Intel-64 and IA-32 architectures also allow for global pages when the PGE flag (bit 7) is 1 in CR4.
  // PGE must be zero.

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
