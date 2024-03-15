/** @file
  C based implementation of IA32 interrupt handling only
  requiring a minimal assembly interrupt entry point.

  Copyright (c) 2006 - 2021, Intel Corporation. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-2-Clause-Patent

**/

#include "CpuDxe.h"
#include "CpuGdt.h"

//
// Global descriptor table (GDT) Template
//
STATIC GDT  mGdtTemplate = {
  .Null = {
    .SegmentLimit_15_0  = 0x0,
    .BaseAddress_15_0   = 0x0,
    .BaseAddress_23_16  = 0x0,
    .Type               = 0x0,
    .S                  = 0,
    .DPL                = 0,
    .P                  = 0,
    .SegmentLimit_19_16 = 0x0,
    .AVL                = 0,
    .L                  = 0,
    .D_B                = 0,
    .G                  = 0,
    .BaseAddress_31_24  = 0x0
  },
  .Linear = {
    .SegmentLimit_15_0        = 0xFFFF,
    .BaseAddress_15_0         = 0x0,
    .BaseAddress_23_16        = 0x0,

    .Accessed                 = 0,
    .Writable                 = 1,
    .ExpansionDirection       = 0,
    .IsCode                   = 0,
    .IsNotSystemSegment       = 1,
    .DescriptorPrivilegeLevel = 0,
    .SegmentPresent           = 1,

    .SegmentLimit_19_16       = 0xF,
    .Available                = 0,
    .Reserved                 = 0,
    .UpperBound               = 1,
    .Granularity              = 1,
    .BaseAddress_31_24        = 0x0
  },
  .LinearCode = {
    .SegmentLimit_15_0        = 0xFFFF,
    .BaseAddress_15_0         = 0x0,
    .BaseAddress_23_16        = 0x0,

    .Accessed                 = 1,
    .Readable                 = 1,
    .Conforming               = 1,
    .IsCode                   = 1,
    .IsNotSystemSegment       = 1,
    .DescriptorPrivilegeLevel = 0,
    .SegmentPresent           = 1,

    .SegmentLimit_19_16       = 0xF,
    .Available                = 0,
    .Reserved                 = 0,
    .Is32Bit                  = 1,
    .Granularity              = 1,
    .BaseAddress_31_24        = 0x0
  },
  .SysCode = {
    .SegmentLimit_15_0        = 0xFFFF,
    .BaseAddress_15_0         = 0x0,
    .BaseAddress_23_16        = 0x0,

    .Accessed                 = 0,
    .Readable                 = 1,
    .Conforming               = 0,
    .IsCode                   = 1,
    .IsNotSystemSegment       = 1,
    .DescriptorPrivilegeLevel = 0,
    .SegmentPresent           = 1,

    .SegmentLimit_19_16       = 0xF,
    .Available                = 0,
    .Reserved                 = 0,
    .Is32Bit                  = 1,
    .Granularity              = 1,
    .BaseAddress_31_24        = 0x0
  },
  .SysData = {
    .SegmentLimit_15_0        = 0xFFFF,
    .BaseAddress_15_0         = 0x0,
    .BaseAddress_23_16        = 0x0,

    .Accessed                 = 1,
    .Writable                 = 1,
    .ExpansionDirection       = 0,
    .IsCode                   = 0,
    .IsNotSystemSegment       = 1,
    .DescriptorPrivilegeLevel = 0,
    .SegmentPresent           = 1,

    .SegmentLimit_19_16       = 0xF,
    .Available                = 0,
    .Reserved                 = 0,
    .UpperBound               = 1,
    .Granularity              = 1,
    .BaseAddress_31_24        = 0x0
  },
  .Ring3Code32 = {
    .SegmentLimit_15_0        = 0xFFFF,
    .BaseAddress_15_0         = 0x0,
    .BaseAddress_23_16        = 0x0,

    .Accessed                 = 0,
    .Readable                 = 1,
    .Conforming               = 0,
    .IsCode                   = 1,
    .IsNotSystemSegment       = 1,
    .DescriptorPrivilegeLevel = 3,
    .SegmentPresent           = 1,

    .SegmentLimit_19_16       = 0xF,
    .Available                = 0,
    .Reserved                 = 0,
    .Is32Bit                  = 1,
    .Granularity              = 1,
    .BaseAddress_31_24        = 0x0
  },
  .Ring3Data32 = {
    .SegmentLimit_15_0        = 0xFFFF,
    .BaseAddress_15_0         = 0x0,
    .BaseAddress_23_16        = 0x0,

    .Accessed                 = 1,
    .Writable                 = 1,
    .ExpansionDirection       = 0,
    .IsCode                   = 0,
    .IsNotSystemSegment       = 1,
    .DescriptorPrivilegeLevel = 3,
    .SegmentPresent           = 1,

    .SegmentLimit_19_16       = 0xF,
    .Available                = 0,
    .Reserved                 = 0,
    .UpperBound               = 1,
    .Granularity              = 1,
    .BaseAddress_31_24        = 0x0
  },
  .SysCode16 = {
    .SegmentLimit_15_0        = 0xFFFF,
    .BaseAddress_15_0         = 0x0,
    .BaseAddress_23_16        = 0x0,

    .Accessed                 = 0,
    .Readable                 = 1,
    .Conforming               = 0,
    .IsCode                   = 1,
    .IsNotSystemSegment       = 1,
    .DescriptorPrivilegeLevel = 0,
    .SegmentPresent           = 1,

    .SegmentLimit_19_16       = 0xF,
    .Available                = 0,
    .Reserved                 = 0,
    .Is32Bit                  = 0,
    .Granularity              = 1,
    .BaseAddress_31_24        = 0x0
  },
  .LinearCode64 = {
    .Reserved1                = 0x0,
    .Reserved2                = 0x0,

    .Accessed                 = 0,
    .Readable                 = 1,
    .Conforming               = 0,
    .IsCode                   = 1,
    .IsNotSystemSegment       = 1,
    .DescriptorPrivilegeLevel = 0,
    .SegmentPresent           = 1,

    .Reserved3                = 0x0,
    .Available                = 0,
    .LongMode                 = 1,
    .Is32Bit                  = 0,
    .Granularity              = 1,
    .Reserved4                = 0x0
  },
  .LinearData64 = {
    .SegmentLimit_15_0        = 0xFFFF,
    .BaseAddress_15_0         = 0x0,
    .BaseAddress_23_16        = 0x0,

    .Accessed                 = 0,
    .Writable                 = 1,
    .ExpansionDirection       = 0,
    .IsCode                   = 0,
    .IsNotSystemSegment       = 1,
    .DescriptorPrivilegeLevel = 0,
    .SegmentPresent           = 1,

    .SegmentLimit_19_16       = 0xF,
    .Available                = 0,
    .Reserved                 = 0,
    .UpperBound               = 1,
    .Granularity              = 1,
    .BaseAddress_31_24        = 0x0
  },
  .Spare5 = {
    .SegmentLimit_15_0  = 0x0,
    .BaseAddress_15_0   = 0x0,
    .BaseAddress_23_16  = 0x0,
    .Type               = 0x0,
    .S                  = 0,
    .DPL                = 0,
    .P                  = 0,
    .SegmentLimit_19_16 = 0x0,
    .AVL                = 0,
    .L                  = 0,
    .D_B                = 0,
    .G                  = 0,
    .BaseAddress_31_24  = 0x0,
  },
  .Ring3Data64 = {
    .SegmentLimit_15_0        = 0xFFFF,
    .BaseAddress_15_0         = 0x0,
    .BaseAddress_23_16        = 0x0,

    .Accessed                 = 0,
    .Writable                 = 1,
    .ExpansionDirection       = 0,
    .IsCode                   = 0,
    .IsNotSystemSegment       = 1,
    .DescriptorPrivilegeLevel = 3,
    .SegmentPresent           = 1,

    .SegmentLimit_19_16       = 0xF,
    .Available                = 0,
    .Reserved                 = 0,
    .UpperBound               = 1,
    .Granularity              = 1,
    .BaseAddress_31_24        = 0x0
  },
  .Ring3Code64 = {
    .Reserved1                = 0x0,
    .Reserved2                = 0x0,

    .Accessed                 = 0,
    .Readable                 = 1,
    .Conforming               = 0,
    .IsCode                   = 1,
    .IsNotSystemSegment       = 1,
    .DescriptorPrivilegeLevel = 3,
    .SegmentPresent           = 1,

    .Reserved3                = 0x0,
    .Available                = 0,
    .LongMode                 = 1,
    .Is32Bit                  = 0,
    .Granularity              = 1,
    .Reserved4                = 0x0
  },
};

/**
  Initialize Global Descriptor Table.

**/
VOID
InitGlobalDescriptorTable (
  VOID
  )
{
  EFI_STATUS            Status;
  GDT                   *Gdt;
  IA32_DESCRIPTOR       Gdtr;
  EFI_PHYSICAL_ADDRESS  Memory;

  //
  // Allocate Runtime Data below 4GB for the GDT
  // AP uses the same GDT when it's waken up from real mode so
  // the GDT needs to be below 4GB.
  //
  Memory = SIZE_4GB - 1;
  Status = gBS->AllocatePages (
                  AllocateMaxAddress,
                  EfiRuntimeServicesData,
                  EFI_SIZE_TO_PAGES (sizeof (mGdtTemplate)),
                  &Memory
                  );
  ASSERT_EFI_ERROR (Status);
  ASSERT ((Memory != 0) && (Memory < SIZE_4GB));
  Gdt = (GDT *)(UINTN)Memory;

  //
  // Initialize all GDT entries
  //
  CopyMem (Gdt, &mGdtTemplate, sizeof (mGdtTemplate));

  //
  // Write GDT register
  //
  Gdtr.Base  = (UINT32)(UINTN)Gdt;
  Gdtr.Limit = (UINT16)(sizeof (mGdtTemplate) - 1);
  AsmWriteGdtr (&Gdtr);

  //
  // Update selector (segment) registers base on new GDT
  //
  SetCodeSelector ((UINT16)CPU_CODE_SEL);
  SetDataSelectors ((UINT16)CPU_DATA_SEL);
}
