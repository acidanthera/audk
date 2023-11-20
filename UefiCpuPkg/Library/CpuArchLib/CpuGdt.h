/** @file
  C based implementation of IA32 interrupt handling only
  requiring a minimal assembly interrupt entry point.

  Copyright (c) 2006 - 2015, Intel Corporation. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-2-Clause-Patent

**/

#ifndef _CPU_GDT_H_
#define _CPU_GDT_H_

//
// Local structure definitions
//

#pragma pack (1)

//
// Global Descriptor Entry structures
//

typedef struct {
  UINT16    SegmentLimit_15_0;
  UINT16    BaseAddress_15_0;
  UINT8     BaseAddress_23_16;
  UINT8     Type : 4;
  UINT8     S    : 1;
  UINT8     DPL  : 2;
  UINT8     P    : 1;
  UINT8     SegmentLimit_19_16 : 4;
  UINT8     AVL                : 1;
  UINT8     L                  : 1;
  UINT8     D_B                : 1;
  UINT8     G                  : 1;
  UINT8     BaseAddress_31_24;
} SEGMENT_DESCRIPTOR;

typedef struct {
  UINT16    SegmentLimit_15_0;
  UINT16    BaseAddress_15_0;
  UINT8     BaseAddress_23_16;
  //
  // Type
  //
  UINT8     Accessed           : 1;
  UINT8     Writable           : 1;
  UINT8     ExpansionDirection : 1;
  UINT8     IsCode             : 1;
  UINT8     IsNotSystemSegment       : 1;
  UINT8     DescriptorPrivilegeLevel : 2;
  UINT8     SegmentPresent           : 1;

  UINT8     SegmentLimit_19_16 : 4;
  UINT8     Available          : 1;
  UINT8     Reserved           : 1;
  UINT8     UpperBound         : 1;
  UINT8     Granularity        : 1;
  UINT8     BaseAddress_31_24;
} DATA_SEGMENT_32;

typedef struct {
  UINT16    SegmentLimit_15_0;
  UINT16    BaseAddress_15_0;
  UINT8     BaseAddress_23_16;
  //
  // Type
  //
  UINT8     Accessed   : 1;
  UINT8     Readable   : 1;
  UINT8     Conforming : 1;
  UINT8     IsCode     : 1;
  UINT8     IsNotSystemSegment       : 1;
  UINT8     DescriptorPrivilegeLevel : 2;
  UINT8     SegmentPresent           : 1;

  UINT8     SegmentLimit_19_16 : 4;
  UINT8     Available          : 1;
  UINT8     Reserved           : 1;
  UINT8     Is32Bit            : 1;
  UINT8     Granularity        : 1;
  UINT8     BaseAddress_31_24;
} CODE_SEGMENT_32;

typedef struct {
  UINT32    Reserved1;
  UINT8     Reserved2;
  //
  // Type
  //
  UINT8     Accessed   : 1;
  UINT8     Readable   : 1;
  UINT8     Conforming : 1;
  UINT8     IsCode     : 1;
  UINT8     IsNotSystemSegment       : 1;
  UINT8     DescriptorPrivilegeLevel : 2;
  UINT8     SegmentPresent           : 1;

  UINT8     Reserved3   : 4;
  UINT8     Available   : 1;
  UINT8     LongMode    : 1;
  UINT8     Is32Bit     : 1;
  UINT8     Granularity : 1;
  UINT8     Reserved4;
} CODE_SEGMENT_64;

typedef struct {
  UINT16    SegmentLimit_15_0;
  UINT16    BaseAddress_15_0;
  UINT8     BaseAddress_23_16;

  UINT8     Type                     : 4;
  UINT8     IsNotSystemSegment       : 1;
  UINT8     DescriptorPrivilegeLevel : 2;
  UINT8     SegmentPresent           : 1;

  UINT8     SegmentLimit_19_16 : 4;
  UINT8     Reserved           : 3;
  UINT8     Granularity        : 1;
  UINT8     BaseAddress_31_24;
} SYSTEM_SEGMENT;

typedef struct {
  UINT16    OffsetInSegment_15_0;
  UINT16    SegmentSelector;

  UINT8     ParameterCount : 5;
  UINT8     Reserved       : 3;

  UINT8     Type                     : 4;
  UINT8     IsNotSystemSegment       : 1;
  UINT8     DescriptorPrivilegeLevel : 2;
  UINT8     SegmentPresent           : 1;
  UINT16    OffsetInSegment_31_16;
} CALL_GATE_32;

typedef struct {
  CALL_GATE_32  Common;
  UINT32        OffsetInSegment_63_31;
  UINT32        Reserved;
} CALL_GATE_64;

typedef union {
  DATA_SEGMENT_32    DataSegment32;
  CODE_SEGMENT_32    CodeSegment32;
  CODE_SEGMENT_64    CodeSegment64;
  CALL_GATE_32       CallGate32;
  SYSTEM_SEGMENT     SystemSegment;
  SEGMENT_DESCRIPTOR SegmentDescriptor;
} GDT_ENTRY;

typedef struct {
  SEGMENT_DESCRIPTOR Null;
  DATA_SEGMENT_32    Linear;
  CODE_SEGMENT_32    LinearCode;
  DATA_SEGMENT_32    SysData;
  CODE_SEGMENT_32    SysCode;
  CODE_SEGMENT_32    SysCode16;
  DATA_SEGMENT_32    LinearData64;
  CODE_SEGMENT_64    LinearCode64;
  SEGMENT_DESCRIPTOR Spare5;
} GDT_ENTRIES;

#pragma pack ()

#define NULL_SEL           OFFSET_OF (GDT_ENTRIES, Null)
#define LINEAR_SEL         OFFSET_OF (GDT_ENTRIES, Linear)
#define LINEAR_CODE_SEL    OFFSET_OF (GDT_ENTRIES, LinearCode)
#define SYS_DATA_SEL       OFFSET_OF (GDT_ENTRIES, SysData)
#define SYS_CODE_SEL       OFFSET_OF (GDT_ENTRIES, SysCode)
#define SYS_CODE16_SEL     OFFSET_OF (GDT_ENTRIES, SysCode16)
#define LINEAR_DATA64_SEL  OFFSET_OF (GDT_ENTRIES, LinearData64)
#define LINEAR_CODE64_SEL  OFFSET_OF (GDT_ENTRIES, LinearCode64)
#define SPARE5_SEL         OFFSET_OF (GDT_ENTRIES, Spare5)

#if defined (MDE_CPU_IA32)
#define CPU_CODE_SEL  LINEAR_CODE_SEL
#define CPU_DATA_SEL  LINEAR_SEL
#elif defined (MDE_CPU_X64)
#define CPU_CODE_SEL  LINEAR_CODE64_SEL
#define CPU_DATA_SEL  LINEAR_DATA64_SEL
#else
  #error CPU type not supported for CPU GDT initialization!
#endif

#endif // _CPU_GDT_H_
