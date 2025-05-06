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

#define NULL_SEL           OFFSET_OF (GDT, Null)
#define LINEAR_SEL         OFFSET_OF (GDT, Linear)
#define LINEAR_CODE_SEL    OFFSET_OF (GDT, LinearCode)
#define SYS_DATA_SEL       OFFSET_OF (GDT, SysData)
#define SYS_CODE_SEL       OFFSET_OF (GDT, SysCode)
#define SYS_CODE16_SEL     OFFSET_OF (GDT, SysCode16)
#define LINEAR_DATA64_SEL  OFFSET_OF (GDT, LinearData64)
#define LINEAR_CODE64_SEL  OFFSET_OF (GDT, LinearCode64)
#define SPARE5_SEL         OFFSET_OF (GDT, Spare5)

#if defined (MDE_CPU_IA32)
#define CPU_CODE_SEL  SYS_CODE_SEL
#define CPU_DATA_SEL  SYS_DATA_SEL
#elif defined (MDE_CPU_X64)
#define CPU_CODE_SEL  LINEAR_CODE64_SEL
#define CPU_DATA_SEL  LINEAR_DATA64_SEL
#else
  #error CPU type not supported for CPU GDT initialization!
#endif

#endif // _CPU_GDT_H_
