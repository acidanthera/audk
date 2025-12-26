/** @file
  EFI image format for PE32+. Please note some data structures are different
  for IA-32 and Itanium-based images, look for UINTN and the #ifdef EFI_IA64

  @bug Fix text - doc as defined in MSFT EFI specification.

  Copyright (c) 2006 - 2018, Intel Corporation. All rights reserved.<BR>
  Portions copyright (c) 2011 - 2013, ARM Ltd. All rights reserved.<BR>
  Copyright (c) 2020, Hewlett Packard Enterprise Development LP. All rights reserved.<BR>
  Copyright (c) 2022, Loongson Technology Corporation Limited. All rights reserved.<BR>

  SPDX-License-Identifier: BSD-2-Clause-Patent

**/

#ifndef __BT_PE_IMAGE_H__
#define __BT_PE_IMAGE_H__

#include <IndustryStandard/PeImage.h>

//
// PE32+ Machine type for EFI images
//
#define IMAGE_FILE_MACHINE_ARM   0x01c0
#define IMAGE_FILE_MACHINE_ARMT  IMAGE_FILE_MACHINE_ARMTHUMB_MIXED

//
// Support old names for backward compatible
//
#define EFI_IMAGE_MACHINE_ARMT  EFI_IMAGE_MACHINE_ARMTHUMB_MIXED

#define EFI_IMAGE_FILE_LARGE_ADDRESS_AWARE  0x0020  // Supports addresses > 2-GB

//
// Based export types.
//
#define EFI_IMAGE_EXPORT_ORDINAL_BASE  1
#define EFI_IMAGE_EXPORT_ADDR_SIZE     4
#define EFI_IMAGE_EXPORT_ORDINAL_SIZE  2

//
// .pdata entries for X64
//
typedef struct {
  UINT32    FunctionStartAddress;
  UINT32    FunctionEndAddress;
  UINT32    UnwindInfoAddress;
} RUNTIME_FUNCTION;

typedef struct {
  UINT8    Version             : 3;
  UINT8    Flags               : 5;
  UINT8    SizeOfProlog;
  UINT8    CountOfUnwindCodes;
  UINT8    FrameRegister       : 4;
  UINT8    FrameRegisterOffset : 4;
} UNWIND_INFO;

#endif
