/** @file
  CPU DXE Module to produce CPU ARCH Protocol.
  Copyright (c) 2008 - 2022, Intel Corporation. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-2-Clause-Patent
**/

#ifndef _CPU_ARCH_LIB_H_
#define _CPU_ARCH_LIB_H_

/**
  Initialize the state information for the CPU Architectural Protocol.

  @retval EFI_SUCCESS           Thread can be successfully created
  @retval EFI_OUT_OF_RESOURCES  Can not allocate protocol data structure
  @retval EFI_DEVICE_ERROR      Can not create the thread
**/
EFI_STATUS
InitializeCpu (
  VOID
  );

/**
  Initialize Multi-processor support.

**/
VOID
InitializeMpSupport (
  VOID
  );

#endif // _CPU_ARCH_LIB_H_
