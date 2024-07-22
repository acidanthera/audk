/** @file
  Processor or Compiler specific defines for all supported processors.

  This file is stand alone self consistent set of definitions.

  Copyright (c) 2006 - 2018, Intel Corporation. All rights reserved.<BR>
  Copyright (C) 2024 Advanced Micro Devices, Inc. All rights reserved.

  SPDX-License-Identifier: BSD-2-Clause-Patent

**/

#ifndef __BT_BASE_TYPES_H__
#define __BT_BASE_TYPES_H__

#include "WinNtInclude.h"

#include <stdarg.h>
#include <stdint.h>

//
// Base.h is a C header and must be linked against as such.
// Without this, MSVC may fail to link against _ReturnAddress.
//
#ifdef __cplusplus
extern "C" {
#endif

//
// These macros may have been declared previously by C standard libraries.
//
#undef NULL
#undef FALSE
#undef TRUE

#include <Base.h>

#ifdef __cplusplus
}
#endif

#endif
