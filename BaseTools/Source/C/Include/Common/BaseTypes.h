/** @file
  Processor or Compiler specific defines for all supported processors.

  This file is stand alone self consistent set of definitions.

  Copyright (c) 2006 - 2018, Intel Corporation. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-2-Clause-Patent

**/

#ifndef __BT_BASE_TYPES_H__
#define __BT_BASE_TYPES_H__

//
// To be able to safely include Windows headers, we need to include
// WinNtInclude.h first.
//
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
