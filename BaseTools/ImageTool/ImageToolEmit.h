/** @file
  Copyright (c) 2023, Marvin Häuser. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause
**/

#ifndef IMAGE_TOOL_EMIT_H
#define IMAGE_TOOL_EMIT_H

#include <stdint.h>

#include <Base.h>

void *
ToolImageEmit (
  OUT uint32_t    *OutputFileSize,
  IN  const void  *Buffer,
  IN  uint32_t    BufferSize,
  IN  int8_t      Format,
  IN  int32_t     Type,
  IN  void        *HiiFile,
  IN  uint32_t    HiiFileSize,
  IN  bool        Relocate,
  IN  uint64_t    BaseAddress,
  IN  const char  *SymbolsPath OPTIONAL,
  IN  bool        Strip,
  IN  bool        FixedAddress
  );

#endif // IMAGE_TOOL_EMIT_H
