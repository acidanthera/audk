/** @file
  Provides APIs to perform safe overflow-aware arithmetic.

  Copyright (c) 2020, Marvin Häuser. All rights reserved.<BR>
  Copyright (c) 2020, Vitaly Cheptsov. All rights reserved.<BR>
  Copyright (c) 2020, ISP RAS. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-3-Clause
**/

#ifndef BASE_OVERFLOW_H
#define BASE_OVERFLOW_H

BOOLEAN
BaseOverflowAddU32 (
  UINT32  A,
  UINT32  B,
  UINT32  *Result
  );

BOOLEAN
BaseOverflowSubU32 (
  UINT32  A,
  UINT32  B,
  UINT32  *Result
  );

BOOLEAN
BaseOverflowSubU16 (
  UINT16  A,
  UINT16  B,
  UINT16  *Result
  );

BOOLEAN
BaseOverflowMulU32 (
  UINT32  A,
  UINT32  B,
  UINT32  *Result
  );

BOOLEAN
BaseOverflowAlignUpU32 (
  IN  UINT32  Value,
  IN  UINT32  Alignment,
  OUT UINT32  *Result
  );

#endif // BASE_OVERFLOW_H
