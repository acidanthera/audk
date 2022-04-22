/** @file
  Provides APIs to perform safe overflow-aware arithmetic.

  Copyright (c) 2020 - 2021, Marvin Häuser. All rights reserved.<BR>
  Copyright (c) 2020, Vitaly Cheptsov. All rights reserved.<BR>
  Copyright (c) 2020, ISP RAS. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-3-Clause
**/

#ifndef BASE_OVERFLOW_H_
#define BASE_OVERFLOW_H_

BOOLEAN
BaseOverflowAddU32 (
  IN  UINT32  A,
  IN  UINT32  B,
  OUT UINT32  *Result
  );

BOOLEAN
BaseOverflowSubU32 (
  IN  UINT32  A,
  IN  UINT32  B,
  OUT UINT32  *Result
  );

BOOLEAN
BaseOverflowSubU16 (
  IN  UINT16  A,
  IN  UINT16  B,
  OUT UINT16  *Result
  );

BOOLEAN
BaseOverflowMulU32 (
  IN  UINT32  A,
  IN  UINT32  B,
  OUT UINT32  *Result
  );

BOOLEAN
BaseOverflowAlignUpU32 (
  IN  UINT32  Value,
  IN  UINT32  Alignment,
  OUT UINT32  *Result
  );

#endif // BASE_OVERFLOW_H_
