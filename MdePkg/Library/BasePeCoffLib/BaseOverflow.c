/** @file
  Implements APIs to perform safe overflow-aware arithmetic.

  Copyright (c) 2020 - 2021, Marvin Häuser. All rights reserved.<BR>
  Copyright (c) 2020, Vitaly Cheptsov. All rights reserved.<BR>
  Copyright (c) 2020, ISP RAS. All rights reserved.<BR>

  SPDX-License-Identifier: BSD-3-Clause
**/

#include "Base.h"
#include "BaseOverflow.h"

BOOLEAN
BaseOverflowAddU32 (
  UINT32  A,
  UINT32  B,
  UINT32  *Result
  )
{
#ifdef PRODUCTION
  return __builtin_add_overflow(A, B, Result);
#else
  UINT32 Temp;

  Temp = A + B;
  *Result = Temp;

  if (Temp < A) {
    return TRUE;
  }

  return FALSE;
#endif
}

BOOLEAN
BaseOverflowSubU32 (
  UINT32  A,
  UINT32  B,
  UINT32  *Result
  )
{
#ifdef PRODUCTION
  return __builtin_sub_overflow(A, B, Result);
#else
  *Result = A - B;

  if (B > A) {
    return TRUE;
  }

  return FALSE;
#endif
}

BOOLEAN
BaseOverflowSubU16 (
  UINT16  A,
  UINT16  B,
  UINT16  *Result
  )
{
#ifdef PRODUCTION
  return __builtin_sub_overflow(A, B, Result);
#else
  *Result = (UINT16) (A - B);

  if (B > A) {
    return TRUE;
  }

  return FALSE;
#endif
}

BOOLEAN
BaseOverflowMulU32 (
  UINT32  A,
  UINT32  B,
  UINT32  *Result
  )
{
#ifdef PRODUCTION
  return __builtin_mul_overflow(A, B, Result);
#else
  UINT64 Temp;

  Temp = (UINT64) A * B;
  *Result = (UINT32) Temp;

  if (Temp > MAX_UINT32) {
    return TRUE;
  }

  return FALSE;
#endif
}

BOOLEAN
BaseOverflowAlignUpU32 (
  IN  UINT32  Value,
  IN  UINT32  Alignment,
  OUT UINT32  *Result
  )
{
  BOOLEAN Overflow;
  UINT32  AddResult;

  Overflow = BaseOverflowAddU32 (Value, Alignment - 1U, &AddResult);
  *Result = (AddResult & ~(Alignment - 1U));

  return Overflow;
}
