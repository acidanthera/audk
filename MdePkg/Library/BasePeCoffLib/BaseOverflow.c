/** @file
  Implements APIs to perform safe overflow-aware arithmetic.

  Copyright (c) 2020, Marvin Häuser. All rights reserved.<BR>
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

  /*@ assigns Temp;
    @ ensures Temp == A +% B;
  */
  Temp = A +/*@%*/ B;

  /*@ assigns *Result;
    @ ensures *Result == A +% B;
  */
  *Result = Temp;

  /*@ assigns \nothing;
    @ ensures A + B <= MAX_UINT32;
  */
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
  /*@ assigns *Result;
    @ ensures *Result == A -% B;
  */
  *Result = A -/*@%*/ B;

  /*@ assigns \nothing;
    @ ensures 0 <= A - B;
  */
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
  /*@ assigns *Result;
    @ ensures *Result == A -% B;
  */
  *Result = (UINT16)/*@%*/ (A -/*@%*/ B);

  /*@ assigns \nothing;
    @ ensures 0 <= A - B;
  */
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
  UINT64  Temp;

  /*@ assigns Temp;
    @ ensures Temp == A * B;
  */
  Temp = (UINT64) A * B;

  /*@ assigns *Result;
    @ ensures *Result == A *% B;
  */
  *Result = (UINT32)/*@%*/ Temp;

  /*@ assigns \nothing;
    @ ensures A * B <= MAX_UINT32;
  */
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
  BOOLEAN Status;

  /*@ assigns Status, *Result;
    @ ensures *Result == Value +% (Alignment -% 1);
    @ ensures !Status <==> *Result == Value + (Alignment - 1);
    @ ensures !Status <==> align_safe_32 (Value, Alignment);
  */
  Status = BaseOverflowAddU32 (Value, Alignment -/*@%*/ 1U, Result);

  /*@ assigns *Result;
    @ ensures *Result == ((Value +% (Alignment -% 1)) & ~(Alignment -% 1));
    @ ensures !Status <==> *Result == align_up (Value, Alignment);
  */
  *Result &= ~(Alignment - 1U);

  return Status;
}
