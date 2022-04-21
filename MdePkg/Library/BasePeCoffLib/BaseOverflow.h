/** @file
  Provides APIs to perform safe overflow-aware arithmetic.

  Copyright (c) 2020, Marvin Häuser. All rights reserved.<BR>
  Copyright (c) 2020, Vitaly Cheptsov. All rights reserved.<BR>
  Copyright (c) 2020, ISP RAS. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-3-Clause
**/

#ifndef OC_OVERFLOW_H
#define OC_OVERFLOW_H

/*@ requires \valid(Result);
  @
  @ assigns *Result;
  @
  @ ensures *Result == A +% B;
  @ ensures !\result <==> A + B <= MAX_UINT32;
  @ ensures !\result <==> *Result == A + B;
*/
BOOLEAN
BaseOverflowAddU32 (
  UINT32  A,
  UINT32  B,
  UINT32  *Result
  );

/*@ requires \valid(Result);
  @
  @ assigns *Result;
  @
  @ ensures *Result == A -% B;
  @ ensures !\result <==> 0 <= A - B;
  @ ensures !\result <==> *Result == A - B;
*/
BOOLEAN
BaseOverflowSubU32 (
  UINT32  A,
  UINT32  B,
  UINT32  *Result
  );

/*@ requires \valid(Result);
  @
  @ assigns *Result;
  @
  @ ensures *Result == A -% B;
  @ ensures !\result <==> 0 <= A - B;
  @ ensures !\result <==> *Result == A - B;
*/
BOOLEAN
BaseOverflowSubU16 (
  UINT16  A,
  UINT16  B,
  UINT16  *Result
  );

/*@ requires \valid(Result);
  @
  @ assigns *Result;
  @
  @ ensures *Result == A *% B;
  @ ensures !\result <==> A * B <= MAX_UINT32;
  @ ensures !\result <==> *Result == A * B;
*/
BOOLEAN
BaseOverflowMulU32 (
  UINT32  A,
  UINT32  B,
  UINT32  *Result
  );

/*@ requires is_pow2_32 (Alignment);
  @ requires \valid(Result);
  @
  @ assigns *Result;
  @
  @ ensures *Result == align_up_32 (Value, Alignment);
  @ ensures !\result <==> align_up (Value, Alignment) <= MAX_UINT32;
  @ ensures !\result <==> align_safe_32 (Value, Alignment);
  @ ensures !\result <==> *Result == align_up (Value, Alignment);
*/
BOOLEAN
BaseOverflowAlignUpU32 (
  IN  UINT32  Value,
  IN  UINT32  Alignment,
  OUT UINT32  *Result
  );

#endif // OC_OVERFLOW_H
