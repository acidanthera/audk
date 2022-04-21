/** @file
  Provides abstractions to ease proving with the AstraVer Toolset.

  Copyright (c) 2020, Marvin Häuser. All rights reserved.<BR>
  Copyright (c) 2020, Vitaly Cheptsov. All rights reserved.<BR>
  Copyright (c) 2020, ISP RAS. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-3-Clause
**/

#ifndef AV_MACROS_H
#define AV_MACROS_H

#include "Base.h"
#ifndef PRODUCTION
#include "Frama.h"
#endif

#ifndef ASSERT
#if defined(FUZZING)
  #include <assert.h>
  #define ASSERT  assert
#elif defined(PRODUCTION)
  #define ASSERT(c)  do { if (!(c)) { __builtin_unreachable (); } } while (FALSE)
#else
  #define ASSERT(...)
#endif
#endif

#ifndef PRODUCTION
  #define STATIC_ASSERT(...)
#else
  #define STATIC_ASSERT  _Static_assert
#endif

#ifndef PRODUCTION
  /*@ requires \typeof(Ptr) <: \type(char *);
    @ requires \valid(((char *) Ptr) + (0 .. 1));
    @ requires pointer_aligned(Ptr, AV_ALIGNOF (UINT16));
    @ assigns \nothing;
    @ ensures \result == uint16_from_char ((char *) Ptr);
  */
  UINT16
  ReadAligned16 (
    IN CONST VOID  *Ptr
    );

  /*@ requires \typeof(Ptr) <: \type(char *);
    @ requires \valid(((char *) Ptr) + (0 .. 1));
    @ requires pointer_aligned(Ptr, AV_ALIGNOF (UINT16));
    @ assigns ((char *) Ptr)[0 .. 1];
    @ ensures uint16_from_char ((char *) Ptr) == Val;
  */
  VOID
  WriteAligned16 (
    OUT VOID    *Ptr,
    IN  UINT16  Val
    );

  /*@ requires \typeof(Ptr) <: \type(char *);
    @ requires \valid(((char *) Ptr) + (0 .. 3));
    @ requires pointer_aligned(Ptr, AV_ALIGNOF (UINT32));
    @ assigns \nothing;
    @ ensures \result == uint32_from_char ((char *) Ptr);
  */
  UINT32
  ReadAligned32 (
    IN CONST VOID  *Ptr
    );

  /*@ requires \typeof(Ptr) <: \type(char *);
    @ requires \valid(((char *) Ptr) + (0 .. 3));
    @ requires pointer_aligned(Ptr, AV_ALIGNOF (UINT32));
    @ assigns ((char *) Ptr)[0 .. 3];
    @ ensures uint32_from_char ((char *) Ptr) == Val;
  */
  VOID
  WriteAligned32 (
    OUT VOID    *Ptr,
    IN  UINT32  Val
    );

  /*@ requires \typeof(Ptr) <: \type(char *);
    @ requires \valid(((char *) Ptr) + (0 .. 7));
    @ requires pointer_aligned(Ptr, AV_ALIGNOF (UINT64));
    @ assigns \nothing;
    @ ensures \result == uint64_from_char ((char *) Ptr);
  */
  UINT64
  ReadAligned64 (
    IN CONST VOID  *Ptr
    );

  /*@ requires \typeof(Ptr) <: \type(char *);
    @ requires \valid(((char *) Ptr) + (0 .. 7));
    @ requires pointer_aligned(Ptr, AV_ALIGNOF (UINT64));
    @ assigns ((char *) Ptr)[0 .. 7];
    @ ensures uint64_from_char ((char *) Ptr) == Val;
  */
  VOID
  WriteAligned64 (
    OUT VOID    *Ptr,
    IN  UINT64  Val
    );

  #define READ_ALIGNED_16(x)     (ReadAligned16 (x))
  #define WRITE_ALIGNED_16(x, y) (WriteAligned16 (x, y))
  #define READ_ALIGNED_32(x)     (ReadAligned32 (x))
  #define WRITE_ALIGNED_32(x, y) (WriteAligned32 (x, y))
  #define READ_ALIGNED_64(x)     (ReadAligned64 (x))
  #define WRITE_ALIGNED_64(x, y) (WriteAligned64 (x, y))
#else
  #define READ_ALIGNED_16(x)     (*(CONST UINT16 *) (CONST VOID *) (x))
  #define WRITE_ALIGNED_16(x, y) do { *(UINT16 *) (VOID *) (x) = (y); } while (FALSE)
  #define READ_ALIGNED_32(x)     (*(CONST UINT32 *) (CONST VOID *) (x))
  #define WRITE_ALIGNED_32(x, y) do { *(UINT32 *) (VOID *) (x) = (y); } while (FALSE)
  #define READ_ALIGNED_64(x)     (*(CONST UINT64 *) (CONST VOID *) (x))
  #define WRITE_ALIGNED_64(x, y) do { *(UINT64 *) (VOID *) (x) = (y); } while (FALSE)
#endif

#ifndef PRODUCTION
  #define COMPOSE_32(High, Low)  \
    ((UINT32) ((UINT32) (Low) + ((UINT32) (High) * 65536U)))
  #define SIGNATURE_16(A, B)        ((A) + ((B) * 256U))
  #define SIGNATURE_32(A, B, C, D)  (SIGNATURE_16 (A, B) + SIGNATURE_16 (C, D) * 65536U)
#else
  #define COMPOSE_32(High, Low)  \
    ((UINT32) ((UINT32) (Low) + ((UINT32) (High) * 65536U)))
  #define SIGNATURE_16(A, B)        ((A) | (B << 8))
  #define SIGNATURE_32(A, B, C, D)  (SIGNATURE_16 (A, B) | (SIGNATURE_16 (C, D) << 16))
#endif

/*@ axiomatic Compose32Macro {
  @   lemma shift_eq_mul_16:
  @     \forall uint16_t value; ((uint32_t) value <<% 16) == (value * 65536);
  @
  @   lemma disjunct_add_eq_or_32:
  @     \forall uint32_t v1, v2; (v1 & v2) == 0 ==>
  @       (v1 +% v2) == (v1 | v2);
  @
  @   lemma disjunct_or_16_32:
  @     \forall uint16_t v1, v2;
  @     (((uint32_t) v1 <<% 16) & (uint32_t) v2) == 0;
  @
  @   lemma compose_or_eq_plus_16:
  @     \forall uint16_t High, Low;
  @     (((uint32_t) High <<% 16) | (uint32_t) Low) == (((uint32_t) High <<% 16) + (uint32_t) Low);
  @
  @   logic uint32_t compose_32 (uint16_t High, uint16_t Low) =
  @     ((uint32_t) High <<% 16) | (uint32_t) Low;
  @
  @   lemma compose_32_e_macro:
  @     \forall uint16_t High, Low;
  @     compose_32 (High, Low) == COMPOSE_32 (High, Low);
  @ }
*/

#ifndef PRODUCTION
  /*@ requires \valid((char *) Ptr + (0 .. Size - 1));
    @ assigns \nothing;
    @ ensures \result + Size <= MAX_UINTN;
    @ ensures \result == pointer_to_address (Ptr);
  */
  UINTN
  PtrToAddress (
    IN CONST VOID  *Ptr,
    IN UINTN       Size
    );

  #define PTR_TO_ADDR(Ptr, Size) (PtrToAddress (Ptr, Size))
#else
  #define PTR_TO_ADDR(Ptr, Size) ((UINTN) Ptr)
#endif

#ifndef PRODUCTION
  #define OC_ALIGNOF(Type)  ((UINT32) (sizeof (Type) < AV_MAX_ALIGN ? sizeof (Type) : AV_MAX_ALIGN))
#else
  #define OC_ALIGNOF  _Alignof
#endif

#ifndef PRODUCTION
  /*@ requires HashContext != \null;
    @ requires \typeof(Data) <: \type(char *);
    @ requires \valid((char *) Data + (0 .. DataLength - 1));

    @ assigns \nothing;
  */
  BOOLEAN
  HashUpdate (
    IN OUT  VOID        *HashContext,
    IN      CONST VOID  *Data,
    IN      UINTN       DataLength
    );
#endif

#endif // AV_MACROS_H
