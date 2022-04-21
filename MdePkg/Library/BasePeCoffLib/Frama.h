/** @file
  Provides general annotations and lemmas for proving with the AstraVer Toolset.

  Copyright (c) 2020, Marvin Häuser. All rights reserved.<BR>
  Copyright (c) 2020, Vitaly Cheptsov. All rights reserved.<BR>
  Copyright (c) 2020, ISP RAS. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-3-Clause
**/

#ifndef FRAMA_H
#define FRAMA_H

#include <stdint.h>

/*@ assigns \nothing;
  @ ensures \result == ((x & 0x00FFU) <<% 8U) +%
                       ((x & 0xFF00U) >>  8U);
*/
uint16_t __builtin_bswap16 (uint16_t x);

/*@ assigns \nothing;
  @ ensures \result == ((x & 0x000000FFU) <<% 24U) +%
                       ((x & 0x0000FF00U) <<% 8U)  +%
                       ((x & 0x00FF0000U) >>  8U)  +%
                       ((x & 0xFF000000U) >> 24U);
*/
uint32_t __builtin_bswap32 (uint32_t x);

/*@ assigns \nothing;
  @ ensures \result == ((x & 0x00000000000000FFU) <<% 56U) +%
                       ((x & 0x000000000000FF00U) <<% 40U) +%
                       ((x & 0x0000000000FF0000U) <<% 24U) +%
                       ((x & 0x00000000FF000000U) <<%  8U) +%
                       ((x & 0x000000FF00000000U) >>   8U) +%
                       ((x & 0x0000FF0000000000U) >>  24U) +%
                       ((x & 0x00FF000000000000U) >>  40U) +%
                       ((x & 0xFF00000000000000U) >>  56U);
*/
uint64_t __builtin_bswap64 (uint64_t x);

/*@ terminates \false;
  @ assigns \nothing;
*/
void __builtin_unreachable (void);

//
// We only support integer types.
//
_Static_assert (
  _Alignof (unsigned long long) <= 8,
  "The current alignment model is not sound with the compiler model."
  );

#define AV_MAX_ALIGN     8U
#define AV_ALIGNOF(Type) pointer_alignof (sizeof (Type))

/*@ axiomatic PointerProperties {
  @   logic UINTN pointer_to_address{L} (void *Ptr);
  @
  @   axiom ptr_addr_null_def{L}:
  @     \forall void *Ptr; pointer_to_address (Ptr) == 0 <==> Ptr == \null;
  @
  @   axiom ptr_addr_offset_def{L}:
  @     \forall void *Ptr, UINTN Offset;
  @     pointer_to_address{L} ((char *) Ptr + Offset) == pointer_to_address (Ptr) +% Offset;
  @
  @   predicate pointer_aligned{L} (void *Ptr, UINTN Alignment) =
  @     is_aligned_N (pointer_to_address{L} (Ptr), Alignment);
  @
  @   predicate pointer_max_aligned{L} (void *Ptr) =
  @     pointer_aligned{L} (Ptr, AV_MAX_ALIGN);
  @
  @   logic UINT32 pointer_alignof (integer Size) =
  @     (UINT32) (Size < AV_MAX_ALIGN ? Size : AV_MAX_ALIGN);
  @
  @   lemma ptr_max_alignment{L}:
  @     \forall void *Ptr, UINTN Alignment; is_pow2_N (Alignment) && Alignment <= AV_MAX_ALIGN && pointer_max_aligned{L} (Ptr) ==>
  @       pointer_aligned{L} (Ptr, Alignment);
  @
  @   lemma ptr_offset_alignment{L}:
  @     \forall void *Ptr, UINTN Offset, UINTN Alignment; is_pow2_N (Alignment) && Alignment <= AV_MAX_ALIGN ==>
  @       pointer_aligned{L} (Ptr, Alignment) && is_aligned_N (Offset, Alignment) ==>
  @         pointer_aligned{L} ((char *) Ptr + Offset, Alignment);
  @ }
*/

/*@ requires n >= 0 &&
  @          n % (sizeof (UINT64)) == 0 &&
  @          \let _n = n / sizeof (UINT64);
  @          \valid(((UINT64 *) dest)+(0 .. _n - 1));
  @ assigns ((UINT64 *) dest)[0 .. (n / sizeof (UINT64)) - 1] \from val;
  @ allocates \nothing;
  @ ensures \let _n = n / sizeof (UINT64);
  @           val == 0 ==>
  @             \forall integer k; 0 <= k < _n ==> dest[k] == 0;
*/
extern void *memset_UINT64 (UINT64 *dest, int val, size_t n);

/*@ axiomatic BinaryPow2_32 {
  @   predicate is_pow2_32 (UINT32 v) =
  @     (v != 0 && (v & (v -% 1)) == 0);
  @
  @   axiom bin_pow2_rem_32:
  @     \forall UINT32 v, a; is_pow2_32 (a) ==>
  @       (v % a) == (v & (a -% 1));
  @
  @   axiom bin_pow2_rem_sub_32:
  @     \forall UINT32 v, a; is_pow2_32 (a) ==>
  @       v - (v % a) == (v & ~(a -% 1));
  @ }
*/

/*@ axiomatic BinaryPow2_64 {
  @   predicate is_pow2_64 (UINT64 v) =
  @     (v != 0 && (v & (v -% 1)) == 0);
  @
  @   axiom bin_pow2_rem_64:
  @     \forall UINT64 v, a; is_pow2_64 (a) ==>
  @       (v % a) == (v & (a -% 1));
  @
  @   axiom bin_pow2_rem_sub_64:
  @     \forall UINT64 v, a; is_pow2_64 (a) ==>
  @       v - (v % a) == (v & ~(a -% 1));
  @ }
*/

/*@ axiomatic BinaryPow2_N {
  @   predicate is_pow2_N (UINTN v) =
  @     (sizeof (UINTN) == sizeof (UINT32) ?
  @       is_pow2_32 ((UINT32) v) :
  @     (sizeof (UINTN) == sizeof (UINT64) ?
  @       is_pow2_64 ((UINT64) v) :
  @       FALSE));
  @ }
*/

/*@ axiomatic Alignment_32 {
  @   predicate is_aligned_32 (UINT32 v, UINT32 a) =
  @     is_pow2_32 (a) && ((v & (a -% 1)) == 0);
  @
  @   lemma is_aligned_le_32:
  @     \forall UINT32 v, a; is_aligned_32 (v, a) ==>
  @       (\forall UINT32 le; le <= a && is_pow2_32 (le) ==>
  @         is_aligned_32 (v, le));
  @
  @   lemma is_aligned_add_trans_32:
  @     \forall UINT32 v1, v2, a; is_aligned_32 (v1, a) && is_aligned_32 (v2, a) ==>
  @       is_aligned_32 (v1 +% v2, a);
  @ }
*/

/*@ axiomatic Alignment_64 {
  @   predicate is_aligned_64 (UINT64 v, UINT64 a) =
  @     is_pow2_64 (a) && ((v & (a -% 1)) == 0);
  @
  @   lemma is_aligned_le_64:
  @     \forall UINT64 v, a; is_aligned_64 (v, a) ==>
  @       (\forall UINT64 le; le <= a && is_pow2_64 (le) ==>
  @         is_aligned_64 (v, le));
  @
  @   lemma is_aligned_add_trans_64:
  @     \forall UINT64 v1, v2, a; is_aligned_64 (v1, a) && is_aligned_64 (v2, a) ==>
  @       is_aligned_64 (v1 +% v2, a);
  @ }
*/

/*@ axiomatic Alignment_N {
  @   predicate is_aligned_N (UINTN v, UINTN a) =
  @     (sizeof (UINTN) == sizeof (UINT32) ?
  @       is_aligned_32 ((UINT32) v, (UINT32) a) :
  @     (sizeof (UINTN) == sizeof (UINT64) ?
  @       is_aligned_64 ((UINT64) v, (UINT64) a) :
  @       FALSE));
  @ }
*/

/*@ axiomatic Alignment {
  @   predicate align_safe (integer v, integer a, integer m) =
  @     v + (a - 1) <= m;
  @
  @   logic integer align_up (integer v, integer a) =
  @     (v + (a - 1)) - ((v + (a - 1)) % a);
  @ }
*/

/*@ axiomatic AlignmentPow2_32 {
  @   predicate align_safe_32 (UINT32 v, UINT32 a) =
  @     align_safe (v, a, MAX_UINT32);
  @
  @   logic UINT32 align_up_32 (UINT32 v, UINT32 a) =
  @     (v +% (a -% 1)) & ~(a -% 1);
  @
  @   lemma align_safety_32:
  @     \forall UINT32 v, a; is_pow2_32 (a) ==>
  @       (align_safe_32 (v, a) ==> align_up (v, a) <= MAX_UINT32);
  @
  @   axiom align_safety_32_accurate:
  @     \forall UINT32 v, a; is_pow2_32 (a) ==>
  @       (align_up (v, a) <= MAX_UINT32 ==> align_safe_32 (v, a));
  @
  @   lemma align_up_mod_32:
  @     \forall uint32_t v, a; is_pow2_32 (a) ==>
  @       is_aligned_32 (align_up_32 (v, a), a);
  @
  @   lemma align_up_ge_v_32:
  @     \forall UINT32 v, a; is_pow2_32 (a) ==>
  @       v <= align_up (v, a);
  @
  @   lemma align_up_ge_a_32:
  @     \forall UINT32 v, a; 0 < v && is_pow2_32 (a) ==>
  @       a <= align_up (v, a);
  @
  @   lemma int_e_bin_align_32:
  @     \forall UINT32 v, a; is_pow2_32 (a) && align_safe_32 (v, a) ==>
  @       align_up (v, a) == align_up_32 (v, a);
  @
  @   lemma align_aligned_noop_32:
  @     \forall UINT32 v, a; is_aligned_32 (v, a) ==>
  @       align_up (v, a) == v;
  @ }
*/

/*@ axiomatic AlignmentPow2_64 {
  @   predicate align_safe_64 (UINT64 v, UINT64 a) =
  @     align_safe (v, a, MAX_UINT64);
  @
  @   logic UINT64 align_up_64 (UINT64 v, UINT64 a) =
  @     (v +% (a -% 1)) & ~(a -% 1);
  @
  @   lemma align_safety_64:
  @     \forall UINT64 v, a; is_pow2_64 (a) ==>
  @       (align_safe_64 (v, a) ==> align_up (v, a) <= MAX_UINT64);
  @
  @   axiom align_safety_64_accurate:
  @     \forall UINT64 v, a; is_pow2_64 (a) ==>
  @       (align_up (v, a) <= MAX_UINT64 ==> align_safe_64 (v, a));
  @
  @   lemma align_up_mod_64:
  @     \forall uint64_t v, a; is_pow2_64 (a) ==>
  @       is_aligned_64 (align_up_64 (v, a), a);
  @
  @   lemma align_up_ge_v_64:
  @     \forall UINT64 v, a; is_pow2_64 (a) ==>
  @       v <= align_up (v, a);
  @
  @   lemma align_up_ge_a_64:
  @     \forall UINT64 v, a; 0 < v && is_pow2_64 (a) ==>
  @       a <= align_up (v, a);
  @
  @   lemma int_e_bin_align_64:
  @     \forall UINT64 v, a; is_pow2_64 (a) && align_safe_64 (v, a) ==>
  @       align_up (v, a) == align_up_64 (v, a);
  @
  @   lemma align_aligned_noop_64:
  @     \forall UINT64 v, a; is_aligned_64 (v, a) ==>
  @       align_up (v, a) == v;
  @ }
*/

/*@ axiomatic AlignmentPow2_N {
  @   predicate align_safe_N (UINTN v, UINTN a) =
  @     (sizeof (UINTN) == sizeof (UINT32) ?
  @       align_safe_32 ((UINT32) v, (UINT32) a) :
  @     (sizeof (UINTN) == sizeof (UINT64) ?
  @       align_safe_64 ((UINT64) v, (UINT64) a) :
  @       FALSE));
  @
  @   logic UINTN align_up_N (UINTN v, UINTN a) =
  @     (sizeof (UINTN) == sizeof (UINT32) ?
  @       align_up_32 ((UINT32) v, (UINT32) a) :
  @     (sizeof (UINTN) == sizeof (UINT64) ?
  @       align_up_64 ((UINT64) v, (UINT64) a) :
  @       0));
  @
  @   lemma pow2_32_is_pow2_N:
  @     \forall UINT32 a; is_pow2_32 (a) ==> is_pow2_N ((UINTN) a);
  @
  @   lemma int_e_bin_align_N:
  @     \forall UINTN v, a; is_pow2_N (a) && align_safe_N (v, a) ==>
  @       align_up (v, a) == align_up_N (v, a);
  @ }
*/

/*@ axiomatic CharMemoryOperations {
  @   predicate char_equals{L1, L2}(char *p1, char *p2, integer n) =
  @     \forall integer k; 0 <= k < n ==>
  @       \at(p1[k], L1) == \at(p2[k], L2);
  @
  @   predicate char_zero{L1}(char *p1, integer n) =
  @     \forall integer k; 0 <= k < n ==>
  @       \at(p1[k], L1) == 0;
  @
  @   lemma sub_mem{L1, L2}:
  @     \forall integer n, s1, s2, char *buf1, *buf2;
  @       \forall integer s, n2; 0 <= s <= n && 0 <= n2 <= n - s ==>
  @       char_equals{L1,L2}(buf1 + s1, buf2 +s2, n) ==>
  @         char_equals{L1,L2}(buf1 + s1 + s, buf2 + s2 + s, n2);
  @
  @   lemma trans_state_equals{L1, L2}:
  @     \forall integer n, s1,s2, char *buf1, *buf2;
  @     char_equals{L1, L1}(buf1 + s1, buf2 + s2, n) && char_equals{L1,L2}(buf2 + s2, buf2 + s2, n) ==>
  @       char_equals{L1, L2}(buf1 + s1, buf2 + s2, n);
  @
  @   lemma trans_state_zero{L1, L2}:
  @     \forall integer n, s1,s2, char *buf1, *buf2;
  @     char_zero{L1}(buf1 + s1, n) && char_equals{L1,L2}(buf1 + s1, buf2 + s2, n) ==>
  @       char_zero{L2}(buf2 + s2, n);
  @ }
*/

/*@ logic integer uint16_from_char (char *Buffer) =
  @   Buffer[0] +
  @   Buffer[1] * 0x100;
*/

/*@ logic integer uint32_from_char (char *Buffer) =
  @   Buffer[0] +
  @   Buffer[1] * 0x100  +
  @   Buffer[2] * 0x10000 +
  @   Buffer[3] * 0x1000000;
*/

/*@ logic integer uint64_from_char (char *Buffer) =
  @   Buffer[0] +
  @   Buffer[1] * 0x100  +
  @   Buffer[2] * 0x10000 +
  @   Buffer[3] * 0x1000000 +
  @   Buffer[4] * 0x100000000 +
  @   Buffer[5] * 0x10000000000 +
  @   Buffer[6] * 0x1000000000000 +
  @   Buffer[7] * 0x100000000000000;
*/

#endif
