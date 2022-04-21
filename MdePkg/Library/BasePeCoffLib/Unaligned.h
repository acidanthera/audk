/** @file
  Provides APIs for unaligned memory accesses.

  Copyright (c) 2006 - 2019, Intel Corporation. All rights reserved.<BR>
  Portions copyright (c) 2008 - 2009, Apple Inc. All rights reserved.<BR>
  Copyright (c) Microsoft Corporation.<BR>
  Portions Copyright (c) 2020, Hewlett Packard Enterprise Development LP. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-2-Clause-Patent
**/

#ifndef UNALIGNED_H
#define UNALIGNED_H

/*@ requires \typeof(Ptr) <: \type(char *);
  @ requires \valid(((char *) Ptr) + (0 .. 1));
  @ assigns \nothing;
  @ ensures \result == uint16_from_char ((char *) Ptr);
*/
UINT16
EFIAPI
ReadUnaligned16 (
  IN CONST VOID  *Ptr
  );

/*@ requires \typeof(Ptr) <: \type(char *);
  @ requires \valid(((char *) Ptr) + (0 .. 1));
  @ assigns ((char *) Ptr)[0 .. 1];
  @ ensures uint16_from_char ((char *) Ptr) == Val;
*/
#ifdef PRODUCTION
UINT16
#else
VOID
#endif
EFIAPI
WriteUnaligned16 (
  OUT VOID    *Ptr,
  IN  UINT16  Val
  );

/*@ requires \typeof(Ptr) <: \type(char *);
  @ requires \valid(((char *) Ptr) + (0 .. 3));
  @ assigns \nothing;
  @ ensures \result == uint32_from_char ((char *) Ptr);
*/
UINT32
EFIAPI
ReadUnaligned32 (
  IN CONST VOID  *Ptr
  );

/*@ requires \typeof(Ptr) <: \type(char *);
  @ requires \valid(((char *) Ptr) + (0 .. 3));
  @ assigns ((char *) Ptr)[0 .. 3];
  @ ensures uint32_from_char ((char *) Ptr) == Val;
*/
#ifdef PRODUCTION
UINT32
#else
VOID
#endif
EFIAPI
WriteUnaligned32 (
  OUT VOID    *Ptr,
  IN  UINT32  Val
  );

/*@ requires \typeof(Ptr) <: \type(char *);
  @ requires \valid(((char *) Ptr) + (0 .. 7));
  @ assigns \nothing;
  @ ensures \result == uint64_from_char ((char *) Ptr);
*/
UINT64
EFIAPI
ReadUnaligned64 (
  IN CONST VOID  *Ptr
  );

/*@ requires \typeof(Ptr) <: \type(char *);
  @ requires \valid(((char *) Ptr) + (0 .. 7));
  @ assigns ((char *) Ptr)[0 .. 7];
  @ ensures uint64_from_char ((char *) Ptr) == Val;
*/
#ifdef PRODUCTION
UINT64
#else
VOID
#endif
EFIAPI
WriteUnaligned64 (
  OUT VOID    *Ptr,
  IN  UINT64  Val
  );

#endif // UNALIGNED_H
