//------------------------------------------------------------------------------
// Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
// SPDX-License-Identifier: BSD-3-Clause
//------------------------------------------------------------------------------

#include <AsmMacroIoLib.h>

//------------------------------------------------------------------------------
// EFI_STATUS
// EFIAPI
// SysCall (
//   IN  UINT8  Type,
//   ...
//   );
//------------------------------------------------------------------------------
ASM_FUNC(SysCall)

  bx    LR

//------------------------------------------------------------------------------
// VOID
// EFIAPI
// Ring3EntryPoint (
//   IN RING3_CALL_DATA *Data
//   );
//
//   (rcx) RIP of Ring3EntryPoint saved for SYSRET in CallRing3().
//   (rdx) Data
//------------------------------------------------------------------------------
ASM_FUNC(Ring3EntryPoint)

  bx    LR
