//------------------------------------------------------------------------------
// Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
// SPDX-License-Identifier: BSD-3-Clause
//------------------------------------------------------------------------------

#include <AsmMacroIoLibV8.h>

//------------------------------------------------------------------------------
// EFI_STATUS
// EFIAPI
// SysCall (
//   IN  UINT8  Type,
//   ...
//   );
//------------------------------------------------------------------------------
ASM_FUNC(SysCall)

  ret

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

  ret
