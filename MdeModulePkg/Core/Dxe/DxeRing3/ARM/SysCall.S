//------------------------------------------------------------------------------
// Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
// SPDX-License-Identifier: BSD-3-Clause
//------------------------------------------------------------------------------

#include <AsmMacroIoLib.h>

.extern ASM_PFX(Ring3Call)

//------------------------------------------------------------------------------
// EFI_STATUS
// EFIAPI
// SysCall (
//   IN  UINT8  Type,
//   ...
//   );
//------------------------------------------------------------------------------
ASM_FUNC(SysCall)
  svc #0
  bx  LR

//------------------------------------------------------------------------------
// VOID
// EFIAPI
// Ring3EntryPoint (
//   IN RING3_CALL_DATA *Data
//   );
//
//   (r0) Data
//------------------------------------------------------------------------------
ASM_FUNC(Ring3EntryPoint)
  b ASM_PFX(Ring3Call)
