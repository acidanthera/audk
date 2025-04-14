//------------------------------------------------------------------------------
// Copyright (c) 2024 - 2025, Mikhail Krichanov. All rights reserved.
// SPDX-License-Identifier: BSD-3-Clause
//------------------------------------------------------------------------------

#include <AsmMacroLib.h>

.extern ASM_PFX(UserSpaceCall)

//------------------------------------------------------------------------------
// EFI_STATUS
// EFIAPI
// SysCall (
//   IN UINT8  Type,
//   IN UINT8  NumberOfArguments,
//   ...
//   );
//------------------------------------------------------------------------------
ASM_FUNC(SysCall)
  svc #0
  bx  LR

//------------------------------------------------------------------------------
// VOID
// EFIAPI
// UserSpaceEntryPoint (
//   IN USER_SPACE_CALL_DATA  *Data
//   );
//
//   (r0) Data
//------------------------------------------------------------------------------
ASM_FUNC(UserSpaceEntryPoint)
  b ASM_PFX(UserSpaceCall)
