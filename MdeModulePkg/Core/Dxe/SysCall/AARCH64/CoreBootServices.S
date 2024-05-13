//------------------------------------------------------------------------------
//
// Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
// SPDX-License-Identifier: BSD-3-Clause
//
//------------------------------------------------------------------------------

#include <AsmMacroIoLibV8.h>

//------------------------------------------------------------------------------
// VOID
// EFIAPI
// DisableSMAP (
//   VOID
//   );
//------------------------------------------------------------------------------
ASM_FUNC(DisableSMAP)
    ret

//------------------------------------------------------------------------------
// VOID
// EFIAPI
// EnableSMAP (
//   VOID
//   );
//------------------------------------------------------------------------------
ASM_FUNC(EnableSMAP)
    ret

//------------------------------------------------------------------------------
// EFI_STATUS
// EFIAPI
// CallInstallMultipleProtocolInterfaces (
//   IN EFI_HANDLE  *Handle,
//   IN VOID        **ArgList,
//   IN UINT32      ArgListSize,
//   IN VOID        *Function
//   );
//------------------------------------------------------------------------------
ASM_FUNC(CallInstallMultipleProtocolInterfaces)
    ret

//------------------------------------------------------------------------------
// EFI_STATUS
// EFIAPI
// CoreBootServices (
//   IN  UINT8  Type,
//   ...
//   );
//
//   (rcx) RIP of the next instruction saved by SYSCALL in SysCall().
//   (rdx) Argument 1 of the called function.
//   (r8)  Argument 2 of the called function.
//   (r9)  Argument 3 of the called function.
//   (r10) Type.
//   (r11) RFLAGS saved by SYSCALL in SysCall().
//
//   (On User Stack) Argument 4, 5, ...
//------------------------------------------------------------------------------
ASM_FUNC(CoreBootServices)
    ret

//------------------------------------------------------------------------------
// EFI_STATUS
// EFIAPI
// CallRing3 (
//   IN RING3_CALL_DATA *Data
//   );
//
//   (rcx) Data
//------------------------------------------------------------------------------
ASM_FUNC(CallRing3)
    ret
