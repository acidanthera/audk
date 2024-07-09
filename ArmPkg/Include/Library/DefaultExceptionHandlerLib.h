/** @file

  Copyright (c) 2008 - 2010, Apple Inc. All rights reserved.<BR>

  SPDX-License-Identifier: BSD-2-Clause-Patent

**/

#ifndef DEFAULT_EXCEPTION_HANDLER_LIB_H_
#define DEFAULT_EXCEPTION_HANDLER_LIB_H_

typedef
EFI_STATUS
(EFIAPI *EFI_SYS_CALL_BOOT_SERVICE)(
  IN  UINT8  Type,
  IN  VOID   *CoreRbp,
  IN  VOID   *UserRsp
  );

/**
  This is the default action to take on an unexpected exception

  @param  ExceptionType    Type of the exception
  @param  SystemContext    Register state at the time of the Exception

**/
EFI_STATUS
EFIAPI
DefaultExceptionHandler (
  IN     EFI_EXCEPTION_TYPE  ExceptionType,
  IN OUT EFI_SYSTEM_CONTEXT  SystemContext
  );

VOID
EFIAPI
InitializeSysCallHandler (
  IN EFI_SYS_CALL_BOOT_SERVICE  Handler
  );

#endif // DEFAULT_EXCEPTION_HANDLER_LIB_H_
