::
::  Copyright (c) 2022, Mikhail Krichanov. All rights reserved.
::  SPDX-License-Identifier: BSD-3-Clause
::
@echo off
set args=%2
:start
shift /2
if "%2"=="" goto done
set args=%args% %2
goto start

:done
if "%1%"=="IA32" (
  call ImageTool32.exe %args%
) else (
  if "%1%"=="X64" (
    call ImageTool64.exe %args%
  ) else (
    echo Unable to find the command to run!
  )
)
