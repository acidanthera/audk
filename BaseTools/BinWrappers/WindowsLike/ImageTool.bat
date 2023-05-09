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
  exit
  )
if "%1%"=="ARM" (
  call ImageTool32.exe %args%
  exit
  )
if "%1%"=="X64" (
  call ImageTool64.exe %args%
  exit
)
if "%1%"=="AARCH64" (
  call ImageTool64.exe %args%
  exit
)
echo ImageTool for %1% is not supported
