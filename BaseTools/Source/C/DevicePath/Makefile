## @file
# Windows makefile for 'DevicePath' module build.
#
# Copyright (c) 2017, Intel Corporation. All rights reserved.<BR>
# SPDX-License-Identifier: BSD-2-Clause-Patent
#
!INCLUDE ..\Makefiles\ms.common

APPNAME = DevicePath

LIBS = $(LIB_PATH)\Common.lib

OBJECTS = DevicePath.obj

OBJECTS = $(OBJECTS) \
  $(EDK2_OBJPATH)\MdePkg\Library\UefiDevicePathLib\DevicePathFromText.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\UefiDevicePathLib\DevicePathToText.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\UefiDevicePathLib\DevicePathUtilities.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\UefiDevicePathLib\DevicePathUtilitiesBase.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\UefiDevicePathLib\UefiDevicePathLib.obj

#CFLAGS = $(CFLAGS) /nodefaultlib:libc.lib

!INCLUDE ..\Makefiles\ms.app

