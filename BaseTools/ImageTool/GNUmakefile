## @file
# Copyright (c) 2021, Marvin Häuser. All rights reserved.
# Copyright (c) 2022, Mikhail Krichanov. All rights reserved.
# SPDX-License-Identifier: BSD-3-Clause
##

PROJECT = ImageTool
OBJS    = $(PROJECT).o
OBJS    += Image.o PeEmit.o PeScan.o ElfScan.o BinEmit.o
OBJS    += UefiImageExtraActionLib.o
OBJS    += PeCoffInit.o PeCoffInfo.o PeCoffLoad.o PeCoffRelocate.o PeCoffHii.o PeCoffDebug.o

DEBUG    = 1
SANITIZE = 0
OC_USER  = ../../OpenCorePkg
UDK_PATH = ../..

include $(OC_USER)/User/Makefile

.DEFAULT_GOAL := Tools

CFLAGS += -include Pcds.h -Werror

VPATH  += ../../MdePkg/Library/BasePeCoffLib2:$\
					../../MdePkg/Library/BaseUefiImageExtraActionLibNull

Tools: Tool32 Tool64

Tool32:
	$(MAKE) all CFLAGS="$(CFLAGS) -DEFI_TARGET32" PRODUCT=ImageTool32 INFIX=_Tool32

Tool64:
	$(MAKE) all CFLAGS="$(CFLAGS) -DEFI_TARGET64" PRODUCT=ImageTool64 INFIX=_Tool64
