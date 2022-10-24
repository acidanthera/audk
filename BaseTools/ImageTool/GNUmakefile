## @file
# Copyright (c) 2021, Marvin Häuser. All rights reserved.
# SPDX-License-Identifier: BSD-3-Clause
##

PROJECT = ImageTool
PRODUCT = $(PROJECT)
OBJS    = $(PROJECT).o
OBJS    += Image.o PeEmit.o PeScan.o UeEmit.o ElfScan.o
OBJS    += BaseOverflow.o PeCoffInit.o PeCoffInfo.o PeCoffLoad.o PeCoffHii.o PeCoffDebug.o UeImageLib.o

DEBUG    = 1
SANITIZE = 1
OC_USER  = ../../OpenCorePkg

include $(OC_USER)/User/Makefile

.DEFAULT_GOAL := Tools

CFLAGS += -include Pcds.h -Werror -DEFI_TARGET64

VPATH  += ../../MdePkg/Library/BasePeCoffLib2:$\
				  ../../MdePkg/Library/BaseUeImageLib

Tools: Tool32 clean Tool64

Tool32: CFLAGS := $(filter-out -DEFI_TARGET64,$(CFLAGS)) -DEFI_TARGET32
Tool32: all
	cp $(PRODUCT) ImageTool32

Tool64:
	$(MAKE) all
	cp $(PRODUCT) ImageTool64
