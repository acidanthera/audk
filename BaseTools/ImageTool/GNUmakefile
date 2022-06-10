## @file
# Copyright (c) 2021, Marvin Häuser. All rights reserved.
# SPDX-License-Identifier: BSD-3-Clause
##

PROJECT = ImageTool
PRODUCT = $(PROJECT)
OBJS    = $(PROJECT).o
OBJS    += Image.o PeEmit.o PeScan.o UeEmit.o ElfToPe.o
OBJS    += BaseOverflow.o PeCoffInit.o PeCoffInfo.o PeCoffLoad.o PeCoffHii.o PeCoffDebug.o UeImageLib.o

DEBUG    = 1
SANITIZE = 1
OC_USER  = ../../OpenCorePkg

include $(OC_USER)/User/Makefile

CFLAGS += -include Pcds.h -Werror -D EFI_TARGET64

VPATH  += ../../MdePkg/Library/BasePeCoffLib2:$\
				  ../../MdePkg/Library/BaseUeImageLib
