## @file
# Copyright (c) 2021, Marvin Häuser. All rights reserved.
# SPDX-License-Identifier: BSD-3-Clause
##

PROJECT = ImageTool
PRODUCT = $(PROJECT)

OBJS = ImageTool.o Image.o UeEmit.o PeEmit.o PeScan.o BaseOverflow.o PeCoffInit.o PeCoffInfo.o PeCoffLoad.o PeCoffHii.o PeCoffDebug.o UeImageLib.o

VPATH = $(UDK_PATH)/MdePkg/Library/BasePeCoffLib2:$\
				$(UDK_PATH)/MdePkg/Library/BaseUeImageLib

UDK_PATH = ..
OC_USER  = ../../Vendor/Acidanthera/OpenCorePkg

DEBUG    = 1
SANITIZE = 1

include ../../Vendor/Acidanthera/OpenCorePkg/User/Makefile

CFLAGS += -include Pcds.h -Werror
