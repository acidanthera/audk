## @file
# Copyright (c) 2021, Marvin Häuser. All rights reserved.
# Copyright (c) 2022, Mikhail Krichanov. All rights reserved.
# SPDX-License-Identifier: BSD-3-Clause
##

PROJECT = ImageTool
PRODUCT = $(PROJECT)$(INFIX)$(SUFFIX)
OBJS    = $(PROJECT).o
OBJS    += Image.o UefiImageScan.o UeEmit.o UeScan.o PeEmit32.o PeEmit64.o PeEmitCommon.o PeScan.o ElfScan32.o ElfScan64.o ElfScanCommon.o BinEmit.o ImageToolEmit.o
OBJS    += UeImageLib.o UefiImageExtraActionLib.o
OBJS    += PeCoffInit.o PeCoffInfo.o PeCoffLoad.o PeCoffRelocate.o PeCoffHii.o PeCoffDebug.o PeCoffHash.o
OBJS    += PeSupport.o UeSupport.o UefiImageLib.o CommonSupport.o DynamicBuffer.o

WERROR   = 1
DEBUG    = 1
SANITIZE = 0
OC_USER  = ../../OpenCorePkg
UDK_PATH = ../..

VPATH  += ../../MdePkg/Library/BasePeCoffLib2:$\
					../../MdePkg/Library/BaseUefiImageExtraActionLibNull:$\
					../../MdePkg/Library/BaseUefiImageLib:$\
					../../MdePkg/Library/BaseUeImageLib

include $(OC_USER)/User/Makefile

CFLAGS += -DUEFI_IMAGE_FORMAT_SUPPORT_SOURCES=0x02
