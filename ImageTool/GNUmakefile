PROJECT = ImageTool
PRODUCT = $(PROJECT)

OBJS = ImageTool.o EmitUe.o ScanPe.o BaseOverflow.o PeCoffInit.o PeCoffInfo.o PeCoffHii.o PeCoffDebug.o UeImageLib.o

VPATH = $(UDK_PATH)/MdePkg/Library/BasePeCoffLib2:$\
				$(UDK_PATH)/MdePkg/Library/BaseUeImageLib

## @file
# Copyright (c) 2020, PMheart. All rights reserved.
# SPDX-License-Identifier: BSD-3-Clause
##

.DEFAULT_GOAL := all

LCOV          ?= lcov
GENHTML       ?= genhtml
CC            ?= gcc
MKDIR         := mkdir -p

UDK_PATH = ..
OC_USER  = ../../Vendor/Acidanthera/OpenCorePkg

DEBUG    = 1
SANITIZE = 1

include ../../Vendor/Acidanthera/OpenCorePkg/User/Makefile

CFLAGS += -include Pcds.h
