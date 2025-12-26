## @file
# GNU/Linux makefile for 'Common' module build.
#
# Copyright (c) 2007 - 2018, Intel Corporation. All rights reserved.<BR>
# SPDX-License-Identifier: BSD-2-Clause-Patent
#
MAKEROOT ?= ..

# VPATH = ..

LIBNAME = Common

OBJECTS = \
  BasePeCoff.o \
  BinderFuncs.o \
  CommonLib.o \
  Crc32.o \
  Decompress.o \
  EfiCompress.o \
  EfiUtilityMsgs.o \
  FirmwareVolumeBuffer.o \
  FvLib.o \
  MemoryFile.o \
  MyAlloc.o \
  OsPath.o \
  ParseGuidedSectionTools.o \
  ParseInf.o \
  PeCoffLoaderEx.o \
  SimpleFileParsing.o \
  StringFuncs.o \
  TianoCompress.o

OBJECTS += AutoGen.o DebugLib.o

OBJECTS += \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseDebugPrintErrorLevelLib/BaseDebugPrintErrorLevelLib.o

OBJECTS += \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseLib/ARShiftU64.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseLib/BitField.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseLib/CheckSum.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseLib/DivS64x64Remainder.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseLib/DivU64x32.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseLib/DivU64x32Remainder.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseLib/DivU64x64Remainder.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseLib/FilePaths.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseLib/GetPowerOfTwo32.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseLib/GetPowerOfTwo64.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseLib/HighBitSet32.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseLib/HighBitSet64.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseLib/LinkedList.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseLib/LowBitSet32.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseLib/LRotU32.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseLib/LRotU64.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseLib/LShiftU64.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseLib/Math64.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseLib/ModU64x32.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseLib/MultS64x64.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseLib/MultU64x32.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseLib/MultU64x64.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseLib/QuickSort.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseLib/RRotU32.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseLib/RRotU64.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseLib/RShiftU64.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseLib/SafeString.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseLib/SafeString.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseLib/String.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseLib/SwapBytes16.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseLib/SwapBytes32.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseLib/SwapBytes64.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseLib/Unaligned.o

OBJECTS += \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseMemoryLib/CompareMemWrapper.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseMemoryLib/CopyMem.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseMemoryLib/CopyMemWrapper.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseMemoryLib/IsZeroBufferWrapper.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseMemoryLib/MemLibGeneric.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseMemoryLib/MemLibGuid.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseMemoryLib/ScanMem8Wrapper.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseMemoryLib/ScanMem16Wrapper.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseMemoryLib/ScanMem32Wrapper.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseMemoryLib/ScanMem64Wrapper.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseMemoryLib/SetMem.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseMemoryLib/SetMem16Wrapper.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseMemoryLib/SetMem32Wrapper.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseMemoryLib/SetMem64Wrapper.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseMemoryLib/SetMemWrapper.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BaseMemoryLib/ZeroMemWrapper.o

OBJECTS += \
  $(EDK2_OBJPATH)/MdePkg/Library/BasePrintLib/PrintLib.o \
  $(EDK2_OBJPATH)/MdePkg/Library/BasePrintLib/PrintLibInternal.o

OBJECTS += \
  $(EDK2_OBJPATH)/MdeModulePkg/Library/BaseMemoryProfileLibNull/BaseMemoryProfileLibNull.o

OBJECTS += \
  $(EDK2_OBJPATH)/MdeModulePkg/Library/CommonMemoryAllocationLib/CommonMemoryAllocationLib.o \
  $(EDK2_OBJPATH)/MdeModulePkg/Library/CommonMemoryAllocationLib/CommonMemoryAllocationLibEx.o

include $(MAKEROOT)/Makefiles/lib.makefile
