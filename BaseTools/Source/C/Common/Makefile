## @file
# Windows makefile for 'Common' module build.
#
# Copyright (c) 2007 - 2010, Intel Corporation. All rights reserved.<BR>
# SPDX-License-Identifier: BSD-2-Clause-Patent
#
!INCLUDE ..\Makefiles\ms.common

# VPATH = ..

LIBNAME = Common

OBJECTS = \
  BinderFuncs.obj \
  CommonLib.obj \
  Crc32.obj \
  Decompress.obj \
  EfiCompress.obj \
  EfiUtilityMsgs.obj \
  FirmwareVolumeBuffer.obj \
  FvLib.obj \
  MemoryFile.obj \
  MyAlloc.obj \
  OsPath.obj \
  ParseGuidedSectionTools.obj \
  ParseInf.obj \
  SimpleFileParsing.obj \
  StringFuncs.obj \
  TianoCompress.obj

OBJECTS = $(OBJECTS) AutoGen.obj DebugLib.obj

OBJECTS = $(OBJECTS) \
  $(EDK2_OBJPATH)\BaseTools\ImageTool\ImageToolEmit.obj \
  $(EDK2_OBJPATH)\BaseTools\ImageTool\Image.obj \
  $(EDK2_OBJPATH)\BaseTools\ImageTool\ElfScan32.obj \
  $(EDK2_OBJPATH)\BaseTools\ImageTool\ElfScan64.obj \
  $(EDK2_OBJPATH)\BaseTools\ImageTool\ElfScanCommon.obj \
  $(EDK2_OBJPATH)\BaseTools\ImageTool\UefiImageScan.obj \
  $(EDK2_OBJPATH)\BaseTools\ImageTool\PeScan.obj \
  $(EDK2_OBJPATH)\BaseTools\ImageTool\PeEmit32.obj \
  $(EDK2_OBJPATH)\BaseTools\ImageTool\PeEmit64.obj \
  $(EDK2_OBJPATH)\BaseTools\ImageTool\PeEmitCommon.obj \
  $(EDK2_OBJPATH)\BaseTools\ImageTool\BinEmit.obj \
  $(EDK2_OBJPATH)\BaseTools\ImageTool\DynamicBuffer.obj \
  $(EDK2_OBJPATH)\OpenCorePkg\User\Library\UserFile.obj

OBJECTS = $(OBJECTS) \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseDebugPrintErrorLevelLib\BaseDebugPrintErrorLevelLib.obj

OBJECTS = $(OBJECTS) \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseLib\ARShiftU64.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseLib\BitField.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseLib\CheckSum.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseLib\DivS64x64Remainder.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseLib\DivU64x32.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseLib\DivU64x32Remainder.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseLib\DivU64x64Remainder.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseLib\FilePaths.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseLib\GetPowerOfTwo32.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseLib\GetPowerOfTwo64.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseLib\HighBitSet32.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseLib\HighBitSet64.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseLib\LinkedList.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseLib\LowBitSet32.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseLib\LRotU32.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseLib\LRotU64.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseLib\LShiftU64.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseLib\Math64.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseLib\ModU64x32.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseLib\MultS64x64.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseLib\MultU64x32.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseLib\MultU64x64.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseLib\QuickSort.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseLib\RRotU32.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseLib\RRotU64.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseLib\RShiftU64.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseLib\SafeString.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseLib\String.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseLib\SwapBytes16.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseLib\SwapBytes32.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseLib\SwapBytes64.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseLib\Unaligned.obj

OBJECTS = $(OBJECTS) \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseMemoryLib\CompareMemWrapper.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseMemoryLib\CopyMem.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseMemoryLib\CopyMemWrapper.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseMemoryLib\IsZeroBufferWrapper.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseMemoryLib\MemLibGeneric.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseMemoryLib\MemLibGuid.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseMemoryLib\ScanMem8Wrapper.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseMemoryLib\ScanMem16Wrapper.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseMemoryLib\ScanMem32Wrapper.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseMemoryLib\ScanMem64Wrapper.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseMemoryLib\SetMem.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseMemoryLib\SetMem16Wrapper.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseMemoryLib\SetMem32Wrapper.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseMemoryLib\SetMem64Wrapper.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseMemoryLib\SetMemWrapper.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseMemoryLib\ZeroMemWrapper.obj

OBJECTS = $(OBJECTS) \
  $(EDK2_OBJPATH)\MdePkg\Library\BasePrintLib\PrintLib.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BasePrintLib\PrintLibInternal.obj

OBJECTS = $(OBJECTS) \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseOverflowLib\BaseAlignment.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseOverflowLib\BaseBitOverflow.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseOverflowLib\BaseMath.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseOverflowLib\BaseNativeOverflow.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseOverflowLib\BaseTripleOverflow.obj

OBJECTS = $(OBJECTS) \
  $(EDK2_OBJPATH)\MdePkg\Library\BasePeCoffLib2\PeCoffDebug.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BasePeCoffLib2\PeCoffHash.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BasePeCoffLib2\PeCoffHii.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BasePeCoffLib2\PeCoffInfo.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BasePeCoffLib2\PeCoffInit.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BasePeCoffLib2\PeCoffLoad.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BasePeCoffLib2\PeCoffRelocate.obj

OBJECTS = $(OBJECTS) \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseUefiImageLib\CommonSupport.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseUefiImageLib\PeSupport.obj \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseUefiImageLib\UefiImageLib.obj

OBJECTS = $(OBJECTS) \
  $(EDK2_OBJPATH)\MdePkg\Library\BaseUefiImageExtraActionLibNull\UefiImageExtraActionLib.obj

OBJECTS = $(OBJECTS) \
  $(EDK2_OBJPATH)\MdeModulePkg\Library\BaseMemoryProfileLibNull\BaseMemoryProfileLibNull.obj

OBJECTS = $(OBJECTS) \
  $(EDK2_OBJPATH)\MdeModulePkg\Library\CommonMemoryAllocationLib\CommonMemoryAllocationLib.obj \
  $(EDK2_OBJPATH)\MdeModulePkg\Library\CommonMemoryAllocationLib\CommonMemoryAllocationLibEx.obj

!INCLUDE ..\Makefiles\ms.lib



