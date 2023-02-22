## @file
# Windows makefile for 'ImageTool' module build.
#
# Copyright (c) 2022, Mikhail Krichanov. All rights reserved.
# SPDX-License-Identifier: BSD-3-Clause
#
!INCLUDE ..\Source\C\Makefiles\ms.common

APP = ImageTool

OC_USER  = ..\..\OpenCorePkg
UDK_PATH = ..\..
UDK_ARCH = $(HOST_ARCH)
OUT_DIR  = .\Windows_$(INFIX)

OV = $(UDK_PATH)\MdePkg\Library\BaseOverflowLib
PE = $(UDK_PATH)\MdePkg\Library\BasePeCoffLib2
UE = $(UDK_PATH)\MdePkg\Library\BaseUeImageLib
UA = $(UDK_PATH)\MdePkg\Library\BaseUefiImageExtraActionLibNull

OBJECTS = ImageTool.obj Image.obj PeEmit.obj PeScan.obj UeEmit.obj ElfScan.obj BinEmit.obj
OBJECTS = $(OBJECTS) {$(OV)}BaseAlignment.obj BaseBitOverflow.obj {$(UE)}UeImageLib.obj {$(UA)}UefiImageExtraActionLib.obj
OBJECTS = $(OBJECTS) {$(PE)}PeCoffInit.obj PeCoffInfo.obj PeCoffRelocate.obj PeCoffLoad.obj PeCoffHii.obj PeCoffDebug.obj

BASE = $(UDK_PATH)\MdePkg\Library\BaseLib
OUT  = $(UDK_PATH)\MdePkg\Library\UefiDebugLibConOut
PRIN = $(UDK_PATH)\MdePkg\Library\BasePrintLib
ERRO = $(UDK_PATH)\MdePkg\Library\BaseDebugPrintErrorLevelLib
USER = $(OC_USER)\User\Library
OBJECTS = $(OBJECTS) {$(BASE)}SafeString.obj String.obj SwapBytes16.obj SwapBytes32.obj CpuDeadLoop.obj CheckSum.obj
OBJECTS = $(OBJECTS) {$(OUT)}DebugLib.obj {$(PRIN)}PrintLib.obj PrintLibInternal.obj {$(ERRO)}BaseDebugPrintErrorLevelLib.obj
OBJECTS = $(OBJECTS) {$(USER)}UserFile.obj UserBaseMemoryLib.obj UserMath.obj UserPcd.obj UserMisc.obj UserGlobalVar.obj UserBootServices.obj

INC = -I . -I $(OC_USER)\User\Include -I $(OC_USER)\Include\Acidanthera
INC = $(INC) -I $(UDK_PATH)\MdePkg\Include -I $(UDK_PATH)\MdePkg\Include\Library -I $(UDK_PATH)\MdePkg\Include\$(UDK_ARCH)
INC = $(INC) -I $(UDK_PATH)\MdePkg\Library\BaseLib -I $(UDK_PATH)\MdeModulePkg\Include -I $(UDK_PATH)\UefiCpuPkg\Include
INC = $(INC) /FI $(OC_USER)\User\Include\UserPcd.h /FI $(UDK_PATH)\MdePkg\Include\Base.h /FI $(OC_USER)\User\Include\UserGlobalVar.h

all:
	-if not exist $(OUT_DIR)64 mkdir $(OUT_DIR)64
	$(MAKE) $(APP)64 CFLAGS="$(CFLAGS) /D EFI_TARGET64" INFIX=64
	-if not exist $(OUT_DIR)32 mkdir $(OUT_DIR)32
	$(MAKE) $(APP)32 CFLAGS="$(CFLAGS) /D EFI_TARGET32" INFIX=32

$(APP)$(INFIX) : $(OBJECTS)
	-@if not exist $(BIN_PATH) mkdir $(BIN_PATH)
	@cd $(OUT_DIR)
	$(LD) /nologo /debug /OPT:REF /OPT:ICF=10 /incremental:no /nodefaultlib:libc.lib /out:..\$@ $(LIBS) $**
	@copy /y ..\$@ $(BIN_PATH)\$@.exe

.PHONY:clean
.PHONY:cleanall

clean:
	del /f /q $(OUT_DIR)32 $(OUT_DIR)64 $(APP)32 $(APP)64 *.pdb > nul

cleanall:
	del /f /q $(OUT_DIR)32 $(OUT_DIR)64 *.pdb $(BIN_PATH)\$(APP)64.exe $(BIN_PATH)\$(APP)32.exe > nul

.c.obj :
	$(CC) -c $(CFLAGS) $(INC) $< -Fo$@
	@move $@ $(OUT_DIR)\

{$(OV)}.c.obj :
  $(CC) -c $(CFLAGS) $(INC) $< -Fo$@
	@move $@ $(OUT_DIR)\

{$(PE)}.c.obj :
  $(CC) -c $(CFLAGS) $(INC) /FI Pcds.h $< -Fo$@
	@move $@ $(OUT_DIR)\

{$(UE)}.c.obj :
  $(CC) -c $(CFLAGS) $(INC) /FI Pcds.h $< -Fo$@
	@move $@ $(OUT_DIR)\

{$(UA)}.c.obj :
  $(CC) -c $(CFLAGS) $(INC) $< -Fo$@
	@move $@ $(OUT_DIR)\

{$(BASE)}.c.obj :
  $(CC) -c $(CFLAGS) $(INC) /wd 4005 $< -Fo$@
	@move $@ $(OUT_DIR)\

{$(OUT)}.c.obj :
  $(CC) -c $(CFLAGS) $(INC) $< -Fo$@
	@move $@ $(OUT_DIR)\

{$(PRIN)}.c.obj :
  $(CC) -c $(CFLAGS) $(INC) /wd 4005 $< -Fo$@
	@move $@ $(OUT_DIR)\

{$(ERRO)}.c.obj :
  $(CC) -c $(CFLAGS) $(INC) $< -Fo$@
	@move $@ $(OUT_DIR)\

{$(USER)}.c.obj :
  $(CC) -c $(CFLAGS) $(INC) /D WIN32 /wd 4754 $< -Fo$@
	@move $@ $(OUT_DIR)\
