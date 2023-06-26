## @file
# Windows makefile for 'MicroTool' module build.
#
# Copyright (c) 2022, Mikhail Krichanov. All rights reserved.
# SPDX-License-Identifier: BSD-3-Clause
#
!INCLUDE ..\Source\C\Makefiles\ms.common

APP = MicroTool

OC_USER  = ..\..\OpenCorePkg
UDK_PATH = ..\..
UDK_ARCH = $(HOST_ARCH)
OUT_DIR  = .\Windows

OBJECTS = MicroTool.obj

BASE = $(UDK_PATH)\MdePkg\Library\BaseLib
OUT  = $(UDK_PATH)\MdePkg\Library\UefiDebugLibConOut
PRIN = $(UDK_PATH)\MdePkg\Library\BasePrintLib
ERRO = $(UDK_PATH)\MdePkg\Library\BaseDebugPrintErrorLevelLib
BMPN = $(UDK_PATH)\MdeModulePkg\Library\BaseMemoryProfileLibNull
CMEM = $(UDK_PATH)\MdeModulePkg\Library\CommonMemoryAllocationLib
USER = $(OC_USER)\User\Library
OBJECTS = $(OBJECTS) {$(BASE)}SafeString.obj String.obj SwapBytes16.obj SwapBytes32.obj CpuDeadLoop.obj CheckSum.obj
OBJECTS = $(OBJECTS) {$(OUT)}DebugLib.obj {$(PRIN)}PrintLib.obj PrintLibInternal.obj {$(ERRO)}BaseDebugPrintErrorLevelLib.obj
OBJECTS = $(OBJECTS) {$(USER)}UserFile.obj UserBaseMemoryLib.obj UserMath.obj UserPcd.obj UserMisc.obj UserGlobalVar.obj UserBootServices.obj
OBJECTS = $(OBJECTS) {$(BMPN)}BaseMemoryProfileLibNull.obj {$(CMEM)}CommonMemoryAllocationLib.obj {$(CMEM)}CommonMemoryAllocationLibEx.obj

INC = -I . -I $(OC_USER)\User\Include -I $(OC_USER)\Include\Acidanthera
INC = $(INC) -I $(UDK_PATH)\MdePkg\Include -I $(UDK_PATH)\MdePkg\Include\Library -I $(UDK_PATH)\MdePkg\Include\$(UDK_ARCH)
INC = $(INC) -I $(UDK_PATH)\MdePkg\Library\BaseLib -I $(UDK_PATH)\MdeModulePkg\Include -I $(UDK_PATH)\UefiCpuPkg\Include
INC = $(INC) /FI $(OC_USER)\User\Include\UserPcd.h /FI $(UDK_PATH)\MdePkg\Include\Base.h /FI $(OC_USER)\User\Include\UserGlobalVar.h

all:
	-@if not exist $(OUT_DIR) mkdir $(OUT_DIR)
	$(MAKE) $(APP)

$(APP) : $(OBJECTS)
	-@if not exist $(BIN_PATH) mkdir $(BIN_PATH)
	@cd $(OUT_DIR)
	$(LD) /nologo /debug /OPT:REF /OPT:ICF=10 /incremental:no /nodefaultlib:libc.lib /out:..\$@ $(LIBS) $**
	@copy /y ..\$@ $(BIN_PATH)\$@.exe

.PHONY:clean
.PHONY:cleanall

clean:
	del /f /q $(OUT_DIR) $(APP) *.pdb > nul

cleanall:
	del /f /q $(OUT_DIR) *.pdb $(BIN_PATH)\$(APP).exe $(BIN_PATH)\$(APP).exe > nul

.c.obj :
	$(CC) -c $(CFLAGS) $(INC) $< -Fo$@
	@move $@ $(OUT_DIR)\

{$(BASE)}.c.obj :
  $(CC) -c $(CFLAGS) $(INC) /wd 4005 $< -Fo$@
	@move $@ $(OUT_DIR)\

{$(BMPN)}.c.obj :
  $(CC) -c $(CFLAGS) $(INC) $< -Fo$@
	@move $@ $(OUT_DIR)\

{$(CMEM)}.c.obj :
  $(CC) -c $(CFLAGS) $(INC) $< -Fo$@
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
