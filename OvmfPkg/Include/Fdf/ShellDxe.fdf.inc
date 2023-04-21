##
#    SPDX-License-Identifier: BSD-2-Clause-Patent
##

!if $(BUILD_SHELL) == TRUE && $(SECURE_BOOT_ENABLE) == FALSE

!if $(NETWORK_ENABLE) == TRUE
INF  ShellPkg/DynamicCommand/TftpDynamicCommand/TftpDynamicCommand.inf
INF  ShellPkg/DynamicCommand/HttpDynamicCommand/HttpDynamicCommand.inf
!endif
INF  ShellPkg/DynamicCommand/VariablePolicyDynamicCommand/VariablePolicyDynamicCommand.inf
INF  OvmfPkg/LinuxInitrdDynamicShellCommand/LinuxInitrdDynamicShellCommand.inf

INF  ShellPkg/Application/Shell/Shell.inf
!endif
