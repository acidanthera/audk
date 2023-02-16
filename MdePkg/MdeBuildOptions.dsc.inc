## @file
# Mde DSC include file for [BuildOptions*] section of all Architectures.
#
# This file can be included to a platform DSC file by using
# "!include MdePkg/MdeBuildOptions.dsc.inc" to specify common build options.
#
# Copyright (c) 2021, Marvin Häuser. All rights reserved.<BR>
# Copyright (c) 2023, Mikhail Krichanov. All rights reserved.<BR>
#
#    SPDX-License-Identifier: BSD-2-Clause-Patent
#
##

#
# MDEPKG_REDUCE_FW_SIZE:
#   Align boot-time images at a 1024 bytes boundary to reduce firmware size.
#

!if $(MDEPKG_REDUCE_FW_SIZE) == TRUE
  [BuildOptions]
    MSFT:*_*_*_DLINK_FLAGS     = /ALIGN:1024
    INTEL:*_*_*_DLINK_FLAGS    = /ALIGN:1024
    CLANGPDB:*_*_*_DLINK_FLAGS = /ALIGN:1024 /FILEALIGN:1024
    GCC:*_*_*_DLINK_FLAGS      = -z max-page-size=0x400
    CLANGGCC:*_*_*_DLINK_FLAGS = -z max-page-size=0x400
    XCODE:*_*_*_DLINK_FLAGS    = -seg1addr 0x400 -segalign 0x400
    XCODE:*_*_*_MTOC_FLAGS     = -align 0x400
!endif

!if $(MDEPKG_MERGE_RODATA_INTO_TEXT) == TRUE
  [BuildOptions]
    MSFT:*_*_*_DLINK_FLAGS        = /MERGE:.rdata=.text
    CLANGPDB:*_*_*_DLINK_FLAGS    = /MERGE:.rdata=.text
    GCC:*_*_*_DLINK2_FLAGS        = -Wl,--script=$(EDK_TOOLS_PATH)/Scripts/Merge.lds
    GCC:*_*_*_ASLDLINK_FLAGS      = -Wl,--script=$(EDK_TOOLS_PATH)/Scripts/Merge.lds
    CLANGGCC:*_*_*_DLINK2_FLAGS   = -Wl,--script=$(EDK_TOOLS_PATH)/Scripts/Merge.lds
    CLANGGCC:*_*_*_ASLDLINK_FLAGS = -Wl,--script=$(EDK_TOOLS_PATH)/Scripts/Merge.lds
    XCODE:*_*_*_DLINK_FLAGS       = -rename_section __DATA_CONST __text_const __TEXT __const -rename_section __DATA_CONST __cstring __TEXT __cstring -rename_section __DATA_CONST __ustring __TEXT __ustring -rename_section __DATA_CONST __const __TEXT __data_const
!else
    CLANGGCC:*_*_*_DLINK2_FLAGS   = -Wl,--script=$(EDK_TOOLS_PATH)/Scripts/Base.lds
    CLANGGCC:*_*_*_ASLDLINK_FLAGS = -Wl,--script=$(EDK_TOOLS_PATH)/Scripts/Base.lds
!endif
