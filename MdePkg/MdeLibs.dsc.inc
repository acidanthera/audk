## @file
# Mde DSC include file for [LibraryClasses*] section of all Architectures.
#
# This file can be included to the [LibraryClasses*] section(s) of a platform DSC file
# by using "!include MdePkg/MdeLibs.dsc.inc" to specify the library instances
# of some EDKII basic/common library classes.
#
# Copyright (c) 2021 - 2024, Intel Corporation. All rights reserved.<BR>
#
#    SPDX-License-Identifier: BSD-2-Clause-Patent
#
##

[Defines]
!ifndef CUSTOM_STACK_CHECK_LIB
  # The DSC parser will set any unset macros to 0. Then, below when we check for STATIC or DYNAMIC, even if we couch
  # that in a !ifdef CUSTOM_STACK_CHECK_LIB, the parser will issue a warning that we are comparing a boolean (0) against
  # a string, which will always fail. So we set it to a dummy value here.
  DEFINE CUSTOM_STACK_CHECK_LIB = NONE
!endif

[LibraryClasses]
  OrderedCollectionLib|MdePkg/Library/BaseOrderedCollectionRedBlackTreeLib/BaseOrderedCollectionRedBlackTreeLib.inf
  ArmTrngLib|MdePkg/Library/BaseArmTrngLibNull/BaseArmTrngLibNull.inf
  RegisterFilterLib|MdePkg/Library/RegisterFilterLibNull/RegisterFilterLibNull.inf
  CpuLib|MdePkg/Library/BaseCpuLib/BaseCpuLib.inf
  SmmCpuRendezvousLib|MdePkg/Library/SmmCpuRendezvousLibNull/SmmCpuRendezvousLibNull.inf
  SafeIntLib|MdePkg/Library/BaseSafeIntLib/BaseSafeIntLib.inf
  SynchronizationLib|MdePkg/Library/BaseSynchronizationLib/BaseSynchronizationLib.inf
  MmUnblockMemoryLib|MdePkg/Library/MmUnblockMemoryLib/MmUnblockMemoryLibNull.inf
  BaseOverflowLib|MdePkg/Library/BaseOverflowLib/BaseOverflowLib.inf

  MemoryProfileLib|MdeModulePkg/Library/BaseMemoryProfileLibNull/BaseMemoryProfileLibNull.inf
  CommonMemoryAllocationLib|MdeModulePkg/Library/CommonMemoryAllocationLib/CommonMemoryAllocationLib.inf
  StackCheckFailureHookLib|MdePkg/Library/StackCheckFailureHookLibNull/StackCheckFailureHookLibNull.inf
  FvLib|MdePkg/Library/FvLib/FvLib.inf

!if $(CUSTOM_STACK_CHECK_LIB) == STATIC
  # To only use the static stack cookie, we just include the checking functionality.
  StackCheckLib|MdePkg/Library/StackCheckLib/StackCheckLib.inf
!elseif $(CUSTOM_STACK_CHECK_LIB) == DYNAMIC
  StackCheckLib|MdePkg/Library/StackCheckLib/StackCheckLib.inf

  # To use the dynamic stack cookie, we need to include the entry point libraries that will set up the stack cookie.
  # Typically, PeiCore and PEIMs will not use dynamic stack cookies, so they are not included generally.
  # If dynamic stack cookies are not enabled, we do not setup the entry points, as the existing behavior was
  # for a platform to define them.
  # StandaloneMmCoreEntryPoint is not included here because support dynamic stack cookies is not available for
  # AARCH64 here. X64 platforms should include the DynamicStackCookieEntryPointLib in their DSC file.
  DxeCoreEntryPoint|MdePkg/Library/DynamicStackCookieEntryPointLib/DxeCoreEntryPoint.inf
  StandaloneMmDriverEntryPoint|MdePkg/Library/DynamicStackCookieEntryPointLib/StandaloneMmDriverEntryPoint.inf
  UefiApplicationEntryPoint|MdePkg/Library/DynamicStackCookieEntryPointLib/UefiApplicationEntryPoint.inf
  UefiDriverEntryPoint|MdePkg/Library/DynamicStackCookieEntryPointLib/UefiDriverEntryPoint.inf

!else
  # If CUSTOM_STACK_CHECK_LIB is set, MdeLibs.dsc.inc will not link StackCheckLibNull and it is expected that the
  # DSC being built is providing it's own implementation of StackCheckLib.
  StackCheckLib|MdePkg/Library/StackCheckLibNull/StackCheckLibNull.inf
!endif

  #
  # For security and code size optimization reasons, the UefiImageLib design is
  # complicated. To not expose FV-only UEFI image formats via, e.g., DxeCore to
  # untrusted sources, UefiImageLib can be configured to support different UEFI
  # image formats per source. While compilers generally manage to optimize the
  # initial parsing steps, complex control flow can make them lose track of the
  # UefiImageLib source property and thus conditionally call into code for UEFI
  # image formats that are not required by the module at all (e.g., because it
  # only ever deals with FV images).
  #
  # To have the code for unsupported UEFI image file formats removed,
  # UefiImageLib comes in multiple flavours that support FV-only, non-FV-only,
  # or all UEFI image formats. These flavours are supposed to be used by
  # top-level modules that have a clear scope. As libraries may depend on
  # UefiImageLib too, however, they should consume the general UefiImageLib with
  # no clear flavour.
  #
  # If they consume libraries with UefiImageLib dependencies, modules must have
  # their general UefiImageLib set to their corresponding flavour for correct
  # linkage. In order to make this easier, there is a heuristic below, based on
  # module types, to set the most likely instance of UefiImageLib. In rare
  # cases, manual overriding in the platform DSC may be necessary.
  #
  UefiImageOnlyNonFvLib|MdePkg/Library/BaseUefiImageLib/BaseUefiImageOnlyNonFvLib.inf
  UefiImageOnlyFvLib|MdePkg/Library/BaseUefiImageLib/BaseUefiImageOnlyFvLib.inf
  UefiImageAllLib|MdePkg/Library/BaseUefiImageLib/BaseUefiImageAllLib.inf
  UeImageLib|MdePkg/Library/BaseUeImageLib/BaseUeImageLib.inf

[LibraryClasses.common.USER_DEFINED, LibraryClasses.common.SEC, LibraryClasses.common.PEI_CORE, LibraryClasses.common.PEIM, LibraryClasses.common.SMM_CORE, LibraryClasses.common.MM_CORE_STANDALONE, LibraryClasses.common.DXE_SMM_DRIVER, LibraryClasses.common.MM_STANDALONE]
  UefiImageLib|MdePkg/Library/BaseUefiImageLib/BaseUefiImageOnlyFvLib.inf

[LibraryClasses.common.DXE_CORE, LibraryClasses.common.DXE_DRIVER, LibraryClasses.common.DXE_RUNTIME_DRIVER, LibraryClasses.common.UEFI_DRIVER, LibraryClasses.common.UEFI_APPLICATION]
  UefiImageLib|MdePkg/Library/BaseUefiImageLib/BaseUefiImageAllLib.inf

[LibraryClasses.common.SEC, LibraryClasses.common.PEI_CORE]
  # edk2 does not implement exception handling for SEC and PEI_CORE, so StackCheckLibNull is used, as failing
  # stack cookies will generate an exception, which if unhandled can lead to a hung system state. If a platform
  # implements exception handling for SEC and PEI_CORE, it can use StackCheckLib for these phases in its DSC.
  StackCheckLib|MdePkg/Library/StackCheckLibNull/StackCheckLibNull.inf

[LibraryClasses.AARCH64]
  #
  # It is not possible to prevent the AARCH64 compilers from inserting generic intrinsic functions.
  # This library provides the intrinsic functions generated by these compilers.
  #
  # Linking this here as a null library will cause all AARCH64 files to link against it and have
  # definitions for the intrinsic functions.
  #
  NULL|MdePkg/Library/CompilerIntrinsicsLib/CompilerIntrinsicsLib.inf

[LibraryClasses.LOONGARCH64]
  #
  # Some LOONGARCH/LOONGARCH64 compilers may replace memory operations with libc functions to improve performance,
  # and there is no way to prevent the LOONGARCH/LOONGARCH64 compilers from inserting generic intrinsics.
  # This library provides the intrinsic functions generated by these compilers.
  #
  # Linking this here as a null library will cause all LOONGARCH/LOONGARCH64 files to link against it and have
  # definitions for the intrinsic functions.
  #
  NULL|MdePkg/Library/CompilerIntrinsicsLib/CompilerIntrinsicsLib.inf
