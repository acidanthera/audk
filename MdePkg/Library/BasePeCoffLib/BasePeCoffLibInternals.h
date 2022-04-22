/** @file
  Copyright (c) 2020, Marvin Häuser. All rights reserved.<BR>
  Copyright (c) 2020, Vitaly Cheptsov. All rights reserved.<BR>
  Copyright (c) 2020, ISP RAS. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-3-Clause
**/

#ifndef BASE_PECOFF_LIB_INTERNALS_H
#define BASE_PECOFF_LIB_INTERNALS_H

#include "Base.h"
#include <Library/DebugLib.h>
#include <IndustryStandard/PeImage.h>
#include <Library/PeCoffLib.h>
#include "BaseOverflow.h"
#include <Library/BaseMemoryLib.h>
#include <Library/BaseLib.h>

#define IS_ALIGNED(v, a)  (((v) & ((a) - 1U)) == 0U)
#define IS_POW2(v)        ((v) != 0 && ((v) & ((v) - 1U)) == 0)
#define OC_ALIGNOF        _Alignof

/**
  Returns the type of a Base Relocation.

  @param[in] Relocation  The composite Base Relocation value.
**/
#define IMAGE_RELOC_TYPE(Relocation)    ((Relocation) >> 12U)

/**
  Returns the target offset of a Base Relocation.

  @param[in] Relocation  The composite Base Relocation value.
**/
#define IMAGE_RELOC_OFFSET(Relocation)  ((Relocation) & 0x0FFFU)

/**
  Returns whether the Image targets the UEFI Subsystem.

  @param[in] Subsystem  The Subsystem value from the Image Header.
**/
#define IMAGE_IS_EFI_SUBYSYSTEM(Subsystem) \
  ((Subsystem) >= EFI_IMAGE_SUBSYSTEM_EFI_APPLICATION && \
   (Subsystem) <= EFI_IMAGE_SUBSYSTEM_SAL_RUNTIME_DRIVER)

#endif // BASE_PECOFF_LIB_INTERNALS_H
