/** @file
  AutoGen definitions for edk2 package code consumption in BaseTools.

  Copyright (c) 2023, Marvin Häuser. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-2-Clause-Patent

**/

#ifndef _BT_AUTOGENH
#define _BT_AUTOGENH

#ifdef __cplusplus
extern "C" {
#endif

#include <Base.h>
#include <Library/PcdLib.h>

extern GUID   gEfiCallerIdGuid;
extern GUID   gEdkiiDscPlatformGuid;
extern CHAR8  *gEfiCallerBaseName;

#define EFI_CALLER_ID_GUID \
  {0x00000000, 0x0000, 0x0000, {0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00}}
#define EDKII_DSC_PLATFORM_GUID \
  {0x00000000, 0x0000, 0x0000, {0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00}}

// Definition of SkuId Array
extern UINT64  _gPcd_SkuId_Array[];

// Definition of PCDs used in this module

#define _PCD_TOKEN_PcdMaximumAsciiStringLength          0U
#define _PCD_SIZE_PcdMaximumAsciiStringLength           4
#define _PCD_GET_MODE_SIZE_PcdMaximumAsciiStringLength  _PCD_SIZE_PcdMaximumAsciiStringLength
#define _PCD_VALUE_PcdMaximumAsciiStringLength          0U
#define _PCD_GET_MODE_32_PcdMaximumAsciiStringLength    _PCD_VALUE_PcdMaximumAsciiStringLength
// #define _PCD_SET_MODE_32_PcdMaximumAsciiStringLength  ASSERT(FALSE)  // It is not allowed to set value for a FIXED_AT_BUILD PCD

#define _PCD_TOKEN_PcdMaximumUnicodeStringLength          0U
#define _PCD_SIZE_PcdMaximumUnicodeStringLength           4
#define _PCD_GET_MODE_SIZE_PcdMaximumUnicodeStringLength  _PCD_SIZE_PcdMaximumUnicodeStringLength
#define _PCD_VALUE_PcdMaximumUnicodeStringLength          0U
#define _PCD_GET_MODE_32_PcdMaximumUnicodeStringLength    _PCD_VALUE_PcdMaximumUnicodeStringLength
// #define _PCD_SET_MODE_32_PcdMaximumUnicodeStringLength  ASSERT(FALSE)  // It is not allowed to set value for a FIXED_AT_BUILD PCD

#define _PCD_TOKEN_PcdMaximumLinkedListLength          0U
#define _PCD_SIZE_PcdMaximumLinkedListLength           4
#define _PCD_GET_MODE_SIZE_PcdMaximumLinkedListLength  _PCD_SIZE_PcdMaximumLinkedListLength
#define _PCD_VALUE_PcdMaximumLinkedListLength          0U
#define _PCD_GET_MODE_32_PcdMaximumLinkedListLength    _PCD_VALUE_PcdMaximumLinkedListLength
// #define _PCD_SET_MODE_32_PcdMaximumLinkedListLength  ASSERT(FALSE)  // It is not allowed to set value for a FIXED_AT_BUILD PCD

#define _PCD_TOKEN_PcdMaximumDevicePathNodeCount          0U
#define _PCD_SIZE_PcdMaximumDevicePathNodeCount           4
#define _PCD_GET_MODE_SIZE_PcdMaximumDevicePathNodeCount  _PCD_SIZE_PcdMaximumDevicePathNodeCount
#define _PCD_VALUE_PcdMaximumDevicePathNodeCount          0U
#define _PCD_GET_MODE_32_PcdMaximumDevicePathNodeCount    _PCD_VALUE_PcdMaximumDevicePathNodeCount
// #define _PCD_SET_MODE_32_PcdMaximumDevicePathNodeCount  ASSERT(FALSE)  // It is not allowed to set value for a FIXED_AT_BUILD PCD

#define _PCD_TOKEN_PcdVerifyNodeInList          0U
#define _PCD_SIZE_PcdVerifyNodeInList           1
#define _PCD_GET_MODE_SIZE_PcdVerifyNodeInList  _PCD_SIZE_PcdVerifyNodeInList
#define _PCD_VALUE_PcdVerifyNodeInList          1U
#define _PCD_GET_MODE_BOOL_PcdVerifyNodeInList  _PCD_VALUE_PcdVerifyNodeInList
// #define _PCD_SET_MODE_BOOL_PcdVerifyNodeInList  ASSERT(FALSE)  // It is not allowed to set value for a FIXED_AT_BUILD PCD

#define _PCD_TOKEN_PcdFixedDebugPrintErrorLevel          0U
#define _PCD_SIZE_PcdFixedDebugPrintErrorLevel           4
#define _PCD_GET_MODE_SIZE_PcdFixedDebugPrintErrorLevel  _PCD_SIZE_PcdFixedDebugPrintErrorLevel
#define _PCD_VALUE_PcdFixedDebugPrintErrorLevel          0xFFFFFFFFU
#define _PCD_GET_MODE_32_PcdFixedDebugPrintErrorLevel    _PCD_VALUE_PcdFixedDebugPrintErrorLevel
// #define _PCD_SET_MODE_32_PcdFixedDebugPrintErrorLevel  ASSERT(FALSE)  // It is not allowed to set value for a FIXED_AT_BUILD PCD

#define _PCD_TOKEN_PcdDebugPropertyMask          0U
#define _PCD_SIZE_PcdDebugPropertyMask           1
#define _PCD_GET_MODE_SIZE_PcdDebugPropertyMask  _PCD_SIZE_PcdDebugPropertyMask
#define _PCD_VALUE_PcdDebugPropertyMask          0xFFU
#define _PCD_GET_MODE_8_PcdDebugPropertyMask     _PCD_VALUE_PcdDebugPropertyMask
// #define _PCD_SET_MODE_8_PcdDebugPropertyMask  ASSERT(FALSE)  // It is not allowed to set value for a FIXED_AT_BUILD PCD

#define _PCD_TOKEN_PcdDebugClearMemoryValue          0U
#define _PCD_SIZE_PcdDebugClearMemoryValue           1
#define _PCD_GET_MODE_SIZE_PcdDebugClearMemoryValue  _PCD_SIZE_PcdDebugClearMemoryValue
#define _PCD_VALUE_PcdDebugClearMemoryValue          0xAFU
#define _PCD_GET_MODE_8_PcdDebugClearMemoryValue     _PCD_VALUE_PcdDebugClearMemoryValue
// #define _PCD_SET_MODE_8_PcdDebugClearMemoryValue  ASSERT(FALSE)  // It is not allowed to set value for a FIXED_AT_BUILD PCD

#define _PCD_TOKEN_PcdDebugPrintErrorLevel          0U
#define _PCD_SIZE_PcdDebugPrintErrorLevel           4
#define _PCD_GET_MODE_SIZE_PcdDebugPrintErrorLevel  _PCD_SIZE_PcdDebugPrintErrorLevel
#define _PCD_VALUE_PcdDebugPrintErrorLevel          0x8000004F
#define _PCD_GET_MODE_32_PcdDebugPrintErrorLevel    _PCD_VALUE_PcdDebugPrintErrorLevel
// #define _PCD_SET_MODE_32_PcdDebugPrintErrorLevel  ASSERT(FALSE)  // It is not allowed to set value for a FIXED_AT_BUILD PCD

#define _PCD_TOKEN_PcdImageLoaderDebugSupport          0U
#define _PCD_SIZE_PcdImageLoaderDebugSupport           1
#define _PCD_GET_MODE_SIZE_PcdImageLoaderDebugSupport  _PCD_SIZE_PcdImageLoaderDebugSupport
#define _PCD_VALUE_PcdImageLoaderDebugSupport          TRUE
#define _PCD_GET_MODE_BOOL_PcdImageLoaderDebugSupport  _PCD_VALUE_PcdImageLoaderDebugSupport
// #define _PCD_SET_MODE_BOOL_PcdImageLoaderDebugSupport  ASSERT(FALSE)  // It is not allowed to set value for a FIXED_AT_BUILD PCD

#define _PCD_TOKEN_PcdImageLoaderHashProhibitOverlap          0U
#define _PCD_SIZE_PcdImageLoaderHashProhibitOverlap           1
#define _PCD_GET_MODE_SIZE_PcdImageLoaderHashProhibitOverlap  _PCD_SIZE_PcdImageLoaderHashProhibitOverlap
#define _PCD_VALUE_PcdImageLoaderHashProhibitOverlap          FALSE
#define _PCD_GET_MODE_BOOL_PcdImageLoaderHashProhibitOverlap  _PCD_VALUE_PcdImageLoaderHashProhibitOverlap
// #define _PCD_SET_MODE_BOOL_PcdImageLoaderHashProhibitOverlap  ASSERT(FALSE)  // It is not allowed to set value for a FIXED_AT_BUILD PCD

#define _PCD_TOKEN_PcdImageLoaderAllowMisalignedOffset          0U
#define _PCD_SIZE_PcdImageLoaderAllowMisalignedOffset           1
#define _PCD_GET_MODE_SIZE_PcdImageLoaderAllowMisalignedOffset  _PCD_SIZE_PcdImageLoaderAllowMisalignedOffset
#define _PCD_VALUE_PcdImageLoaderAllowMisalignedOffset          FALSE
#define _PCD_GET_MODE_BOOL_PcdImageLoaderAllowMisalignedOffset  _PCD_VALUE_PcdImageLoaderAllowMisalignedOffset
// #define _PCD_SET_MODE_BOOL_PcdImageLoaderAllowMisalignedOffset  ASSERT(FALSE)  // It is not allowed to set value for a FIXED_AT_BUILD PCD

#define _PCD_TOKEN_PcdImageLoaderRemoveXForWX          0U
#define _PCD_SIZE_PcdImageLoaderRemoveXForWX           1
#define _PCD_GET_MODE_SIZE_PcdImageLoaderRemoveXForWX  _PCD_SIZE_PcdImageLoaderRemoveXForWX
#define _PCD_VALUE_PcdImageLoaderRemoveXForWX          FALSE
#define _PCD_GET_MODE_BOOL_PcdImageLoaderRemoveXForWX  _PCD_VALUE_PcdImageLoaderRemoveXForWX
// #define _PCD_SET_MODE_BOOL_PcdImageLoaderRemoveXForWX  ASSERT(FALSE)  // It is not allowed to set value for a FIXED_AT_BUILD PCD

#define _PCD_TOKEN_PcdImageLoaderWXorX          0U
#define _PCD_SIZE_PcdImageLoaderWXorX           1
#define _PCD_GET_MODE_SIZE_PcdImageLoaderWXorX  _PCD_SIZE_PcdImageLoaderWXorX
#define _PCD_VALUE_PcdImageLoaderWXorX          TRUE
#define _PCD_GET_MODE_BOOL_PcdImageLoaderWXorX  _PCD_VALUE_PcdImageLoaderWXorX
// #define _PCD_SET_MODE_BOOL_PcdImageLoaderWXorX  ASSERT(FALSE)  // It is not allowed to set value for a FIXED_AT_BUILD PCD

#define _PCD_TOKEN_PcdImageLoaderLoadHeader          0U
#define _PCD_SIZE_PcdImageLoaderLoadHeader           1
#define _PCD_GET_MODE_SIZE_PcdImageLoaderLoadHeader  _PCD_SIZE_PcdImageLoaderLoadHeader
#define _PCD_VALUE_PcdImageLoaderLoadHeader          TRUE
#define _PCD_GET_MODE_BOOL_PcdImageLoaderLoadHeader  _PCD_VALUE_PcdImageLoaderLoadHeader
// #define _PCD_SET_MODE_BOOL_PcdImageLoaderLoadHeader  ASSERT(FALSE)  // It is not allowed to set value for a FIXED_AT_BUILD PCD

#define _PCD_TOKEN_PcdImageLoaderRtRelocAllowTargetMismatch          0U
#define _PCD_SIZE_PcdImageLoaderRtRelocAllowTargetMismatch           1
#define _PCD_GET_MODE_SIZE_PcdImageLoaderRtRelocAllowTargetMismatch  _PCD_SIZE_PcdImageLoaderRtRelocAllowTargetMismatch
#define _PCD_VALUE_PcdImageLoaderRtRelocAllowTargetMismatch          TRUE
#define _PCD_GET_MODE_BOOL_PcdImageLoaderRtRelocAllowTargetMismatch  _PCD_VALUE_PcdImageLoaderRtRelocAllowTargetMismatch
// #define _PCD_SET_MODE_BOOL_PcdImageLoaderRtRelocAllowTargetMismatch  ASSERT(FALSE)  // It is not allowed to set value for a FIXED_AT_BUILD PCD

#define _PCD_TOKEN_PcdImageLoaderAlignmentPolicy          0U
#define _PCD_SIZE_PcdImageLoaderAlignmentPolicy           4
#define _PCD_GET_MODE_SIZE_PcdImageLoaderAlignmentPolicy  _PCD_SIZE_PcdImageLoaderAlignmentPolicy
#define _PCD_VALUE_PcdImageLoaderAlignmentPolicy          0U
#define _PCD_GET_MODE_32_PcdImageLoaderAlignmentPolicy    _PCD_VALUE_PcdImageLoaderAlignmentPolicy
// #define _PCD_SET_MODE_32_PcdImageLoaderAlignmentPolicy  ASSERT(FALSE)  // It is not allowed to set value for a FIXED_AT_BUILD PCD

#define _PCD_TOKEN_PcdImageLoaderRelocTypePolicy          0U
#define _PCD_SIZE_PcdImageLoaderRelocTypePolicy           4
#define _PCD_GET_MODE_SIZE_PcdImageLoaderRelocTypePolicy  _PCD_SIZE_PcdImageLoaderRelocTypePolicy
#define _PCD_VALUE_PcdImageLoaderRelocTypePolicy          0U
#define _PCD_GET_MODE_32_PcdImageLoaderRelocTypePolicy    _PCD_VALUE_PcdImageLoaderRelocTypePolicy
// #define _PCD_SET_MODE_32_PcdImageLoaderRelocTypePolicy  ASSERT(FALSE)  // It is not allowed to set value for a FIXED_AT_BUILD PCD

#define _PCD_TOKEN_PcdDebugRaisePropertyMask          0U
#define _PCD_SIZE_PcdDebugRaisePropertyMask           1
#define _PCD_GET_MODE_SIZE_PcdDebugRaisePropertyMask  _PCD_SIZE_PcdDebugRaisePropertyMask
#define _PCD_VALUE_PcdDebugRaisePropertyMask          0xFFU
#define _PCD_GET_MODE_8_PcdDebugRaisePropertyMask     _PCD_VALUE_PcdDebugRaisePropertyMask
// #define _PCD_SET_MODE_8_PcdDebugRaisePropertyMask  ASSERT(FALSE)  // It is not allowed to set value for a FIXED_AT_BUILD PCD

#define _PCD_TOKEN_PcdUefiImageFormatSupportNonFv          0U
#define _PCD_VALUE_PcdUefiImageFormatSupportNonFv          0x00
#define _PCD_SIZE_PcdUefiImageFormatSupportNonFv           1
#define _PCD_GET_MODE_SIZE_PcdUefiImageFormatSupportNonFv  _PCD_SIZE_PcdUefiImageFormatSupportNonFv
#define _PCD_GET_MODE_8_PcdUefiImageFormatSupportNonFv     _PCD_VALUE_PcdUefiImageFormatSupportNonFv
// #define _PCD_SET_MODE_8_PcdUefiImageFormatSupportNonFv  ASSERT(FALSE)  // It is not allowed to set value for a FIXED_AT_BUILD PCD

#define _PCD_TOKEN_PcdUefiImageFormatSupportFv          0U
#define _PCD_VALUE_PcdUefiImageFormatSupportFv          0x01
#define _PCD_SIZE_PcdUefiImageFormatSupportFv           1
#define _PCD_GET_MODE_SIZE_PcdUefiImageFormatSupportFv  _PCD_SIZE_PcdUefiImageFormatSupportFv
#define _PCD_GET_MODE_8_PcdUefiImageFormatSupportFv     _PCD_VALUE_PcdUefiImageFormatSupportFv
// #define _PCD_SET_MODE_8_PcdUefiImageFormatSupportFv  ASSERT(FALSE)  // It is not allowed to set value for a FIXED_AT_BUILD PCD

#ifdef __cplusplus
}
#endif

#endif
