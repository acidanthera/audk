/** @file
  Definition for Device Path library.

Copyright (c) 2017, Intel Corporation. All rights reserved.<BR>
SPDX-License-Identifier: BSD-2-Clause-Patent

**/
#ifndef _UEFI_DEVICE_PATH_LIB_H_
#define _UEFI_DEVICE_PATH_LIB_H_

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <assert.h>
#ifdef __GNUC__
#include <unistd.h>
#else
#include <direct.h>
#endif
#include <Common/UefiBaseTypes.h>
#include <Protocol/DevicePath.h>
#include <Protocol/DevicePathUtilities.h>
#include "CommonLib.h"
#include "EfiUtilityMsgs.h"


#include <Library/DevicePathLib.h>
#define UefiDevicePathLibConvertTextToDevicePath  ConvertTextToDevicePath


#include <Protocol/DebugPort.h>
#define EFI_UART_DEVICE_PATH_GUID  DEVICE_PATH_MESSAGING_UART_FLOW_CONTROL

#endif
