/** @file

  Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause

**/

#include "DxeMain.h"

EFI_DRIVER_BINDING_SUPPORTED mUserDriverBindingSupported;
EFI_DRIVER_BINDING_START     mUserDriverBindingStart;
EFI_DRIVER_BINDING_STOP      mUserDriverBindingStop;

typedef enum {
  UserDriverBindingSupported = 1,
  UserDriverBindingStart     = 2,
  UserDriverBindingStop      = 3,
  UserCallMax
} USER_CALL_TYPE;

EFI_STATUS
EFIAPI
CallRing3 (
  IN UINT8  Type,
  IN UINT16 CodeSelector,
  IN UINT16 DataSelector,
  IN VOID   *FunctionAddress,
  ...
  );

EFI_STATUS
EFIAPI
CoreDriverBindingSupported (
  IN EFI_DRIVER_BINDING_PROTOCOL *This,
  IN EFI_HANDLE                  ControllerHandle,
  IN EFI_DEVICE_PATH_PROTOCOL    *RemainingDevicePath OPTIONAL
  )
{
  return CallRing3 (
           UserDriverBindingSupported,
           (UINT16)RING3_CODE64_SEL,
           (UINT16)RING3_DATA64_SEL,
           (VOID *)mUserDriverBindingSupported,
           This,
           ControllerHandle,
           RemainingDevicePath
           );
}

EFI_STATUS
EFIAPI
CoreDriverBindingStart (
  IN EFI_DRIVER_BINDING_PROTOCOL *This,
  IN EFI_HANDLE                  ControllerHandle,
  IN EFI_DEVICE_PATH_PROTOCOL    *RemainingDevicePath OPTIONAL
  )
{
  return CallRing3 (
           UserDriverBindingStart,
           (UINT16)RING3_CODE64_SEL,
           (UINT16)RING3_DATA64_SEL,
           (VOID *)mUserDriverBindingStart,
           This,
           ControllerHandle,
           RemainingDevicePath
           );
}

EFI_STATUS
EFIAPI
CoreDriverBindingStop (
  IN EFI_DRIVER_BINDING_PROTOCOL *This,
  IN EFI_HANDLE                  ControllerHandle,
  IN UINTN                       NumberOfChildren,
  IN EFI_HANDLE                  *ChildHandleBuffer OPTIONAL
  )
{
  return CallRing3 (
           UserDriverBindingStop,
           (UINT16)RING3_CODE64_SEL,
           (UINT16)RING3_DATA64_SEL,
           (VOID *)mUserDriverBindingStop,
           This,
           ControllerHandle,
           NumberOfChildren,
           ChildHandleBuffer
           );
}
