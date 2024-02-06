/** @file

  Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause

**/

extern EFI_DRIVER_BINDING_SUPPORTED mUserDriverBindingSupported;
extern EFI_DRIVER_BINDING_START     mUserDriverBindingStart;
extern EFI_DRIVER_BINDING_STOP      mUserDriverBindingStop;

EFI_STATUS
EFIAPI
CoreDriverBindingSupported (
  IN EFI_DRIVER_BINDING_PROTOCOL            *This,
  IN EFI_HANDLE                             ControllerHandle,
  IN EFI_DEVICE_PATH_PROTOCOL               *RemainingDevicePath OPTIONAL
  );

EFI_STATUS
EFIAPI
CoreDriverBindingStart (
  IN EFI_DRIVER_BINDING_PROTOCOL            *This,
  IN EFI_HANDLE                             ControllerHandle,
  IN EFI_DEVICE_PATH_PROTOCOL               *RemainingDevicePath OPTIONAL
  );

EFI_STATUS
EFIAPI
CoreDriverBindingStop (
  IN EFI_DRIVER_BINDING_PROTOCOL            *This,
  IN  EFI_HANDLE                            ControllerHandle,
  IN  UINTN                                 NumberOfChildren,
  IN  EFI_HANDLE                            *ChildHandleBuffer OPTIONAL
  );
