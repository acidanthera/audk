/** @file

  Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause

**/

#include "DxeMain.h"

EFI_DRIVER_BINDING_SUPPORTED mUserDriverBindingSupported;
EFI_DRIVER_BINDING_START     mUserDriverBindingStart;
EFI_DRIVER_BINDING_STOP      mUserDriverBindingStop;

EFI_STATUS
EFIAPI
GoToRing3 (
  IN UINT8 Number,
  IN VOID  *EntryPoint,
  ...
  )
{
  EFI_STATUS       Status;
  RING3_CALL_DATA  *Input;
  VA_LIST          Marker;
  UINTN            Index;

  DisableSMAP ();
  Status = gBS->AllocatePool (
                  EfiRing3MemoryType,
                  sizeof (RING3_CALL_DATA) + Number * sizeof (UINTN),
                  (VOID **)&Input
                  );
  if (EFI_ERROR (Status)) {
    DEBUG ((DEBUG_ERROR, "Ring0: Failed to allocate memory for Input data.\n"));
    EnableSMAP ();
    return Status;
  }

  Input->NumberOfArguments = Number;
  Input->EntryPoint        = EntryPoint;

  VA_START (Marker, EntryPoint);
  for (Index = 0; Index < Number; ++Index) {
    Input->Arguments[Index] = VA_ARG (Marker, UINTN);
  }
  VA_END (Marker);
  EnableSMAP ();

  return CallRing3 (Input);
}

EFI_STATUS
EFIAPI
CoreDriverBindingSupported (
  IN EFI_DRIVER_BINDING_PROTOCOL *This,
  IN EFI_HANDLE                  ControllerHandle,
  IN EFI_DEVICE_PATH_PROTOCOL    *RemainingDevicePath OPTIONAL
  )
{
  return GoToRing3 (
           3,
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
  return GoToRing3 (
           3,
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
  return GoToRing3 (
           4,
           (VOID *)mUserDriverBindingStop,
           This,
           ControllerHandle,
           NumberOfChildren,
           ChildHandleBuffer
           );
}
