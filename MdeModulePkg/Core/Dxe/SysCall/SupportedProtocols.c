/** @file

  Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause

**/

#include "DxeMain.h"

EFI_DRIVER_BINDING_PROTOCOL  mRing3DriverBindingProtocol;

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

  //
  // Necessary fix for ProcessLibraryConstructorList() -> DxeCcProbeLibConstructor()
  //
  SetUefiImageMemoryAttributes (
    FixedPcdGet32 (PcdOvmfWorkAreaBase),
    FixedPcdGet32 (PcdOvmfWorkAreaSize),
    EFI_MEMORY_XP | EFI_MEMORY_USER
    );

  Status = CallRing3 (Input);

  SetUefiImageMemoryAttributes (
    FixedPcdGet32 (PcdOvmfWorkAreaBase),
    FixedPcdGet32 (PcdOvmfWorkAreaSize),
    EFI_MEMORY_XP
    );

  return Status;
}

EFI_STATUS
EFIAPI
CoreDriverBindingSupported (
  IN EFI_DRIVER_BINDING_PROTOCOL *This,
  IN EFI_HANDLE                  ControllerHandle,
  IN EFI_DEVICE_PATH_PROTOCOL    *RemainingDevicePath OPTIONAL
  )
{
  EFI_STATUS  Status;

  DisableSMAP ();
  This = AllocateRing3Copy (
           This,
           sizeof (EFI_DRIVER_BINDING_PROTOCOL),
           sizeof (EFI_DRIVER_BINDING_PROTOCOL)
           );
  if (This == NULL) {
    EnableSMAP ();
    return EFI_OUT_OF_RESOURCES;
  }
  EnableSMAP ();

  Status = GoToRing3 (
             3,
             (VOID *)mRing3DriverBindingProtocol.Supported,
             This,
             ControllerHandle,
             RemainingDevicePath
             );

  DisableSMAP ();
  FreePool (This);
  EnableSMAP ();

  return Status;
}

EFI_STATUS
EFIAPI
CoreDriverBindingStart (
  IN EFI_DRIVER_BINDING_PROTOCOL *This,
  IN EFI_HANDLE                  ControllerHandle,
  IN EFI_DEVICE_PATH_PROTOCOL    *RemainingDevicePath OPTIONAL
  )
{
  EFI_STATUS  Status;

  DisableSMAP ();
  This = AllocateRing3Copy (
           This,
           sizeof (EFI_DRIVER_BINDING_PROTOCOL),
           sizeof (EFI_DRIVER_BINDING_PROTOCOL)
           );
  if (This == NULL) {
    EnableSMAP ();
    return EFI_OUT_OF_RESOURCES;
  }
  EnableSMAP ();

  Status = GoToRing3 (
             3,
             (VOID *)mRing3DriverBindingProtocol.Start,
             This,
             ControllerHandle,
             RemainingDevicePath
             );

  DisableSMAP ();
  FreePool (This);
  EnableSMAP ();

  return Status;
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
  EFI_STATUS  Status;

  DisableSMAP ();
  This = AllocateRing3Copy (
           This,
           sizeof (EFI_DRIVER_BINDING_PROTOCOL),
           sizeof (EFI_DRIVER_BINDING_PROTOCOL)
           );
  if (This == NULL) {
    EnableSMAP ();
    return EFI_OUT_OF_RESOURCES;
  }
  EnableSMAP ();

  Status = GoToRing3 (
             4,
             (VOID *)mRing3DriverBindingProtocol.Stop,
             This,
             ControllerHandle,
             NumberOfChildren,
             ChildHandleBuffer
             );

  DisableSMAP ();
  FreePool (This);
  EnableSMAP ();

  return Status;
}
