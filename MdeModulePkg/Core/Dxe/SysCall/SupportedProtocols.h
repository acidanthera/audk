/** @file

  Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause

**/

#include <Protocol/BlockIo.h>
#include <Protocol/ComponentName.h>
#include <Protocol/DevicePathUtilities.h>
#include <Protocol/DiskIo.h>
#include <Protocol/UnicodeCollation.h>

extern EFI_DRIVER_BINDING_PROTOCOL      mRing3DriverBindingProtocol;
extern EFI_SIMPLE_FILE_SYSTEM_PROTOCOL  mRing3SimpleFileSystemProtocol;
extern EFI_SIMPLE_FILE_SYSTEM_PROTOCOL  *mRing3SimpleFileSystemPointer;

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

EFI_STATUS
EFIAPI
CoreOpenVolume (
  IN EFI_SIMPLE_FILE_SYSTEM_PROTOCOL        *This,
  OUT EFI_FILE_PROTOCOL                     **Root
  );
