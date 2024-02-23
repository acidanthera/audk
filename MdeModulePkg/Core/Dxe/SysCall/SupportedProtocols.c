/** @file

  Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause

**/

#include "DxeMain.h"

EFI_DRIVER_BINDING_PROTOCOL      mRing3DriverBindingProtocol;
EFI_SIMPLE_FILE_SYSTEM_PROTOCOL  mRing3SimpleFileSystemProtocol;
EFI_FILE_PROTOCOL                mRing3FileProtocol;

EFI_SIMPLE_FILE_SYSTEM_PROTOCOL  *mRing3SimpleFileSystemPointer;
EFI_FILE_PROTOCOL                *mRing3FilePointer;

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

  if (Number == 2) {
    //
    // Necessary fix for ProcessLibraryConstructorList() -> DxeCcProbeLibConstructor()
    //
    SetUefiImageMemoryAttributes (
      FixedPcdGet32 (PcdOvmfWorkAreaBase),
      FixedPcdGet32 (PcdOvmfWorkAreaSize),
      EFI_MEMORY_XP | EFI_MEMORY_USER
      );
  }

  Status = CallRing3 (Input);

  if (Number == 2) {
    SetUefiImageMemoryAttributes (
      FixedPcdGet32 (PcdOvmfWorkAreaBase),
      FixedPcdGet32 (PcdOvmfWorkAreaSize),
      EFI_MEMORY_XP
      );
  }

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

EFI_STATUS
EFIAPI
CoreFileOpen (
  IN EFI_FILE_PROTOCOL        *This,
  OUT EFI_FILE_PROTOCOL       **NewHandle,
  IN CHAR16                   *FileName,
  IN UINT64                   OpenMode,
  IN UINT64                   Attributes
  )
{
  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
CoreFileClose (
  IN EFI_FILE_PROTOCOL  *This
  )
{
  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
CoreFileDelete (
  IN EFI_FILE_PROTOCOL  *This
  )
{
  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
CoreFileRead (
  IN EFI_FILE_PROTOCOL        *This,
  IN OUT UINTN                *BufferSize,
  OUT VOID                    *Buffer
  )
{
  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
CoreFileWrite (
  IN EFI_FILE_PROTOCOL        *This,
  IN OUT UINTN                *BufferSize,
  IN VOID                     *Buffer
  )
{
  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
CoreFileSetPosition (
  IN EFI_FILE_PROTOCOL        *This,
  IN UINT64                   Position
  )
{
  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
CoreFileGetPosition (
  IN EFI_FILE_PROTOCOL        *This,
  OUT UINT64                  *Position
  )
{
  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
CoreFileGetInfo (
  IN EFI_FILE_PROTOCOL        *This,
  IN EFI_GUID                 *InformationType,
  IN OUT UINTN                *BufferSize,
  OUT VOID                    *Buffer
  )
{
  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
CoreFileSetInfo (
  IN EFI_FILE_PROTOCOL        *This,
  IN EFI_GUID                 *InformationType,
  IN UINTN                    BufferSize,
  IN VOID                     *Buffer
  )
{
  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
CoreFileFlush (
  IN EFI_FILE_PROTOCOL  *This
  )
{
  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
CoreFileOpenEx (
  IN EFI_FILE_PROTOCOL        *This,
  OUT EFI_FILE_PROTOCOL       **NewHandle,
  IN CHAR16                   *FileName,
  IN UINT64                   OpenMode,
  IN UINT64                   Attributes,
  IN OUT EFI_FILE_IO_TOKEN    *Token
  )
{
  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
CoreFileReadEx (
  IN EFI_FILE_PROTOCOL        *This,
  IN OUT EFI_FILE_IO_TOKEN    *Token
  )
{
  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
CoreFileWriteEx (
  IN EFI_FILE_PROTOCOL        *This,
  IN OUT EFI_FILE_IO_TOKEN    *Token
  )
{
  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
CoreFileFlushEx (
  IN EFI_FILE_PROTOCOL        *This,
  IN OUT EFI_FILE_IO_TOKEN    *Token
  )
{
  return EFI_UNSUPPORTED;
}

EFI_STATUS
EFIAPI
CoreOpenVolume (
  IN  EFI_SIMPLE_FILE_SYSTEM_PROTOCOL *This,
  OUT EFI_FILE_PROTOCOL               **Root
  )
{
  EFI_STATUS         Status;
  EFI_FILE_PROTOCOL  **Ring3Root;

  DisableSMAP ();
  Status = CoreAllocatePool (EfiRing3MemoryType, sizeof (EFI_FILE_PROTOCOL *), (VOID **)&Ring3Root);
  EnableSMAP ();
  if (EFI_ERROR (Status)) {
    return EFI_OUT_OF_RESOURCES;
  }

  Status = GoToRing3 (
             2,
             (VOID *)mRing3SimpleFileSystemProtocol.OpenVolume,
             mRing3SimpleFileSystemPointer,
             Ring3Root
             );
  if (EFI_ERROR (Status)) {
    *Root = NULL;
    DisableSMAP ();
    FreePool (Ring3Root);
    EnableSMAP ();
    return Status;
  }

  *Root = AllocatePool (sizeof (EFI_FILE_PROTOCOL));

  DisableSMAP ();
  mRing3FileProtocol.Revision    = (*Ring3Root)->Revision;
  mRing3FileProtocol.Open        = (*Ring3Root)->Open;
  mRing3FileProtocol.Close       = (*Ring3Root)->Close;
  mRing3FileProtocol.Delete      = (*Ring3Root)->Delete;
  mRing3FileProtocol.Read        = (*Ring3Root)->Read;
  mRing3FileProtocol.Write       = (*Ring3Root)->Write;
  mRing3FileProtocol.GetPosition = (*Ring3Root)->GetPosition;
  mRing3FileProtocol.SetPosition = (*Ring3Root)->SetPosition;
  mRing3FileProtocol.GetInfo     = (*Ring3Root)->GetInfo;
  mRing3FileProtocol.SetInfo     = (*Ring3Root)->SetInfo;
  mRing3FileProtocol.Flush       = (*Ring3Root)->Flush;
  mRing3FileProtocol.OpenEx      = (*Ring3Root)->OpenEx;
  mRing3FileProtocol.ReadEx      = (*Ring3Root)->ReadEx;
  mRing3FileProtocol.WriteEx     = (*Ring3Root)->WriteEx;
  mRing3FileProtocol.FlushEx     = (*Ring3Root)->FlushEx;

  mRing3FilePointer = *Ring3Root;

  FreePool (Ring3Root);
  EnableSMAP ();

  (*Root)->Revision    = mRing3FileProtocol.Revision;
  (*Root)->Open        = CoreFileOpen;
  (*Root)->Close       = CoreFileClose;
  (*Root)->Delete      = CoreFileDelete;
  (*Root)->Read        = CoreFileRead;
  (*Root)->Write       = CoreFileWrite;
  (*Root)->GetPosition = CoreFileGetPosition;
  (*Root)->SetPosition = CoreFileSetPosition;
  (*Root)->GetInfo     = CoreFileGetInfo;
  (*Root)->SetInfo     = CoreFileSetInfo;
  (*Root)->Flush       = CoreFileFlush;
  (*Root)->OpenEx      = CoreFileOpenEx;
  (*Root)->ReadEx      = CoreFileReadEx;
  (*Root)->WriteEx     = CoreFileWriteEx;
  (*Root)->FlushEx     = CoreFileFlushEx;

  return Status;
}
