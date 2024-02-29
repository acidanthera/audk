/** @file

  Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause

**/

#include "DxeMain.h"

EFI_DRIVER_BINDING_PROTOCOL      mRing3DriverBindingProtocol;
EFI_SIMPLE_FILE_SYSTEM_PROTOCOL  mRing3SimpleFileSystemProtocol;
EFI_FILE_PROTOCOL                mRing3FileProtocol;

EFI_SIMPLE_FILE_SYSTEM_PROTOCOL  *mRing3SimpleFileSystemPointer;

typedef struct {
  EFI_FILE_PROTOCOL  Protocol;
  EFI_FILE_PROTOCOL  *Ring3File;
} RING3_EFI_FILE_PROTOCOL;

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

STATIC
EFIAPI
VOID *
Ring3Copy (
  IN VOID    *Core,
  IN UINT32  Size
  )
{
  EFI_STATUS  Status;
  VOID        *Ring3;

  Status = CoreAllocatePages (
             AllocateAnyPages,
             EfiRing3MemoryType,
             1,
             (EFI_PHYSICAL_ADDRESS *)&Ring3
             );
  if (EFI_ERROR (Status)) {
    return NULL;
  }

  DisableSMAP ();
  CopyMem (Ring3, Core, Size);
  EnableSMAP ();

  return Ring3;
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

  This = Ring3Copy (This, sizeof (EFI_DRIVER_BINDING_PROTOCOL));
  if (This == NULL) {
    return EFI_OUT_OF_RESOURCES;
  }

  Status = GoToRing3 (
             3,
             (VOID *)mRing3DriverBindingProtocol.Supported,
             This,
             ControllerHandle,
             RemainingDevicePath
             );

  CoreFreePages ((EFI_PHYSICAL_ADDRESS)This, 1);

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

  This = Ring3Copy (This, sizeof (EFI_DRIVER_BINDING_PROTOCOL));
  if (This == NULL) {
    return EFI_OUT_OF_RESOURCES;
  }

  Status = GoToRing3 (
             3,
             (VOID *)mRing3DriverBindingProtocol.Start,
             This,
             ControllerHandle,
             RemainingDevicePath
             );

  CoreFreePages ((EFI_PHYSICAL_ADDRESS)This, 1);

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

  This = Ring3Copy (This, sizeof (EFI_DRIVER_BINDING_PROTOCOL));
  if (This == NULL) {
    return EFI_OUT_OF_RESOURCES;
  }

  Status = GoToRing3 (
             4,
             (VOID *)mRing3DriverBindingProtocol.Stop,
             This,
             ControllerHandle,
             NumberOfChildren,
             ChildHandleBuffer
             );

  CoreFreePages ((EFI_PHYSICAL_ADDRESS)This, 1);

  return Status;
}

STATIC
EFI_STATUS
EFIAPI
CoreFileClose (
  IN EFI_FILE_PROTOCOL  *This
  )
{
  EFI_STATUS              Status;
  RING3_EFI_FILE_PROTOCOL *File;

  File = (RING3_EFI_FILE_PROTOCOL *)This;

  Status = GoToRing3 (
             1,
             (VOID *)mRing3FileProtocol.Close,
             File->Ring3File
             );

  FreePool (This);

  return Status;
}

STATIC
EFI_STATUS
EFIAPI
CoreFileDelete (
  IN EFI_FILE_PROTOCOL  *This
  )
{
  return EFI_UNSUPPORTED;
}

STATIC
EFI_STATUS
EFIAPI
CoreFileRead (
  IN EFI_FILE_PROTOCOL        *This,
  IN OUT UINTN                *BufferSize,
  OUT VOID                    *Buffer
  )
{
  EFI_STATUS              Status;
  RING3_EFI_FILE_PROTOCOL *File;
  UINTN                   *Ring3BufferSize;
  VOID                    *Ring3Buffer;

  File            = (RING3_EFI_FILE_PROTOCOL *)This;
  Ring3Buffer     = NULL;
  Ring3BufferSize = NULL;

  DisableSMAP ();
  if (BufferSize != NULL) {
    Status = CoreAllocatePool (EfiRing3MemoryType, sizeof (UINTN *), (VOID **)&Ring3BufferSize);
    if (EFI_ERROR (Status)) {
      EnableSMAP ();
      return Status;
    }

    *Ring3BufferSize = *BufferSize;
  }

  if (Buffer != NULL) {
    Status = CoreAllocatePool (EfiRing3MemoryType, *BufferSize, (VOID **)&Ring3Buffer);
    if (EFI_ERROR (Status)) {
      if (Ring3BufferSize != NULL) {
        FreePool (Ring3BufferSize);
      }
      EnableSMAP ();
      return Status;
    }
  }
  EnableSMAP ();

  Status = GoToRing3 (
             3,
             (VOID *)mRing3FileProtocol.Read,
             File->Ring3File,
             Ring3BufferSize,
             Ring3Buffer
             );

  DisableSMAP ();
  if ((Ring3Buffer != NULL) && (Buffer != NULL) && (*BufferSize >= *Ring3BufferSize)) {
    CopyMem (Buffer, Ring3Buffer, *Ring3BufferSize);
  }

  if (Ring3Buffer != NULL) {
    FreePool (Ring3Buffer);
  }

  if (Ring3BufferSize != NULL) {
    *BufferSize = *Ring3BufferSize;

    FreePool (Ring3BufferSize);
  }
  EnableSMAP ();

  return Status;
}

STATIC
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

STATIC
EFI_STATUS
EFIAPI
CoreFileSetPosition (
  IN EFI_FILE_PROTOCOL        *This,
  IN UINT64                   Position
  )
{
  RING3_EFI_FILE_PROTOCOL *File;

  File = (RING3_EFI_FILE_PROTOCOL *)This;

  return GoToRing3 (
           2,
           (VOID *)mRing3FileProtocol.SetPosition,
           File->Ring3File,
           Position
           );
}

STATIC
EFI_STATUS
EFIAPI
CoreFileGetPosition (
  IN EFI_FILE_PROTOCOL        *This,
  OUT UINT64                  *Position
  )
{
  EFI_STATUS              Status;
  RING3_EFI_FILE_PROTOCOL *File;
  UINT64                  *Ring3Position;

  File          = (RING3_EFI_FILE_PROTOCOL *)This;
  Ring3Position = NULL;

  if (Position != NULL) {
    DisableSMAP ();
    Status = CoreAllocatePool (EfiRing3MemoryType, sizeof (UINT64), (VOID **)&Ring3Position);
    if (EFI_ERROR (Status)) {
      EnableSMAP ();
      return Status;
    }

    *Ring3Position = *Position;
    EnableSMAP ();
  }

  Status = GoToRing3 (
             2,
             (VOID *)mRing3FileProtocol.GetPosition,
             File->Ring3File,
             Ring3Position
             );

  if (Ring3Position != NULL) {
    DisableSMAP ();
    *Position = *Ring3Position;

    FreePool (Ring3Position);
    EnableSMAP ();
  }

  return Status;
}

STATIC
EFI_STATUS
EFIAPI
CoreFileGetInfo (
  IN EFI_FILE_PROTOCOL        *This,
  IN EFI_GUID                 *InformationType,
  IN OUT UINTN                *BufferSize,
  OUT VOID                    *Buffer
  )
{
  EFI_STATUS              Status;
  RING3_EFI_FILE_PROTOCOL *File;
  EFI_GUID                *Ring3InformationType;
  UINTN                   *Ring3BufferSize;
  VOID                    *Ring3Buffer;

  File                 = (RING3_EFI_FILE_PROTOCOL *)This;
  Ring3Buffer          = NULL;
  Ring3BufferSize      = NULL;
  Ring3InformationType = NULL;

  DisableSMAP ();
  if (BufferSize != NULL) {
    Status = CoreAllocatePool (EfiRing3MemoryType, sizeof (UINTN *), (VOID **)&Ring3BufferSize);
    if (EFI_ERROR (Status)) {
      EnableSMAP ();
      return Status;
    }

    *Ring3BufferSize = *BufferSize;
  }

  if (Buffer != NULL) {
    Status = CoreAllocatePool (EfiRing3MemoryType, *BufferSize, (VOID **)&Ring3Buffer);
    if (EFI_ERROR (Status)) {
      if (Ring3BufferSize != NULL) {
        FreePool (Ring3BufferSize);
      }
      EnableSMAP ();
      return Status;
    }
  }

  if (InformationType != NULL) {
    Status = CoreAllocatePool (EfiRing3MemoryType, sizeof (EFI_GUID), (VOID **)&Ring3InformationType);
    if (EFI_ERROR (Status)) {
      if (Ring3BufferSize != NULL) {
        FreePool (Ring3BufferSize);
      }
      if (Ring3Buffer != NULL) {
        FreePool (Ring3Buffer);
      }
      EnableSMAP ();
      return Status;
    }

    CopyGuid (Ring3InformationType, InformationType);
  }
  EnableSMAP ();

  Status = GoToRing3 (
             4,
             (VOID *)mRing3FileProtocol.GetInfo,
             File->Ring3File,
             Ring3InformationType,
             Ring3BufferSize,
             Ring3Buffer
             );

  DisableSMAP ();
  if ((Ring3Buffer != NULL) && (Buffer != NULL) && (*BufferSize >= *Ring3BufferSize)) {
    CopyMem (Buffer, Ring3Buffer, *Ring3BufferSize);
  }

  if (Ring3BufferSize != NULL) {
    *BufferSize = *Ring3BufferSize;

    FreePool (Ring3BufferSize);
  }

  if (Ring3Buffer != NULL) {
    FreePool (Ring3Buffer);
  }

  if (Ring3InformationType != NULL) {
    FreePool (Ring3InformationType);
  }
  EnableSMAP ();

  return Status;
}

STATIC
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

STATIC
EFI_STATUS
EFIAPI
CoreFileFlush (
  IN EFI_FILE_PROTOCOL  *This
  )
{
  return EFI_UNSUPPORTED;
}

STATIC
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

STATIC
EFI_STATUS
EFIAPI
CoreFileReadEx (
  IN EFI_FILE_PROTOCOL        *This,
  IN OUT EFI_FILE_IO_TOKEN    *Token
  )
{
  return EFI_UNSUPPORTED;
}

STATIC
EFI_STATUS
EFIAPI
CoreFileWriteEx (
  IN EFI_FILE_PROTOCOL        *This,
  IN OUT EFI_FILE_IO_TOKEN    *Token
  )
{
  return EFI_UNSUPPORTED;
}

STATIC
EFI_STATUS
EFIAPI
CoreFileFlushEx (
  IN EFI_FILE_PROTOCOL        *This,
  IN OUT EFI_FILE_IO_TOKEN    *Token
  )
{
  return EFI_UNSUPPORTED;
}

STATIC
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
  EFI_STATUS              Status;
  RING3_EFI_FILE_PROTOCOL *File;
  RING3_EFI_FILE_PROTOCOL *NewFile;
  EFI_FILE_PROTOCOL       **Ring3NewHandle;
  CHAR16                  *Ring3FileName;

  File = (RING3_EFI_FILE_PROTOCOL *)This;

  DisableSMAP ();
  Status = CoreAllocatePool (EfiRing3MemoryType, sizeof (EFI_FILE_PROTOCOL *), (VOID **)&Ring3NewHandle);
  if (EFI_ERROR (Status)) {
    EnableSMAP ();
    return Status;
  }

  Status = CoreAllocatePool (EfiRing3MemoryType, StrSize (FileName), (VOID **)&Ring3FileName);
  if (EFI_ERROR (Status)) {
    FreePool (Ring3NewHandle);
    EnableSMAP ();
    return Status;
  }

  Status = StrCpyS (Ring3FileName, StrLen (FileName) + 1, FileName);
  if (EFI_ERROR (Status)) {
    FreePool (Ring3NewHandle);
    FreePool (Ring3FileName);
    EnableSMAP ();
    return Status;
  }
  EnableSMAP ();

  Status = GoToRing3 (
             5,
             (VOID *)mRing3FileProtocol.Open,
             File->Ring3File,
             Ring3NewHandle,
             Ring3FileName,
             OpenMode,
             Attributes
             );
  if (EFI_ERROR (Status)) {
    *NewHandle = NULL;
    DisableSMAP ();
    FreePool (Ring3NewHandle);
    FreePool (Ring3FileName);
    EnableSMAP ();
    return Status;
  }

  NewFile = AllocatePool (sizeof (RING3_EFI_FILE_PROTOCOL));
  if (NewFile == NULL) {
    *NewHandle = NULL;
    DisableSMAP ();
    FreePool (Ring3NewHandle);
    FreePool (Ring3FileName);
    EnableSMAP ();
    return EFI_OUT_OF_RESOURCES;
  }

  NewFile->Protocol.Revision    = mRing3FileProtocol.Revision;
  NewFile->Protocol.Open        = CoreFileOpen;
  NewFile->Protocol.Close       = CoreFileClose;
  NewFile->Protocol.Delete      = CoreFileDelete;
  NewFile->Protocol.Read        = CoreFileRead;
  NewFile->Protocol.Write       = CoreFileWrite;
  NewFile->Protocol.GetPosition = CoreFileGetPosition;
  NewFile->Protocol.SetPosition = CoreFileSetPosition;
  NewFile->Protocol.GetInfo     = CoreFileGetInfo;
  NewFile->Protocol.SetInfo     = CoreFileSetInfo;
  NewFile->Protocol.Flush       = CoreFileFlush;
  NewFile->Protocol.OpenEx      = CoreFileOpenEx;
  NewFile->Protocol.ReadEx      = CoreFileReadEx;
  NewFile->Protocol.WriteEx     = CoreFileWriteEx;
  NewFile->Protocol.FlushEx     = CoreFileFlushEx;

  DisableSMAP ();
  NewFile->Ring3File = *Ring3NewHandle;

  FreePool (Ring3NewHandle);
  FreePool (Ring3FileName);
  EnableSMAP ();

  *NewHandle = (EFI_FILE_PROTOCOL *)NewFile;

  return Status;
}

EFI_STATUS
EFIAPI
CoreOpenVolume (
  IN  EFI_SIMPLE_FILE_SYSTEM_PROTOCOL *This,
  OUT EFI_FILE_PROTOCOL               **Root
  )
{
  EFI_STATUS              Status;
  EFI_FILE_PROTOCOL       **Ring3Root;
  RING3_EFI_FILE_PROTOCOL *File;

  DisableSMAP ();
  Status = CoreAllocatePool (EfiRing3MemoryType, sizeof (EFI_FILE_PROTOCOL *), (VOID **)&Ring3Root);
  EnableSMAP ();
  if (EFI_ERROR (Status)) {
    return Status;
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

  File = AllocatePool (sizeof (RING3_EFI_FILE_PROTOCOL));
  if (File == NULL) {
    *Root = NULL;
    DisableSMAP ();
    FreePool (Ring3Root);
    EnableSMAP ();
    return EFI_OUT_OF_RESOURCES;
  }

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

  File->Ring3File = *Ring3Root;

  FreePool (Ring3Root);
  EnableSMAP ();

  File->Protocol.Revision    = mRing3FileProtocol.Revision;
  File->Protocol.Open        = CoreFileOpen;
  File->Protocol.Close       = CoreFileClose;
  File->Protocol.Delete      = CoreFileDelete;
  File->Protocol.Read        = CoreFileRead;
  File->Protocol.Write       = CoreFileWrite;
  File->Protocol.GetPosition = CoreFileGetPosition;
  File->Protocol.SetPosition = CoreFileSetPosition;
  File->Protocol.GetInfo     = CoreFileGetInfo;
  File->Protocol.SetInfo     = CoreFileSetInfo;
  File->Protocol.Flush       = CoreFileFlush;
  File->Protocol.OpenEx      = CoreFileOpenEx;
  File->Protocol.ReadEx      = CoreFileReadEx;
  File->Protocol.WriteEx     = CoreFileWriteEx;
  File->Protocol.FlushEx     = CoreFileFlushEx;

  *Root = (EFI_FILE_PROTOCOL *)File;

  return Status;
}
