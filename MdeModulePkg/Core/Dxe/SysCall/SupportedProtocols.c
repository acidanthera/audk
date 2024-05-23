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
  EFI_STATUS            Status;
  RING3_CALL_DATA       *Input;
  VA_LIST               Marker;
  UINTN                 Index;
  EFI_PHYSICAL_ADDRESS  Ring3Pages;
  UINT32                PagesNumber;

  PagesNumber = (UINT32)EFI_SIZE_TO_PAGES (sizeof (RING3_CALL_DATA) + Number * sizeof (UINTN));

  Status = CoreAllocatePages (
             AllocateAnyPages,
             EfiRing3MemoryType,
             PagesNumber,
             &Ring3Pages
             );
  if (EFI_ERROR (Status)) {
    return Status;
  }

  Input = (RING3_CALL_DATA *)(UINTN)Ring3Pages;

  DisableSMAP ();
  Input->NumberOfArguments = Number;
  Input->EntryPoint        = EntryPoint;

  VA_START (Marker, EntryPoint);
  for (Index = 0; Index < Number; ++Index) {
    Input->Arguments[Index] = VA_ARG (Marker, UINTN);
  }
  VA_END (Marker);
  EnableSMAP ();

#if defined (MDE_CPU_X64) || defined (MDE_CPU_IA32)
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
#endif

  Status = CallRing3 (Input);

#if defined (MDE_CPU_X64) || defined (MDE_CPU_IA32)
  if (Number == 2) {
    SetUefiImageMemoryAttributes (
      FixedPcdGet32 (PcdOvmfWorkAreaBase),
      FixedPcdGet32 (PcdOvmfWorkAreaSize),
      EFI_MEMORY_XP
      );
  }
#endif

  CoreFreePages (Ring3Pages, PagesNumber);

  return Status;
}

STATIC
VOID *
EFIAPI
Ring3Copy (
  IN VOID    *Core,
  IN UINT32  Size
  )
{
  EFI_STATUS            Status;
  EFI_PHYSICAL_ADDRESS  Ring3;

  Status = CoreAllocatePages (
             AllocateAnyPages,
             EfiRing3MemoryType,
             1,
             &Ring3
             );
  if (EFI_ERROR (Status)) {
    return NULL;
  }

  DisableSMAP ();
  CopyMem ((VOID *)(UINTN)Ring3, Core, Size);
  EnableSMAP ();

  return (VOID *)(UINTN)Ring3;
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

  CoreFreePages ((EFI_PHYSICAL_ADDRESS)(UINTN)This, 1);

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

  CoreFreePages ((EFI_PHYSICAL_ADDRESS)(UINTN)This, 1);

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

  CoreFreePages ((EFI_PHYSICAL_ADDRESS)(UINTN)This, 1);

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
  EFI_PHYSICAL_ADDRESS    Ring3Pages;
  UINT32                  PagesNumber;

  if ((This == NULL) || (BufferSize == NULL)) {
    return EFI_INVALID_PARAMETER;
  }

  File        = (RING3_EFI_FILE_PROTOCOL *)This;
  Ring3Buffer = NULL;
  Ring3Pages  = 0;

  PagesNumber = (UINT32)EFI_SIZE_TO_PAGES (sizeof (UINTN *) + *BufferSize);

  Status = CoreAllocatePages (
             AllocateAnyPages,
             EfiRing3MemoryType,
             PagesNumber,
             &Ring3Pages
             );
  if (EFI_ERROR (Status)) {
    return Status;
  }

  Ring3BufferSize = (UINTN *)(UINTN)Ring3Pages;

  DisableSMAP ();
  *Ring3BufferSize = *BufferSize;
  EnableSMAP ();

  if (Buffer != NULL) {
    Ring3Buffer = (VOID *)((UINTN *)(UINTN)Ring3Pages + 1);
  }

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

  *BufferSize = *Ring3BufferSize;
  EnableSMAP ();

  CoreFreePages (Ring3Pages, PagesNumber);

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

#if defined (MDE_CPU_X64) || defined (MDE_CPU_AARCH64)
  return GoToRing3 (
           2,
           (VOID *)mRing3FileProtocol.SetPosition,
           File->Ring3File,
           Position
           );
#elif defined (MDE_CPU_IA32)
  //
  // UINT64 Position is passed as 2 double words on stack.
  //
  return GoToRing3 (
           3,
           (VOID *)mRing3FileProtocol.SetPosition,
           File->Ring3File,
           Position
           );
#else
  return GoToRing3 (
           2,
           (VOID *)mRing3FileProtocol.SetPosition,
           File->Ring3File,
           Position
           );
#endif

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
  EFI_PHYSICAL_ADDRESS    Ring3Position;

  if ((This == NULL) || (Position == NULL)) {
    return EFI_INVALID_PARAMETER;
  }

  File          = (RING3_EFI_FILE_PROTOCOL *)This;
  Ring3Position = 0;

  Status = CoreAllocatePages (
             AllocateAnyPages,
             EfiRing3MemoryType,
             1,
             &Ring3Position
             );
  if (EFI_ERROR (Status)) {
    return Status;
  }

  DisableSMAP ();
  *(UINT64 *)(UINTN)Ring3Position = *Position;
  EnableSMAP ();

  Status = GoToRing3 (
             2,
             (VOID *)mRing3FileProtocol.GetPosition,
             File->Ring3File,
             Ring3Position
             );

  DisableSMAP ();
  *Position = *(UINT64 *)(UINTN)Ring3Position;
  EnableSMAP ();

  CoreFreePages (Ring3Position, 1);

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
  EFI_PHYSICAL_ADDRESS    Ring3Pages;
  UINT32                  PagesNumber;

  if ((This == NULL) || (BufferSize == NULL)) {
    return EFI_INVALID_PARAMETER;
  }

  File                 = (RING3_EFI_FILE_PROTOCOL *)This;
  Ring3Buffer          = NULL;
  Ring3InformationType = NULL;
  Ring3Pages           = 0;

  PagesNumber = (UINT32)EFI_SIZE_TO_PAGES (sizeof (UINTN *) + *BufferSize + sizeof (EFI_GUID));

  Status = CoreAllocatePages (
             AllocateAnyPages,
             EfiRing3MemoryType,
             PagesNumber,
             &Ring3Pages
             );
  if (EFI_ERROR (Status)) {
    return Status;
  }

  Ring3BufferSize = (UINTN *)(UINTN)Ring3Pages;

  DisableSMAP ();
  *Ring3BufferSize = *BufferSize;
  EnableSMAP ();

  if (Buffer != NULL) {
    Ring3Buffer = (VOID *)((UINTN *)(UINTN)Ring3Pages + 1);
  }

  if (InformationType != NULL) {
    Ring3InformationType = (EFI_GUID *)((UINTN)Ring3Pages + sizeof (UINTN *) + *BufferSize);

    DisableSMAP ();
    CopyGuid (Ring3InformationType, InformationType);
    EnableSMAP ();
  }

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

  *BufferSize = *Ring3BufferSize;
  EnableSMAP ();

  CoreFreePages (Ring3Pages, PagesNumber);

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
  EFI_PHYSICAL_ADDRESS    Ring3Pages;
  UINT32                  PagesNumber;

  if ((This == NULL) || (NewHandle == NULL) || (FileName == NULL)) {
    return EFI_INVALID_PARAMETER;
  }

  File           = (RING3_EFI_FILE_PROTOCOL *)This;
  Ring3NewHandle = NULL;
  Ring3FileName  = NULL;
  Ring3Pages     = 0;

  PagesNumber = (UINT32)EFI_SIZE_TO_PAGES (sizeof (EFI_FILE_PROTOCOL *) + StrSize (FileName));

  Status = CoreAllocatePages (
             AllocateAnyPages,
             EfiRing3MemoryType,
             PagesNumber,
             &Ring3Pages
             );
  if (EFI_ERROR (Status)) {
    *NewHandle = NULL;
    return Status;
  }

  Ring3NewHandle = (EFI_FILE_PROTOCOL **)(UINTN)Ring3Pages;
  Ring3FileName  = (CHAR16 *)((EFI_FILE_PROTOCOL **)(UINTN)Ring3Pages + 1);

  DisableSMAP ();
  Status = StrCpyS (Ring3FileName, StrLen (FileName) + 1, FileName);
  EnableSMAP ();
  if (EFI_ERROR (Status)) {
    *NewHandle = NULL;
    CoreFreePages (Ring3Pages, PagesNumber);
    return Status;
  }

#if defined (MDE_CPU_X64) || defined (MDE_CPU_AARCH64)
  Status = GoToRing3 (
             5,
             (VOID *)mRing3FileProtocol.Open,
             File->Ring3File,
             Ring3NewHandle,
             Ring3FileName,
             OpenMode,
             Attributes
             );
#elif defined (MDE_CPU_IA32)
  //
  // UINT64 OpenMode and Attributes are each passed as 2 double words on stack.
  //
  Status = GoToRing3 (
             7,
             (VOID *)mRing3FileProtocol.Open,
             File->Ring3File,
             Ring3NewHandle,
             Ring3FileName,
             OpenMode,
             Attributes
             );
#else
  Status = GoToRing3 (
             5,
             (VOID *)mRing3FileProtocol.Open,
             File->Ring3File,
             Ring3NewHandle,
             Ring3FileName,
             OpenMode,
             Attributes
             );
#endif
  if (EFI_ERROR (Status)) {
    *NewHandle = NULL;
    CoreFreePages (Ring3Pages, PagesNumber);
    return Status;
  }

  NewFile = AllocatePool (sizeof (RING3_EFI_FILE_PROTOCOL));
  if (NewFile == NULL) {
    *NewHandle = NULL;
    CoreFreePages (Ring3Pages, PagesNumber);
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
  EnableSMAP ();

  *NewHandle = (EFI_FILE_PROTOCOL *)NewFile;

  CoreFreePages (Ring3Pages, PagesNumber);

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
  EFI_PHYSICAL_ADDRESS    Physical;

  if (Root == NULL) {
    return EFI_INVALID_PARAMETER;
  }

  Status = CoreAllocatePages (
             AllocateAnyPages,
             EfiRing3MemoryType,
             1,
             &Physical
             );
  if (EFI_ERROR (Status)) {
    *Root = NULL;
    return Status;
  }

  Ring3Root = (EFI_FILE_PROTOCOL **)(UINTN)Physical;

  Status = GoToRing3 (
             2,
             (VOID *)mRing3SimpleFileSystemProtocol.OpenVolume,
             mRing3SimpleFileSystemPointer,
             Ring3Root
             );
  if (EFI_ERROR (Status)) {
    *Root = NULL;
    CoreFreePages (Physical, 1);
    return Status;
  }

  File = AllocatePool (sizeof (RING3_EFI_FILE_PROTOCOL));
  if (File == NULL) {
    *Root = NULL;
    CoreFreePages (Physical, 1);
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

  CoreFreePages (Physical, 1);

  return Status;
}
