/** @file

  Copyright (c) 2024 - 2025, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause

**/

#include "DxeMain.h"
#include "SupportedProtocols.h"

#define MAX_CALL 1

LIST_ENTRY gUserSpaceDriversHead = INITIALIZE_LIST_HEAD_VARIABLE (gUserSpaceDriversHead);

EFI_STATUS
EFIAPI
CallUserSpace (
  IN USER_SPACE_CALL_DATA  *Data,
  IN UINTN                 UserStackTop
  );

EFI_STATUS
EFIAPI
GoToUserSpace (
  IN UINT8              Number,
  IN VOID               *EntryPoint,
  IN USER_SPACE_DRIVER  *UserDriver,
  ...
  )
{
  EFI_STATUS            Status;
  USER_SPACE_CALL_DATA  *Input;
  VA_LIST               Marker;
  UINTN                 Index;
  UINTN                 UserStackTop;
  UINTN                 UserStackBase;

  if (UserDriver->NumberOfCalls > MAX_CALL) {
    return EFI_OUT_OF_RESOURCES;
  }

  UserStackBase = (UINTN)AllocatePages (EFI_SIZE_TO_PAGES (STACK_SIZE));
  if (UserStackBase == 0) {
    return EFI_OUT_OF_RESOURCES;
  }

  UserStackTop = UserStackBase + STACK_SIZE - (sizeof (USER_SPACE_CALL_DATA) + Number * sizeof (UINTN));

  Input = (USER_SPACE_CALL_DATA *)UserStackTop;

  Input->NumberOfArguments = Number;
  Input->EntryPoint        = EntryPoint;

  VA_START (Marker, UserDriver);
  for (Index = 0; Index < Number; ++Index) {
    Input->Arguments[Index] = VA_ARG (Marker, UINTN);
  }
  VA_END (Marker);

  SetUefiImageMemoryAttributes (UserStackBase, STACK_SIZE, EFI_MEMORY_XP | EFI_MEMORY_USER);

  gCpu->SetUserMemoryAttributes (
          gCpu,
          UserDriver->UserPageTable,
          UserStackBase,
          STACK_SIZE,
          EFI_MEMORY_XP | EFI_MEMORY_USER
          );

  ++UserDriver->NumberOfCalls;
  //
  // Reserve space on stack for 4 arguments (X64 NOOPT prerequisite).
  //
  UserStackTop = ALIGN_VALUE (UserStackTop - 8*4 - CPU_STACK_ALIGNMENT, CPU_STACK_ALIGNMENT);

  Status = CallUserSpace (
             Input,
             UserStackTop
             );

  --UserDriver->NumberOfCalls;

  CoreFreePages (UserStackBase, EFI_SIZE_TO_PAGES (STACK_SIZE));

  return Status;
}

STATIC
USER_SPACE_DRIVER *
EFIAPI
FindUserSpaceDriver (
  IN  VOID   *CoreWrapper,
  OUT UINTN  *OldPageTable
  )
{
  LIST_ENTRY         *Link;
  USER_SPACE_DRIVER  *UserDriver;

  ASSERT (OldPageTable != NULL);

  for (Link = gUserSpaceDriversHead.ForwardLink; Link != &gUserSpaceDriversHead; Link = Link->ForwardLink) {
    UserDriver = BASE_CR (Link, USER_SPACE_DRIVER, Link);

    if (UserDriver->CoreWrapper == CoreWrapper) {
      *OldPageTable  = gUserPageTable;
      gUserPageTable = UserDriver->UserPageTable;
      return UserDriver;
    }
  }

  return NULL;
}

EFI_STATUS
EFIAPI
CoreDriverBindingSupported (
  IN EFI_DRIVER_BINDING_PROTOCOL  *This,
  IN EFI_HANDLE                   ControllerHandle,
  IN EFI_DEVICE_PATH_PROTOCOL     *RemainingDevicePath OPTIONAL
  )
{
  EFI_STATUS         Status;
  USER_SPACE_DRIVER  *UserDriver;
  VOID               *EntryPoint;
  UINTN              OldPageTable;

  UserDriver = FindUserSpaceDriver (This, &OldPageTable);
  ASSERT (UserDriver != NULL);

  This = UserDriver->UserSpaceDriver;

  AllowSupervisorAccessToUserMemory ();
  EntryPoint = (VOID *)This->Supported;
  ForbidSupervisorAccessToUserMemory ();

  Status = GoToUserSpace (
             3,
             EntryPoint,
             UserDriver,
             This,
             ControllerHandle,
             RemainingDevicePath
             );

  gUserPageTable = OldPageTable;

  return Status;
}

EFI_STATUS
EFIAPI
CoreDriverBindingStart (
  IN EFI_DRIVER_BINDING_PROTOCOL  *This,
  IN EFI_HANDLE                   ControllerHandle,
  IN EFI_DEVICE_PATH_PROTOCOL     *RemainingDevicePath OPTIONAL
  )
{
  EFI_STATUS         Status;
  USER_SPACE_DRIVER  *UserDriver;
  VOID               *EntryPoint;
  UINTN              OldPageTable;

  UserDriver = FindUserSpaceDriver (This, &OldPageTable);
  ASSERT (UserDriver != NULL);

  This = UserDriver->UserSpaceDriver;

  AllowSupervisorAccessToUserMemory ();
  EntryPoint = (VOID *)This->Start;
  ForbidSupervisorAccessToUserMemory ();

  Status = GoToUserSpace (
             3,
             EntryPoint,
             UserDriver,
             This,
             ControllerHandle,
             RemainingDevicePath
             );

  gUserPageTable = OldPageTable;

  return Status;
}

EFI_STATUS
EFIAPI
CoreDriverBindingStop (
  IN EFI_DRIVER_BINDING_PROTOCOL  *This,
  IN EFI_HANDLE                   ControllerHandle,
  IN UINTN                        NumberOfChildren,
  IN EFI_HANDLE                   *ChildHandleBuffer OPTIONAL
  )
{
  EFI_STATUS         Status;
  USER_SPACE_DRIVER  *UserDriver;
  VOID               *EntryPoint;
  UINTN              OldPageTable;

  UserDriver = FindUserSpaceDriver (This, &OldPageTable);
  ASSERT (UserDriver != NULL);

  This = UserDriver->UserSpaceDriver;

  AllowSupervisorAccessToUserMemory ();
  EntryPoint = (VOID *)This->Stop;
  ForbidSupervisorAccessToUserMemory ();

  Status = GoToUserSpace (
             4,
             EntryPoint,
             UserDriver,
             This,
             ControllerHandle,
             NumberOfChildren,
             ChildHandleBuffer
             );

  gUserPageTable = OldPageTable;

  return Status;
}

STATIC
EFI_STATUS
EFIAPI
CoreFileClose (
  IN EFI_FILE_PROTOCOL  *This
  )
{
  EFI_STATUS         Status;
  USER_SPACE_DRIVER  *UserDriver;
  VOID               *EntryPoint;
  UINTN              OldPageTable;

  UserDriver = FindUserSpaceDriver (This, &OldPageTable);
  ASSERT (UserDriver != NULL);

  This = UserDriver->UserSpaceDriver;

  AllowSupervisorAccessToUserMemory ();
  EntryPoint = (VOID *)This->Close;
  ForbidSupervisorAccessToUserMemory ();

  Status = GoToUserSpace (
             1,
             EntryPoint,
             UserDriver,
             This
             );

  FreePool (UserDriver->CoreWrapper);
  RemoveEntryList (&UserDriver->Link);
  FreePool (UserDriver);

  gUserPageTable = OldPageTable;

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
  IN     EFI_FILE_PROTOCOL  *This,
  IN OUT UINTN              *BufferSize,
     OUT VOID               *Buffer
  )
{
  EFI_STATUS            Status;
  UINTN                 *UserSpaceBufferSize;
  VOID                  *UserSpaceBuffer;
  EFI_PHYSICAL_ADDRESS  UserSpacePages;
  UINT32                PagesNumber;
  USER_SPACE_DRIVER     *UserDriver;
  VOID                  *EntryPoint;
  UINTN                 OldPageTable;

  if ((This == NULL) || (BufferSize == NULL)) {
    return EFI_INVALID_PARAMETER;
  }
  //
  // gUserPageTable must be set before alloctation of EfiUserSpaceMemoryType pages.
  //
  UserDriver = FindUserSpaceDriver (This, &OldPageTable);
  ASSERT (UserDriver != NULL);

  This = UserDriver->UserSpaceDriver;

  UserSpaceBuffer = NULL;
  UserSpacePages  = 0;
  PagesNumber     = (UINT32)EFI_SIZE_TO_PAGES (sizeof (UINTN *) + *BufferSize);

  Status = CoreAllocatePages (
             AllocateAnyPages,
             EfiUserSpaceMemoryType,
             PagesNumber,
             &UserSpacePages
             );
  if (EFI_ERROR (Status)) {
    gUserPageTable = OldPageTable;
    return Status;
  }

  UserSpaceBufferSize = (UINTN *)(UINTN)UserSpacePages;

  AllowSupervisorAccessToUserMemory ();
  *UserSpaceBufferSize = *BufferSize;
  EntryPoint           = (VOID *)This->Read;
  ForbidSupervisorAccessToUserMemory ();

  if (Buffer != NULL) {
    UserSpaceBuffer = (VOID *)((UINTN *)(UINTN)UserSpacePages + 1);
  }

  Status = GoToUserSpace (
             3,
             EntryPoint,
             UserDriver,
             This,
             UserSpaceBufferSize,
             UserSpaceBuffer
             );

  AllowSupervisorAccessToUserMemory ();
  if ((UserSpaceBuffer != NULL) && (Buffer != NULL) && (*BufferSize >= *UserSpaceBufferSize)) {
    CopyMem (Buffer, UserSpaceBuffer, *UserSpaceBufferSize);
  }

  *BufferSize = *UserSpaceBufferSize;
  ForbidSupervisorAccessToUserMemory ();

  CoreFreePages (UserSpacePages, PagesNumber);

  gUserPageTable = OldPageTable;

  return Status;
}

STATIC
EFI_STATUS
EFIAPI
CoreFileWrite (
  IN     EFI_FILE_PROTOCOL  *This,
  IN OUT UINTN              *BufferSize,
  IN     VOID               *Buffer
  )
{
  return EFI_UNSUPPORTED;
}

STATIC
EFI_STATUS
EFIAPI
CoreFileSetPosition (
  IN EFI_FILE_PROTOCOL  *This,
  IN UINT64             Position
  )
{
  EFI_STATUS         Status;
  USER_SPACE_DRIVER  *UserDriver;
  VOID               *EntryPoint;
  UINTN              OldPageTable;

  UserDriver = FindUserSpaceDriver (This, &OldPageTable);
  ASSERT (UserDriver != NULL);

  This = UserDriver->UserSpaceDriver;

  AllowSupervisorAccessToUserMemory ();
  EntryPoint = (VOID *)This->SetPosition;
  ForbidSupervisorAccessToUserMemory ();

#if defined (MDE_CPU_X64) || defined (MDE_CPU_AARCH64)
  Status = GoToUserSpace (
             2,
             EntryPoint,
             UserDriver,
             This,
             Position
             );
#elif defined (MDE_CPU_IA32)
  //
  // UINT64 Position is passed as 2 double words on stack.
  //
  Status = GoToUserSpace (
             3,
             EntryPoint,
             UserDriver,
             This,
             Position
             );
#elif defined (MDE_CPU_ARM)
  //
  // UINT64 Position is passed as 2 words in 2 registers and is aligned on 8 bytes.
  // R0 == This, R1 == NULL, R2 == Position_Low, R3 == Position_High.
  //
  Status = GoToUserSpace (
             4,
             EntryPoint,
             UserDriver,
             This,
             NULL,
             (UINT32)Position,
             (UINT32)(Position >> 32)
             );
#endif

  gUserPageTable = OldPageTable;

  return Status;
}

STATIC
EFI_STATUS
EFIAPI
CoreFileGetPosition (
  IN  EFI_FILE_PROTOCOL  *This,
  OUT UINT64             *Position
  )
{
  EFI_STATUS            Status;
  EFI_PHYSICAL_ADDRESS  UserSpacePosition;
  USER_SPACE_DRIVER     *UserDriver;
  VOID                  *EntryPoint;
  UINTN                 OldPageTable;

  if ((This == NULL) || (Position == NULL)) {
    return EFI_INVALID_PARAMETER;
  }

  UserDriver = FindUserSpaceDriver (This, &OldPageTable);
  ASSERT (UserDriver != NULL);

  This = UserDriver->UserSpaceDriver;

  Status = CoreAllocatePages (
             AllocateAnyPages,
             EfiUserSpaceMemoryType,
             1,
             &UserSpacePosition
             );
  if (EFI_ERROR (Status)) {
    gUserPageTable = OldPageTable;
    return Status;
  }

  AllowSupervisorAccessToUserMemory ();
  *(UINT64 *)(UINTN)UserSpacePosition = *Position;
  EntryPoint                          = (VOID *)This->GetPosition;
  ForbidSupervisorAccessToUserMemory ();

  Status = GoToUserSpace (
             2,
             EntryPoint,
             UserDriver,
             This,
             UserSpacePosition
             );

  AllowSupervisorAccessToUserMemory ();
  *Position = *(UINT64 *)(UINTN)UserSpacePosition;
  ForbidSupervisorAccessToUserMemory ();

  CoreFreePages (UserSpacePosition, 1);

  gUserPageTable = OldPageTable;

  return Status;
}

STATIC
EFI_STATUS
EFIAPI
CoreFileGetInfo (
  IN     EFI_FILE_PROTOCOL  *This,
  IN     EFI_GUID           *InformationType,
  IN OUT UINTN              *BufferSize,
     OUT VOID               *Buffer
  )
{
  EFI_STATUS            Status;
  EFI_GUID              *UserSpaceInformationType;
  UINTN                 *UserSpaceBufferSize;
  VOID                  *UserSpaceBuffer;
  EFI_PHYSICAL_ADDRESS  UserSpacePages;
  UINT32                PagesNumber;
  USER_SPACE_DRIVER     *UserDriver;
  VOID                  *EntryPoint;
  UINTN                 OldPageTable;

  if ((This == NULL) || (BufferSize == NULL)) {
    return EFI_INVALID_PARAMETER;
  }

  UserDriver = FindUserSpaceDriver (This, &OldPageTable);
  ASSERT (UserDriver != NULL);

  This = UserDriver->UserSpaceDriver;

  UserSpaceBuffer          = NULL;
  UserSpaceInformationType = NULL;
  UserSpacePages           = 0;

  PagesNumber = (UINT32)EFI_SIZE_TO_PAGES (sizeof (UINTN *) + *BufferSize + sizeof (EFI_GUID));

  Status = CoreAllocatePages (
             AllocateAnyPages,
             EfiUserSpaceMemoryType,
             PagesNumber,
             &UserSpacePages
             );
  if (EFI_ERROR (Status)) {
    gUserPageTable = OldPageTable;
    return Status;
  }

  UserSpaceBufferSize = (UINTN *)(UINTN)UserSpacePages;

  AllowSupervisorAccessToUserMemory ();
  *UserSpaceBufferSize = *BufferSize;
  EntryPoint           = (VOID *)This->GetInfo;
  ForbidSupervisorAccessToUserMemory ();

  if (Buffer != NULL) {
    UserSpaceBuffer = (VOID *)((UINTN *)(UINTN)UserSpacePages + 1);
  }

  if (InformationType != NULL) {
    UserSpaceInformationType = (EFI_GUID *)((UINTN)UserSpacePages + sizeof (UINTN *) + *BufferSize);

    AllowSupervisorAccessToUserMemory ();
    CopyGuid (UserSpaceInformationType, InformationType);
    ForbidSupervisorAccessToUserMemory ();
  }

  Status = GoToUserSpace (
             4,
             EntryPoint,
             UserDriver,
             This,
             UserSpaceInformationType,
             UserSpaceBufferSize,
             UserSpaceBuffer
             );

  AllowSupervisorAccessToUserMemory ();
  if ((UserSpaceBuffer != NULL) && (Buffer != NULL) && (*BufferSize >= *UserSpaceBufferSize)) {
    CopyMem (Buffer, UserSpaceBuffer, *UserSpaceBufferSize);
  }

  *BufferSize = *UserSpaceBufferSize;
  ForbidSupervisorAccessToUserMemory ();

  CoreFreePages (UserSpacePages, PagesNumber);

  gUserPageTable = OldPageTable;

  return Status;
}

STATIC
EFI_STATUS
EFIAPI
CoreFileSetInfo (
  IN EFI_FILE_PROTOCOL  *This,
  IN EFI_GUID           *InformationType,
  IN UINTN              BufferSize,
  IN VOID               *Buffer
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
  IN     EFI_FILE_PROTOCOL  *This,
     OUT EFI_FILE_PROTOCOL  **NewHandle,
  IN     CHAR16             *FileName,
  IN     UINT64             OpenMode,
  IN     UINT64             Attributes,
  IN OUT EFI_FILE_IO_TOKEN  *Token
  )
{
  return EFI_UNSUPPORTED;
}

STATIC
EFI_STATUS
EFIAPI
CoreFileReadEx (
  IN     EFI_FILE_PROTOCOL  *This,
  IN OUT EFI_FILE_IO_TOKEN  *Token
  )
{
  return EFI_UNSUPPORTED;
}

STATIC
EFI_STATUS
EFIAPI
CoreFileWriteEx (
  IN     EFI_FILE_PROTOCOL  *This,
  IN OUT EFI_FILE_IO_TOKEN  *Token
  )
{
  return EFI_UNSUPPORTED;
}

STATIC
EFI_STATUS
EFIAPI
CoreFileFlushEx (
  IN     EFI_FILE_PROTOCOL  *This,
  IN OUT EFI_FILE_IO_TOKEN  *Token
  )
{
  return EFI_UNSUPPORTED;
}

STATIC
EFI_STATUS
EFIAPI
CoreFileOpen (
  IN  EFI_FILE_PROTOCOL  *This,
  OUT EFI_FILE_PROTOCOL  **NewHandle,
  IN  CHAR16             *FileName,
  IN  UINT64             OpenMode,
  IN  UINT64             Attributes
  )
{
  EFI_STATUS            Status;
  EFI_FILE_PROTOCOL     *NewFile;
  EFI_FILE_PROTOCOL     **UserSpaceNewHandle;
  CHAR16                *UserSpaceFileName;
  EFI_PHYSICAL_ADDRESS  UserSpacePages;
  UINT32                PagesNumber;
  USER_SPACE_DRIVER     *UserDriver;
  USER_SPACE_DRIVER     *NewDriver;
  VOID                  *EntryPoint;
  UINTN                 OldPageTable;

  if ((This == NULL) || (NewHandle == NULL) || (FileName == NULL)) {
    return EFI_INVALID_PARAMETER;
  }

  UserDriver = FindUserSpaceDriver (This, &OldPageTable);
  ASSERT (UserDriver != NULL);

  This = UserDriver->UserSpaceDriver;

  UserSpaceNewHandle = NULL;
  UserSpaceFileName  = NULL;
  UserSpacePages     = 0;

  PagesNumber = (UINT32)EFI_SIZE_TO_PAGES (sizeof (EFI_FILE_PROTOCOL *) + StrSize (FileName));

  Status = CoreAllocatePages (
             AllocateAnyPages,
             EfiUserSpaceMemoryType,
             PagesNumber,
             &UserSpacePages
             );
  if (EFI_ERROR (Status)) {
    *NewHandle = NULL;
    gUserPageTable = OldPageTable;
    return Status;
  }

  UserSpaceNewHandle = (EFI_FILE_PROTOCOL **)(UINTN)UserSpacePages;
  UserSpaceFileName  = (CHAR16 *)((EFI_FILE_PROTOCOL **)(UINTN)UserSpacePages + 1);

  AllowSupervisorAccessToUserMemory ();
  Status     = StrCpyS (UserSpaceFileName, StrLen (FileName) + 1, FileName);
  EntryPoint = (VOID *)This->Open;
  ForbidSupervisorAccessToUserMemory ();
  if (EFI_ERROR (Status)) {
    *NewHandle = NULL;
    CoreFreePages (UserSpacePages, PagesNumber);
    gUserPageTable = OldPageTable;
    return Status;
  }

#if defined (MDE_CPU_X64) || defined (MDE_CPU_AARCH64)
  Status = GoToUserSpace (
             5,
             EntryPoint,
             UserDriver,
             This,
             UserSpaceNewHandle,
             UserSpaceFileName,
             OpenMode,
             Attributes
             );
#elif defined (MDE_CPU_IA32)
  //
  // UINT64 OpenMode and Attributes are each passed as 2 double words on stack.
  //
  Status = GoToUserSpace (
             7,
             EntryPoint,
             UserDriver,
             This,
             UserSpaceNewHandle,
             UserSpaceFileName,
             OpenMode,
             Attributes
             );
#elif defined (MDE_CPU_ARM)
  //
  // UINT64 OpenMode and Attributes are each passed as 2 words on stack.
  // Each of them is aligned on 8 bytes.
  // R0 == This, R1 == UserSpaceNewHandle, R2 == UserSpaceFileName, R3 == NULL,
  // [SP] == OpenMode, [SP + 8] == Attributes.
  //
  Status = GoToUserSpace (
             8,
             EntryPoint,
             UserDriver,
             This,
             UserSpaceNewHandle,
             UserSpaceFileName,
             NULL,
             (UINT32)OpenMode,
             (UINT32)(OpenMode >> 32),
             (UINT32)Attributes,
             (UINT32)(Attributes >> 32)
             );
#endif
  if (EFI_ERROR (Status)) {
    *NewHandle = NULL;
    CoreFreePages (UserSpacePages, PagesNumber);
    gUserPageTable = OldPageTable;
    return Status;
  }

  NewFile = AllocatePool (sizeof (EFI_FILE_PROTOCOL));
  if (NewFile == NULL) {
    *NewHandle = NULL;
    CoreFreePages (UserSpacePages, PagesNumber);
    gUserPageTable = OldPageTable;
    return EFI_OUT_OF_RESOURCES;
  }

  NewDriver = AllocatePool (sizeof (USER_SPACE_DRIVER));
  if (NewDriver == NULL) {
    *NewHandle = NULL;
    FreePool (NewFile);
    CoreFreePages (UserSpacePages, PagesNumber);
    gUserPageTable = OldPageTable;
    return EFI_OUT_OF_RESOURCES;
  }

  NewDriver->CoreWrapper   = NewFile;
  NewDriver->UserPageTable = UserDriver->UserPageTable;
  NewDriver->NumberOfCalls = 0;

  AllowSupervisorAccessToUserMemory ();
  NewDriver->UserSpaceDriver = *UserSpaceNewHandle;
  NewFile->Revision          = (*UserSpaceNewHandle)->Revision;
  ForbidSupervisorAccessToUserMemory ();

  InsertTailList (&gUserSpaceDriversHead, &NewDriver->Link);

  NewFile->Open        = CoreFileOpen;
  NewFile->Close       = CoreFileClose;
  NewFile->Delete      = CoreFileDelete;
  NewFile->Read        = CoreFileRead;
  NewFile->Write       = CoreFileWrite;
  NewFile->GetPosition = CoreFileGetPosition;
  NewFile->SetPosition = CoreFileSetPosition;
  NewFile->GetInfo     = CoreFileGetInfo;
  NewFile->SetInfo     = CoreFileSetInfo;
  NewFile->Flush       = CoreFileFlush;
  NewFile->OpenEx      = CoreFileOpenEx;
  NewFile->ReadEx      = CoreFileReadEx;
  NewFile->WriteEx     = CoreFileWriteEx;
  NewFile->FlushEx     = CoreFileFlushEx;

  *NewHandle = (EFI_FILE_PROTOCOL *)NewFile;

  CoreFreePages (UserSpacePages, PagesNumber);

  gUserPageTable = OldPageTable;

  return Status;
}

EFI_STATUS
EFIAPI
CoreSimpleFileSystemOpenVolume (
  IN  EFI_SIMPLE_FILE_SYSTEM_PROTOCOL  *This,
  OUT EFI_FILE_PROTOCOL                 **Root
  )
{
  EFI_STATUS            Status;
  EFI_FILE_PROTOCOL     **UserSpaceRoot;
  EFI_FILE_PROTOCOL     *File;
  EFI_PHYSICAL_ADDRESS  Physical;
  USER_SPACE_DRIVER     *UserDriver;
  USER_SPACE_DRIVER     *NewDriver;
  VOID                  *EntryPoint;
  UINTN                 OldPageTable;

  if (Root == NULL) {
    return EFI_INVALID_PARAMETER;
  }

  UserDriver = FindUserSpaceDriver (This, &OldPageTable);
  ASSERT (UserDriver != NULL);

  This = UserDriver->UserSpaceDriver;

  AllowSupervisorAccessToUserMemory ();
  EntryPoint = (VOID *)This->OpenVolume;
  ForbidSupervisorAccessToUserMemory ();

  Status = CoreAllocatePages (
             AllocateAnyPages,
             EfiUserSpaceMemoryType,
             1,
             &Physical
             );
  if (EFI_ERROR (Status)) {
    *Root = NULL;
    gUserPageTable = OldPageTable;
    return Status;
  }

  UserSpaceRoot = (EFI_FILE_PROTOCOL **)(UINTN)Physical;

  Status = GoToUserSpace (
             2,
             EntryPoint,
             UserDriver,
             This,
             UserSpaceRoot
             );
  if (EFI_ERROR (Status)) {
    *Root = NULL;
    CoreFreePages (Physical, 1);
    gUserPageTable = OldPageTable;
    return Status;
  }

  File = AllocatePool (sizeof (EFI_FILE_PROTOCOL));
  if (File == NULL) {
    *Root = NULL;
    CoreFreePages (Physical, 1);
    gUserPageTable = OldPageTable;
    return EFI_OUT_OF_RESOURCES;
  }

  NewDriver = AllocatePool (sizeof (USER_SPACE_DRIVER));
  if (NewDriver == NULL) {
    *Root = NULL;
    FreePool (File);
    CoreFreePages (Physical, 1);
    gUserPageTable = OldPageTable;
    return EFI_OUT_OF_RESOURCES;
  }

  NewDriver->CoreWrapper   = File;
  NewDriver->UserPageTable = UserDriver->UserPageTable;
  NewDriver->NumberOfCalls = 0;

  AllowSupervisorAccessToUserMemory ();
  NewDriver->UserSpaceDriver = *UserSpaceRoot;
  File->Revision             = (*UserSpaceRoot)->Revision;
  ForbidSupervisorAccessToUserMemory ();

  InsertTailList (&gUserSpaceDriversHead, &NewDriver->Link);

  File->Open        = CoreFileOpen;
  File->Close       = CoreFileClose;
  File->Delete      = CoreFileDelete;
  File->Read        = CoreFileRead;
  File->Write       = CoreFileWrite;
  File->GetPosition = CoreFileGetPosition;
  File->SetPosition = CoreFileSetPosition;
  File->GetInfo     = CoreFileGetInfo;
  File->SetInfo     = CoreFileSetInfo;
  File->Flush       = CoreFileFlush;
  File->OpenEx      = CoreFileOpenEx;
  File->ReadEx      = CoreFileReadEx;
  File->WriteEx     = CoreFileWriteEx;
  File->FlushEx     = CoreFileFlushEx;

  *Root = (EFI_FILE_PROTOCOL *)File;

  CoreFreePages (Physical, 1);

  gUserPageTable = OldPageTable;

  return Status;
}

INTN
EFIAPI
CoreUnicodeCollationStriColl (
  IN EFI_UNICODE_COLLATION_PROTOCOL  *This,
  IN CHAR16                          *Str1,
  IN CHAR16                          *Str2
  )
{
  EFI_STATUS            Status;
  EFI_PHYSICAL_ADDRESS  UserMem;
  USER_SPACE_DRIVER     *UserDriver;
  VOID                  *EntryPoint;
  UINTN                 Size1;
  UINTN                 Size2;
  UINTN                 OldPageTable;

  UserDriver = FindUserSpaceDriver (This, &OldPageTable);
  ASSERT (UserDriver != NULL);

  This = UserDriver->UserSpaceDriver;

  Size1 = StrSize (Str1);
  Size2 = StrSize (Str2);

  Status = CoreAllocatePages (
             AllocateAnyPages,
             EfiUserSpaceMemoryType,
             EFI_SIZE_TO_PAGES (Size1 + Size2),
             &UserMem
             );
  if (EFI_ERROR (Status)) {
    gUserPageTable = OldPageTable;
    return 0;
  }

  AllowSupervisorAccessToUserMemory ();
  CopyMem ((VOID *)(UINTN)UserMem, (VOID *)Str1, Size1);
  CopyMem ((VOID *)((UINTN)UserMem + Size1), (VOID *)Str2, Size2);
  EntryPoint = (VOID *)This->StriColl;
  ForbidSupervisorAccessToUserMemory ();

  Status = GoToUserSpace (
             3,
             EntryPoint,
             UserDriver,
             This,
             (UINTN)UserMem,
             (UINTN)UserMem + Size1
             );

  CoreFreePages (UserMem, EFI_SIZE_TO_PAGES (Size1 + Size2));

  gUserPageTable = OldPageTable;

  return (INTN)Status;
}

BOOLEAN
EFIAPI
CoreUnicodeCollationMetaiMatch (
  IN EFI_UNICODE_COLLATION_PROTOCOL  *This,
  IN CHAR16                          *String,
  IN CHAR16                          *Pattern
  )
{
  EFI_STATUS            Status;
  EFI_PHYSICAL_ADDRESS  UserMem;
  USER_SPACE_DRIVER     *UserDriver;
  VOID                  *EntryPoint;
  UINTN                 Size1;
  UINTN                 Size2;
  UINTN                 OldPageTable;

  UserDriver = FindUserSpaceDriver (This, &OldPageTable);
  ASSERT (UserDriver != NULL);

  This = UserDriver->UserSpaceDriver;

  Size1 = StrSize (String);
  Size2 = StrSize (Pattern);

  Status = CoreAllocatePages (
             AllocateAnyPages,
             EfiUserSpaceMemoryType,
             EFI_SIZE_TO_PAGES (Size1 + Size2),
             &UserMem
             );
  if (EFI_ERROR (Status)) {
    gUserPageTable = OldPageTable;
    return FALSE;
  }

  AllowSupervisorAccessToUserMemory ();
  CopyMem ((VOID *)(UINTN)UserMem, (VOID *)String, Size1);
  CopyMem ((VOID *)((UINTN)UserMem + Size1), (VOID *)Pattern, Size2);
  EntryPoint = (VOID *)This->MetaiMatch;
  ForbidSupervisorAccessToUserMemory ();

  Status = GoToUserSpace (
             3,
             EntryPoint,
             UserDriver,
             This,
             (UINTN)UserMem,
             (UINTN)UserMem + Size1
             );

  CoreFreePages (UserMem, EFI_SIZE_TO_PAGES (Size1 + Size2));

  gUserPageTable = OldPageTable;

  return (BOOLEAN)Status;
}

VOID
EFIAPI
CoreUnicodeCollationStrLwr (
  IN     EFI_UNICODE_COLLATION_PROTOCOL  *This,
  IN OUT CHAR16                          *Str
  )
{
  EFI_STATUS            Status;
  EFI_PHYSICAL_ADDRESS  UserMem;
  USER_SPACE_DRIVER     *UserDriver;
  VOID                  *EntryPoint;
  UINTN                 Size1;
  UINTN                 OldPageTable;

  UserDriver = FindUserSpaceDriver (This, &OldPageTable);
  ASSERT (UserDriver != NULL);

  This = UserDriver->UserSpaceDriver;

  Size1 = StrSize (Str);

  Status = CoreAllocatePages (
             AllocateAnyPages,
             EfiUserSpaceMemoryType,
             EFI_SIZE_TO_PAGES (Size1),
             &UserMem
             );
  if (EFI_ERROR (Status)) {
    gUserPageTable = OldPageTable;
    return;
  }

  AllowSupervisorAccessToUserMemory ();
  CopyMem ((VOID *)(UINTN)UserMem, (VOID *)Str, Size1);
  EntryPoint = (VOID *)This->StrLwr;
  ForbidSupervisorAccessToUserMemory ();

  Status = GoToUserSpace (
             2,
             EntryPoint,
             UserDriver,
             This,
             (UINTN)UserMem
             );

  AllowSupervisorAccessToUserMemory ();
  CopyMem ((VOID *)Str, (VOID *)(UINTN)UserMem, Size1);
  ForbidSupervisorAccessToUserMemory ();

  CoreFreePages (UserMem, EFI_SIZE_TO_PAGES (Size1));

  gUserPageTable = OldPageTable;
}

VOID
EFIAPI
CoreUnicodeCollationStrUpr (
  IN     EFI_UNICODE_COLLATION_PROTOCOL  *This,
  IN OUT CHAR16                          *Str
  )
{
  EFI_STATUS            Status;
  EFI_PHYSICAL_ADDRESS  UserMem;
  USER_SPACE_DRIVER     *UserDriver;
  VOID                  *EntryPoint;
  UINTN                 Size1;
  UINTN                 OldPageTable;

  UserDriver = FindUserSpaceDriver (This, &OldPageTable);
  ASSERT (UserDriver != NULL);

  This = UserDriver->UserSpaceDriver;

  Size1 = StrSize (Str);

  Status = CoreAllocatePages (
             AllocateAnyPages,
             EfiUserSpaceMemoryType,
             EFI_SIZE_TO_PAGES (Size1),
             &UserMem
             );
  if (EFI_ERROR (Status)) {
    gUserPageTable = OldPageTable;
    return;
  }

  AllowSupervisorAccessToUserMemory ();
  CopyMem ((VOID *)(UINTN)UserMem, (VOID *)Str, Size1);
  EntryPoint = (VOID *)This->StrUpr;
  ForbidSupervisorAccessToUserMemory ();

  Status = GoToUserSpace (
             2,
             EntryPoint,
             UserDriver,
             This,
             (UINTN)UserMem
             );

  AllowSupervisorAccessToUserMemory ();
  CopyMem ((VOID *)Str, (VOID *)(UINTN)UserMem, Size1);
  ForbidSupervisorAccessToUserMemory ();

  CoreFreePages (UserMem, EFI_SIZE_TO_PAGES (Size1));

  gUserPageTable = OldPageTable;
}

VOID
EFIAPI
CoreUnicodeCollationFatToStr (
  IN  EFI_UNICODE_COLLATION_PROTOCOL  *This,
  IN  UINTN                           FatSize,
  IN  CHAR8                           *Fat,
  OUT CHAR16                          *String
  )
{
  EFI_STATUS            Status;
  EFI_PHYSICAL_ADDRESS  UserMem;
  USER_SPACE_DRIVER     *UserDriver;
  VOID                  *EntryPoint;
  UINTN                 OldPageTable;

  UserDriver = FindUserSpaceDriver (This, &OldPageTable);
  ASSERT (UserDriver != NULL);

  This = UserDriver->UserSpaceDriver;

  Status = CoreAllocatePages (
             AllocateAnyPages,
             EfiUserSpaceMemoryType,
             EFI_SIZE_TO_PAGES (FatSize * 3),
             &UserMem
             );
  if (EFI_ERROR (Status)) {
    gUserPageTable = OldPageTable;
    return;
  }

  AllowSupervisorAccessToUserMemory ();
  CopyMem ((VOID *)(UINTN)UserMem, (VOID *)Fat, FatSize);
  EntryPoint = (VOID *)This->FatToStr;
  ForbidSupervisorAccessToUserMemory ();

  Status = GoToUserSpace (
             4,
             EntryPoint,
             UserDriver,
             This,
             FatSize,
             (UINTN)UserMem,
             (UINTN)UserMem + FatSize
             );

  AllowSupervisorAccessToUserMemory ();
  CopyMem ((VOID *)String, (VOID *)((UINTN)UserMem + FatSize), FatSize * 2);
  ForbidSupervisorAccessToUserMemory ();

  CoreFreePages (UserMem, EFI_SIZE_TO_PAGES (FatSize * 3));

  gUserPageTable = OldPageTable;
}

BOOLEAN
EFIAPI
CoreUnicodeCollationStrToFat (
  IN  EFI_UNICODE_COLLATION_PROTOCOL  *This,
  IN  CHAR16                          *String,
  IN  UINTN                           FatSize,
  OUT CHAR8                           *Fat
  )
{
  EFI_STATUS            Status;
  EFI_PHYSICAL_ADDRESS  UserMem;
  USER_SPACE_DRIVER     *UserDriver;
  VOID                  *EntryPoint;
  UINTN                 Size1;
  UINTN                 OldPageTable;

  UserDriver = FindUserSpaceDriver (This, &OldPageTable);
  ASSERT (UserDriver != NULL);

  This = UserDriver->UserSpaceDriver;

  Size1 = StrSize (String);

  Status = CoreAllocatePages (
             AllocateAnyPages,
             EfiUserSpaceMemoryType,
             EFI_SIZE_TO_PAGES (FatSize + Size1),
             &UserMem
             );
  if (EFI_ERROR (Status)) {
    gUserPageTable = OldPageTable;
    return FALSE;
  }

  AllowSupervisorAccessToUserMemory ();
  CopyMem ((VOID *)(UINTN)UserMem, (VOID *)String, Size1);
  EntryPoint = (VOID *)This->StrToFat;
  ForbidSupervisorAccessToUserMemory ();

  Status = GoToUserSpace (
             4,
             EntryPoint,
             UserDriver,
             This,
             (UINTN)UserMem,
             FatSize,
             (UINTN)UserMem + Size1
             );

  AllowSupervisorAccessToUserMemory ();
  CopyMem ((VOID *)Fat, (VOID *)((UINTN)UserMem + Size1), FatSize);
  ForbidSupervisorAccessToUserMemory ();

  CoreFreePages (UserMem, EFI_SIZE_TO_PAGES (FatSize + Size1));

  gUserPageTable = OldPageTable;

  return (BOOLEAN)Status;
}
