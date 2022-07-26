/** @file
  EFI_FILE_PROTOCOL implementation for EXT4

  Copyright (c) 2021 Pedro Falcato All rights reserved.
  SPDX-License-Identifier: BSD-2-Clause-Patent
**/

#include "Ext4Dxe.h"

#include <Library/BaseUcs2Utf8Lib.h>

/**
   Duplicates a file structure.

   @param[in]        Original    Pointer to the original file.

   @return Pointer to the new file structure.
**/
STATIC
EXT4_FILE *
Ext4DuplicateFile (
  IN CONST EXT4_FILE  *Original
  );

/**
   Gets the next path segment.

   @param[in]        Path        Pointer to the rest of the path.
   @param[out]       PathSegment Pointer to the buffer that will hold the path segment.
                                 Note: It's necessarily EXT4_NAME_MAX +1 long.
   @param[out]       Length      Pointer to the UINTN that will hold the length of the path segment.

   @retval !EFI_SUCCESS          The path segment is too large(> EXT4_NAME_MAX).
**/
STATIC
EFI_STATUS
GetPathSegment (
  IN CONST CHAR16  *Path,
  OUT CHAR16       *PathSegment,
  OUT UINTN        *Length
  )
{
  CONST CHAR16  *Start;
  CONST CHAR16  *End;

  Start = Path;
  End   = Path;

  // The path segment ends on a backslash or a null terminator
  for ( ; *End != L'\0' && *End != L'\\'; End++) {
  }

  *Length = End - Start;

  return StrnCpyS (PathSegment, EXT4_NAME_MAX, Start, End - Start);
}

/**
   Detects if we have more path segments on the path.

   @param[in] Path   Pointer to the rest of the path.
   @return           True if we're on the last segment, false if there are more
                     segments.
**/
STATIC
BOOLEAN
Ext4IsLastPathSegment (
  IN CONST CHAR16  *Path
  )
{
  while (Path[0] == L'\\') {
    Path++;
  }

  return Path[0] == '\0';
}

#define EXT4_INO_PERM_READ_OWNER   0400
#define EXT4_INO_PERM_WRITE_OWNER  0200
#define EXT4_INO_PERM_EXEC_OWNER   0100

/**
   Detects if we have permissions to open the file on the desired mode.

   @param[in out] File         Pointer to the file we're opening.
   @param[in]     OpenMode     Mode in which to open the file.

   @return           True if the open was succesful, false if we don't have
                     enough permissions.
**/
STATIC
BOOLEAN
Ext4ApplyPermissions (
  IN OUT EXT4_FILE  *File,
  IN UINT64         OpenMode
  )
{
  UINT16  NeededPerms;

  NeededPerms = 0;

  if ((OpenMode & EFI_FILE_MODE_READ) != 0) {
    NeededPerms |= EXT4_INO_PERM_READ_OWNER;
  }

  if ((OpenMode & EFI_FILE_MODE_WRITE) != 0) {
    NeededPerms |= EXT4_INO_PERM_WRITE_OWNER;
  }

  if ((File->Inode->i_mode & NeededPerms) != NeededPerms) {
    return FALSE;
  }

  File->OpenMode = OpenMode;

  return TRUE;
}

/**
   Detects if we have permissions to search on the directory.

   @param[in out] File         Pointer to the open directory.

   @return           True if we have permission to search, else false.
**/
STATIC
BOOLEAN
Ext4DirCanLookup (
  IN CONST EXT4_FILE  *File
  )
{
  // In UNIX, executable permission on directories means that we have permission to look up
  // files in a directory.
  return (File->Inode->i_mode & EXT4_INO_PERM_EXEC_OWNER) == EXT4_INO_PERM_EXEC_OWNER;
}

/**
  Reads a fast symlink file.

  @param[in]      Partition   Pointer to the ext4 partition.
  @param[in]      File        Pointer to the open symlink file.
  @param[out]     AsciiSymlink     Pointer to the output ascii symlink string.
  @param[out]     AsciiSymlinkSize Pointer to the output ascii symlink string length.

  @retval EFI_SUCCESS           Fast symlink was read.
  @retval EFI_OUT_OF_RESOURCES  Memory allocation error.
**/
STATIC
EFI_STATUS
Ext4ReadFastSymlink (
  IN     EXT4_PARTITION  *Partition,
  IN     EXT4_FILE       *File,
  OUT    CHAR8           **AsciiSymlink,
  OUT    UINTN           *AsciiSymlinkSize
  )
{
  EFI_STATUS  Status;
  CHAR8       *AsciiSymlinkTmp;

  AsciiSymlinkTmp = AllocateZeroPool (EXT4_FAST_SYMLINK_SIZE + 1);
  if (AsciiSymlinkTmp == NULL) {
    Status = EFI_OUT_OF_RESOURCES;
    DEBUG ((DEBUG_FS, "[ext4] Failed to allocate symlink ascii string buffer\n"));
    return Status;
  }

  CopyMem (AsciiSymlinkTmp, (CONST CHAR8 *) File->Inode->i_data, EXT4_FAST_SYMLINK_SIZE);

  //
  // Add null-terminator
  //
  AsciiSymlinkTmp[EXT4_FAST_SYMLINK_SIZE] = '\0';

  *AsciiSymlink = AsciiSymlinkTmp;
  *AsciiSymlinkSize = EXT4_FAST_SYMLINK_SIZE;

  Status = EFI_SUCCESS;
  return Status;
}

/**
  Reads a slow symlink file.

  @param[in]      Partition        Pointer to the ext4 partition.
  @param[in]      File             Pointer to the open symlink file.
  @param[out]     AsciiSymlink     Pointer to the output ascii symlink string.
  @param[out]     AsciiSymlinkSize Pointer to the output ascii symlink string length.

  @retval EFI_SUCCESS           Slow symlink was read.
  @retval EFI_OUT_OF_RESOURCES  Memory allocation error.
  @retval EFI_INVALID_PARAMETER Slow symlink path has incorrect length
  @retval EFI_VOLUME_CORRUPTED  Symlink read block size differ from inode value
**/
STATIC
EFI_STATUS
Ext4ReadSlowSymlink (
  IN     EXT4_PARTITION  *Partition,
  IN     EXT4_FILE       *File,
  OUT    CHAR8           **AsciiSymlink,
  OUT    UINTN           *AsciiSymlinkSize
  )
{
  EFI_STATUS  Status;
  CHAR8       *SymlinkTmp;
  UINTN       SymlinkSizeTmp;
  UINTN       SymlinkAllocateSize;

  SymlinkSizeTmp = (UINTN) EXT4_INODE_SIZE(File->Inode) & MAX_UINTN;

  //
  // Allocate EXT4_INODE_SIZE + 1
  //
  if (EFI_PATH_MAX - SymlinkSizeTmp >= 1) {
    SymlinkAllocateSize = SymlinkSizeTmp + 1;
  } else {
    Status = EFI_INVALID_PARAMETER;
    DEBUG ((
      DEBUG_FS,
      "[ext4] Error! Symlink path maximum length was hit!\n"
      ));
    return Status;
  }

  SymlinkTmp = AllocateZeroPool (SymlinkAllocateSize);
  if (SymlinkTmp == NULL) {
    Status = EFI_OUT_OF_RESOURCES;
    DEBUG ((DEBUG_FS, "[ext4] Failed to allocate symlink ascii string buffer\n"));
    return Status;
  }

  Status = Ext4Read (Partition, File, SymlinkTmp, File->Position, &SymlinkSizeTmp);
  if (!EFI_ERROR (Status)) {
    File->Position += SymlinkSizeTmp;
  } else {
    DEBUG ((DEBUG_FS, "[ext4] Failed to read symlink from blocks with Status %r\n", Status));
    FreePool (SymlinkTmp);
    return Status;
  }

  //
  // Add null-terminator
  //
  SymlinkTmp[SymlinkSizeTmp] = '\0';

  if (SymlinkSizeTmp != EXT4_INODE_SIZE (File->Inode)
      || SymlinkAllocateSize != AsciiStrSize (SymlinkTmp)) {
    Status = EFI_VOLUME_CORRUPTED;
    DEBUG ((
      DEBUG_FS,
      "[ext4] Error! The sz of the read block doesn't match the value from the inode!\n"
      ));
    return Status;
  }

  *AsciiSymlinkSize = SymlinkSizeTmp;
  *AsciiSymlink = SymlinkTmp;

  Status = EFI_SUCCESS;
  return Status;
}

/**
  Reads a symlink file.

  @param[in]      Partition   Pointer to the ext4 partition.
  @param[in]      File        Pointer to the open symlink file.
  @param[out]     Symlink     Pointer to the output unicode symlink string.

  @retval EFI_SUCCESS           Symlink was read.
  @retval EFI_ACCESS_DENIED     Symlink is encrypted.
  @retval EFI_OUT_OF_RESOURCES  Memory allocation error.
  @retval EFI_INVALID_PARAMETER Symlink path has incorrect length
  @retval EFI_VOLUME_CORRUPTED  Symlink read block size differ from inode value
**/
EFI_STATUS
Ext4ReadSymlink (
  IN     EXT4_PARTITION  *Partition,
  IN     EXT4_FILE       *File,
  OUT    CHAR16          **Symlink
  )
{
  EFI_STATUS  Status;
  CHAR8       *SymlinkTmp;
  UINTN       SymlinkSize;
  UINTN       SymlinkAllocateSize;
  CHAR16      *Symlink16Tmp;
  CHAR16      *Needle;

  //
  // Assume that we alread read Inode via Ext4ReadInode
  // Skip reading, just check encryption flag
  //
  if ((File->Inode->i_flags & EXT4_ENCRYPT_FL) != 0) {
    Status = EFI_ACCESS_DENIED;
    DEBUG ((DEBUG_FS, "[ext4] Error, symlink is encrypted\n"));
    return Status;
  }

  if (Ext4SymlinkIsFastSymlink(File)) {
    Status = Ext4ReadFastSymlink (Partition, File, &SymlinkTmp, &SymlinkSize);
  } else {
    Status = Ext4ReadSlowSymlink (Partition, File, &SymlinkTmp, &SymlinkSize);
  }

  if (EFI_ERROR (Status)) {
    DEBUG ((DEBUG_FS, "[ext4] Symlink read error with Status %r\n", Status));
    return Status;
  }

  SymlinkAllocateSize = SymlinkSize + 1;

  Symlink16Tmp = AllocateZeroPool (SymlinkAllocateSize * sizeof (CHAR16));
  if (Symlink16Tmp == NULL) {
    Status = EFI_OUT_OF_RESOURCES;
    DEBUG ((DEBUG_FS, "[ext4] Failed to allocate symlink unicode string buffer\n"));
    FreePool (SymlinkTmp);
    return Status;
  }

  Status = AsciiStrToUnicodeStrS (
    SymlinkTmp,
    Symlink16Tmp,
    SymlinkSize * sizeof (CHAR16)
    );

  if (EFI_ERROR (Status)) {
    DEBUG ((
      DEBUG_FS,
      "[ext4] Failed to convert ascii symlink to unicode with Status %r\n",
      Status
      ));
    FreePool (SymlinkTmp);
    FreePool (Symlink16Tmp);
    return Status;
  }

  FreePool (SymlinkTmp);

  //
  // Convert to UEFI slashes
  //
  Needle = Symlink16Tmp;
  while ((Needle = StrStr (Needle, L"/")) != NULL) {
    *Needle++ = L'\\';
  }

  *Symlink = Symlink16Tmp;

  Status = EFI_SUCCESS;

  return Status;
}

/**
  Opens a new file relative to the source file's location.

  @param[in]  Source     A pointer to the EXT4_FILE instance that is the file
                         handle to the source location. This would typically be an open
                         handle to a directory.
  @param[out] FoundFile  A pointer to the location to return the opened handle for the new
                         file.
  @param[in]  FileName   The Null-terminated string of the name of the file to be opened.
                         The file name may contain the following path modifiers: "\", ".",
                         and "..".
  @param[in]  OpenMode   The mode to open the file. The only valid combinations that the
                         file may be opened with are: Read, Read/Write, or Create/Read/Write.
  @param[in]  Attributes Only valid for EFI_FILE_MODE_CREATE, in which case these are the
                         attribute bits for the newly created file.

  @retval EFI_SUCCESS          The file was opened.
  @retval EFI_NOT_FOUND        The specified file could not be found on the device.
  @retval EFI_NO_MEDIA         The device has no medium.
  @retval EFI_MEDIA_CHANGED    The device has a different medium in it or the medium is no
                               longer supported.
  @retval EFI_DEVICE_ERROR     The device reported an error.
  @retval EFI_VOLUME_CORRUPTED The file system structures are corrupted.
  @retval EFI_WRITE_PROTECTED  An attempt was made to create a file, or open a file for write
                               when the media is write-protected.
  @retval EFI_ACCESS_DENIED    The service denied access to the file.
  @retval EFI_OUT_OF_RESOURCES Not enough resources were available to open the file.
  @retval EFI_VOLUME_FULL      The volume is full.

**/
EFI_STATUS
Ext4OpenInternal (
  IN EXT4_FILE           *Source,
  OUT EXT4_FILE          **FoundFile,
  IN CHAR16              *FileName,
  IN UINT64              OpenMode,
  IN UINT64              Attributes
  )
{
  EXT4_FILE       *Current;
  EXT4_PARTITION  *Partition;
  UINTN           Level;
  CHAR16          PathSegment[EXT4_NAME_MAX + 1];
  UINTN           Length;
  EXT4_FILE       *File;
  CHAR16          *Symlink;
  EFI_STATUS      Status;

  Current   = Source;
  Partition = Current->Partition;
  Level     = 0;

  DEBUG ((DEBUG_FS, "[ext4] Ext4OpenInternal %s\n", FileName));
  // If the path starts with a backslash, we treat the root directory as the base directory
  if (FileName[0] == L'\\') {
    FileName++;
    Current = Partition->Root;
  }

  while (FileName[0] != L'\0') {
    if (Partition->Root->Symloops > SYMLOOP_MAX) {
      DEBUG ((DEBUG_FS, "[ext4] Symloop limit is hit !\n"));
      return EFI_ACCESS_DENIED;
    }

    // Discard leading path separators
    while (FileName[0] == L'\\') {
      FileName++;
    }

    if (GetPathSegment (FileName, PathSegment, &Length) != EFI_SUCCESS) {
      return EFI_BUFFER_TOO_SMALL;
    }

    // Reached the end of the path
    if (Length == 0) {
      break;
    }

    FileName += Length;

    if (StrCmp (PathSegment, L".") == 0) {
      // Opens of "." are a no-op
      continue;
    }

    DEBUG ((DEBUG_FS, "[ext4] Opening %s\n", PathSegment));

    if (!Ext4FileIsDir (Current)) {
      return EFI_INVALID_PARAMETER;
    }

    if (!Ext4IsLastPathSegment (FileName)) {
      if (!Ext4DirCanLookup (Current)) {
        return EFI_ACCESS_DENIED;
      }
    }

    Status = Ext4OpenFile (Current, PathSegment, Partition, EFI_FILE_MODE_READ, &File);

    if (EFI_ERROR (Status) && (Status != EFI_NOT_FOUND)) {
      return Status;
    } else if (Status == EFI_NOT_FOUND) {
      // We explicitly ignore the EFI_FILE_MODE_CREATE flag, since we don't have write support
      /// If/ we add write support, this should be changed.
      return Status;
    }

    // Check if this is a valid file to open in EFI
    if (!Ext4FileIsOpenable (File)) {
      Ext4CloseInternal (File);
      // This looks like an /okay/ status to return.
      return EFI_ACCESS_DENIED;
    }

    //
    // Reading symlink and then trying to follow it
    //
    if (Ext4FileIsSymlink (File)) {
      Partition->Root->Symloops++;
      DEBUG ((DEBUG_FS, "[ext4] File %s is symlink, trying to read it\n", PathSegment));
      Status = Ext4ReadSymlink (Partition, File, &Symlink);
      if (EFI_ERROR (Status)) {
        DEBUG ((DEBUG_FS, "[ext4] Error reading %s symlink!\n", PathSegment));
        return Status;
      }
      DEBUG ((DEBUG_FS, "[ext4] File %s is linked to %s\n", PathSegment, Symlink));
      //
      // Close symlink file
      //
      Ext4CloseInternal (File);
      //
      // Open linked file by recursive call of Ext4OpenFile
      //
      Status = Ext4OpenInternal (Current, FoundFile, Symlink, OpenMode, Attributes);
      if (EFI_ERROR (Status)) {
        DEBUG ((DEBUG_FS, "[ext4] Error opening linked file %s\n", Symlink));
        FreePool (Symlink);
        return Status;
      }
      FreePool (Symlink);
      //
      // Set File to newly opened
      //
      File = *FoundFile;
    }

    if (Level != 0) {
      // Careful not to close the base directory
      Ext4CloseInternal (Current);
    }

    Level++;

    Current = File;
  }

  if (Level == 0) {
    // We opened the base directory again, so we need to duplicate the file structure
    Current = Ext4DuplicateFile (Current);
    if (Current == NULL) {
      return EFI_OUT_OF_RESOURCES;
    }
  }

  if (!Ext4ApplyPermissions (Current, OpenMode)) {
    Ext4CloseInternal (Current);
    return EFI_ACCESS_DENIED;
  }

  *FoundFile = Current;

  DEBUG ((DEBUG_FS, "[ext4] Opened filename %s\n", Current->Dentry->Name));
  return EFI_SUCCESS;
}

/**
  Opens a new file relative to the source file's location.
  @param[in]  This       A pointer to the EFI_FILE_PROTOCOL instance that is the file
                         handle to the source location. This would typically be an open
                         handle to a directory.
  @param[out] NewHandle  A pointer to the location to return the opened handle for the new
                         file.
  @param[in]  FileName   The Null-terminated string of the name of the file to be opened.
                         The file name may contain the following path modifiers: "\", ".",
                         and "..".
  @param[in]  OpenMode   The mode to open the file. The only valid combinations that the
                         file may be opened with are: Read, Read/Write, or Create/Read/Write.
  @param[in]  Attributes Only valid for EFI_FILE_MODE_CREATE, in which case these are the
                         attribute bits for the newly created file.
  @retval EFI_SUCCESS          The file was opened.
  @retval EFI_NOT_FOUND        The specified file could not be found on the device.
  @retval EFI_NO_MEDIA         The device has no medium.
  @retval EFI_MEDIA_CHANGED    The device has a different medium in it or the medium is no
                               longer supported.
  @retval EFI_DEVICE_ERROR     The device reported an error.
  @retval EFI_VOLUME_CORRUPTED The file system structures are corrupted.
  @retval EFI_WRITE_PROTECTED  An attempt was made to create a file, or open a file for write
                               when the media is write-protected.
  @retval EFI_ACCESS_DENIED    The service denied access to the file.
  @retval EFI_OUT_OF_RESOURCES Not enough resources were available to open the file.
  @retval EFI_VOLUME_FULL      The volume is full.
**/
EFI_STATUS
EFIAPI
Ext4Open (
  IN EFI_FILE_PROTOCOL   *This,
  OUT EFI_FILE_PROTOCOL  **NewHandle,
  IN CHAR16              *FileName,
  IN UINT64              OpenMode,
  IN UINT64              Attributes
  )
{
  EFI_STATUS      Status;
  EXT4_FILE       *FoundFile;
  EXT4_PARTITION  *Partition = ((EXT4_FILE *) This)->Partition;

  //
  // Reset Symloops counter
  //
  Partition->Root->Symloops = 0;

  Status = Ext4OpenInternal (
    (EXT4_FILE *) This,
    &FoundFile,
    FileName,
    OpenMode,
    Attributes
    );

  if (!EFI_ERROR (Status)) {
    *NewHandle = &FoundFile->Protocol;
  }

  return Status;
}

/**
  Closes a specified file handle.

  @param[in]  This          A pointer to the EFI_FILE_PROTOCOL instance that is the file
                            handle to close.

  @retval EFI_SUCCESS   The file was closed.

**/
EFI_STATUS
EFIAPI
Ext4Close (
  IN EFI_FILE_PROTOCOL  *This
  )
{
  return Ext4CloseInternal ((EXT4_FILE *)This);
}

/**
   Closes a file.

   @param[in]        File        Pointer to the file.

   @return Status of the closing of the file.
**/
EFI_STATUS
Ext4CloseInternal (
  IN EXT4_FILE  *File
  )
{
  if ((File == File->Partition->Root) && !File->Partition->Unmounting) {
    return EFI_SUCCESS;
  }

  DEBUG ((DEBUG_FS, "[ext4] Closed file %p (inode %lu)\n", File, File->InodeNum));
  RemoveEntryList (&File->OpenFilesListNode);
  FreePool (File->Inode);
  Ext4FreeExtentsMap (File);
  Ext4UnrefDentry (File->Dentry);
  FreePool (File);
  return EFI_SUCCESS;
}

/**
  Close and delete the file handle.

  @param[in]  This                     A pointer to the EFI_FILE_PROTOCOL instance that is the
                                       handle to the file to delete.

  @retval EFI_SUCCESS              The file was closed and deleted, and the handle was closed.
  @retval EFI_WARN_DELETE_FAILURE  The handle was closed, but the file was not deleted.

**/
EFI_STATUS
EFIAPI
Ext4Delete (
  IN EFI_FILE_PROTOCOL  *This
  )
{
  // We do a regular close here since we don't have write support.
  Ext4Close (This);
  return EFI_WARN_DELETE_FAILURE;
}

/**
  Reads data from a file.

  @param[in]      This             A pointer to the EFI_FILE_PROTOCOL instance that is the file
                                   handle to read data from.
  @param[in out]  BufferSize       On input, the size of the Buffer. On output, the amount of data
                                   returned in Buffer. In both cases, the size is measured in bytes.
  @param[out]     Buffer           The buffer into which the data is read.

  @retval EFI_SUCCESS          Data was read.
  @retval EFI_NO_MEDIA         The device has no medium.
  @retval EFI_DEVICE_ERROR     The device reported an error.
  @retval EFI_DEVICE_ERROR     An attempt was made to read from a deleted file.
  @retval EFI_DEVICE_ERROR     On entry, the current file position is beyond the end of the file.
  @retval EFI_VOLUME_CORRUPTED The file system structures are corrupted.
  @retval EFI_BUFFER_TOO_SMALL The BufferSize is too small to read the current directory
                               entry. BufferSize has been updated with the size
                               needed to complete the request.

**/
EFI_STATUS
EFIAPI
Ext4ReadFile (
  IN EFI_FILE_PROTOCOL  *This,
  IN OUT UINTN          *BufferSize,
  OUT VOID              *Buffer
  )
{
  EXT4_FILE       *File;
  EXT4_PARTITION  *Partition;
  EFI_STATUS      Status;

  File      = (EXT4_FILE *)This;
  Partition = File->Partition;

  ASSERT (Ext4FileIsOpenable (File));

  if (Ext4FileIsReg (File)) {
    Status = Ext4Read (Partition, File, Buffer, File->Position, BufferSize);
    if (Status == EFI_SUCCESS) {
      File->Position += *BufferSize;
    }

    return Status;
  } else if (Ext4FileIsDir (File)) {
    Status = Ext4ReadDir (Partition, File, Buffer, File->Position, BufferSize);

    return Status;
  }

  return EFI_SUCCESS;
}

/**
  Writes data to a file.

  @param[in]      This        A pointer to the EFI_FILE_PROTOCOL instance that is the file
                              handle to write data to.
  @param[in out]  BufferSize  On input, the size of the Buffer. On output, the amount of data
                              actually written. In both cases, the size is measured in bytes.
  @param[in]      Buffer      The buffer of data to write.

  @retval EFI_SUCCESS          Data was written.
  @retval EFI_UNSUPPORTED      Writes to open directory files are not supported.
  @retval EFI_NO_MEDIA         The device has no medium.
  @retval EFI_DEVICE_ERROR     The device reported an error.
  @retval EFI_DEVICE_ERROR     An attempt was made to write to a deleted file.
  @retval EFI_VOLUME_CORRUPTED The file system structures are corrupted.
  @retval EFI_WRITE_PROTECTED  The file or medium is write-protected.
  @retval EFI_ACCESS_DENIED    The file was opened read only.
  @retval EFI_VOLUME_FULL      The volume is full.

**/
EFI_STATUS
EFIAPI
Ext4WriteFile (
  IN EFI_FILE_PROTOCOL  *This,
  IN OUT UINTN          *BufferSize,
  IN VOID               *Buffer
  )
{
  EXT4_FILE  *File;

  File = (EXT4_FILE *)This;

  if (!(File->OpenMode & EFI_FILE_MODE_WRITE)) {
    return EFI_ACCESS_DENIED;
  }

  return EFI_WRITE_PROTECTED;
}

/**
  Returns a file's current position.

  @param[in]   This            A pointer to the EFI_FILE_PROTOCOL instance that is the file
                               handle to get the current position on.
  @param[out]  Position        The address to return the file's current position value.

  @retval EFI_SUCCESS      The position was returned.
  @retval EFI_UNSUPPORTED  The request is not valid on open directories.
  @retval EFI_DEVICE_ERROR An attempt was made to get the position from a deleted file.

**/
EFI_STATUS
EFIAPI
Ext4GetPosition (
  IN EFI_FILE_PROTOCOL  *This,
  OUT UINT64            *Position
  )
{
  EXT4_FILE  *File;

  File = (EXT4_FILE *)This;

  if (Ext4FileIsDir (File)) {
    return EFI_UNSUPPORTED;
  }

  *Position = File->Position;

  return EFI_SUCCESS;
}

/**
  Sets a file's current position.

  @param[in]  This            A pointer to the EFI_FILE_PROTOCOL instance that is the
                              file handle to set the requested position on.
  @param[in] Position        The byte position from the start of the file to set.

  @retval EFI_SUCCESS      The position was set.
  @retval EFI_UNSUPPORTED  The seek request for nonzero is not valid on open
                           directories.
  @retval EFI_DEVICE_ERROR An attempt was made to set the position of a deleted file.

**/
EFI_STATUS
EFIAPI
Ext4SetPosition (
  IN EFI_FILE_PROTOCOL  *This,
  IN UINT64             Position
  )
{
  EXT4_FILE  *File;

  File = (EXT4_FILE *)This;

  // Only seeks to 0 (so it resets the ReadDir operation) are allowed
  if (Ext4FileIsDir (File) && (Position != 0)) {
    return EFI_UNSUPPORTED;
  }

  // -1 (0xffffff.......) seeks to the end of the file
  if (Position == (UINT64)-1) {
    Position = EXT4_INODE_SIZE (File->Inode);
  }

  File->Position = Position;

  return EFI_SUCCESS;
}

/**
   Retrieves information about the file and stores it in the EFI_FILE_INFO format.

   @param[in]      File           Pointer to an opened file.
   @param[out]     Info           Pointer to a EFI_FILE_INFO.
   @param[in out]  BufferSize     Pointer to the buffer size

   @return Status of the file information request.
**/
EFI_STATUS
Ext4GetFileInfo (
  IN EXT4_FILE       *File,
  OUT EFI_FILE_INFO  *Info,
  IN OUT UINTN       *BufferSize
  )
{
  UINTN         FileNameLen;
  UINTN         FileNameSize;
  UINTN         NeededLength;
  CONST CHAR16  *FileName;

  if (File->InodeNum == EXT4_ROOT_INODE_NR) {
    // Root inode gets a filename of "", regardless of how it was opened.
    FileName = L"";
  } else {
    FileName = File->Dentry->Name;
  }

  FileNameLen  = StrLen (FileName);
  FileNameSize = StrSize (FileName);

  NeededLength = SIZE_OF_EFI_FILE_INFO + FileNameSize;

  if (*BufferSize < NeededLength) {
    *BufferSize = NeededLength;
    return EFI_BUFFER_TOO_SMALL;
  }

  Info->FileSize     = EXT4_INODE_SIZE (File->Inode);
  Info->PhysicalSize = Ext4FilePhysicalSpace (File);
  Ext4FileATime (File, &Info->LastAccessTime);
  Ext4FileMTime (File, &Info->ModificationTime);
  Ext4FileCreateTime (File, &Info->LastAccessTime);
  Info->Attribute = 0;
  Info->Size      = NeededLength;

  if (Ext4FileIsDir (File)) {
    Info->Attribute |= EFI_FILE_DIRECTORY;
  }

  *BufferSize = NeededLength;

  return StrCpyS (Info->FileName, FileNameLen + 1, FileName);
}

/**
   Retrieves the volume name.

   @param[in]      Part           Pointer to the opened partition.
   @param[out]     Info           Pointer to a CHAR16*.
   @param[out]     BufferSize     Pointer to a UINTN, where the string length
                                  of the name will be put.

   @return Status of the volume name request.
**/
EFI_STATUS
Ext4GetVolumeName (
  IN EXT4_PARTITION  *Partition,
  OUT CHAR16         **OutVolName,
  OUT UINTN          *VolNameLen
  )
{
  CHAR8       TempVolName[16 + 1];
  CHAR16      *VolumeName;
  UINTN       VolNameLength;
  EFI_STATUS  Status;

  VolNameLength = 0;
  VolumeName    = NULL;

  // s_volume_name is only valid on dynamic revision; old filesystems don't support this
  if (Partition->SuperBlock.s_rev_level == EXT4_DYNAMIC_REV) {
    CopyMem (TempVolName, (CONST CHAR8 *)Partition->SuperBlock.s_volume_name, 16);
    TempVolName[16] = '\0';

    Status = UTF8StrToUCS2 (TempVolName, &VolumeName);

    if (EFI_ERROR (Status)) {
      return Status;
    }

    VolNameLength = StrLen (VolumeName);
  } else {
    VolumeName    = AllocateZeroPool (sizeof (CHAR16));
    VolNameLength = 0;
  }

  *OutVolName = VolumeName;
  *VolNameLen = VolNameLength;

  return EFI_SUCCESS;
}

/**
   Retrieves information about the filesystem and stores it in the EFI_FILE_SYSTEM_INFO format.

   @param[in]      Part           Pointer to the opened partition.
   @param[out]     Info           Pointer to a EFI_FILE_SYSTEM_INFO.
   @param[in out]  BufferSize     Pointer to the buffer size

   @return Status of the file information request.
**/
STATIC
EFI_STATUS
Ext4GetFilesystemInfo (
  IN EXT4_PARTITION         *Part,
  OUT EFI_FILE_SYSTEM_INFO  *Info,
  IN OUT UINTN              *BufferSize
  )
{
  // Length of s_volume_name + null terminator
  EFI_STATUS     Status;
  UINTN          NeededLength;
  EXT4_BLOCK_NR  TotalBlocks;
  EXT4_BLOCK_NR  FreeBlocks;
  CHAR16         *VolumeName;
  UINTN          VolNameLength;

  Status = Ext4GetVolumeName (Part, &VolumeName, &VolNameLength);

  if (EFI_ERROR (Status)) {
    return Status;
  }

  NeededLength = SIZE_OF_EFI_FILE_SYSTEM_INFO;

  NeededLength += StrSize (VolumeName);

  if (*BufferSize < NeededLength) {
    *BufferSize = NeededLength;

    FreePool (VolumeName);

    return EFI_BUFFER_TOO_SMALL;
  }

  TotalBlocks = Part->NumberBlocks;

  FreeBlocks = EXT4_BLOCK_NR_FROM_HALFS (
                 Part,
                 Part->SuperBlock.s_free_blocks_count,
                 Part->SuperBlock.s_free_blocks_count_hi
                 );

  Info->BlockSize  = Part->BlockSize;
  Info->Size       = NeededLength;
  Info->ReadOnly   = Part->ReadOnly;
  Info->VolumeSize = MultU64x32 (TotalBlocks, Part->BlockSize);
  Info->FreeSpace  = MultU64x32 (FreeBlocks, Part->BlockSize);

  StrCpyS (Info->VolumeLabel, VolNameLength + 1, VolumeName);

  FreePool (VolumeName);

  *BufferSize = NeededLength;

  return EFI_SUCCESS;
}

/**
   Retrieves the volume label and stores it in the EFI_FILE_SYSTEM_VOLUME_LABEL format.

   @param[in]      Part           Pointer to the opened partition.
   @param[out]     Info           Pointer to a EFI_FILE_SYSTEM_VOLUME_LABEL.
   @param[in out]  BufferSize     Pointer to the buffer size

   @return Status of the file information request.
**/
STATIC
EFI_STATUS
Ext4GetVolumeLabelInfo (
  IN EXT4_PARTITION                 *Part,
  OUT EFI_FILE_SYSTEM_VOLUME_LABEL  *Info,
  IN OUT UINTN                      *BufferSize
  )
{
  // Length of s_volume_name + null terminator
  CHAR16      *VolumeName;
  UINTN       VolNameLength;
  EFI_STATUS  Status;
  UINTN       NeededLength;

  Status = Ext4GetVolumeName (Part, &VolumeName, &VolNameLength);

  if (EFI_ERROR (Status)) {
    return Status;
  }

  NeededLength = (VolNameLength + 1) * sizeof (CHAR16);

  if (NeededLength > *BufferSize) {
    *BufferSize = NeededLength;

    FreePool (VolumeName);

    return EFI_BUFFER_TOO_SMALL;
  }

  Status = StrCpyS (Info->VolumeLabel, VolNameLength + 1, VolumeName);

  ASSERT_EFI_ERROR (Status);

  FreePool (VolumeName);

  *BufferSize = NeededLength;

  return EFI_SUCCESS;
}

/**
  Returns information about a file.

  @param[in]      This            A pointer to the EFI_FILE_PROTOCOL instance that is the file
                                  handle the requested information is for.
  @param[in]      InformationType The type identifier for the information being requested.
  @param[in out]  BufferSize      On input, the size of Buffer. On output, the amount of data
                                  returned in Buffer. In both cases, the size is measured in bytes.
  @param[out]     Buffer          A pointer to the data buffer to return. The buffer's type is
                                  indicated by InformationType.

  @retval EFI_SUCCESS          The information was returned.
  @retval EFI_UNSUPPORTED      The InformationType is not known.
  @retval EFI_NO_MEDIA         The device has no medium.
  @retval EFI_DEVICE_ERROR     The device reported an error.
  @retval EFI_VOLUME_CORRUPTED The file system structures are corrupted.
  @retval EFI_BUFFER_TOO_SMALL The BufferSize is too small to read the current directory entry.
                               BufferSize has been updated with the size needed to complete
                               the request.
**/
EFI_STATUS
EFIAPI
Ext4GetInfo (
  IN EFI_FILE_PROTOCOL  *This,
  IN EFI_GUID           *InformationType,
  IN OUT UINTN          *BufferSize,
  OUT VOID              *Buffer
  )
{
  EXT4_PARTITION  *Partition;

  Partition = ((EXT4_FILE *)This)->Partition;

  if (CompareGuid (InformationType, &gEfiFileInfoGuid)) {
    return Ext4GetFileInfo ((EXT4_FILE *)This, Buffer, BufferSize);
  }

  if (CompareGuid (InformationType, &gEfiFileSystemInfoGuid)) {
    return Ext4GetFilesystemInfo (Partition, Buffer, BufferSize);
  }

  if (CompareGuid (InformationType, &gEfiFileSystemVolumeLabelInfoIdGuid)) {
    return Ext4GetVolumeLabelInfo (Partition, Buffer, BufferSize);
  }

  return EFI_UNSUPPORTED;
}

/**
   Duplicates a file structure.

   @param[in]        Original    Pointer to the original file.

   @return Pointer to the new file structure.
**/
STATIC
EXT4_FILE *
Ext4DuplicateFile (
  IN CONST EXT4_FILE  *Original
  )
{
  EXT4_PARTITION  *Partition;
  EXT4_FILE       *File;
  EFI_STATUS      Status;

  Partition = Original->Partition;
  File      = AllocateZeroPool (sizeof (EXT4_FILE));

  if (File == NULL) {
    return NULL;
  }

  File->Inode = Ext4AllocateInode (Partition);
  if (File->Inode == NULL) {
    FreePool (File);
    return NULL;
  }

  CopyMem (File->Inode, Original->Inode, Partition->InodeSize);

  File->Position = 0;
  Ext4SetupFile (File, Partition);
  File->InodeNum = Original->InodeNum;
  File->OpenMode = 0; // Will be filled by other code

  Status = Ext4InitExtentsMap (File);
  if (EFI_ERROR (Status)) {
    FreePool (File->Inode);
    FreePool (File);
    return NULL;
  }

  File->Dentry = Original->Dentry;

  Ext4RefDentry (File->Dentry);

  InsertTailList (&Partition->OpenFiles, &File->OpenFilesListNode);

  return File;
}

/**
  Sets information about a file.

  @param[in]  This            A pointer to the EFI_FILE_PROTOCOL instance that is the file
                              handle the information is for.
  @param[in]  InformationType The type identifier for the information being set.
  @param[in]  BufferSize      The size, in bytes, of Buffer.
  @param[in]  Buffer          A pointer to the data buffer to write. The buffer's type is
                              indicated by InformationType.

  @retval EFI_SUCCESS          The information was set.
  @retval EFI_UNSUPPORTED      The InformationType is not known.
  @retval EFI_NO_MEDIA         The device has no medium.
  @retval EFI_DEVICE_ERROR     The device reported an error.
  @retval EFI_VOLUME_CORRUPTED The file system structures are corrupted.
  @retval EFI_WRITE_PROTECTED  InformationType is EFI_FILE_INFO_ID and the media is
                               read-only.
  @retval EFI_WRITE_PROTECTED  InformationType is EFI_FILE_PROTOCOL_SYSTEM_INFO_ID
                               and the media is read only.
  @retval EFI_WRITE_PROTECTED  InformationType is EFI_FILE_SYSTEM_VOLUME_LABEL_ID
                               and the media is read-only.
  @retval EFI_ACCESS_DENIED    An attempt is made to change the name of a file to a
                               file that is already present.
  @retval EFI_ACCESS_DENIED    An attempt is being made to change the EFI_FILE_DIRECTORY
                               Attribute.
  @retval EFI_ACCESS_DENIED    An attempt is being made to change the size of a directory.
  @retval EFI_ACCESS_DENIED    InformationType is EFI_FILE_INFO_ID and the file was opened
                               read-only and an attempt is being made to modify a field
                               other than Attribute.
  @retval EFI_VOLUME_FULL      The volume is full.
  @retval EFI_BAD_BUFFER_SIZE  BufferSize is smaller than the size of the type indicated
                               by InformationType.

**/
EFI_STATUS
EFIAPI
Ext4SetInfo (
  IN EFI_FILE_PROTOCOL  *This,
  IN EFI_GUID           *InformationType,
  IN UINTN              BufferSize,
  IN VOID               *Buffer
  )
{
  EXT4_FILE       *File;
  EXT4_PARTITION  *Part;

  File = (EXT4_FILE *)This;
  Part = File->Partition;

  if (Part->ReadOnly) {
    return EFI_WRITE_PROTECTED;
  }

  // There's no write support just yet.
  return EFI_UNSUPPORTED;
}