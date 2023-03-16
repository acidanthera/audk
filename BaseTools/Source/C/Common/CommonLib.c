/** @file
Common basic Library Functions

Copyright (c) 2004 - 2018, Intel Corporation. All rights reserved.<BR>
SPDX-License-Identifier: BSD-2-Clause-Patent

**/

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <ctype.h>
#ifdef __GNUC__
#include <unistd.h>
#else
#include <direct.h>
#endif
#include "CommonLib.h"
#include "EfiUtilityMsgs.h"

INTN
BtCompareGuid (
  IN EFI_GUID     *Guid1,
  IN EFI_GUID     *Guid2
  )
/*++

Routine Description:

  Compares to GUIDs

Arguments:

  Guid1 - guid to compare
  Guid2 - guid to compare

Returns:
  =  0  if Guid1 == Guid2
  != 0  if Guid1 != Guid2

--*/
{
  return !CompareGuid (Guid1, Guid2);
}

EFI_STATUS
GetFileImage (
  IN CHAR8    *InputFileName,
  OUT CHAR8   **InputFileImage,
  OUT UINT32  *BytesRead
  )
/*++

Routine Description:

  This function opens a file and reads it into a memory buffer.  The function
  will allocate the memory buffer and returns the size of the buffer.

Arguments:

  InputFileName     The name of the file to read.
  InputFileImage    A pointer to the memory buffer.
  BytesRead         The size of the memory buffer.

Returns:

  EFI_SUCCESS              The function completed successfully.
  EFI_INVALID_PARAMETER    One of the input parameters was invalid.
  EFI_ABORTED              An error occurred.
  EFI_OUT_OF_RESOURCES     No resource to complete operations.

--*/
{
  FILE    *InputFile;
  UINT32  FileSize;

  //
  // Verify input parameters.
  //
  if (InputFileName == NULL || strlen (InputFileName) == 0 || InputFileImage == NULL) {
    return EFI_INVALID_PARAMETER;
  }
  //
  // Open the file and copy contents into a memory buffer.
  //
  //
  // Open the file
  //
  InputFile = fopen (LongFilePath (InputFileName), "rb");
  if (InputFile == NULL) {
    Error (NULL, 0, 0001, "Error opening the input file", InputFileName);
    return EFI_ABORTED;
  }
  //
  // Go to the end so that we can determine the file size
  //
  if (fseek (InputFile, 0, SEEK_END)) {
    Error (NULL, 0, 0004, "Error reading the input file", InputFileName);
    fclose (InputFile);
    return EFI_ABORTED;
  }
  //
  // Get the file size
  //
  FileSize = ftell (InputFile);
  if (FileSize == -1) {
    Error (NULL, 0, 0003, "Error parsing the input file", InputFileName);
    fclose (InputFile);
    return EFI_ABORTED;
  }
  //
  // Allocate a buffer
  //
  *InputFileImage = malloc (FileSize);
  if (*InputFileImage == NULL) {
    fclose (InputFile);
    return EFI_OUT_OF_RESOURCES;
  }
  //
  // Reset to the beginning of the file
  //
  if (fseek (InputFile, 0, SEEK_SET)) {
    Error (NULL, 0, 0004, "Error reading the input file", InputFileName);
    fclose (InputFile);
    free (*InputFileImage);
    *InputFileImage = NULL;
    return EFI_ABORTED;
  }
  //
  // Read all of the file contents.
  //
  *BytesRead = fread (*InputFileImage, sizeof (UINT8), FileSize, InputFile);
  if (*BytesRead != sizeof (UINT8) * FileSize) {
    Error (NULL, 0, 0004, "Error reading the input file", InputFileName);
    fclose (InputFile);
    free (*InputFileImage);
    *InputFileImage = NULL;
    return EFI_ABORTED;
  }
  //
  // Close the file
  //
  fclose (InputFile);

  return EFI_SUCCESS;
}

EFI_STATUS
PutFileImage (
  IN CHAR8    *OutputFileName,
  IN CHAR8    *OutputFileImage,
  IN UINT32   BytesToWrite
  )
/*++

Routine Description:

  This function opens a file and writes OutputFileImage into the file.

Arguments:

  OutputFileName     The name of the file to write.
  OutputFileImage    A pointer to the memory buffer.
  BytesToWrite       The size of the memory buffer.

Returns:

  EFI_SUCCESS              The function completed successfully.
  EFI_INVALID_PARAMETER    One of the input parameters was invalid.
  EFI_ABORTED              An error occurred.
  EFI_OUT_OF_RESOURCES     No resource to complete operations.

--*/
{
  FILE    *OutputFile;
  UINT32  BytesWrote;

  //
  // Verify input parameters.
  //
  if (OutputFileName == NULL || strlen (OutputFileName) == 0 || OutputFileImage == NULL) {
    return EFI_INVALID_PARAMETER;
  }
  //
  // Open the file and copy contents into a memory buffer.
  //
  //
  // Open the file
  //
  OutputFile = fopen (LongFilePath (OutputFileName), "wb");
  if (OutputFile == NULL) {
    Error (NULL, 0, 0001, "Error opening the output file", OutputFileName);
    return EFI_ABORTED;
  }

  //
  // Write all of the file contents.
  //
  BytesWrote = fwrite (OutputFileImage, sizeof (UINT8), BytesToWrite, OutputFile);
  if (BytesWrote != sizeof (UINT8) * BytesToWrite) {
    Error (NULL, 0, 0002, "Error writing the output file", OutputFileName);
    fclose (OutputFile);
    return EFI_ABORTED;
  }
  //
  // Close the file
  //
  fclose (OutputFile);

  return EFI_SUCCESS;
}

UINT16
BtCalculateChecksum16 (
  IN UINT16       *Buffer,
  IN UINTN        Size
  )
/*++

Routine Description::

  This function calculates the value needed for a valid UINT16 checksum

Arguments:

  Buffer      Pointer to buffer containing byte data of component.
  Size        Size of the buffer

Returns:

  The 16 bit checksum value needed.

--*/
{
  return CalculateCheckSum16 (Buffer, Size * sizeof (UINT16));
}

UINT16
BtCalculateSum16 (
  IN UINT16       *Buffer,
  IN UINTN        Size
  )
/*++

Routine Description:

  This function calculates the UINT16 sum for the requested region.

Arguments:

  Buffer      Pointer to buffer containing byte data of component.
  Size        Size of the buffer

Returns:

  The 16 bit checksum

--*/
{
  return CalculateSum16 (Buffer, Size * sizeof (UINT16));
}

EFI_STATUS
PrintGuid (
  IN EFI_GUID *Guid
  )
/*++

Routine Description:

  This function prints a GUID to STDOUT.

Arguments:

  Guid    Pointer to a GUID to print.

Returns:

  EFI_SUCCESS             The GUID was printed.
  EFI_INVALID_PARAMETER   The input was NULL.

--*/
{
  if (Guid == NULL) {
    Error (NULL, 0, 2000, "Invalid parameter", "PrintGuidToBuffer() called with a NULL value");
    return EFI_INVALID_PARAMETER;
  }

  printf (
    "%08x-%04x-%04x-%02x%02x-%02x%02x%02x%02x%02x%02x\n",
    (unsigned) Guid->Data1,
    Guid->Data2,
    Guid->Data3,
    Guid->Data4[0],
    Guid->Data4[1],
    Guid->Data4[2],
    Guid->Data4[3],
    Guid->Data4[4],
    Guid->Data4[5],
    Guid->Data4[6],
    Guid->Data4[7]
    );
  return EFI_SUCCESS;
}

EFI_STATUS
PrintGuidToBuffer (
  IN EFI_GUID     *Guid,
  IN OUT UINT8    *Buffer,
  IN UINT32       BufferLen,
  IN BOOLEAN      Uppercase
  )
/*++

Routine Description:

  This function prints a GUID to a buffer

Arguments:

  Guid      - Pointer to a GUID to print.
  Buffer    - Pointer to a user-provided buffer to print to
  BufferLen - Size of the Buffer
  Uppercase - If use upper case.

Returns:

  EFI_SUCCESS             The GUID was printed.
  EFI_INVALID_PARAMETER   The input was NULL.
  EFI_BUFFER_TOO_SMALL    The input buffer was not big enough

--*/
{
  if (Guid == NULL) {
    Error (NULL, 0, 2000, "Invalid parameter", "PrintGuidToBuffer() called with a NULL value");
    return EFI_INVALID_PARAMETER;
  }

  if (BufferLen < PRINTED_GUID_BUFFER_SIZE) {
    Error (NULL, 0, 2000, "Invalid parameter", "PrintGuidToBuffer() called with invalid buffer size");
    return EFI_BUFFER_TOO_SMALL;
  }

  if (Uppercase) {
    sprintf (
      (CHAR8 *)Buffer,
      "%08X-%04X-%04X-%02X%02X-%02X%02X%02X%02X%02X%02X",
      (unsigned) Guid->Data1,
      Guid->Data2,
      Guid->Data3,
      Guid->Data4[0],
      Guid->Data4[1],
      Guid->Data4[2],
      Guid->Data4[3],
      Guid->Data4[4],
      Guid->Data4[5],
      Guid->Data4[6],
      Guid->Data4[7]
      );
  } else {
    sprintf (
      (CHAR8 *)Buffer,
      "%08x-%04x-%04x-%02x%02x-%02x%02x%02x%02x%02x%02x",
      (unsigned) Guid->Data1,
      Guid->Data2,
      Guid->Data3,
      Guid->Data4[0],
      Guid->Data4[1],
      Guid->Data4[2],
      Guid->Data4[3],
      Guid->Data4[4],
      Guid->Data4[5],
      Guid->Data4[6],
      Guid->Data4[7]
      );
  }

  return EFI_SUCCESS;
}

#ifdef __GNUC__

size_t _filelength(int fd)
{
  struct stat stat_buf;
  fstat(fd, &stat_buf);
  return stat_buf.st_size;
}

#ifndef __CYGWIN__
char *strlwr(char *s)
{
  char *p = s;
  for(;*s;s++) {
    *s = tolower(*s);
  }
  return p;
}
#endif
#endif

#define WINDOWS_EXTENSION_PATH "\\\\?\\"
#define WINDOWS_UNC_EXTENSION_PATH "\\\\?\\UNC"

//
// Global data to store full file path. It is not required to be free.
//
CHAR8 mCommonLibFullPath[MAX_LONG_FILE_PATH];

CHAR8 *
LongFilePath (
 IN CHAR8 *FileName
 )
/*++

Routine Description:
  Convert FileName to the long file path, which can support larger than 260 length.

Arguments:
  FileName         - FileName.

Returns:
  LongFilePath      A pointer to the converted long file path.

--*/
{
#ifdef __GNUC__
  //
  // __GNUC__ may not be good way to differentiate unix and windows. Need more investigation here.
  // unix has no limitation on file path. Just return FileName.
  //
  return FileName;
#else
  CHAR8 *RootPath;
  CHAR8 *PathPointer;
  CHAR8 *NextPointer;

  PathPointer = (CHAR8 *) FileName;

  if (FileName != NULL) {
    //
    // Add the extension string first to support long file path.
    //
    mCommonLibFullPath[0] = 0;
    strcpy (mCommonLibFullPath, WINDOWS_EXTENSION_PATH);

    if (strlen (FileName) > 1 && FileName[0] == '\\' && FileName[1] == '\\') {
      //
      // network path like \\server\share to \\?\UNC\server\share
      //
      strcpy (mCommonLibFullPath, WINDOWS_UNC_EXTENSION_PATH);
      FileName ++;
    } else if (strlen (FileName) < 3 || FileName[1] != ':' || (FileName[2] != '\\' && FileName[2] != '/')) {
      //
      // Relative file path. Convert it to absolute path.
      //
      RootPath = getcwd (NULL, 0);
      if (RootPath != NULL) {
        if (strlen (mCommonLibFullPath) + strlen (RootPath) > MAX_LONG_FILE_PATH - 1) {
          Error (NULL, 0, 2000, "Invalid parameter", "RootPath is too long!");
          free (RootPath);
          return NULL;
        }
        strncat (mCommonLibFullPath, RootPath, MAX_LONG_FILE_PATH - strlen (mCommonLibFullPath) - 1);
        if (FileName[0] != '\\' && FileName[0] != '/') {
          if (strlen (mCommonLibFullPath) + 1 > MAX_LONG_FILE_PATH - 1) {
            Error (NULL, 0, 2000, "Invalid parameter", "RootPath is too long!");
            free (RootPath);
            return NULL;
          }
          //
          // Attach directory separator
          //
          strncat (mCommonLibFullPath, "\\", MAX_LONG_FILE_PATH - strlen (mCommonLibFullPath) - 1);
        }
        free (RootPath);
      }
    }

    //
    // Construct the full file path
    //
    if (strlen (mCommonLibFullPath) + strlen (FileName) > MAX_LONG_FILE_PATH - 1) {
      Error (NULL, 0, 2000, "Invalid parameter", "FileName %s is too long!", FileName);
      return NULL;
    }
    strncat (mCommonLibFullPath, FileName, MAX_LONG_FILE_PATH - strlen (mCommonLibFullPath) - 1);

    //
    // Convert directory separator '/' to '\\'
    //
    PathPointer = (CHAR8 *) mCommonLibFullPath;
    do {
      if (*PathPointer == '/') {
        *PathPointer = '\\';
      }
    } while (*PathPointer ++ != '\0');

    //
    // Convert ":\\\\" to ":\\", because it doesn't work with WINDOWS_EXTENSION_PATH.
    //
    if ((PathPointer = strstr (mCommonLibFullPath, ":\\\\")) != NULL) {
      *(PathPointer + 2) = '\0';
      strncat (mCommonLibFullPath, PathPointer + 3, MAX_LONG_FILE_PATH - strlen (mCommonLibFullPath) - 1);
    }

    //
    // Convert ".\\" to "", because it doesn't work with WINDOWS_EXTENSION_PATH.
    //
    while ((PathPointer = strstr (mCommonLibFullPath, ".\\")) != NULL) {
      *PathPointer = '\0';
      strncat (mCommonLibFullPath, PathPointer + 2, MAX_LONG_FILE_PATH - strlen (mCommonLibFullPath) - 1);
    }

    //
    // Convert "\\.\\" to "\\", because it doesn't work with WINDOWS_EXTENSION_PATH.
    //
    while ((PathPointer = strstr (mCommonLibFullPath, "\\.\\")) != NULL) {
      *PathPointer = '\0';
      strncat (mCommonLibFullPath, PathPointer + 2, MAX_LONG_FILE_PATH - strlen (mCommonLibFullPath) - 1);
    }

    //
    // Convert "\\..\\" to last directory, because it doesn't work with WINDOWS_EXTENSION_PATH.
    //
    while ((PathPointer = strstr (mCommonLibFullPath, "\\..\\")) != NULL) {
      NextPointer = PathPointer + 3;
      do {
        PathPointer --;
      } while (PathPointer > mCommonLibFullPath && *PathPointer != ':' && *PathPointer != '\\');

      if (*PathPointer == '\\') {
        //
        // Skip one directory
        //
        *PathPointer = '\0';
        strncat (mCommonLibFullPath, NextPointer, MAX_LONG_FILE_PATH - strlen (mCommonLibFullPath) - 1);
      } else {
        //
        // No directory is found. Just break.
        //
        break;
      }
    }

    PathPointer = mCommonLibFullPath;
  }

  return PathPointer;
#endif
}


VOID *
InternalAllocatePool (
   UINTN   AllocationSize
  )
{
  VOID * Memory;

  Memory = malloc(AllocationSize);
  ASSERT(Memory != NULL);
  return Memory;
}


VOID *
InternalReallocatePool (
   UINTN            OldSize,
   UINTN            NewSize,
   VOID             *OldBuffer  OPTIONAL
  )
{
  VOID  *NewBuffer;

  NewBuffer = AllocateZeroPool (NewSize);
  if (NewBuffer != NULL && OldBuffer != NULL) {
    memcpy (NewBuffer, OldBuffer, MIN (OldSize, NewSize));
    free(OldBuffer);
  }
  return NewBuffer;
}

VOID *
EFIAPI
ReallocatePool (
   UINTN  OldSize,
   UINTN  NewSize,
   VOID   *OldBuffer  OPTIONAL
  )
{
  return InternalReallocatePool (OldSize, NewSize, OldBuffer);
}

VOID *
InternalAllocateCopyPool (
   UINTN            AllocationSize,
   CONST VOID       *Buffer
  )
{
  VOID  *Memory;

  ASSERT (Buffer != NULL);

  Memory = malloc (AllocationSize);
  if (Memory != NULL) {
     Memory = memcpy (Memory, Buffer, AllocationSize);
  }
  return Memory;
}

VOID *
EFIAPI
AllocateCopyPool (
   UINTN       AllocationSize,
   CONST VOID  *Buffer
  )
{
  return InternalAllocateCopyPool (AllocationSize, Buffer);
}

VOID *
EFIAPI
AllocateZeroPool (
  UINTN  AllocationSize
  )
{
  VOID * Memory;
  Memory = malloc(AllocationSize);
  ASSERT (Memory != NULL);
  if (Memory == NULL) {
    fprintf(stderr, "Not memory for malloc\n");
  }
  memset(Memory, 0, AllocationSize);
  return Memory;
}

VOID *
EFIAPI
AllocatePool (
  UINTN  AllocationSize
  )
{
  return InternalAllocatePool (AllocationSize);
}

VOID
EFIAPI
FreePool (
  IN VOID  *Buffer
  )
{
  ASSERT (Buffer != NULL);
  free (Buffer);
}

VOID
EFIAPI
CpuBreakpoint (
  VOID
  )
{
  abort ();
}

VOID
EFIAPI
CpuDeadLoop (
  VOID
  )
{
  abort ();
}
