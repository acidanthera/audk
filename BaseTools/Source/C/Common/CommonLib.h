/** @file
Common library assistance routines.

Copyright (c) 2004 - 2025, Intel Corporation. All rights reserved.<BR>
SPDX-License-Identifier: BSD-2-Clause-Patent

**/

#ifndef _EFI_COMMON_LIB_H
#define _EFI_COMMON_LIB_H

#include <Common/UefiBaseTypes.h>
#include <Common/BuildVersion.h>
#include <assert.h>
#ifndef _WIN32
#include <limits.h>
#endif

#include <Library/BaseLib.h>
#include <Library/BaseMemoryLib.h>
#include <Library/DebugLib.h>
#include <Library/MemoryAllocationLib.h>

#define PRINTED_GUID_BUFFER_SIZE  37  // including null-termination

#ifdef PATH_MAX
#define MAX_LONG_FILE_PATH PATH_MAX
#else
#define MAX_LONG_FILE_PATH 500
#endif

#define MAX_UINT64 ((UINT64)0xFFFFFFFFFFFFFFFFULL)
#define MAX_UINT32 ((UINT32)0xFFFFFFFF)
#define MAX_UINT16  ((UINT16)0xFFFF)
#define MAX_UINT8   ((UINT8)0xFF)
#define ARRAY_SIZE(Array) (sizeof (Array) / sizeof ((Array)[0]))
#define ASCII_RSIZE_MAX 1000000
#undef RSIZE_MAX
#define RSIZE_MAX 1000000

#define IS_COMMA(a)                ((a) == L',')
#define IS_HYPHEN(a)               ((a) == L'-')
#define IS_DOT(a)                  ((a) == L'.')
#define IS_LEFT_PARENTH(a)         ((a) == L'(')
#define IS_RIGHT_PARENTH(a)        ((a) == L')')
#define IS_SLASH(a)                ((a) == L'/')
#define IS_NULL(a)                 ((a) == L'\0')

#ifdef __cplusplus
extern "C" {
#endif

//
// Function declarations
//
INTN
BtCompareGuid (
  IN EFI_GUID     *Guid1,
  IN EFI_GUID     *Guid2
  )
;

EFI_STATUS
GetFileImage (
  IN CHAR8    *InputFileName,
  OUT CHAR8   **InputFileImage,
  OUT UINT32  *BytesRead
  )
;

EFI_STATUS
PutFileImage (
  IN CHAR8    *OutputFileName,
  IN CHAR8    *OutputFileImage,
  IN UINT32   BytesToWrite
  )
;

#define CalculateChecksum8   CalculateCheckSum8

UINT16
BtCalculateChecksum16 (
  IN UINT16       *Buffer,
  IN UINTN        Size
  )
;

UINT16
BtCalculateSum16 (
  IN UINT16       *Buffer,
  IN UINTN        Size
  )
;

EFI_STATUS
PrintGuid (
  IN EFI_GUID                     *Guid
  )
;

#define PRINTED_GUID_BUFFER_SIZE  37  // including null-termination
EFI_STATUS
PrintGuidToBuffer (
  IN EFI_GUID     *Guid,
  IN OUT UINT8    *Buffer,
  IN UINT32       BufferLen,
  IN BOOLEAN      Uppercase
  )
;

CHAR8 *
LongFilePath (
 IN CHAR8 *FileName
);

EFI_STATUS
GetAlignmentFromFile (
  IN  CHAR8   *InFile,
  OUT UINT32  *Alignment
  );

/*++

Routine Description:
  Convert FileName to the long file path, which can support larger than 260 length.

Arguments:
  FileName         - FileName.

Returns:
  LongFilePath      A pointer to the converted long file path.

--*/

#ifdef __cplusplus
}
#endif

#ifdef __GNUC__
#include <stdio.h>
#include <sys/stat.h>
#define stricmp strcasecmp
#define _stricmp strcasecmp
#define strnicmp strncasecmp
#define strcmpi strcasecmp
#ifndef __CYGWIN__
char *strlwr(char *s);
#endif
#endif

#ifdef _WIN32
#include <io.h> // io.h provides the declaration of _filelength on Windows
#else
size_t _filelength(int fd); // Only declare this on non-Windows systems
#endif

//
// On windows, mkdir only has one parameter.
// On unix, it has two parameters
//
#if defined(__GNUC__)
#define mkdir(dir, perm) mkdir(dir, perm)
#else
#define mkdir(dir, perm) mkdir(dir)
#endif

#endif
