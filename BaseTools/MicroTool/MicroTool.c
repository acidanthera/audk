/** @file
  Copyright (c) 2022, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause
**/

#include <assert.h>
#include <ctype.h>
#include <errno.h>
#include <stdbool.h>

#include <UserFile.h>

#define DEFAULT_MC_ALIGNMENT       16
#define DEFAULT_MC_PAD_BYTE_VALUE  0xFF

typedef struct {
  UINT32  HeaderVersion;
  UINT32  PatchId;
  UINT32  Date;
  UINT32  CpuId;
  UINT32  Checksum;
  UINT32  LoaderVersion;
  UINT32  PlatformId;
  UINT32  DataSize;   // if 0, then TotalSize = 2048, and TotalSize field is invalid
  UINT32  TotalSize;  // number of bytes
  UINT32  Reserved[3];
} MICROCODE_HEADER;

static
RETURN_STATUS
TxtToBin (
  IN const char *TxtName,
  IN const char *BinName
  )
{
  char              *Txt;
  char              *TxtStart;
  uint32_t          TxtSize;
  UINT32            *Buffer;
  UINT32            *BufferStart;
  UINT32            FileLength;
  UINT32            Index;
  MICROCODE_HEADER  *Micro;
  UINT32            CheckSum;

  assert (TxtName != NULL);
  assert (BinName != NULL);

  Txt = (char *)UserReadFile (TxtName, &TxtSize);
  if (Txt == NULL) {
    fprintf (stderr, "MicroTool: Could not open %s: %s\n", TxtName, strerror (errno));
    return RETURN_ABORTED;
  }

  Buffer = calloc (1, TxtSize);
  if (Buffer == NULL) {
    fprintf (stderr, "MicroTool: Could not allocate memory for Buffer\n");
    free (Txt);
    return RETURN_OUT_OF_RESOURCES;
  }

  BufferStart = Buffer;
  TxtStart    = Txt;
  FileLength  = 0;
  for (Index = 0; Index < TxtSize; ++Index, ++Txt) {
    //
    // Skip Blank Lines and Comment Lines
    //
    if (isspace ((int)*Txt)) {
      continue;
    }

    if (*Txt == ';') {
      while ((Index < TxtSize) && (*Txt != '\n')) {
        ++Index;
        ++Txt;
      }

      if (Index == TxtSize) {
        break;
      }

      ++Index;
      ++Txt;
    }
    //
    // Look for
    // dd 000000001h ; comment
    // dd XXXXXXXX
    // DD  XXXXXXXXX
    //  DD XXXXXXXXX
    //
    if (((Index + 2) < TxtSize) && (tolower ((int)Txt[0]) == 'd') && (tolower ((int)Txt[1]) == 'd') && isspace ((int)Txt[2])) {
      //
      // Skip blanks and look for a hex digit
      //
      Txt   += 3;
      Index += 3;
      while ((Index < TxtSize) && isspace ((int)*Txt)) {
        ++Index;
        ++Txt;
      }

      if (Index == TxtSize) {
        break;
      }

      if (isxdigit ((int)*Txt)) {
        if (sscanf (Txt, "%X", Buffer) != 1) {
          fprintf (stderr, "MicroTool: Could not write into Buffer\n");
          free (TxtStart);
          free (BufferStart);
          return RETURN_ABORTED;
        }

        while ((Index < TxtSize) && (*Txt != '\n')) {
          ++Index;
          ++Txt;
        }
      }

      ++Buffer;
      FileLength += sizeof (*Buffer);
      continue;
    }

    fprintf (stderr, "MicroTool: Corrupted input file\n");
    break;
  }

  free (TxtStart);

  if (FileLength == 0) {
    fprintf (stderr, "MicroTool: No parseable data found in file %s\n", TxtName);
    free (BufferStart);
    return RETURN_INVALID_PARAMETER;
  }

  if (FileLength < sizeof (MICROCODE_HEADER)) {
    fprintf (stderr, "MicroTool: Amount of parsable data in %s is insufficient to contain a microcode header\n", TxtName);
    free (BufferStart);
    return RETURN_VOLUME_CORRUPTED;
  }

  //
  // Can't do much checking on the header because, per the spec, the
  // DataSize field may be 0, which means DataSize = 2000 and TotalSize = 2K,
  // and the TotalSize field is invalid (actually missing). Thus we can't
  // even verify the Reserved fields are 0.
  //
  Micro = (MICROCODE_HEADER *)BufferStart;
  if (Micro->DataSize == 0) {
    Index = 2048;
  } else {
    Index = Micro->TotalSize;
  }

  if (Index != FileLength) {
    fprintf (stderr, "MicroTool: File length of %s (0x%x) does not equal expected TotalSize: 0x%04X\n", TxtName, FileLength, Index);
    free (BufferStart);
    return RETURN_VOLUME_CORRUPTED;
  }

  //
  // Checksum the contents
  //
  Buffer = BufferStart;
  CheckSum  = 0;
  Index     = 0;
  while (Index < FileLength) {
    CheckSum += *Buffer;

    ++Buffer;
    Index += sizeof (*Buffer);
  }

  if (CheckSum != 0) {
    fprintf (stderr, "MicroTool: Checksum (0x%x) failed on file %s\n", CheckSum, TxtName);
    free (BufferStart);
    return RETURN_VOLUME_CORRUPTED;
  }

  UserWriteFile (BinName, BufferStart, FileLength);

  free (BufferStart);

  return RETURN_SUCCESS;
}

static
RETURN_STATUS
Merge (
  IN const char *Output,
  IN const char *FileNames[],
  IN UINT32     NumOfFiles
  )
{
  void      *File;
  uint32_t  FileSize;
  UINT32    Index;
  UINT32    Total;
  char      *Buffer;
  char      *BufferStart;
  UINT32    Addend;

  assert (Output    != NULL);
  assert (FileNames != NULL);

  Total = 0;

  for (Index = 0; Index < NumOfFiles; ++Index) {
    File = UserReadFile (FileNames[Index], &FileSize);
    if (File == NULL) {
      fprintf (stderr, "MicroTool: Could not open %s: %s\n", FileNames[Index], strerror (errno));
      return RETURN_ABORTED;
    }

    Total += ALIGN_VALUE (FileSize, DEFAULT_MC_ALIGNMENT);

    free (File);
  }

  Buffer = calloc (1, Total);
  if (Buffer == NULL) {
    fprintf (stderr, "MicroTool: Could not allocate memory for Buffer\n");
    return RETURN_OUT_OF_RESOURCES;
  }

  BufferStart = Buffer;

  for (Index = 0; Index < NumOfFiles; ++Index) {
    File = UserReadFile (FileNames[Index], &FileSize);
    if (File == NULL) {
      fprintf (stderr, "MicroTool: Could not reopen %s: %s\n", FileNames[Index], strerror (errno));
      free (BufferStart);
      return RETURN_ABORTED;
    }

    memcpy (Buffer, File, FileSize);
    Buffer += FileSize;

    Addend = ALIGN_VALUE_ADDEND (FileSize, DEFAULT_MC_ALIGNMENT);
    memset (Buffer, DEFAULT_MC_PAD_BYTE_VALUE, Addend);
    Buffer += Addend;

    free (File);
  }

  UserWriteFile (Output, BufferStart, Total);

  free (BufferStart);

  return RETURN_SUCCESS;
}

int main (int argc, const char *argv[])
{
  RETURN_STATUS Status;
  UINT32        NumOfFiles;

  if (argc < 2) {
    fprintf (stderr, "MicroTool: No command is specified\n");
    assert (false);
    return -1;
  }

  if (strcmp (argv[1], "TxtToBin") == 0) {
    if (argc < 4) {
      fprintf (stderr, "MicroTool: Command arguments are missing\n");
      fprintf (stderr, "    Usage: MicroTool TxtToBin InputFile OutputFile\n");
      assert (false);
      return -1;
    }

    Status = TxtToBin (argv[2], argv [3]);
    if (RETURN_ERROR (Status)) {
      assert (false);
      return -1;
    }
  } else if (strcmp (argv[1], "Merge") == 0) {
    if (argc < 4) {
      fprintf (stderr, "MicroTool: Command arguments are missing\n");
      fprintf (stderr, "    Usage: MicroTool Merge OutputFile InputFile1 InputFile2 ...\n");
      assert (false);
      return -1;
    }

    NumOfFiles = (UINT32)argc - 3U;

    Status = Merge (argv[2], &argv[3], NumOfFiles);
    if (RETURN_ERROR (Status)) {
      assert (false);
      return -1;
    }
  }

  return 0;
}
