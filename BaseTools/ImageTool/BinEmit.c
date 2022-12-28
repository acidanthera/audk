/** @file
  Copyright (c) 2022, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause
**/

#include "ImageTool.h"

static
EFI_IMAGE_RESOURCE_DIRECTORY_ENTRY *
CreateEntry (
  IN     UINT8    *HiiSectionHeader,
  IN OUT UINT32   *HiiSectionOffset,
  IN     BOOLEAN  DataIsDirectory
  )
{
  EFI_IMAGE_RESOURCE_DIRECTORY        *RDir;
  EFI_IMAGE_RESOURCE_DIRECTORY_ENTRY  *Entry;

  assert (HiiSectionHeader != NULL);
  assert (HiiSectionOffset != NULL);

  RDir                       = (EFI_IMAGE_RESOURCE_DIRECTORY *)(HiiSectionHeader + *HiiSectionOffset);
  *HiiSectionOffset         += sizeof (EFI_IMAGE_RESOURCE_DIRECTORY);
  RDir->NumberOfNamedEntries = 1;

  Entry                    = (EFI_IMAGE_RESOURCE_DIRECTORY_ENTRY *)(HiiSectionHeader + *HiiSectionOffset);
  *HiiSectionOffset       += sizeof (EFI_IMAGE_RESOURCE_DIRECTORY_ENTRY);
  Entry->u1.s.NameIsString = 1;

  if (DataIsDirectory) {
    Entry->u2.s.DataIsDirectory   = 1;
    Entry->u2.s.OffsetToDirectory = *HiiSectionOffset;
  }

  return Entry;
}

static
void
CreateStringEntry (
  IN OUT EFI_IMAGE_RESOURCE_DIRECTORY_ENTRY  *Entry,
  IN     UINT8                               *HiiSectionHeader,
  IN OUT UINT32                              *HiiSectionOffset,
  IN     CHAR16                              *String
  )
{
  EFI_IMAGE_RESOURCE_DIRECTORY_STRING  *RDStr;

  assert (Entry            != NULL);
  assert (HiiSectionHeader != NULL);
  assert (HiiSectionOffset != NULL);
  assert (String           != NULL);

  Entry->u1.s.NameOffset = *HiiSectionOffset;
  RDStr                  = (EFI_IMAGE_RESOURCE_DIRECTORY_STRING *)(HiiSectionHeader + *HiiSectionOffset);
  RDStr->Length          = (UINT16)StrLen (String);
  memcpy (RDStr->String, String, RDStr->Length * sizeof (RDStr->String[0]));
  *HiiSectionOffset += sizeof (*RDStr) + RDStr->Length * sizeof (RDStr->String[0]);
}

static
UINT8 *
CreateHiiResouceSectionHeader (
  OUT UINT32  *HiiHeaderSize,
  IN  UINT32  HiiDataSize
  )
{
  UINT32                              HiiSectionHeaderSize;
  UINT32                              HiiSectionOffset;
  UINT8                               *HiiSectionHeader;
  EFI_IMAGE_RESOURCE_DIRECTORY_ENTRY  *TypeRDirEntry;
  EFI_IMAGE_RESOURCE_DIRECTORY_ENTRY  *NameRDirEntry;
  EFI_IMAGE_RESOURCE_DIRECTORY_ENTRY  *LangRDirEntry;
  EFI_IMAGE_RESOURCE_DATA_ENTRY       *ResourceDataEntry;

  assert (HiiHeaderSize != NULL);
  //
  // Calculate the total size for the resource header (include Type, Name and Language)
  // then allocate memory for whole Hii file.
  //
  HiiSectionHeaderSize = 3 * (sizeof (EFI_IMAGE_RESOURCE_DIRECTORY) + sizeof (EFI_IMAGE_RESOURCE_DIRECTORY_ENTRY)
                              + sizeof (EFI_IMAGE_RESOURCE_DIRECTORY_STRING) + 3 * sizeof (CHAR16)) + sizeof (EFI_IMAGE_RESOURCE_DATA_ENTRY);
  HiiSectionHeader = calloc (1, HiiSectionHeaderSize + HiiDataSize);
  if (HiiSectionHeader == NULL) {
    fprintf (stderr, "ImageTool: Could not allocate memory for Hii\n");
    return NULL;
  }

  HiiSectionOffset = 0;
  //
  // Create Type, Name, Language entries
  //
  TypeRDirEntry = CreateEntry (HiiSectionHeader, &HiiSectionOffset, TRUE);
  NameRDirEntry = CreateEntry (HiiSectionHeader, &HiiSectionOffset, TRUE);
  LangRDirEntry = CreateEntry (HiiSectionHeader, &HiiSectionOffset, FALSE);
  //
  // Create string entry for Type, Name, Language
  //
  CreateStringEntry (TypeRDirEntry, HiiSectionHeader, &HiiSectionOffset, L"HII");
  CreateStringEntry (NameRDirEntry, HiiSectionHeader, &HiiSectionOffset, L"EFI");
  CreateStringEntry (LangRDirEntry, HiiSectionHeader, &HiiSectionOffset, L"BIN");
  //
  // Create Leaf data
  //
  LangRDirEntry->u2.OffsetToData  = HiiSectionOffset;
  ResourceDataEntry               = (EFI_IMAGE_RESOURCE_DATA_ENTRY *)(HiiSectionHeader + HiiSectionOffset);
  HiiSectionOffset               += sizeof (EFI_IMAGE_RESOURCE_DATA_ENTRY);
  ResourceDataEntry->OffsetToData = HiiSectionOffset;
  ResourceDataEntry->Size         = HiiDataSize;

  *HiiHeaderSize = HiiSectionHeaderSize;

  return HiiSectionHeader;
}

RETURN_STATUS
ConstructHii (
  IN  const char  *FileNames[],
  IN  UINT32      NumOfFiles,
  IN  GUID        *HiiGuid,
  OUT void        **Hii,
  OUT UINT32      *HiiSize,
  IN  BOOLEAN     IsElf
  )
{
  UINT8                        *HiiPackageDataPointer;
  EFI_HII_PACKAGE_LIST_HEADER  HiiPackageListHeader;
  EFI_HII_PACKAGE_HEADER       *HiiPackageHeader;
  EFI_IFR_FORM_SET             *IfrFormSet;
  EFI_HII_PACKAGE_HEADER       EndPackage;
  UINT32                       HiiSectionHeaderSize;
  UINT8                        *HiiSectionHeader;
  const char                   *HiiPackageRCFileHeader;
  UINT32                       Index;
  UINT32                       Total;
  UINT8                        *Buffer;
  UINT8                        *BufferStart;
  UINT32                       Step;
  void                         *File;
  UINT32                       FileSize;
  UINT8                        NumberOfFormPackages;
  UINT32                       TempSize;

  assert (Hii       != NULL);
  assert (HiiGuid   != NULL);
  assert (FileNames != NULL);

  NumberOfFormPackages = 0;

  EndPackage.Length = sizeof (EFI_HII_PACKAGE_HEADER);
  EndPackage.Type   = EFI_HII_PACKAGE_END;

  HiiPackageListHeader.PackageLength = sizeof (EFI_HII_PACKAGE_LIST_HEADER) + sizeof (EndPackage);

  for (Index = 0; Index < NumOfFiles; ++Index) {
    File = UserReadFile (FileNames[Index], &FileSize);
    if (File == NULL) {
      fprintf (stderr, "ImageTool: Could not open %s: %s\n", FileNames[Index], strerror (errno));
      return RETURN_ABORTED;
    }

    HiiPackageHeader = (EFI_HII_PACKAGE_HEADER *)File;
    if (HiiPackageHeader->Type == EFI_HII_PACKAGE_FORMS) {
      if (HiiPackageHeader->Length != FileSize) {
        fprintf (stderr, "ImageTool: Wrong package size in HII package file %s\n", FileNames[Index]);
        free (File);
        return RETURN_ABORTED;
      }

      if (IsZeroGuid (HiiGuid)) {
        IfrFormSet = (EFI_IFR_FORM_SET *)(HiiPackageHeader + 1);
        CopyGuid (HiiGuid, &IfrFormSet->Guid);
      }

      ++NumberOfFormPackages;
    }

    HiiPackageListHeader.PackageLength += FileSize;
    free (File);
  }

  if (NumberOfFormPackages > 1) {
    fprintf (stderr, "ImageTool: The input HII packages contain more than one HII Form package\n");
    return RETURN_INVALID_PARAMETER;
  }

  if (IsZeroGuid (HiiGuid)) {
    fprintf (stderr, "ImageTool: HII package list guid is not specified\n");
    return RETURN_ABORTED;
  }

  CopyGuid (&HiiPackageListHeader.PackageListGuid, HiiGuid);

  if (IsElf) {
    HiiSectionHeader = CreateHiiResouceSectionHeader (&HiiSectionHeaderSize, HiiPackageListHeader.PackageLength);
    if (HiiSectionHeader == NULL) {
      return RETURN_OUT_OF_RESOURCES;
    }

    HiiPackageDataPointer = HiiSectionHeader + HiiSectionHeaderSize;

    memcpy (HiiPackageDataPointer, &HiiPackageListHeader, sizeof (HiiPackageListHeader));
    HiiPackageDataPointer += sizeof (HiiPackageListHeader);

    for (Index = 0; Index < NumOfFiles; ++Index) {
      File = UserReadFile (FileNames[Index], &FileSize);
      if (File == NULL) {
        fprintf (stderr, "ImageTool: Could not open %s: %s\n", FileNames[Index], strerror (errno));
        free (HiiSectionHeader);
        return RETURN_ABORTED;
      }

      memcpy (HiiPackageDataPointer, File, FileSize);
      HiiPackageDataPointer += FileSize;

      free (File);
    }

    memcpy (HiiPackageDataPointer, &EndPackage, sizeof (EndPackage));

    *Hii     = HiiSectionHeader;
    *HiiSize = HiiSectionHeaderSize + HiiPackageListHeader.PackageLength;

    return RETURN_SUCCESS;
  }

  HiiPackageRCFileHeader = "//\n//  DO NOT EDIT -- auto-generated file\n//\n\n1 HII\n{";
  HiiSectionHeaderSize   = (UINT32)AsciiStrLen (HiiPackageRCFileHeader);

  TempSize         = HiiSectionHeaderSize + 5 * HiiPackageListHeader.PackageLength;
  HiiSectionHeader = calloc (1, TempSize);
  if (HiiSectionHeader == NULL) {
    fprintf (stderr, "ImageTool: Could not allocate memory for HiiRC\n");
    return RETURN_OUT_OF_RESOURCES;
  }

  Buffer = calloc (1, HiiPackageListHeader.PackageLength);
  if (Buffer == NULL) {
    fprintf (stderr, "ImageTool: Could not allocate memory for Buffer\n");
    free (HiiSectionHeader);
    return RETURN_OUT_OF_RESOURCES;
  }

  BufferStart = Buffer;
  memcpy (Buffer, &HiiPackageListHeader, sizeof (HiiPackageListHeader));
  Buffer += sizeof (HiiPackageListHeader);

  for (Index = 0; Index < NumOfFiles; ++Index) {
    File = UserReadFile (FileNames[Index], &FileSize);
    if (File == NULL) {
      fprintf (stderr, "ImageTool: Could not open %s: %s\n", FileNames[Index], strerror (errno));
      free (HiiSectionHeader);
      free (BufferStart);
      return RETURN_ABORTED;
    }

    memcpy (Buffer, File, FileSize);
    Buffer += FileSize;

    free (File);
  }

  memcpy (Buffer, &EndPackage, sizeof (EndPackage));

  memcpy (HiiSectionHeader, HiiPackageRCFileHeader, HiiSectionHeaderSize);
  HiiPackageDataPointer = HiiSectionHeader + HiiSectionHeaderSize;

  Total  = HiiSectionHeaderSize;
  Buffer = BufferStart;
  for (Index = 0; Index + 2 < HiiPackageListHeader.PackageLength; Index += 2) {
    if (Index % 16 == 0) {
      Step                   = snprintf ((char *)HiiPackageDataPointer, TempSize - Total, "\n ");
      HiiPackageDataPointer += Step;
      Total                 += Step;
    }

    Step                   = snprintf ((char *)HiiPackageDataPointer, TempSize - Total, " 0x%04X,", *(UINT16 *)Buffer);
    HiiPackageDataPointer += Step;
    Total                 += Step;
    Buffer                += 2;
  }

  if (Index % 16 == 0) {
    Step                   = snprintf ((char *)HiiPackageDataPointer, TempSize - Total, "\n ");
    HiiPackageDataPointer += Step;
    Total                 += Step;
  }

  if ((Index + 2) == HiiPackageListHeader.PackageLength) {
    Total += snprintf ((char *)HiiPackageDataPointer, TempSize - Total, " 0x%04X\n}\n", *(UINT16 *)Buffer);
  } else if ((Index + 1) == HiiPackageListHeader.PackageLength) {
    Total += snprintf ((char *)HiiPackageDataPointer, TempSize - Total, " 0x%04X\n}\n", *(UINT8 *)Buffer);
  }

  *Hii     = HiiSectionHeader;
  *HiiSize = Total;

  free (BufferStart);

  return RETURN_SUCCESS;
}
