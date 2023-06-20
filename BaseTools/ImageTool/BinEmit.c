/** @file
  Copyright (c) 2022, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause
**/

#include "ImageTool.h"

#include <Uefi/UefiBaseType.h>
#include <Uefi/UefiSpec.h>

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

  Entry->u1.s.NameOffset = *HiiSectionOffset;
  RDStr                  = (EFI_IMAGE_RESOURCE_DIRECTORY_STRING *)(HiiSectionHeader + *HiiSectionOffset);
  RDStr->Length          = (UINT16)StrLen (String);
  memcpy (RDStr->String, String, RDStr->Length * sizeof (RDStr->String[0]));
  *HiiSectionOffset += sizeof (*RDStr) + RDStr->Length * sizeof (RDStr->String[0]);
}

GLOBAL_REMOVE_IF_UNREFERENCED CONST UINT8 mHiiResourceSectionHeaderSize =
  3 * (sizeof (EFI_IMAGE_RESOURCE_DIRECTORY) + sizeof (EFI_IMAGE_RESOURCE_DIRECTORY_ENTRY)
       + sizeof (EFI_IMAGE_RESOURCE_DIRECTORY_STRING) + 3 * sizeof (CHAR16)) + sizeof (EFI_IMAGE_RESOURCE_DATA_ENTRY);

VOID
InitializeHiiResouceSectionHeader (
  OUT UINT8   *HiiSectionHeader,
  IN  UINT32  HiiDataAddress,
  IN  UINT32  HiiDataSize
  )
{
  UINT32                              HiiSectionOffset;
  EFI_IMAGE_RESOURCE_DIRECTORY_ENTRY  *TypeRDirEntry;
  EFI_IMAGE_RESOURCE_DIRECTORY_ENTRY  *NameRDirEntry;
  EFI_IMAGE_RESOURCE_DIRECTORY_ENTRY  *LangRDirEntry;
  EFI_IMAGE_RESOURCE_DATA_ENTRY       *ResourceDataEntry;

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
  ResourceDataEntry->OffsetToData = HiiDataAddress + HiiSectionOffset;
  ResourceDataEntry->Size         = HiiDataSize;
}

RETURN_STATUS
ConstructHii (
  IN  const char  *FileNames[],
  IN  UINT32      NumOfFiles,
  IN  GUID        *HiiGuid,
  OUT void        **Hii,
  OUT UINT32      *HiiSize
  )
{
  UINT8                        *HiiPackageData;
  UINT8                        *HiiPackageDataPointer;
  EFI_HII_PACKAGE_LIST_HEADER  HiiPackageListHeader;
  EFI_HII_PACKAGE_HEADER       *HiiPackageHeader;
  EFI_IFR_FORM_SET             *IfrFormSet;
  EFI_HII_PACKAGE_HEADER       EndPackage;
  UINT32                       Index;
  void                         *File;
  UINT32                       FileSize;
  UINT8                        NumberOfFormPackages;

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

  HiiPackageData = AllocateZeroPool (HiiPackageListHeader.PackageLength);
  if (HiiPackageData == NULL) {
    return RETURN_OUT_OF_RESOURCES;
  }

  memmove (HiiPackageData, &HiiPackageListHeader, sizeof (HiiPackageListHeader));

  HiiPackageDataPointer = HiiPackageData + sizeof (HiiPackageListHeader);
  for (Index = 0; Index < NumOfFiles; ++Index) {
    File = UserReadFile (FileNames[Index], &FileSize);
    if (File == NULL) {
      fprintf (stderr, "ImageTool: Could not open %s: %s\n", FileNames[Index], strerror (errno));
      free (HiiPackageData);
      return RETURN_ABORTED;
    }

    memmove (HiiPackageDataPointer, File, FileSize);
    HiiPackageDataPointer += FileSize;

    free (File);
  }

  memmove (HiiPackageDataPointer, &EndPackage, sizeof (EndPackage));

  *Hii     = HiiPackageData;
  *HiiSize = HiiPackageListHeader.PackageLength;

  return RETURN_SUCCESS;
}
