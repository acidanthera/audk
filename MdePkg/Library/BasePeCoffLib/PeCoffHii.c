/** @file
  Implements APIs to retrieve UEFI HII data from PE/COFF Images.

  Portions copyright (c) 2006 - 2019, Intel Corporation. All rights reserved.<BR>
  Portions copyright (c) 2008 - 2010, Apple Inc. All rights reserved.<BR>
  Portions Copyright (c) 2020, Hewlett Packard Enterprise Development LP. All rights reserved.<BR>
  Copyright (c) 2020, Marvin Häuser. All rights reserved.<BR>
  Copyright (c) 2020, Vitaly Cheptsov. All rights reserved.<BR>
  Copyright (c) 2020, ISP RAS. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-3-Clause
**/

#include "BasePeCoffLibInternals.h"

#include "PeCoffHii.h"

RETURN_STATUS
PeCoffLoaderGetHiiResourceSection (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  OUT UINT32                              *HiiOffset,
  OUT UINT32                              *MaxHiiSize
  )
{
  UINT16                                    Index;
  CONST EFI_IMAGE_NT_HEADERS32              *Pe32Hdr;
  CONST EFI_IMAGE_NT_HEADERS64              *Pe32PlusHdr;
  CONST EFI_IMAGE_DATA_DIRECTORY            *DirectoryEntry;
  CONST EFI_IMAGE_RESOURCE_DIRECTORY        *ResourceDir;
  CONST EFI_IMAGE_RESOURCE_DIRECTORY_ENTRY  *ResourceDirEntry;
  CONST EFI_IMAGE_RESOURCE_DIRECTORY_STRING *ResourceDirString;
  CONST EFI_IMAGE_RESOURCE_DATA_ENTRY       *ResourceDataEntry;
  BOOLEAN                                   Result;
  UINT32                                    Offset;
  UINT32                                    TopOffset;
  UINT8                                     ResourceLevel;
  //
  // Get Image's HII resource section
  //
  switch (Context->ImageType) {
    case ImageTypeTe:
      return RETURN_NOT_FOUND;

    case ImageTypePe32:
      Pe32Hdr = (CONST EFI_IMAGE_NT_HEADERS32 *) (CONST VOID *) (
                  (CONST CHAR8 *) Context->FileBuffer + Context->ExeHdrOffset
                  );
      if (Pe32Hdr->NumberOfRvaAndSizes <= EFI_IMAGE_DIRECTORY_ENTRY_RESOURCE) {
        return RETURN_NOT_FOUND;
      }

      DirectoryEntry = &Pe32Hdr->DataDirectory[EFI_IMAGE_DIRECTORY_ENTRY_RESOURCE];
      break;

    case ImageTypePe32Plus:
      Pe32PlusHdr = (CONST EFI_IMAGE_NT_HEADERS64 *) (CONST VOID *) (
                      (CONST CHAR8 *) Context->FileBuffer + Context->ExeHdrOffset
                      );
      if (Pe32PlusHdr->NumberOfRvaAndSizes <= EFI_IMAGE_DIRECTORY_ENTRY_RESOURCE) {
        return RETURN_NOT_FOUND;
      }

      DirectoryEntry = &Pe32PlusHdr->DataDirectory[EFI_IMAGE_DIRECTORY_ENTRY_RESOURCE];
      break;
  }
  //
  // If we do not at least have one entry, we are lost anyway.
  //
  if (DirectoryEntry->Size < sizeof (EFI_IMAGE_RESOURCE_DIRECTORY) + sizeof (*ResourceDir->Entries)) {
    return RETURN_NOT_FOUND;
  }

  if (!IS_ALIGNED (DirectoryEntry->VirtualAddress, ALIGNOF (EFI_IMAGE_RESOURCE_DIRECTORY))) {
    DEBUG ((DEBUG_WARN, "%u, %u\n", DirectoryEntry->VirtualAddress, DirectoryEntry->Size));
    ASSERT (FALSE);
    return RETURN_UNSUPPORTED;
  }

  Result = BaseOverflowAddU32 (
             DirectoryEntry->VirtualAddress,
             DirectoryEntry->Size,
             &TopOffset
             );
  if (Result || TopOffset > Context->SizeOfImage) {
    ASSERT (FALSE);
    return RETURN_UNSUPPORTED;
  }

  ResourceDir = (CONST EFI_IMAGE_RESOURCE_DIRECTORY *) (CONST VOID *) (
                  (CONST CHAR8 *) Context->ImageBuffer + DirectoryEntry->VirtualAddress
                  );

  STATIC_ASSERT (
    sizeof (*ResourceDirEntry) * MAX_UINT16 <= ((UINT64) MAX_UINT32 + 1U) / 2 - sizeof (EFI_IMAGE_RESOURCE_DIRECTORY),
    "The following arithmetic may overflow."
    );
  TopOffset = sizeof (EFI_IMAGE_RESOURCE_DIRECTORY) + sizeof (*ResourceDirEntry) *
                ((UINT32) ResourceDir->NumberOfNamedEntries + ResourceDir->NumberOfIdEntries);
  if (TopOffset > DirectoryEntry->Size) {
    ASSERT (FALSE);
    return RETURN_UNSUPPORTED;
  }

  for (Index = 0; Index < ResourceDir->NumberOfNamedEntries; ++Index) {
    ResourceDirEntry = &ResourceDir->Entries[Index];
    if (ResourceDirEntry->u1.s.NameIsString == 0) {
      continue;
    }
    //
    // Check the ResourceDirEntry->u1.s.NameOffset before use it.
    //
    Result = BaseOverflowAddU32 (
               ResourceDirEntry->u1.s.NameOffset,
               sizeof (*ResourceDirString) + 3 * sizeof (CHAR16),
               &TopOffset
               );
    if (Result || TopOffset > DirectoryEntry->Size) {
      ASSERT (FALSE);
      return RETURN_UNSUPPORTED;
    }

    Offset = DirectoryEntry->VirtualAddress + ResourceDirEntry->u1.s.NameOffset;
    if (!IS_ALIGNED (Offset, ALIGNOF (EFI_IMAGE_RESOURCE_DIRECTORY_STRING))) {
      ASSERT (FALSE);
      return RETURN_UNSUPPORTED;
    }

    ResourceDirString = (CONST EFI_IMAGE_RESOURCE_DIRECTORY_STRING *) (CONST VOID *) (
                          (CONST CHAR8 *) Context->ImageBuffer + Offset
                          );

    if (ResourceDirString->Length == 3
     && ResourceDirString->String[0] == L'H'
     && ResourceDirString->String[1] == L'I'
     && ResourceDirString->String[2] == L'I') {
      break;
    }
  }

  if (Index == ResourceDir->NumberOfNamedEntries) {
    return RETURN_NOT_FOUND;
  }
  //
  // Resource Type "HII" found
  //
  for (ResourceLevel = 0; ResourceLevel < 2; ++ResourceLevel) {
    if (ResourceDirEntry->u2.s.DataIsDirectory == 0) {
      break;
    }
    //
    // Move to next level - resource Name / Language
    //
    if (ResourceDirEntry->u2.s.OffsetToDirectory > DirectoryEntry->Size - sizeof (EFI_IMAGE_RESOURCE_DIRECTORY) + sizeof (*ResourceDir->Entries)) {
      ASSERT (FALSE);
      return RETURN_UNSUPPORTED;
    }

    Offset = DirectoryEntry->VirtualAddress + ResourceDirEntry->u2.s.OffsetToDirectory;
    if (!IS_ALIGNED (Offset, ALIGNOF (EFI_IMAGE_RESOURCE_DIRECTORY))) {
      ASSERT (FALSE);
      return RETURN_UNSUPPORTED;
    }

    ResourceDir = (CONST EFI_IMAGE_RESOURCE_DIRECTORY *) (CONST VOID *) (
                    (CONST CHAR8 *) Context->ImageBuffer + Offset
                    );

    if ((UINT32) ResourceDir->NumberOfIdEntries + ResourceDir->NumberOfNamedEntries == 0) {
      ASSERT (FALSE);
      return RETURN_UNSUPPORTED;
    }

    ResourceDirEntry = &ResourceDir->Entries[0];
  }
  //
  // Now it ought to be resource Data
  //
  if (ResourceDirEntry->u2.s.DataIsDirectory != 0) {
    ASSERT (FALSE);
    return RETURN_UNSUPPORTED;
  }

  STATIC_ASSERT (
    sizeof (EFI_IMAGE_RESOURCE_DATA_ENTRY) <= sizeof (EFI_IMAGE_RESOURCE_DIRECTORY),
    "The following arithmetic may overflow."
    );
  if (ResourceDirEntry->u2.OffsetToData >= DirectoryEntry->Size - sizeof (EFI_IMAGE_RESOURCE_DATA_ENTRY)) {
    ASSERT (FALSE);
    return RETURN_UNSUPPORTED;
  }

  Offset = DirectoryEntry->VirtualAddress + ResourceDirEntry->u2.OffsetToData;
  if (!IS_ALIGNED (Offset, ALIGNOF (EFI_IMAGE_RESOURCE_DATA_ENTRY))) {
    ASSERT (FALSE);
    return RETURN_UNSUPPORTED;
  }

  ResourceDataEntry = (CONST EFI_IMAGE_RESOURCE_DATA_ENTRY *) (CONST VOID *) (
                        (CONST CHAR8 *) Context->ImageBuffer + Offset
                        );

  Result = BaseOverflowSubU32 (
              Context->SizeOfImage,
              ResourceDataEntry->OffsetToData,
              MaxHiiSize
              );
  if (Result) {
    ASSERT (FALSE);
    return RETURN_UNSUPPORTED;
  }

  *HiiOffset = ResourceDataEntry->OffsetToData;
  return RETURN_SUCCESS;
}
