/** @file
  Copyright (c) 2021, Marvin Häuser. All rights reserved.
  Copyright (c) 2022, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause
**/

#include "ImageTool.h"
#include <IndustryStandard/Acpi10.h>
#include <IndustryStandard/Acpi30.h>
#include <IndustryStandard/MemoryMappedConfigurationSpaceAccessTable.h>

#define EFI_ACPI_1_0_FIRMWARE_ACPI_CONTROL_STRUCTURE_VERSION  0x0

image_tool_image_info_t mImageInfo;


static
RETURN_STATUS
HiiBin (
  IN const char *HiiName,
  IN const char *Guid,
  IN const char *FileNames[],
  IN UINT32     NumOfFiles,
  IN BOOLEAN    IsElf
  )
{
  RETURN_STATUS Status;
  void          *Hii;
  UINT32        HiiSize;
  GUID          HiiGuid;

  assert (FileNames != NULL);
  assert (HiiName   != NULL);
  assert (Guid      != NULL);

  Status = AsciiStrToGuid (Guid, &HiiGuid);
  if (RETURN_ERROR (Status)) {
    fprintf (stderr, "ImageTool: Invalid GUID - %s\n", Guid);
    return Status;
  }

  Status = ConstructHii (FileNames, NumOfFiles, &HiiGuid, &Hii, &HiiSize, IsElf);
  if (RETURN_ERROR (Status)) {
    fprintf (stderr, "ImageTool: Could not construct HiiBin\n");
    return Status;
  }

  UserWriteFile (HiiName, Hii, HiiSize);

  free (Hii);

  return RETURN_SUCCESS;
}

static
RETURN_STATUS
Rebase (
  IN const char *BaseAddress,
  IN const char *OldName,
  IN const char *NewName
  )
{
  RETURN_STATUS                Status;
  void                         *Pe;
  uint32_t                     PeSize;
  UINT64                       NewBaseAddress;
  PE_COFF_LOADER_IMAGE_CONTEXT Context;
  EFI_IMAGE_NT_HEADERS         *PeHdr;

  assert (BaseAddress != NULL);
  assert (OldName     != NULL);
  assert (NewName     != NULL);

  Status = AsciiStrHexToUint64S (BaseAddress, NULL, &NewBaseAddress);
  if (RETURN_ERROR (Status)) {
    fprintf (stderr, "ImageTool: Could not convert ASCII string to UINT64\n");
    return Status;
  }
#ifdef EFI_TARGET32
  if (NewBaseAddress > MAX_UINT32) {
    fprintf (stderr, "ImageTool: New Base Address exceeds MAX value\n");
    return RETURN_INVALID_PARAMETER;
  }
#endif

  Pe = UserReadFile (OldName, &PeSize);
  if (Pe == NULL) {
    fprintf (stderr, "ImageTool: Could not open %s: %s\n", OldName, strerror (errno));
    return RETURN_ABORTED;
  }

  Status = PeCoffInitializeContext (&Context, Pe, (UINT32)PeSize);
  if (RETURN_ERROR (Status)) {
    fprintf (stderr, "ImageTool: Could not initialise Context\n");
    free (Pe);
    return Status;
  }

  Context.ImageBuffer = (void *)Context.FileBuffer;

  Status = PeCoffRelocateImage (&Context, NewBaseAddress, NULL, 0);
  if (EFI_ERROR (Status)) {
    fprintf (stderr, "ImageTool: Could not relocate image\n");
    free (Pe);
    return Status;
  }

  PeHdr = (EFI_IMAGE_NT_HEADERS *)(void *)((char *)Context.ImageBuffer + Context.ExeHdrOffset);
#ifdef EFI_TARGET32
  PeHdr->ImageBase = (UINT32)NewBaseAddress;
#else
  PeHdr->ImageBase = NewBaseAddress;
#endif

  UserWriteFile (NewName, Pe, PeSize);

  free (Pe);

  return RETURN_SUCCESS;
}

static
RETURN_STATUS
CheckAcpiTable (
  IN const void *AcpiTable,
  IN UINT32     Length
  )
{
  const EFI_ACPI_DESCRIPTION_HEADER                  *AcpiHeader;
  const EFI_ACPI_3_0_FIRMWARE_ACPI_CONTROL_STRUCTURE *Facs;
  UINT32                                             ExpectedLength;

  AcpiHeader = (const EFI_ACPI_DESCRIPTION_HEADER *)AcpiTable;

  if (AcpiHeader->Length > Length) {
    fprintf (stderr, "ImageTool: AcpiTable length section size\n");
    return RETURN_VOLUME_CORRUPTED;
  }

  switch (AcpiHeader->Signature) {
  case EFI_ACPI_3_0_FIXED_ACPI_DESCRIPTION_TABLE_SIGNATURE:
    switch (AcpiHeader->Revision) {
    case EFI_ACPI_1_0_FIXED_ACPI_DESCRIPTION_TABLE_REVISION:
      ExpectedLength = sizeof(EFI_ACPI_1_0_FIXED_ACPI_DESCRIPTION_TABLE);
      break;
    case EFI_ACPI_2_0_FIXED_ACPI_DESCRIPTION_TABLE_REVISION:
      ExpectedLength = sizeof(EFI_ACPI_2_0_FIXED_ACPI_DESCRIPTION_TABLE);
      break;
    case EFI_ACPI_3_0_FIXED_ACPI_DESCRIPTION_TABLE_REVISION:
      ExpectedLength = sizeof(EFI_ACPI_3_0_FIXED_ACPI_DESCRIPTION_TABLE);
      break;
    default:
      if (AcpiHeader->Revision > EFI_ACPI_3_0_FIXED_ACPI_DESCRIPTION_TABLE_REVISION) {
        ExpectedLength = AcpiHeader->Length;
        break;
      }
      fprintf (stderr, "ImageTool: FACP revision check failed\n");
      return RETURN_VOLUME_CORRUPTED;
    }

    if (ExpectedLength != AcpiHeader->Length) {
      fprintf (stderr, "ImageTool: FACP length check failed\n");
      return RETURN_VOLUME_CORRUPTED;
    }
    break;
  case EFI_ACPI_3_0_FIRMWARE_ACPI_CONTROL_STRUCTURE_SIGNATURE:
    Facs = (const EFI_ACPI_3_0_FIRMWARE_ACPI_CONTROL_STRUCTURE *)AcpiTable;
    if (Facs->Version > EFI_ACPI_3_0_FIRMWARE_ACPI_CONTROL_STRUCTURE_VERSION) {
      break;
    }

    if ((Facs->Version != EFI_ACPI_1_0_FIRMWARE_ACPI_CONTROL_STRUCTURE_VERSION)
      && (Facs->Version != EFI_ACPI_2_0_FIRMWARE_ACPI_CONTROL_STRUCTURE_VERSION)
      && (Facs->Version != EFI_ACPI_3_0_FIRMWARE_ACPI_CONTROL_STRUCTURE_VERSION)) {
      fprintf (stderr, "ImageTool: FACS version check failed\n");
      return RETURN_VOLUME_CORRUPTED;
    }

    if ((Facs->Length != sizeof(EFI_ACPI_1_0_FIRMWARE_ACPI_CONTROL_STRUCTURE))
      && (Facs->Length != sizeof(EFI_ACPI_2_0_FIRMWARE_ACPI_CONTROL_STRUCTURE))
      && (Facs->Length != sizeof(EFI_ACPI_3_0_FIRMWARE_ACPI_CONTROL_STRUCTURE))) {
      fprintf (stderr, "ImageTool: FACS length check failed\n");
      return RETURN_VOLUME_CORRUPTED;
    }
    break;
  case EFI_ACPI_3_0_DIFFERENTIATED_SYSTEM_DESCRIPTION_TABLE_SIGNATURE:
    if (AcpiHeader->Revision > EFI_ACPI_3_0_DIFFERENTIATED_SYSTEM_DESCRIPTION_TABLE_REVISION) {
      break;
    }

    if (AcpiHeader->Length <= sizeof(EFI_ACPI_DESCRIPTION_HEADER)) {
      fprintf (stderr, "ImageTool: DSDT length check failed\n");
      return RETURN_VOLUME_CORRUPTED;
    }
    break;
  case EFI_ACPI_3_0_MULTIPLE_APIC_DESCRIPTION_TABLE_SIGNATURE:
    if (AcpiHeader->Revision > EFI_ACPI_3_0_MULTIPLE_APIC_DESCRIPTION_TABLE_REVISION) {
      break;
    }

    if ((AcpiHeader->Revision != EFI_ACPI_1_0_MULTIPLE_APIC_DESCRIPTION_TABLE_REVISION)
      && (AcpiHeader->Revision != EFI_ACPI_2_0_MULTIPLE_APIC_DESCRIPTION_TABLE_REVISION)
      && (AcpiHeader->Revision != EFI_ACPI_3_0_MULTIPLE_APIC_DESCRIPTION_TABLE_REVISION)) {
      fprintf (stderr, "ImageTool: APIC revision check failed\n");
      return RETURN_VOLUME_CORRUPTED;
    }

    if (AcpiHeader->Length <= (sizeof(EFI_ACPI_DESCRIPTION_HEADER) + sizeof(UINT32) + sizeof(UINT32))) {
      fprintf (stderr, "ImageTool: APIC length check failed\n");
      return RETURN_VOLUME_CORRUPTED;
    }
    break;
  case EFI_ACPI_3_0_PCI_EXPRESS_MEMORY_MAPPED_CONFIGURATION_SPACE_BASE_ADDRESS_DESCRIPTION_TABLE_SIGNATURE:
    if (AcpiHeader->Revision > EFI_ACPI_MEMORY_MAPPED_CONFIGURATION_SPACE_ACCESS_TABLE_REVISION) {
      break;
    }

    if (AcpiHeader->Revision != EFI_ACPI_MEMORY_MAPPED_CONFIGURATION_SPACE_ACCESS_TABLE_REVISION) {
      fprintf (stderr, "ImageTool: MCFG revision check failed\n");
      return RETURN_VOLUME_CORRUPTED;
    }

    if (AcpiHeader->Length <= (sizeof(EFI_ACPI_DESCRIPTION_HEADER) + sizeof(UINT64))) {
      fprintf (stderr, "ImageTool: MCFG length check failed\n");
      return RETURN_VOLUME_CORRUPTED;
    }
    break;
  default:
    break;
  }

  return RETURN_SUCCESS;
}

static
RETURN_STATUS
GetAcpi (
  IN const char *PeName,
  IN const char *AcpiName
  )
{
  RETURN_STATUS                  Status;
  void                           *Pe;
  uint32_t                       PeSize;
  PE_COFF_LOADER_IMAGE_CONTEXT   Context;
  UINT16                         NumberOfSections;
  const EFI_IMAGE_SECTION_HEADER *Sections;
  UINT16                         Index;
  UINT32                         FileLength;

  assert (PeName   != NULL);
  assert (AcpiName != NULL);

  Pe = UserReadFile (PeName, &PeSize);
  if (Pe == NULL) {
    fprintf (stderr, "ImageTool: Could not open %s: %s\n", PeName, strerror (errno));
    return RETURN_ABORTED;
  }

  Status = PeCoffInitializeContext (&Context, Pe, (UINT32)PeSize);
  if (RETURN_ERROR (Status)) {
    fprintf (stderr, "ImageTool: Could not initialise Context\n");
    free (Pe);
    return Status;
  }

  NumberOfSections = PeCoffGetSectionTable (&Context, &Sections);
  for (Index = 0; Index < NumberOfSections; ++Index) {
    if ((strcmp ((char *)Sections[Index].Name, ".data") == 0)
      || (strcmp ((char *)Sections[Index].Name, ".sdata") == 0)
      || (strcmp ((char *)Sections[Index].Name, ".rdata") == 0)) {

      if (Sections[Index].VirtualSize < Sections[Index].SizeOfRawData) {
        FileLength = Sections[Index].VirtualSize;
      } else {
        FileLength = Sections[Index].SizeOfRawData;
      }

      Status = CheckAcpiTable ((char *)Context.FileBuffer + Sections[Index].PointerToRawData, FileLength);
      if (RETURN_ERROR (Status)) {
        free (Pe);
        return Status;
      }

      UserWriteFile (AcpiName, (char *)Context.FileBuffer + Sections[Index].PointerToRawData, FileLength);

      free (Pe);

      return RETURN_SUCCESS;
    }
  }

  return RETURN_NOT_FOUND;
}

static
bool
ImageSetModuleType (
  OUT image_tool_image_info_t  *Image,
  IN  const char               *TypeName
  )
{
  uint16_t  ModuleType;

  assert (Image != NULL);

  if ((strcmp (TypeName, "BASE") == 0)
    || (strcmp (TypeName, "SEC") == 0)
    || (strcmp (TypeName, "SECURITY_CORE") == 0)
    || (strcmp (TypeName, "PEI_CORE") == 0)
    || (strcmp (TypeName, "PEIM") == 0)
    || (strcmp (TypeName, "COMBINED_PEIM_DRIVER") == 0)
    || (strcmp (TypeName, "PIC_PEIM") == 0)
    || (strcmp (TypeName, "RELOCATABLE_PEIM") == 0)
    || (strcmp (TypeName, "DXE_CORE") == 0)
    || (strcmp (TypeName, "BS_DRIVER") == 0)
    || (strcmp (TypeName, "DXE_DRIVER") == 0)
    || (strcmp (TypeName, "DXE_SMM_DRIVER") == 0)
    || (strcmp (TypeName, "UEFI_DRIVER") == 0)
    || (strcmp (TypeName, "SMM_CORE") == 0)
    || (strcmp (TypeName, "MM_STANDALONE") == 0)
    || (strcmp (TypeName, "MM_CORE_STANDALONE") == 0)) {
      ModuleType = EFI_IMAGE_SUBSYSTEM_EFI_BOOT_SERVICE_DRIVER;
  } else if ((strcmp (TypeName, "UEFI_APPLICATION") == 0)
    || (strcmp (TypeName, "APPLICATION") == 0)) {
      ModuleType = EFI_IMAGE_SUBSYSTEM_EFI_APPLICATION;
  } else if ((strcmp (TypeName, "DXE_RUNTIME_DRIVER") == 0)
    || (strcmp (TypeName, "RT_DRIVER") == 0)) {
      ModuleType = EFI_IMAGE_SUBSYSTEM_EFI_RUNTIME_DRIVER;
  } else if ((strcmp (TypeName, "DXE_SAL_DRIVER") == 0)
    || (strcmp (TypeName, "SAL_RT_DRIVER") == 0)) {
      ModuleType = EFI_IMAGE_SUBSYSTEM_SAL_RUNTIME_DRIVER;
  } else {
    fprintf (stderr, "ImageTool: Unknown EFI_FILETYPE = %s\n", TypeName);
    return false;
  }

  Image->HeaderInfo.Subsystem = ModuleType;

  return true;
}

static
RETURN_STATUS
GenExecutable (
  IN const char  *OutputFileName,
  IN const char  *InputFileName,
  IN const char  *FormatName,
  IN const char  *TypeName
  )
{
  UINT32         InputFileSize;
  VOID           *InputFile;
  RETURN_STATUS  Status;
  bool           Result;
  void           *OutputFile;
  uint32_t       OutputFileSize;

  InputFile = UserReadFile (InputFileName, &InputFileSize);
  if (InputFile == NULL) {
    fprintf (stderr, "ImageTool: Could not open %s: %s\n", InputFileName, strerror (errno));
    return RETURN_ABORTED;
  }

  Status = ToolContextConstructPe (&mImageInfo, InputFile, InputFileSize);
  if (Status == RETURN_UNSUPPORTED) {
    Status = ScanElf (InputFile, InputFileSize, InputFileName);
  }

  free (InputFile);

  if (RETURN_ERROR (Status)) {
    fprintf (stderr, "ImageTool: Could not parse input file %s - %llx\n", InputFileName, (unsigned long long)Status);
    return Status;
  }

  if (TypeName != NULL) {
    Result = ImageSetModuleType (&mImageInfo, TypeName);
    if (!Result) {
      ToolImageDestruct (&mImageInfo);
      return RETURN_UNSUPPORTED;
    }
  }

  Result = CheckToolImage (&mImageInfo);
  if (!Result) {
    ToolImageDestruct (&mImageInfo);
    return RETURN_UNSUPPORTED;
  }

  if (strcmp (FormatName, "PE") == 0) {
    OutputFile = ToolImageEmitPe (&mImageInfo, &OutputFileSize);
  } else {
    assert (false);
  }

  ToolImageDestruct (&mImageInfo);

  if (OutputFile == NULL) {
    return RETURN_ABORTED;
  }

  UserWriteFile (OutputFileName, OutputFile, OutputFileSize);

  free (OutputFile);

  return RETURN_SUCCESS;
}

int main (int argc, const char *argv[])
{
  RETURN_STATUS Status;
  UINT32        NumOfFiles;

  if (argc < 2) {
    fprintf (stderr, "ImageTool: No command is specified\n");
    raise ();
    return -1;
  }

  if (strcmp (argv[1], "ElfToPe") == 0 || strcmp (argv[1], "PeXip") == 0) {
    if (argc < 5) {
      fprintf (stderr, "ImageTool: Command arguments are missing\n");
      fprintf (stderr, "    Usage: ImageTool %s InputFile OutputFile ModuleType\n", argv[1]);
      raise ();
      return -1;
    }

    Status = GenExecutable (argv[3], argv[2], "PE", argv[4]);
    if (RETURN_ERROR (Status)) {
      raise ();
      return -1;
    }
  } else if (strcmp (argv[1], "HiiBinElf") == 0) {
    if (argc < 5) {
      fprintf (stderr, "ImageTool: Command arguments are missing\n");
      fprintf (stderr, "    Usage: ImageTool HiiBinElf OutputFile GUID InputFile1 InputFile2 ...\n");
      raise ();
      return -1;
    }

    NumOfFiles = (UINT32)argc - 4U;

    Status = HiiBin (argv[2], argv[3], &argv[4], NumOfFiles, TRUE);
    if (RETURN_ERROR (Status)) {
      raise ();
      return -1;
    }
  } else if (strcmp (argv[1], "HiiBinPe") == 0) {
    if (argc < 5) {
      fprintf (stderr, "ImageTool: Command arguments are missing\n");
      fprintf (stderr, "    Usage: ImageTool HiiBinPe OutputFile GUID InputFile1 InputFile2 ...\n");
      raise ();
      return -1;
    }

    NumOfFiles = (UINT32)argc - 4U;

    Status = HiiBin (argv[2], argv[3], &argv[4], NumOfFiles, FALSE);
    if (RETURN_ERROR (Status)) {
      raise ();
      return -1;
    }
  } else if (strcmp (argv[1], "Rebase") == 0) {
    if (argc < 5) {
      fprintf (stderr, "ImageTool: Command arguments are missing\n");
      fprintf (stderr, "    Usage: ImageTool Rebase Address InputFile OutputFile\n");
      raise ();
      return -1;
    }

    Status = Rebase (argv[2], argv[3], argv[4]);
    if (RETURN_ERROR (Status)) {
      raise ();
      return -1;
    }
  } else if (strcmp (argv[1], "GetAcpi") == 0) {
    if (argc < 4) {
      fprintf (stderr, "ImageTool: Command arguments are missing\n");
      fprintf (stderr, "    Usage: ImageTool GetAcpi InputFile OutputFile\n");
      raise ();
      return -1;
    }

    Status = GetAcpi (argv[2], argv[3]);
    if (RETURN_ERROR (Status)) {
      raise ();
      return -1;
    }
  }

  return 0;
}
