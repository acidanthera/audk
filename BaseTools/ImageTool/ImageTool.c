/** @file
  Copyright (c) 2021, Marvin Häuser. All rights reserved.
  Copyright (c) 2022, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause
**/

#include "ImageTool.h"
#include <IndustryStandard/Acpi10.h>
#include <IndustryStandard/Acpi30.h>
#include <IndustryStandard/MemoryMappedConfigurationSpaceAccessTable.h>

#include <Library/UefiImageLib.h>

#include "ImageToolEmit.h"

#define EFI_ACPI_1_0_FIRMWARE_ACPI_CONTROL_STRUCTURE_VERSION  0x0

#define DO_NOT_EDIT_HEADER                    \
  "//\n"                                      \
  "//  DO NOT EDIT -- auto-generated file\n"  \
  "//\n"

static
RETURN_STATUS
HiiSrc (
  IN const char  *HiiName,
  IN const char  *Guid,
  IN const char  *FileNames[],
  IN UINT32      NumOfFiles
  )
{
  RETURN_STATUS  Status;
  void           *Hii;
  UINT32         HiiSize;
  GUID           HiiGuid;
  FILE           *FilePtr;
  UINT32         Index;

  Status = AsciiStrToGuid (Guid, &HiiGuid);
  if (RETURN_ERROR (Status)) {
    fprintf (stderr, "ImageTool: Invalid GUID - %s\n", Guid);
    return Status;
  }

  Status = ConstructHii (FileNames, NumOfFiles, &HiiGuid, &Hii, &HiiSize);
  if (RETURN_ERROR (Status)) {
    fprintf (stderr, "ImageTool: Could not construct HiiSrc\n");
    return Status;
  }

  FilePtr = fopen (HiiName, "w");
  if (FilePtr == NULL) {
    FreePool (Hii);
    return RETURN_NO_MEDIA;
  }

  fprintf (
    FilePtr,
    DO_NOT_EDIT_HEADER
    "\n"
    "#include \"AutoGen.h\"\n"
    "\n"
    "typedef struct {\n"
    "  UINT32  Size;\n"
    "  UINT8   Data[%u];\n"
    "} MODULE_HII_PACKAGE_LIST_%u;\n"
    "\n"
    "STATIC_ASSERT (\n"
    "  OFFSET_OF (MODULE_HII_PACKAGE_LIST_%u, Size) == OFFSET_OF (MODULE_HII_PACKAGE_LIST, Size) &&\n"
    "  OFFSET_OF (MODULE_HII_PACKAGE_LIST_%u, Data) == OFFSET_OF (MODULE_HII_PACKAGE_LIST, Header) &&\n"
    "  sizeof (MODULE_HII_PACKAGE_LIST) == sizeof (UINT32) + sizeof (EFI_HII_PACKAGE_LIST_HEADER),\n"
    "  \"MODULE_HII_PACKAGE_LIST does not have the expected structure.\"\n"
    "  );\n"
    "\n"
    "#if defined (__APPLE__)\n"
    "__attribute__ ((section (\"__HII,__hii\")))\n"
    "#elif defined (__GNUC__) || defined (__clang__)\n"
    "__attribute__ ((section (\".hii\")))\n"
    "#elif defined (_MSC_EXTENSIONS)\n"
    "#pragma section (\".hii\", read)\n"
    "__declspec (allocate(\".hii\"))\n"
    "#endif\n"
    "STATIC CONST MODULE_HII_PACKAGE_LIST_%u  mModuleHiiPackageList = {\n"
    "  %u,\n"
    "  {",
    HiiSize,
    HiiSize,
    HiiSize,
    HiiSize,
    HiiSize,
    HiiSize
    );

  for (Index = 0; Index < HiiSize; ++Index) {
    if (Index % 12 == 0) {
      fprintf (FilePtr, "\n   ");
    }

    fprintf (FilePtr, " 0x%02X,", ((const uint8_t *)Hii)[Index]);
  }

  fprintf (
    FilePtr,
    "\n"
    "  }\n"
    "};\n"
    "\n"
    "GLOBAL_REMOVE_IF_UNREFERENCED CONST MODULE_HII_PACKAGE_LIST  *gModuleHiiPackageList =\n"
    "  (CONST MODULE_HII_PACKAGE_LIST *)&mModuleHiiPackageList;\n"
    );

  fclose (FilePtr);
  FreePool (Hii);

  return RETURN_SUCCESS;
}

static
RETURN_STATUS
CheckAcpiTable (
  IN const void  *AcpiTable,
  IN UINT32      Length
  )
{
  const EFI_ACPI_DESCRIPTION_HEADER                   *AcpiHeader;
  const EFI_ACPI_3_0_FIRMWARE_ACPI_CONTROL_STRUCTURE  *Facs;
  UINT32                                              ExpectedLength;

  AcpiHeader = (const EFI_ACPI_DESCRIPTION_HEADER *)AcpiTable;

  if (AcpiHeader->Length > Length) {
    fprintf (stderr, "ImageTool: AcpiTable length section size\n");
    return RETURN_VOLUME_CORRUPTED;
  }

  switch (AcpiHeader->Signature) {
    case EFI_ACPI_3_0_FIXED_ACPI_DESCRIPTION_TABLE_SIGNATURE:
      switch (AcpiHeader->Revision) {
        case EFI_ACPI_1_0_FIXED_ACPI_DESCRIPTION_TABLE_REVISION:
          ExpectedLength = sizeof (EFI_ACPI_1_0_FIXED_ACPI_DESCRIPTION_TABLE);
          break;
        case EFI_ACPI_2_0_FIXED_ACPI_DESCRIPTION_TABLE_REVISION:
          ExpectedLength = sizeof (EFI_ACPI_2_0_FIXED_ACPI_DESCRIPTION_TABLE);
          break;
        case EFI_ACPI_3_0_FIXED_ACPI_DESCRIPTION_TABLE_REVISION:
          ExpectedLength = sizeof (EFI_ACPI_3_0_FIXED_ACPI_DESCRIPTION_TABLE);
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

      if (  (Facs->Version != EFI_ACPI_1_0_FIRMWARE_ACPI_CONTROL_STRUCTURE_VERSION)
         && (Facs->Version != EFI_ACPI_2_0_FIRMWARE_ACPI_CONTROL_STRUCTURE_VERSION)
         && (Facs->Version != EFI_ACPI_3_0_FIRMWARE_ACPI_CONTROL_STRUCTURE_VERSION))
      {
        fprintf (stderr, "ImageTool: FACS version check failed\n");
        return RETURN_VOLUME_CORRUPTED;
      }

      if (  (Facs->Length != sizeof (EFI_ACPI_1_0_FIRMWARE_ACPI_CONTROL_STRUCTURE))
         && (Facs->Length != sizeof (EFI_ACPI_2_0_FIRMWARE_ACPI_CONTROL_STRUCTURE))
         && (Facs->Length != sizeof (EFI_ACPI_3_0_FIRMWARE_ACPI_CONTROL_STRUCTURE)))
      {
        fprintf (stderr, "ImageTool: FACS length check failed\n");
        return RETURN_VOLUME_CORRUPTED;
      }

      break;
    case EFI_ACPI_3_0_DIFFERENTIATED_SYSTEM_DESCRIPTION_TABLE_SIGNATURE:
      if (AcpiHeader->Revision > EFI_ACPI_3_0_DIFFERENTIATED_SYSTEM_DESCRIPTION_TABLE_REVISION) {
        break;
      }

      if (AcpiHeader->Length <= sizeof (EFI_ACPI_DESCRIPTION_HEADER)) {
        fprintf (stderr, "ImageTool: DSDT length check failed\n");
        return RETURN_VOLUME_CORRUPTED;
      }

      break;
    case EFI_ACPI_3_0_MULTIPLE_APIC_DESCRIPTION_TABLE_SIGNATURE:
      if (AcpiHeader->Revision > EFI_ACPI_3_0_MULTIPLE_APIC_DESCRIPTION_TABLE_REVISION) {
        break;
      }

      if (  (AcpiHeader->Revision != EFI_ACPI_1_0_MULTIPLE_APIC_DESCRIPTION_TABLE_REVISION)
         && (AcpiHeader->Revision != EFI_ACPI_2_0_MULTIPLE_APIC_DESCRIPTION_TABLE_REVISION)
         && (AcpiHeader->Revision != EFI_ACPI_3_0_MULTIPLE_APIC_DESCRIPTION_TABLE_REVISION))
      {
        fprintf (stderr, "ImageTool: APIC revision check failed\n");
        return RETURN_VOLUME_CORRUPTED;
      }

      if (AcpiHeader->Length <= (sizeof (EFI_ACPI_DESCRIPTION_HEADER) + sizeof (UINT32) + sizeof (UINT32))) {
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

      if (AcpiHeader->Length <= (sizeof (EFI_ACPI_DESCRIPTION_HEADER) + sizeof (UINT64))) {
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
  IN const char  *PeName,
  IN const char  *AcpiName
  )
{
  RETURN_STATUS                   Status;
  void                            *Pe;
  uint32_t                        PeSize;
  PE_COFF_LOADER_IMAGE_CONTEXT    Context;
  UINT16                          NumberOfSections;
  const EFI_IMAGE_SECTION_HEADER  *Sections;
  UINT16                          Index;
  UINT32                          FileLength;

  Pe = UserReadFile (PeName, &PeSize);
  if (Pe == NULL) {
    fprintf (stderr, "ImageTool: Could not open %s: %s\n", PeName, strerror (errno));
    return RETURN_ABORTED;
  }

  Status = PeCoffInitializeContext (&Context, Pe, (UINT32)PeSize, UefiImageOriginFv);
  if (RETURN_ERROR (Status)) {
    fprintf (stderr, "ImageTool: Could not initialise Context\n");
    free (Pe);
    return Status;
  }

  NumberOfSections = PeCoffGetSectionTable (&Context, &Sections);
  for (Index = 0; Index < NumberOfSections; ++Index) {
    if (  (strcmp ((char *)Sections[Index].Name, ".data") == 0)
       || (strcmp ((char *)Sections[Index].Name, ".sdata") == 0)
       || (strcmp ((char *)Sections[Index].Name, ".rdata") == 0))
    {
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
int32_t
NameToType (
  IN const char  *TypeName
  )
{
  if (  (strcmp (TypeName, "BASE") == 0)
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
     || (strcmp (TypeName, "MM_CORE_STANDALONE") == 0))
  {
    return EFI_IMAGE_SUBSYSTEM_EFI_BOOT_SERVICE_DRIVER;
  }

  if (  (strcmp (TypeName, "UEFI_APPLICATION") == 0)
     || (strcmp (TypeName, "APPLICATION") == 0))
  {
    return EFI_IMAGE_SUBSYSTEM_EFI_APPLICATION;
  }

  if (  (strcmp (TypeName, "DXE_RUNTIME_DRIVER") == 0)
     || (strcmp (TypeName, "RT_DRIVER") == 0))
  {
    return EFI_IMAGE_SUBSYSTEM_EFI_RUNTIME_DRIVER;
  }

  return -1;
}

static
int8_t
NameToFormat (
  IN const char  *FormatName
  )
{
  if (strcmp (FormatName, "UE") == 0) {
    return UefiImageFormatUe;
  }

  if (strcmp (FormatName, "PE") == 0) {
    return UefiImageFormatPe;
  }

  return -1;
}

static
RETURN_STATUS
GenExecutable (
  IN const char  *OutputFileName,
  IN const char  *InputFileName,
  IN const char  *SymbolsPath OPTIONAL,
  IN const char  *FormatName,
  IN const char  *TypeName,
  IN const char  *BaseAddress,
  IN bool        Xip,
  IN bool        Strip,
  IN bool        FixedAddress
  )
{
  UINT32         InputFileSize;
  VOID           *InputFile;
  int8_t         Format;
  int32_t        Type;
  RETURN_STATUS  Status;
  UINT64         NewBaseAddress;
  void           *OutputFile;
  uint32_t       OutputFileSize;

  Format = -1;
  if (FormatName != NULL) {
    Format = NameToFormat (FormatName);
    if (Format == -1) {
      fprintf (stderr, "ImageTool: Unknown output format %s\n", FormatName);
      return RETURN_UNSUPPORTED;
    }
  }

  Type = -1;
  if (TypeName != NULL) {
    Type = NameToType (TypeName);
    if (Type == -1) {
      fprintf (stderr, "ImageTool: Unknown EFI_FILETYPE = %s\n", TypeName);
      return RETURN_UNSUPPORTED;
    }
  }

  NewBaseAddress = 0;
  if (BaseAddress != NULL) {
    Status = AsciiStrHexToUint64S (BaseAddress, NULL, &NewBaseAddress);
    if (RETURN_ERROR (Status)) {
      fprintf (stderr, "ImageTool: Could not convert ASCII string to UINT64\n");
      return Status;
    }
  }

  InputFile = UserReadFile (InputFileName, &InputFileSize);
  if (InputFile == NULL) {
    fprintf (stderr, "ImageTool: Could not open %s: %s\n", InputFileName, strerror (errno));
    return RETURN_ABORTED;
  }

  if (SymbolsPath == NULL) {
    SymbolsPath = InputFileName;
  }

  OutputFile = ToolImageEmit (
                 &OutputFileSize,
                 InputFile,
                 InputFileSize,
                 Format,
                 Type,
                 BaseAddress != NULL,
                 NewBaseAddress,
                 SymbolsPath,
                 Xip,
                 Strip,
                 FixedAddress
                 );

  if (OutputFile == NULL) {
    DEBUG_RAISE ();
    return RETURN_ABORTED;
  }

  UserWriteFile (OutputFileName, OutputFile, OutputFileSize);

  FreePool (OutputFile);

  return RETURN_SUCCESS;
}

int
main (
  int         argc,
  const char  *argv[]
  )
{
  RETURN_STATUS  Status;
  UINT32         NumOfFiles;
  const char     *OutputName;
  const char     *InputName;
  const char     *SymbolsPath;
  const char     *FormatName;
  const char     *TypeName;
  const char     *BaseAddress;
  bool           Xip;
  bool           Strip;
  bool           FixedAddress;
  int            ArgIndex;

  PcdGet8 (PcdUefiImageFormatSupportNonFv) = 0x00;
  PcdGet8 (PcdUefiImageFormatSupportFv)    = 0x03;
  PcdGet32 (PcdImageProtectionPolicy)      = 0x00;

  if (argc < 2) {
    fprintf (stderr, "ImageTool: No command is specified\n");
    DEBUG_RAISE ();
    return -1;
  }

  //
  // The command structure must prefix all output files with "-o" and all
  // following dash-less parameters must be input files due to scanning for
  // these arguments by BaseTools/GenMake.
  //
  if (strcmp (argv[1], "GenImage") == 0) {
    if (argc < 5) {
      fprintf (stderr, "ImageTool: Command arguments are missing\n");
      fprintf (stderr, "    Usage: ImageTool GenImage [-c Format] [-t ModuleType] [-b BaseAddress] [-d SymbolsPath] [-x] [-s] [-f] -o OutputFile InputFile\n");
      DEBUG_RAISE ();
      return -1;
    }

    OutputName   = NULL;
    InputName    = NULL;
    SymbolsPath  = NULL;
    FormatName   = NULL;
    TypeName     = NULL;
    BaseAddress  = NULL;
    Xip          = false;
    Strip        = false;
    FixedAddress = false;
    for (ArgIndex = 2; ArgIndex < argc; ++ArgIndex) {
      if (strcmp (argv[ArgIndex], "-o") == 0) {
        ++ArgIndex;
        if (ArgIndex == argc) {
          fprintf (stderr, "Must specify an argument to -o\n");
          return -1;
        }

        OutputName = argv[ArgIndex];
      } else if (strcmp (argv[ArgIndex], "-c") == 0) {
        ++ArgIndex;
        if (ArgIndex == argc) {
          fprintf (stderr, "Must specify an argument to -c\n");
          return -1;
        }

        FormatName = argv[ArgIndex];
      } else if (strcmp (argv[ArgIndex], "-t") == 0) {
        ++ArgIndex;
        if (ArgIndex == argc) {
          fprintf (stderr, "Must specify an argument to -t\n");
          return -1;
        }

        TypeName = argv[ArgIndex];
      } else if (strcmp (argv[ArgIndex], "-b") == 0) {
        ++ArgIndex;
        if (ArgIndex == argc) {
          fprintf (stderr, "Must specify an argument to -b\n");
          return -1;
        }

        BaseAddress = argv[ArgIndex];
      } else if (strcmp (argv[ArgIndex], "-d") == 0) {
        ++ArgIndex;
        if (ArgIndex == argc) {
          fprintf (stderr, "Must specify an argument to -d\n");
          return -1;
        }

        SymbolsPath = argv[ArgIndex];
      } else if (strcmp (argv[ArgIndex], "-x") == 0) {
        Xip = true;
      } else if (strcmp (argv[ArgIndex], "-s") == 0) {
        Strip = true;
      } else if (strcmp (argv[ArgIndex], "-f") == 0) {
        FixedAddress = true;
      } else if (argv[ArgIndex][0] == '-') {
        fprintf (stderr, "Unknown parameter %s\n", argv[ArgIndex]);
      } else if (InputName == NULL) {
        InputName = argv[ArgIndex];
      } else {
        fprintf (stderr, "GenImage only supports one input file.\n");
        return -1;
      }
    }

    if (OutputName == NULL) {
      fprintf (stderr, "Must provide an output file.\n");
      return -1;
    }

    if (InputName == NULL) {
      fprintf (stderr, "Must provide an input file.\n");
      return -1;
    }

    Status = GenExecutable (
               OutputName,
               InputName,
               SymbolsPath,
               FormatName,
               TypeName,
               BaseAddress,
               Xip,
               Strip,
               FixedAddress
               );
    if (RETURN_ERROR (Status)) {
      DEBUG_RAISE ();
      return -1;
    }
  } else if (strcmp (argv[1], "HiiSrc") == 0) {
    if ((argc < 5) || (strcmp (argv[3], "-o") != 0)) {
      fprintf (stderr, "ImageTool: Command arguments are missing\n");
      fprintf (stderr, "    Usage: ImageTool HiiBin GUID -o OutputFile InputFile1 InputFile2 ...\n");
      DEBUG_RAISE ();
      return -1;
    }

    NumOfFiles = (UINT32)argc - 5U;

    Status = HiiSrc (argv[4], argv[2], &argv[5], NumOfFiles);
    if (RETURN_ERROR (Status)) {
      DEBUG_RAISE ();
      return -1;
    }
  } else if (strcmp (argv[1], "GetAcpi") == 0) {
    if ((argc != 5) || (strcmp (argv[2], "-o") != 0)) {
      fprintf (stderr, "ImageTool: Command arguments are missing\n");
      fprintf (stderr, "    Usage: ImageTool GetAcpi -o OutputFile InputFile\n");
      DEBUG_RAISE ();
      return -1;
    }

    Status = GetAcpi (argv[4], argv[3]);
    if (RETURN_ERROR (Status)) {
      DEBUG_RAISE ();
      return -1;
    }
  }

  return 0;
}
