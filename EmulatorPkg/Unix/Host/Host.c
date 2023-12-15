/*++ @file

Copyright (c) 2006 - 2022, Intel Corporation. All rights reserved.<BR>
Portions copyright (c) 2008 - 2011, Apple Inc. All rights reserved.<BR>
SPDX-License-Identifier: BSD-2-Clause-Patent

**/

#include "Host.h"

#ifdef __APPLE__
#define MAP_ANONYMOUS  MAP_ANON
#endif

//
// Globals
//

EMU_THUNK_PPI  mSecEmuThunkPpi = {
  GasketSecUnixPeiAutoScan,
  GasketSecUnixFdAddress,
  GasketSecEmuThunkAddress
};

char          *gGdbWorkingFileName      = NULL;
unsigned int  mScriptSymbolChangesCount = 0;

//
// Default information about where the FD is located.
//  This array gets filled in with information from EFI_FIRMWARE_VOLUMES
//  EFI_FIRMWARE_VOLUMES is a host environment variable set by system.cmd.
//  The number of array elements is allocated base on parsing
//  EFI_FIRMWARE_VOLUMES and the memory is never freed.
//
UINTN        gFdInfoCount = 0;
EMU_FD_INFO  *gFdInfo;

//
// Array that supports separate memory ranges.
//  The memory ranges are set in system.cmd via the EFI_MEMORY_SIZE variable.
//  The number of array elements is allocated base on parsing
//  EFI_MEMORY_SIZE and the memory is never freed.
//
UINTN              gSystemMemoryCount = 0;
EMU_SYSTEM_MEMORY  *gSystemMemory;

EFI_PEI_PPI_DESCRIPTOR  *gPpiList;

int  gInXcode = 0;

/*++
  Breakpoint target for Xcode project. Set in the Xcode XML

  Xcode breakpoint will 'source Host.gdb'
  gGdbWorkingFileName is set to Host.gdb

**/
VOID
SecGdbConfigBreak (
  VOID
  )
{
}

/*++

Routine Description:
  Main entry point to SEC for Unix. This is a unix program

Arguments:
  Argc - Number of command line arguments
  Argv - Array of command line argument strings
  Envp - Array of environment variable strings

Returns:
  0 - Normal exit
  1 - Abnormal exit

**/
int
main (
  IN  int   Argc,
  IN  char  **Argv,
  IN  char  **Envp
  )
{
  EFI_STATUS            Status;
  EFI_PHYSICAL_ADDRESS  InitialStackMemory;
  UINT64                InitialStackMemorySize;
  UINTN                 Index;
  UINTN                 Index1;
  UINTN                 Index2;
  UINTN                 PeiIndex;
  CHAR8                 *FileName;
  BOOLEAN               Done;
  EFI_PEI_FILE_HANDLE   FileHandle;
  VOID                  *SecFile;
  UINT32                SecFileSize;
  CHAR16                *MemorySizeStr;
  CHAR16                *FirmwareVolumesStr;
  UINTN                 *StackPointer;
  FILE                  *GdbTempFile;
  EMU_THUNK_PPI         *SecEmuThunkPpi;
  UINT32                AuthenticationStatus;

  //
  // Xcode does not support sourcing gdb scripts directly, so the Xcode XML
  // has a break point script to source the GdbRun.sh script.
  //
  SecGdbConfigBreak ();

  //
  // We build a gdb script to allow the symbols to be loaded.
  //
  Index               = strlen (*Argv);
  gGdbWorkingFileName = AllocatePool (Index + strlen (".gdb") + 1);
  strcpy (gGdbWorkingFileName, *Argv);
  strcat (gGdbWorkingFileName, ".gdb");

  //
  // Empty out the gdb symbols script file.
  //
  GdbTempFile = fopen (gGdbWorkingFileName, "w");
  if (GdbTempFile != NULL) {
    fclose (GdbTempFile);
  }

  printf ("\nEDK II UNIX Host Emulation Environment from http://www.tianocore.org/edk2/\n");

  setbuf (stdout, 0);
  setbuf (stderr, 0);

  MemorySizeStr      = (CHAR16 *)PcdGetPtr (PcdEmuMemorySize);
  FirmwareVolumesStr = (CHAR16 *)PcdGetPtr (PcdEmuFirmwareVolume);

  //
  // PPIs pased into PEI_CORE
  //
  SecEmuThunkPpi = AllocateZeroPool (sizeof (EMU_THUNK_PPI) + FixedPcdGet32 (PcdPersistentMemorySize));
  if (SecEmuThunkPpi == NULL) {
    printf ("ERROR : Can not allocate memory for SecEmuThunkPpi.  Exiting.\n");
    exit (1);
  }

  CopyMem (SecEmuThunkPpi, &mSecEmuThunkPpi, sizeof (EMU_THUNK_PPI));
  SecEmuThunkPpi->Argc                 = Argc;
  SecEmuThunkPpi->Argv                 = Argv;
  SecEmuThunkPpi->Envp                 = Envp;
  SecEmuThunkPpi->PersistentMemorySize = FixedPcdGet32 (PcdPersistentMemorySize);
  AddThunkPpi (EFI_PEI_PPI_DESCRIPTOR_PPI, &gEmuThunkPpiGuid, SecEmuThunkPpi);

  SecInitThunkProtocol ();

  //
  // Emulator Bus Driver Thunks
  //
  AddThunkProtocol (&gX11ThunkIo, (CHAR16 *)PcdGetPtr (PcdEmuGop), TRUE);
  AddThunkProtocol (&gPosixFileSystemThunkIo, (CHAR16 *)PcdGetPtr (PcdEmuFileSystem), TRUE);
  AddThunkProtocol (&gBlockIoThunkIo, (CHAR16 *)PcdGetPtr (PcdEmuVirtualDisk), TRUE);
  AddThunkProtocol (&gSnpThunkIo, (CHAR16 *)PcdGetPtr (PcdEmuNetworkInterface), TRUE);

  //
  // Emulator other Thunks
  //
  AddThunkProtocol (&gPthreadThunkIo, (CHAR16 *)PcdGetPtr (PcdEmuApCount), FALSE);

  // EmuSecLibConstructor ();

  gPpiList = GetThunkPpiList ();

  //
  // Allocate space for gSystemMemory Array
  //
  gSystemMemoryCount = CountSeparatorsInString (MemorySizeStr, '!') + 1;
  gSystemMemory      = AllocateZeroPool (gSystemMemoryCount * sizeof (EMU_SYSTEM_MEMORY));
  if (gSystemMemory == NULL) {
    printf ("ERROR : Can not allocate memory for system.  Exiting.\n");
    exit (1);
  }

  //
  // Allocate space for gSystemMemory Array
  //
  gFdInfoCount = CountSeparatorsInString (FirmwareVolumesStr, '!') + 1;
  gFdInfo      = AllocateZeroPool (gFdInfoCount * sizeof (EMU_FD_INFO));
  if (gFdInfo == NULL) {
    printf ("ERROR : Can not allocate memory for fd info.  Exiting.\n");
    exit (1);
  }

  printf ("  BootMode 0x%02x\n", (unsigned int)PcdGet32 (PcdEmuBootMode));

  //
  // Open up a 128K file to emulate temp memory for SEC.
  //  on a real platform this would be SRAM, or using the cache as RAM.
  //  Set InitialStackMemory to zero so UnixOpenFile will allocate a new mapping
  //
  InitialStackMemorySize = STACK_SIZE;
  InitialStackMemory     = (UINTN)MapMemory (
                                    0,
                                    (UINT32)InitialStackMemorySize,
                                    PROT_READ | PROT_WRITE | PROT_EXEC,
                                    MAP_ANONYMOUS | MAP_PRIVATE
                                    );
  if (InitialStackMemory == 0) {
    printf ("ERROR : Can not open SecStack Exiting\n");
    exit (1);
  }

  printf (
    "  OS Emulator passing in %u KB of temp RAM at 0x%08lx to SEC\n",
    (unsigned int)(InitialStackMemorySize / 1024),
    (unsigned long)InitialStackMemory
    );

  for (StackPointer = (UINTN *)(UINTN)InitialStackMemory;
       StackPointer < (UINTN *)(UINTN)((UINTN)InitialStackMemory + (UINT64)InitialStackMemorySize);
       StackPointer++)
  {
    *StackPointer = 0x5AA55AA5;
  }

  //
  // Open All the firmware volumes and remember the info in the gFdInfo global
  //
  FileName = (CHAR8 *)AllocatePool (StrLen (FirmwareVolumesStr) + 1);
  if (FileName == NULL) {
    printf ("ERROR : Can not allocate memory for firmware volume string\n");
    exit (1);
  }

  Index2 = 0;
  for (Done = FALSE, Index = 0, PeiIndex = 0, SecFile = NULL;
       FirmwareVolumesStr[Index2] != 0;
       Index++)
  {
    for (Index1 = 0; (FirmwareVolumesStr[Index2] != '!') && (FirmwareVolumesStr[Index2] != 0); Index2++) {
      FileName[Index1++] = FirmwareVolumesStr[Index2];
    }

    if (FirmwareVolumesStr[Index2] == '!') {
      Index2++;
    }

    FileName[Index1] = '\0';

    if (Index == 0) {
      // Map FV Recovery Read Only and other areas Read/Write
      Status = MapFd0 (
                 FileName,
                 &gFdInfo[0].Address,
                 &gFdInfo[0].Size
                 );
    } else {
      //
      // Open the FD and remember where it got mapped into our processes address space
      // Maps Read Only
      //
      Status = MapFile (
                 FileName,
                 &gFdInfo[Index].Address,
                 &gFdInfo[Index].Size
                 );
    }

    if (EFI_ERROR (Status)) {
      printf ("ERROR : Can not open Firmware Device File %s (%x).  Exiting.\n", FileName, (unsigned int)Status);
      exit (1);
    }

    printf ("  FD loaded from %s at 0x%08lx", FileName, (unsigned long)gFdInfo[Index].Address);

    if (SecFile == NULL) {
      //
      // Assume the beginning of the FD is an FV and look for the SEC Core.
      // Load the first one we find.
      //
      FileHandle = NULL;
      Status     = PeiServicesFfsFindNextFile (
                     EFI_FV_FILETYPE_SECURITY_CORE,
                     (EFI_PEI_FV_HANDLE)(UINTN)gFdInfo[Index].Address,
                     &FileHandle
                     );
      if (!EFI_ERROR (Status)) {
        Status = PeiServicesFfsFindSectionData4 (
                   EFI_SECTION_PE32,
                   0,
                   FileHandle,
                   &SecFile,
                   &SecFileSize,
                   &AuthenticationStatus
                   );
        if (!EFI_ERROR (Status)) {
          PeiIndex = Index;
          printf (" contains SEC Core");
        }
      }
    }

    printf ("\n");
  }

  if (SecFile == NULL) {
    printf ("ERROR : SEC not found!\n");
    exit (1);
  }

  //
  // Calculate memory regions and store the information in the gSystemMemory
  //  global for later use. The autosizing code will use this data to
  //  map this memory into the SEC process memory space.
  //
  Index1 = 0;
  Index  = 0;
  while (1) {
    UINTN  val = 0;
    //
    // Save the size of the memory.
    //
    while (MemorySizeStr[Index1] >= '0' && MemorySizeStr[Index1] <= '9') {
      val = val * 10 + MemorySizeStr[Index1] - '0';
      Index1++;
    }

    gSystemMemory[Index++].Size = val * 0x100000;
    if (MemorySizeStr[Index1] == 0) {
      break;
    }

    Index1++;
  }

  printf ("\n");

  //
  // Hand off to SEC
  //
  SecLoadFromCore ((UINTN)InitialStackMemory, (UINTN)InitialStackMemorySize, (UINTN)gFdInfo[0].Address, SecFile, SecFileSize);

  //
  // If we get here, then the SEC Core returned. This is an error as SEC should
  //  always hand off to PEI Core and then on to DXE Core.
  //
  printf ("ERROR : SEC returned\n");
  exit (1);
}

EFI_PHYSICAL_ADDRESS *
MapMemory (
  IN INTN    fd,
  IN UINT64  length,
  IN INTN    prot,
  IN INTN    flags
  )
{
  STATIC UINTN  base      = 0x40000000;
  CONST UINTN   align     = (1 << 24);
  VOID          *res      = NULL;
  BOOLEAN       isAligned = 0;

  //
  // Try to get an aligned block somewhere in the address space of this
  // process.
  //
  while ((!isAligned) && (base != 0)) {
    res = mmap ((void *)base, length, prot, flags, fd, 0);
    if (res == MAP_FAILED) {
      return NULL;
    }

    if ((((UINTN)res) & ~(align-1)) == (UINTN)res) {
      isAligned = 1;
    } else {
      munmap (res, length);
      base += align;
    }
  }

  return res;
}

/*++

Routine Description:
  Opens and memory maps a file using Unix services. If BaseAddress is non zero
  the process will try and allocate the memory starting at BaseAddress.

Arguments:
  FileName            - The name of the file to open and map
  MapSize             - The amount of the file to map in bytes
  CreationDisposition - The flags to pass to CreateFile().  Use to create new files for
                        memory emulation, and exiting files for firmware volume emulation
  BaseAddress         - The base address of the mapped file in the user address space.
                         If passed in as NULL the a new memory region is used.
                         If passed in as non NULL the request memory region is used for
                          the mapping of the file into the process space.
  Length              - The size of the mapped region in bytes

Returns:
  EFI_SUCCESS      - The file was opened and mapped.
  EFI_NOT_FOUND    - FileName was not found in the current directory
  EFI_DEVICE_ERROR - An error occurred attempting to map the opened file

**/
EFI_STATUS
MapFile (
  IN  CHAR8                     *FileName,
  IN OUT  EFI_PHYSICAL_ADDRESS  *BaseAddress,
  OUT UINT64                    *Length
  )
{
  int    fd;
  VOID   *res;
  UINTN  FileSize;

  fd = open (FileName, O_RDWR);
  if (fd < 0) {
    return EFI_NOT_FOUND;
  }

  FileSize = lseek (fd, 0, SEEK_END);

  res = MapMemory (fd, FileSize, PROT_READ | PROT_EXEC, MAP_PRIVATE);

  close (fd);

  if (res == NULL) {
    perror ("MapFile() Failed");
    return EFI_DEVICE_ERROR;
  }

  *Length      = (UINT64)FileSize;
  *BaseAddress = (EFI_PHYSICAL_ADDRESS)(UINTN)res;

  return EFI_SUCCESS;
}

EFI_STATUS
MapFd0 (
  IN  CHAR8                     *FileName,
  IN OUT  EFI_PHYSICAL_ADDRESS  *BaseAddress,
  OUT UINT64                    *Length
  )
{
  int    fd;
  void   *res, *res2, *res3;
  UINTN  FileSize;
  UINTN  FvSize;
  void   *EmuMagicPage;

  fd = open (FileName, O_RDWR);
  if (fd < 0) {
    return EFI_NOT_FOUND;
  }

  FileSize = lseek (fd, 0, SEEK_END);

  FvSize = FixedPcdGet64 (PcdEmuFlashFvRecoverySize);

  // Assume start of FD is Recovery FV, and make it write protected
  res = mmap (
          (void *)(UINTN)FixedPcdGet64 (PcdEmuFlashFvRecoveryBase),
          FvSize,
          PROT_READ | PROT_EXEC,
          MAP_PRIVATE,
          fd,
          0
          );
  if (res == MAP_FAILED) {
    perror ("MapFd0() Failed res =");
    close (fd);
    return EFI_DEVICE_ERROR;
  } else if (res != (void *)(UINTN)FixedPcdGet64 (PcdEmuFlashFvRecoveryBase)) {
    // We could not load at the build address, so we need to allow writes
    munmap (res, FvSize);
    res = mmap (
            (void *)(UINTN)FixedPcdGet64 (PcdEmuFlashFvRecoveryBase),
            FvSize,
            PROT_READ | PROT_WRITE | PROT_EXEC,
            MAP_PRIVATE,
            fd,
            0
            );
    if (res == MAP_FAILED) {
      perror ("MapFd0() Failed res =");
      close (fd);
      return EFI_DEVICE_ERROR;
    }
  }

  // Map the rest of the FD as read/write
  res2 = mmap (
           (void *)(UINTN)(FixedPcdGet64 (PcdEmuFlashFvRecoveryBase) + FvSize),
           FileSize - FvSize,
           PROT_READ | PROT_WRITE | PROT_EXEC,
           MAP_SHARED,
           fd,
           FvSize
           );
  close (fd);
  if (res2 == MAP_FAILED) {
    perror ("MapFd0() Failed res2 =");
    return EFI_DEVICE_ERROR;
  }

  //
  // If enabled use the magic page to communicate between modules
  // This replaces the PI PeiServicesTable pointer mechanism that
  // deos not work in the emulator. It also allows the removal of
  // writable globals from SEC, PEI_CORE (libraries), PEIMs
  //
  EmuMagicPage = (void *)(UINTN)FixedPcdGet64 (PcdPeiServicesTablePage);
  if (EmuMagicPage != NULL) {
    res3 =  mmap (
              (void *)EmuMagicPage,
              4096,
              PROT_READ | PROT_WRITE,
              MAP_PRIVATE | MAP_ANONYMOUS,
              0,
              0
              );
    if (res3 != EmuMagicPage) {
      printf ("MapFd0(): Could not allocate PeiServicesTablePage @ %lx\n", (long unsigned int)EmuMagicPage);
      return EFI_DEVICE_ERROR;
    }
  }

  *Length      = (UINT64)FileSize;
  *BaseAddress = (EFI_PHYSICAL_ADDRESS)(UINTN)res;

  return EFI_SUCCESS;
}

/*++

Routine Description:
  This is the service to load the SEC Core from the Firmware Volume

Arguments:
  LargestRegion           - Memory to use for SEC.
  LargestRegionSize       - Size of Memory to use for PEI
  BootFirmwareVolumeBase  - Start of the Boot FV
  PeiCorePe32File         - SEC PE32

Returns:
  Success means control is transferred and thus we should never return

**/
VOID
SecLoadFromCore (
  IN  UINTN  LargestRegion,
  IN  UINTN  LargestRegionSize,
  IN  UINTN  BootFirmwareVolumeBase,
  IN  VOID    *PeiCorePe32File,
  IN  UINT32  PeiCorePe32Size
  )
{
  EFI_STATUS            Status;
  EFI_PHYSICAL_ADDRESS  TopOfMemory;
  VOID                  *TopOfStack;
  EFI_PHYSICAL_ADDRESS  PeiCoreEntryPoint;
  EFI_SEC_PEI_HAND_OFF  *SecCoreData;
  UINTN                 PeiStackSize;

  //
  // Compute Top Of Memory for Stack and PEI Core Allocations
  //
  TopOfMemory  = LargestRegion + LargestRegionSize;
  PeiStackSize = (UINTN)RShiftU64 ((UINT64)STACK_SIZE, 1);

  //
  // |-----------| <---- TemporaryRamBase + TemporaryRamSize
  // |   Heap    |
  // |           |
  // |-----------| <---- StackBase / PeiTemporaryMemoryBase
  // |           |
  // |  Stack    |
  // |-----------| <---- TemporaryRamBase
  //
  TopOfStack  = (VOID *)(LargestRegion + PeiStackSize);
  TopOfMemory = LargestRegion + PeiStackSize;

  //
  // Reservet space for storing PeiCore's parament in stack.
  //
  TopOfStack = (VOID *)((UINTN)TopOfStack - sizeof (EFI_SEC_PEI_HAND_OFF) - CPU_STACK_ALIGNMENT);
  TopOfStack = ALIGN_POINTER (TopOfStack, CPU_STACK_ALIGNMENT);

  //
  // Bind this information into the SEC hand-off state
  //
  SecCoreData                         = (EFI_SEC_PEI_HAND_OFF *)(UINTN)TopOfStack;
  SecCoreData->DataSize               = sizeof (EFI_SEC_PEI_HAND_OFF);
  SecCoreData->BootFirmwareVolumeBase = (VOID *)BootFirmwareVolumeBase;
  SecCoreData->BootFirmwareVolumeSize = PcdGet32 (PcdEmuFirmwareFdSize);
  SecCoreData->TemporaryRamBase       = (VOID *)(UINTN)LargestRegion;
  SecCoreData->TemporaryRamSize       = STACK_SIZE;
  SecCoreData->StackBase              = SecCoreData->TemporaryRamBase;
  SecCoreData->StackSize              = PeiStackSize;
  SecCoreData->PeiTemporaryRamBase    = (VOID *)((UINTN)SecCoreData->TemporaryRamBase + PeiStackSize);
  SecCoreData->PeiTemporaryRamSize    = STACK_SIZE - PeiStackSize;

  //
  // Find the SEC Core Entry Point
  //
  Status = SecUefiImageGetEntryPoint (PeiCorePe32File, PeiCorePe32Size, (VOID **)&PeiCoreEntryPoint);
  if (EFI_ERROR (Status)) {
    return;
  }

  //
  // Transfer control to the SEC Core
  //
  PeiSwitchStacks (
    (SWITCH_STACK_ENTRY_POINT)(UINTN)PeiCoreEntryPoint,
    SecCoreData,
    (VOID *)gPpiList,
    TopOfStack
    );
  //
  // If we get here, then the SEC Core returned.  This is an error
  //
  return;
}

/*++

Routine Description:
  This service is called from Index == 0 until it returns EFI_UNSUPPORTED.
  It allows discontinuous memory regions to be supported by the emulator.
  It uses gSystemMemory[] and gSystemMemoryCount that were created by
  parsing the host environment variable EFI_MEMORY_SIZE.
  The size comes from the variable and the address comes from the call to
  UnixOpenFile.

Arguments:
  Index      - Which memory region to use
  MemoryBase - Return Base address of memory region
  MemorySize - Return size in bytes of the memory region

Returns:
  EFI_SUCCESS - If memory region was mapped
  EFI_UNSUPPORTED - If Index is not supported

**/
EFI_STATUS
SecUnixPeiAutoScan (
  IN  UINTN                 Index,
  OUT EFI_PHYSICAL_ADDRESS  *MemoryBase,
  OUT UINT64                *MemorySize
  )
{
  void  *res;

  if (Index >= gSystemMemoryCount) {
    return EFI_UNSUPPORTED;
  }

  *MemoryBase = 0;
  res         = MapMemory (
                  0,
                  gSystemMemory[Index].Size,
                  PROT_READ | PROT_WRITE | PROT_EXEC,
                  MAP_PRIVATE | MAP_ANONYMOUS
                  );
  if (res == MAP_FAILED) {
    return EFI_DEVICE_ERROR;
  }

  *MemorySize                 = gSystemMemory[Index].Size;
  *MemoryBase                 = (UINTN)res;
  gSystemMemory[Index].Memory = *MemoryBase;

  return EFI_SUCCESS;
}

/*++

Routine Description:
 Check to see if an address range is in the EFI GCD memory map.

 This is all of GCD for system memory passed to DXE Core. FV
 mapping and other device mapped into system memory are not
 included in the check.

Arguments:
  Index      - Which memory region to use
  MemoryBase - Return Base address of memory region
  MemorySize - Return size in bytes of the memory region

Returns:
  TRUE -  Address is in the EFI GCD memory map
  FALSE - Address is NOT in memory map

**/
BOOLEAN
EfiSystemMemoryRange (
  IN  VOID  *MemoryAddress
  )
{
  UINTN                 Index;
  EFI_PHYSICAL_ADDRESS  MemoryBase;

  MemoryBase = (EFI_PHYSICAL_ADDRESS)(UINTN)MemoryAddress;
  for (Index = 0; Index < gSystemMemoryCount; Index++) {
    if ((MemoryBase >= gSystemMemory[Index].Memory) &&
        (MemoryBase < (gSystemMemory[Index].Memory + gSystemMemory[Index].Size)))
    {
      return TRUE;
    }
  }

  return FALSE;
}

/*++

Routine Description:
  Since the SEC is the only Unix program in stack it must export
  an interface to do POSIX calls.  gUnix is initialized in UnixThunk.c.

Arguments:
  InterfaceSize - sizeof (EFI_WIN_NT_THUNK_PROTOCOL);
  InterfaceBase - Address of the gUnix global

Returns:
  EFI_SUCCESS - Data returned

**/
VOID *
SecEmuThunkAddress (
  VOID
  )
{
  return &gEmuThunkProtocol;
}

RETURN_STATUS
EFIAPI
SecUefiImageGetEntryPoint (
  IN     VOID   *Pe32Data,
  IN     UINT32 Pe32Size,
  IN OUT VOID   **EntryPoint
  )
{
  EFI_STATUS                      Status;
  UEFI_IMAGE_LOADER_IMAGE_CONTEXT ImageContext;

  Status = UefiImageInitializeContext (
             &ImageContext,
             Pe32Data,
             Pe32Size,
             UEFI_IMAGE_SOURCE_FV
             );
  if (EFI_ERROR (Status)) {
    return Status;
  }
  //
  // FIXME: This modifies the FD data (which is not possible on real platforms)
  //        and thus re-relocation (i.e., PEIM shadowing) fails badly due to
  //        not updating ImageBase.
  //
  Status = UefiImageRelocateImageInplaceForExecution (&ImageContext);
  if (EFI_ERROR (Status)) {
    return Status;
  }

  SecUefiImageRelocateImageExtraAction (&ImageContext);
  *EntryPoint = (VOID *) (UefiImageLoaderGetImageEntryPoint (&ImageContext));

  return Status;
}

/*++

Routine Description:
  Return the FD Size and base address. Since the FD is loaded from a
  file into host memory only the SEC will know its address.

Arguments:
  Index  - Which FD, starts at zero.
  FdSize - Size of the FD in bytes
  FdBase - Start address of the FD. Assume it points to an FV Header
  FixUp  - Difference between actual FD address and build address

Returns:
  EFI_SUCCESS     - Return the Base address and size of the FV
  EFI_UNSUPPORTED - Index does nto map to an FD in the system

**/
EFI_STATUS
SecUnixFdAddress (
  IN     UINTN                 Index,
  IN OUT EFI_PHYSICAL_ADDRESS  *FdBase,
  IN OUT UINT64                *FdSize,
  IN OUT EFI_PHYSICAL_ADDRESS  *FixUp
  )
{
  if (Index >= gFdInfoCount) {
    return EFI_UNSUPPORTED;
  }

  *FdBase = gFdInfo[Index].Address;
  *FdSize = gFdInfo[Index].Size;
  *FixUp  = 0;

  if ((*FdBase == 0) && (*FdSize == 0)) {
    return EFI_UNSUPPORTED;
  }

  if (Index == 0) {
    //
    // FD 0 has XIP code and well known PCD values
    // If the memory buffer could not be allocated at the FD build address
    // the Fixup is the difference.
    //
    *FixUp = *FdBase - PcdGet64 (PcdEmuFdBaseAddress);
  }

  return EFI_SUCCESS;
}

/*++

Routine Description:
  Count the number of separators in String

Arguments:
  String    - String to process
  Separator - Item to count

Returns:
  Number of Separator in String

**/
UINTN
CountSeparatorsInString (
  IN  const CHAR16  *String,
  IN  CHAR16        Separator
  )
{
  UINTN  Count;

  for (Count = 0; *String != '\0'; String++) {
    if (*String == Separator) {
      Count++;
    }
  }

  return Count;
}

BOOLEAN
IsPdbFile (
  IN  CONST CHAR8   *PdbFileName
  )
{
  UINTN  Len;

  if (PdbFileName == NULL) {
    return FALSE;
  }

  Len = strlen (PdbFileName);
  if ((Len < 5) || (PdbFileName[Len - 4] != '.')) {
    return FALSE;
  }

  if (((PdbFileName[Len - 3] == 'P') || (PdbFileName[Len - 3] == 'p')) &&
      ((PdbFileName[Len - 2] == 'D') || (PdbFileName[Len - 2] == 'd')) &&
      ((PdbFileName[Len - 1] == 'B') || (PdbFileName[Len - 1] == 'b')))
  {
    return TRUE;
  }

  return FALSE;
}

#define MAX_SPRINT_BUFFER_SIZE  0x200

void
PrintLoadAddress (
  IN CONST UEFI_IMAGE_LOADER_IMAGE_CONTEXT       *ImageContext
  )
{
  EFI_STATUS                   Status;
  CONST CHAR8                  *PdbPath;
  UINT32                       PdbPathSize;

  Status = UefiImageGetSymbolsPath (ImageContext, &PdbPath, &PdbPathSize);

  if (EFI_ERROR (Status)) {
    fprintf (
      stderr,
      "0x%08lx (0x%08lx) Loading NO DEBUG with entry point 0x%08lx\n",
      (unsigned long) UefiImageLoaderGetImageAddress (ImageContext),
      (unsigned long) UefiImageLoaderGetDebugAddress (ImageContext),
      (unsigned long) UefiImageLoaderGetImageEntryPoint (ImageContext)
      );
  } else {
    fprintf (
      stderr,
      "0x%08lx (0x%08lx) Loading %s with entry point 0x%08lx\n",
      (unsigned long) UefiImageLoaderGetImageAddress (ImageContext),
      (unsigned long) UefiImageLoaderGetDebugAddress (ImageContext),
      PdbPath,
      (unsigned long) UefiImageLoaderGetImageEntryPoint (ImageContext)
      );
  }

  // Keep output synced up
  fflush (stderr);
}

#ifdef __APPLE__
__attribute__ ((noinline))
#endif
VOID
SecGdbScriptBreak (
  const char          *FileName,
  int                FileNameLength,
  long unsigned int  LoadAddress,
  int                AddSymbolFlag
  )
{
  return;
}

/**
  Adds the image to a gdb script so its symbols can be loaded.
  The AddFirmwareSymbolFile helper macro is used.

  @param  ImageContext  The PE/COFF image context

**/
VOID
GdbScriptAddImage (
  IN CONST UEFI_IMAGE_LOADER_IMAGE_CONTEXT      *ImageContext
  )
{
  EFI_STATUS  Status;
  CONST CHAR8 *PdbPath;
  UINT32      PdbPathSize;

  PrintLoadAddress (ImageContext);

  Status = UefiImageGetSymbolsPath (ImageContext, &PdbPath, &PdbPathSize);
  if (EFI_ERROR (Status)) {
    return;
  }

  if (!IsPdbFile (PdbPath)) {
    FILE  *GdbTempFile;
    if (FeaturePcdGet (PcdEmulatorLazyLoadSymbols)) {
      GdbTempFile = fopen (gGdbWorkingFileName, "a");
      if (GdbTempFile != NULL) {
        long unsigned int SymbolsAddr = (long unsigned int)UefiImageLoaderGetDebugAddress (ImageContext);
        mScriptSymbolChangesCount++;
        fprintf (
          GdbTempFile,
          "AddFirmwareSymbolFile 0x%x %s 0x%08lx\n",
          mScriptSymbolChangesCount,
          PdbPath,
          SymbolsAddr
          );
        fclose (GdbTempFile);
        // This is for the lldb breakpoint only
        SecGdbScriptBreak (PdbPath, PdbPathSize, (long unsigned int)UefiImageLoaderGetDebugAddress (ImageContext), 1);
      } else {
        ASSERT (FALSE);
      }
    } else {
      GdbTempFile = fopen (gGdbWorkingFileName, "w");
      if (GdbTempFile != NULL) {
        fprintf (
          GdbTempFile,
          "add-symbol-file %s -o 0x%08lx\n",
          PdbPath,
          (long unsigned int)UefiImageLoaderGetDebugAddress (ImageContext)
          );
        fclose (GdbTempFile);

        //
        // Target for gdb breakpoint in a script that uses gGdbWorkingFileName to set a breakpoint.
        // Hey what can you say scripting in gdb is not that great....
        // Also used for the lldb breakpoint script. The lldb breakpoint script does
        // not use the file, it uses the arguments.
        //
        SecGdbScriptBreak (PdbPath, PdbPathSize, (long unsigned int)UefiImageLoaderGetDebugAddress (ImageContext), 1);
      } else {
        ASSERT (FALSE);
      }
    }
  }
}

VOID
EFIAPI
SecUefiImageRelocateImageExtraAction (
  IN CONST UEFI_IMAGE_LOADER_IMAGE_CONTEXT      *ImageContext
  )
{
  GdbScriptAddImage (ImageContext);
}

/**
  Adds the image to a gdb script so its symbols can be unloaded.
  The RemoveFirmwareSymbolFile helper macro is used.

  @param  ImageContext  The PE/COFF image context

**/
VOID
GdbScriptRemoveImage (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT      *ImageContext
  )
{
  FILE        *GdbTempFile;
  EFI_STATUS  Status;
  CONST CHAR8 *PdbPath;
  UINT32      PdbPathSize;

  Status = UefiImageGetSymbolsPath (ImageContext, &PdbPath, &PdbPathSize);
  if (EFI_ERROR (Status)) {
    return;
  }

  //
  // Need to skip .PDB files created from VC++
  //
  if (IsPdbFile (PdbPath)) {
    return;
  }

  if (FeaturePcdGet (PcdEmulatorLazyLoadSymbols)) {
    //
    // Write the file we need for the gdb script
    //
    GdbTempFile = fopen (gGdbWorkingFileName, "a");
    if (GdbTempFile != NULL) {
      mScriptSymbolChangesCount++;
      fprintf (
        GdbTempFile,
        "RemoveFirmwareSymbolFile 0x%x %s\n",
        mScriptSymbolChangesCount,
        PdbPath
        );
      fclose (GdbTempFile);
      SecGdbScriptBreak (PdbPath, PdbPathSize, 0, 0);
    } else {
      ASSERT (FALSE);
    }
  } else {
    GdbTempFile = fopen (gGdbWorkingFileName, "w");
    if (GdbTempFile != NULL) {
      fprintf (GdbTempFile, "remove-symbol-file %s\n", PdbPath);
      fclose (GdbTempFile);

      //
      // Target for gdb breakpoint in a script that uses gGdbWorkingFileName to set a breakpoint.
      // Hey what can you say scripting in gdb is not that great....
      //
      SecGdbScriptBreak (PdbPath, PdbPathSize, 0, 0);
    } else {
      ASSERT (FALSE);
    }
  }
}

VOID
EFIAPI
SecUefiImageUnloadImageExtraAction (
  IN UEFI_IMAGE_LOADER_IMAGE_CONTEXT      *ImageContext
  )
{
  GdbScriptRemoveImage (ImageContext);
}
