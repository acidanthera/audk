/** @file
  Core image handling services to load and unload PeImage.

Copyright (c) 2006 - 2019, Intel Corporation. All rights reserved.<BR>
SPDX-License-Identifier: BSD-2-Clause-Patent

**/

#include "DxeMain.h"
#include "Image.h"

#include <Register/Intel/ArchitecturalMsr.h>

//
// Module Globals
//
LOADED_IMAGE_PRIVATE_DATA  *mCurrentImage = NULL;

typedef struct {
  LIST_ENTRY                              Link;
  EDKII_PECOFF_IMAGE_EMULATOR_PROTOCOL    *Emulator;
  UINT16                                  MachineType;
} EMULATOR_ENTRY;

STATIC LIST_ENTRY  mAvailableEmulators;
STATIC EFI_EVENT   mPeCoffEmuProtocolRegistrationEvent;
STATIC VOID        *mPeCoffEmuProtocolNotifyRegistration;

extern BOOLEAN     gBdsStarted;
VOID               *gCoreSysCallStackTop;
VOID               *gRing3CallStackTop;
VOID               *gRing3EntryPoint;
RING3_DATA         *mRing3Data;

//
// This code is needed to build the Image handle for the DXE Core
//
LOADED_IMAGE_PRIVATE_DATA  mCorePrivateImage = {
  LOADED_IMAGE_PRIVATE_DATA_SIGNATURE,         // Signature
  NULL,                                        // Image handle
  EFI_IMAGE_SUBSYSTEM_EFI_BOOT_SERVICE_DRIVER, // Image type
  TRUE,                                        // If entrypoint has been called
  NULL,                                        // EntryPoint
  {
    EFI_LOADED_IMAGE_INFORMATION_REVISION,        // Revision
    NULL,                                         // Parent handle
    NULL,                                         // System handle

    NULL,                                         // Device handle
    NULL,                                         // File path
    NULL,                                         // Reserved

    0,                                            // LoadOptionsSize
    NULL,                                         // LoadOptions

    NULL,                                         // ImageBase
    0,                                            // ImageSize
    EfiBootServicesCode,                          // ImageCodeType
    EfiBootServicesData                           // ImageDataType
  },
  (EFI_PHYSICAL_ADDRESS)0,    // ImageBasePage
  0,                          // NumberOfPages
  NULL,                       // FixupData
  0,                          // Tpl
  EFI_SUCCESS,                // Status
  0,                          // ExitDataSize
  NULL,                       // ExitData
  NULL,                       // JumpBuffer
  NULL,                       // JumpContext
  0,                          // Machine
  NULL,                       // PeCoffEmu
  NULL,                       // RuntimeData
  NULL,                       // LoadedImageDevicePath
  EFI_SUCCESS,                // LoadImageStatus
  NULL,                       // HiiData
  FALSE,                      // IsUserImage
  FALSE                       // IsRing3EntryPoint
};
//
// The field is define for Loading modules at fixed address feature to tracker the PEI code
// memory range usage. It is a bit mapped array in which every bit indicates the correspoding memory page
// available or not.
//
GLOBAL_REMOVE_IF_UNREFERENCED    UINT64  *mDxeCodeMemoryRangeUsageBitMap = NULL;

typedef struct {
  UINT16    MachineType;
  CHAR16    *MachineTypeName;
} MACHINE_TYPE_INFO;

GLOBAL_REMOVE_IF_UNREFERENCED MACHINE_TYPE_INFO  mMachineTypeInfo[] = {
  { EFI_IMAGE_MACHINE_IA32,           L"IA32"        },
  { EFI_IMAGE_MACHINE_IA64,           L"IA64"        },
  { EFI_IMAGE_MACHINE_X64,            L"X64"         },
  { EFI_IMAGE_MACHINE_ARMTHUMB_MIXED, L"ARM"         },
  { EFI_IMAGE_MACHINE_AARCH64,        L"AARCH64"     },
  { EFI_IMAGE_MACHINE_RISCV64,        L"RISCV64"     },
  { EFI_IMAGE_MACHINE_LOONGARCH64,    L"LOONGARCH64" },
};

//  FIXME: RISC-V, IA64
#if defined (MDE_CPU_IA32)
  CONST CHAR16 *mDxeCoreImageMachineTypeName = L"IA32";
#elif defined (MDE_CPU_IPF)
  CONST CHAR16 *mDxeCoreImageMachineTypeName = L"IA64";
#elif defined (MDE_CPU_X64)
  CONST CHAR16 *mDxeCoreImageMachineTypeName = L"X64";
#elif defined (MDE_CPU_ARM)
  CONST CHAR16 *mDxeCoreImageMachineTypeName = L"ARM";
#elif defined (MDE_CPU_AARCH64)
  CONST CHAR16 *mDxeCoreImageMachineTypeName = L"AARCH64";
#else
  #error Unkown CPU architecture
#endif

/**
 Return machine type name.

 @param MachineType The machine type

 @return machine type name
**/
CHAR16 *
GetMachineTypeName (
  UINT16  MachineType
  )
{
  UINTN  Index;

  for (Index = 0; Index < sizeof (mMachineTypeInfo)/sizeof (mMachineTypeInfo[0]); ++Index) {
    if (mMachineTypeInfo[Index].MachineType == MachineType) {
      return mMachineTypeInfo[Index].MachineTypeName;
    }
  }

  return L"<Unknown>";
}

/**
  Notification event handler registered by CoreInitializeImageServices () to
  keep track of which PE/COFF image emulators are available.

  @param  Event          The Event that is being processed, not used.
  @param  Context        Event Context, not used.

**/
STATIC
VOID
EFIAPI
PeCoffEmuProtocolNotify (
  IN  EFI_EVENT  Event,
  IN  VOID       *Context
  )
{
  EFI_STATUS                            Status;
  UINTN                                 BufferSize;
  EFI_HANDLE                            EmuHandle;
  EDKII_PECOFF_IMAGE_EMULATOR_PROTOCOL  *Emulator;
  EMULATOR_ENTRY                        *Entry;

  EmuHandle = NULL;
  Emulator  = NULL;

  while (TRUE) {
    BufferSize = sizeof (EmuHandle);
    Status     = CoreLocateHandle (
                   ByRegisterNotify,
                   NULL,
                   mPeCoffEmuProtocolNotifyRegistration,
                   &BufferSize,
                   &EmuHandle
                   );
    if (EFI_ERROR (Status)) {
      //
      // If no more notification events exit
      //
      return;
    }

    Status = CoreHandleProtocol (
               EmuHandle,
               &gEdkiiPeCoffImageEmulatorProtocolGuid,
               (VOID **)&Emulator
               );
    if (EFI_ERROR (Status) || (Emulator == NULL)) {
      continue;
    }

    Entry = AllocateZeroPool (sizeof (*Entry));
    ASSERT (Entry != NULL);

    Entry->Emulator    = Emulator;
    Entry->MachineType = Entry->Emulator->MachineType;

    InsertTailList (&mAvailableEmulators, &Entry->Link);
  }
}

/**
  Add the Image Services to EFI Boot Services Table and install the protocol
  interfaces for this image.

  @param  HobStart                The HOB to initialize

  @return Status code.

**/
EFI_STATUS
CoreInitializeImageServices (
  IN  VOID                            *HobStart,
  OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT *ImageContext
  )
{
  EFI_STATUS                 Status;
  LOADED_IMAGE_PRIVATE_DATA  *Image;
  EFI_PHYSICAL_ADDRESS       DxeCoreImageBaseAddress;
  UINT64                     DxeCoreImageLength;
  VOID                       *DxeCoreEntryPoint;
  EFI_PEI_HOB_POINTERS       DxeCoreHob;
  EFI_HOB_GUID_TYPE          *GuidHob;
  HOB_IMAGE_CONTEXT          *Hob;

  //
  // Searching for image hob
  //
  DxeCoreHob.Raw = HobStart;
  while ((DxeCoreHob.Raw = GetNextHob (EFI_HOB_TYPE_MEMORY_ALLOCATION, DxeCoreHob.Raw)) != NULL) {
    if (CompareGuid (&DxeCoreHob.MemoryAllocationModule->MemoryAllocationHeader.Name, &gEfiHobMemoryAllocModuleGuid)) {
      //
      // Find Dxe Core HOB
      //
      break;
    }

    DxeCoreHob.Raw = GET_NEXT_HOB (DxeCoreHob);
  }

  ASSERT (DxeCoreHob.Raw != NULL);

  DxeCoreImageBaseAddress = DxeCoreHob.MemoryAllocationModule->MemoryAllocationHeader.MemoryBaseAddress;
  DxeCoreImageLength      = DxeCoreHob.MemoryAllocationModule->MemoryAllocationHeader.MemoryLength;
  DxeCoreEntryPoint       = (VOID *)(UINTN)DxeCoreHob.MemoryAllocationModule->EntryPoint;
  gDxeCoreFileName        = &DxeCoreHob.MemoryAllocationModule->ModuleName;

  //
  // Initialize the fields for an internal driver
  //
  Image = &mCorePrivateImage;

  GuidHob  = GetFirstGuidHob (&gUefiImageLoaderImageContextGuid);
  if (GuidHob == NULL) {
    DEBUG ((DEBUG_ERROR, "UefiImageLoaderImageContextGuid HOB is missing!\n"));
    ASSERT (FALSE);
  }

  Hob = (HOB_IMAGE_CONTEXT *)GET_GUID_HOB_DATA (GuidHob);

  ImageContext->FormatIndex = Hob->FormatIndex;

  if (ImageContext->FormatIndex == UefiImageFormatPe) {
    ImageContext->Ctx.Pe.ImageBuffer         = (VOID *)(UINTN)Hob->Ctx.Pe.ImageBuffer;
    ImageContext->Ctx.Pe.AddressOfEntryPoint = Hob->Ctx.Pe.AddressOfEntryPoint;
    ImageContext->Ctx.Pe.ImageType           = Hob->Ctx.Pe.ImageType;
    ImageContext->Ctx.Pe.FileBuffer          = (CONST VOID *)(UINTN)Hob->Ctx.Pe.FileBuffer;
    ImageContext->Ctx.Pe.ExeHdrOffset        = Hob->Ctx.Pe.ExeHdrOffset;
    ImageContext->Ctx.Pe.SizeOfImage         = Hob->Ctx.Pe.SizeOfImage;
    ImageContext->Ctx.Pe.FileSize            = Hob->Ctx.Pe.FileSize;
    ImageContext->Ctx.Pe.Subsystem           = Hob->Ctx.Pe.Subsystem;
    ImageContext->Ctx.Pe.SectionAlignment    = Hob->Ctx.Pe.SectionAlignment;
    ImageContext->Ctx.Pe.SectionsOffset      = Hob->Ctx.Pe.SectionsOffset;
    ImageContext->Ctx.Pe.NumberOfSections    = Hob->Ctx.Pe.NumberOfSections;
    ImageContext->Ctx.Pe.SizeOfHeaders       = Hob->Ctx.Pe.SizeOfHeaders;
  } else if (ImageContext->FormatIndex == UefiImageFormatUe) {
    ImageContext->Ctx.Ue.ImageBuffer              = (VOID *)(UINTN)Hob->Ctx.Ue.ImageBuffer;
    ImageContext->Ctx.Ue.FileBuffer               = (CONST UINT8 *)(UINTN)Hob->Ctx.Ue.FileBuffer;
    ImageContext->Ctx.Ue.EntryPointAddress        = Hob->Ctx.Ue.EntryPointAddress;
    ImageContext->Ctx.Ue.LoadTablesFileOffset     = Hob->Ctx.Ue.LoadTablesFileOffset;
    ImageContext->Ctx.Ue.NumLoadTables            = Hob->Ctx.Ue.NumLoadTables;
    ImageContext->Ctx.Ue.LoadTables               = (CONST UE_LOAD_TABLE *)(UINTN)Hob->Ctx.Ue.LoadTables;
    ImageContext->Ctx.Ue.Segments                 = (CONST VOID *)(UINTN)Hob->Ctx.Ue.Segments;
    ImageContext->Ctx.Ue.LastSegmentIndex         = Hob->Ctx.Ue.LastSegmentIndex;
    ImageContext->Ctx.Ue.SegmentAlignment         = Hob->Ctx.Ue.SegmentAlignment;
    ImageContext->Ctx.Ue.ImageSize                = Hob->Ctx.Ue.ImageSize;
    ImageContext->Ctx.Ue.Subsystem                = Hob->Ctx.Ue.Subsystem;
    ImageContext->Ctx.Ue.SegmentImageInfoIterSize = Hob->Ctx.Ue.SegmentImageInfoIterSize;
    ImageContext->Ctx.Ue.SegmentsFileOffset       = Hob->Ctx.Ue.SegmentsFileOffset;
  } else {
    ASSERT (FALSE);
  }

  ASSERT ((UINTN) DxeCoreEntryPoint == UefiImageLoaderGetImageEntryPoint (ImageContext));

  Image->EntryPoint     = (EFI_IMAGE_ENTRY_POINT)(UINTN)DxeCoreEntryPoint;
  Image->ImageBasePage  = DxeCoreImageBaseAddress;
  Image->NumberOfPages  = (UINTN)(EFI_SIZE_TO_PAGES ((UINTN)(DxeCoreImageLength)));
  Image->Tpl            = gEfiCurrentTpl;
  Image->Info.ImageBase = (VOID *)(UINTN)DxeCoreImageBaseAddress;
  Image->Info.ImageSize = DxeCoreImageLength;

  //
  // Install the protocol interfaces for this image
  //
  Status = CoreInstallProtocolInterface (
             &Image->Handle,
             &gEfiLoadedImageProtocolGuid,
             EFI_NATIVE_INTERFACE,
             &Image->Info
             );
  ASSERT_EFI_ERROR (Status);

  mCurrentImage = Image;

  //
  // Fill in DXE globals
  //
  gImageHandle        = Image->Handle;
  gDxeCoreLoadedImage = &Image->Info;

  //
  // Create the PE/COFF emulator protocol registration event
  //
  Status = CoreCreateEvent (
             EVT_NOTIFY_SIGNAL,
             TPL_CALLBACK,
             PeCoffEmuProtocolNotify,
             NULL,
             &mPeCoffEmuProtocolRegistrationEvent
             );
  ASSERT_EFI_ERROR (Status);

  //
  // Register for protocol notifications on this event
  //
  Status = CoreRegisterProtocolNotify (
             &gEdkiiPeCoffImageEmulatorProtocolGuid,
             mPeCoffEmuProtocolRegistrationEvent,
             &mPeCoffEmuProtocolNotifyRegistration
             );
  ASSERT_EFI_ERROR (Status);

  InitializeListHead (&mAvailableEmulators);

  return Status;
}

/**
  To check memory usage bit map array to figure out if the memory range the image will be loaded in is available or not. If
  memory range is available, the function will mark the corresponding bits to 1 which indicates the memory range is used.
  The function is only invoked when load modules at fixed address feature is enabled.

  @param  ImageBase                The base address the image will be loaded at.
  @param  ImageSize                The size of the image

  @retval EFI_SUCCESS              The memory range the image will be loaded in is available
  @retval EFI_NOT_FOUND            The memory range the image will be loaded in is not available
**/
EFI_STATUS
CheckAndMarkFixLoadingMemoryUsageBitMap (
  IN  EFI_PHYSICAL_ADDRESS  ImageBase,
  IN  UINTN                 ImageSize
  )
{
  UINT32                DxeCodePageNumber;
  UINT64                DxeCodeSize;
  EFI_PHYSICAL_ADDRESS  DxeCodeBase;
  UINTN                 BaseOffsetPageNumber;
  UINTN                 TopOffsetPageNumber;
  UINTN                 Index;

  //
  // The DXE code range includes RuntimeCodePage range and Boot time code range.
  //
  DxeCodePageNumber  = PcdGet32 (PcdLoadFixAddressRuntimeCodePageNumber);
  DxeCodePageNumber += PcdGet32 (PcdLoadFixAddressBootTimeCodePageNumber);
  DxeCodeSize        = EFI_PAGES_TO_SIZE (DxeCodePageNumber);
  DxeCodeBase        =  gLoadModuleAtFixAddressConfigurationTable.DxeCodeTopAddress - DxeCodeSize;

  //
  // If the memory usage bit map is not initialized,  do it. Every bit in the array
  // indicate the status of the corresponding memory page, available or not
  //
  if (mDxeCodeMemoryRangeUsageBitMap == NULL) {
    mDxeCodeMemoryRangeUsageBitMap = AllocateZeroPool (((DxeCodePageNumber/64) + 1)*sizeof (UINT64));
  }

  //
  // If the Dxe code memory range is not allocated or the bit map array allocation failed, return EFI_NOT_FOUND
  //
  if (!gLoadFixedAddressCodeMemoryReady || (mDxeCodeMemoryRangeUsageBitMap == NULL)) {
    return EFI_NOT_FOUND;
  }

  //
  // Test the memory range for loading the image in the DXE code range.
  //
  if ((gLoadModuleAtFixAddressConfigurationTable.DxeCodeTopAddress < ImageBase + ImageSize) ||
      (DxeCodeBase > ImageBase))
  {
    return EFI_NOT_FOUND;
  }

  //
  // Test if the memory is avalaible or not.
  //
  BaseOffsetPageNumber = EFI_SIZE_TO_PAGES ((UINT32)(ImageBase - DxeCodeBase));
  TopOffsetPageNumber  = EFI_SIZE_TO_PAGES ((UINT32)(ImageBase + ImageSize - DxeCodeBase));
  for (Index = BaseOffsetPageNumber; Index < TopOffsetPageNumber; ++Index) {
    if ((mDxeCodeMemoryRangeUsageBitMap[Index / 64] & LShiftU64 (1, (Index % 64))) != 0) {
      //
      // This page is already used.
      //
      return EFI_NOT_FOUND;
    }
  }

  //
  // Being here means the memory range is available.  So mark the bits for the memory range
  //
  for (Index = BaseOffsetPageNumber; Index < TopOffsetPageNumber; ++Index) {
    mDxeCodeMemoryRangeUsageBitMap[Index / 64] |= LShiftU64 (1, (Index % 64));
  }

  return EFI_SUCCESS;
}

/**

  Get the fixed loading address from image header assigned by build tool. This function only be called
  when Loading module at Fixed address feature enabled.

  @param  ImageContext              Pointer to the image context structure that describes the PE/COFF
                                    image that needs to be examined by this function.
  @retval EFI_SUCCESS               An fixed loading address is assigned to this image by build tools .
  @retval EFI_NOT_FOUND             The image has no assigned fixed loading address.

**/
EFI_STATUS
GetUefiImageFixLoadingAssignedAddress (
  OUT    EFI_PHYSICAL_ADDRESS  *LoadAddress,
  IN     UINT64                ValueInSectionHeader,
  IN     UINT32                ImageDestSize
  )
{
  EFI_STATUS           Status;
  EFI_PHYSICAL_ADDRESS FixLoadingAddress;

  if ((INT64)PcdGet64(PcdLoadModuleAtFixAddressEnable) > 0) {
    //
    // When LMFA feature is configured as Load Module at Fixed Absolute Address mode, PointerToRelocations & PointerToLineNumbers field
    // hold the absolute address of image base running in memory
    //
    FixLoadingAddress = ValueInSectionHeader;
  } else {
    //
    // When LMFA feature is configured as Load Module at Fixed offset mode, PointerToRelocations & PointerToLineNumbers field
    // hold the offset relative to a platform-specific top address.
    //
    FixLoadingAddress = gLoadModuleAtFixAddressConfigurationTable.DxeCodeTopAddress + ValueInSectionHeader;
  }
  //
  // Check if the memory range is available.
  //
  Status       = CheckAndMarkFixLoadingMemoryUsageBitMap (FixLoadingAddress, ImageDestSize);
  *LoadAddress = FixLoadingAddress;

  DEBUG ((EFI_D_INFO|EFI_D_LOAD, "LOADING MODULE FIXED INFO: Loading module at fixed address 0x%11p. Status = %r \n", (VOID *)(UINTN)FixLoadingAddress, Status));
  return Status;
}

/**
  Decides whether a PE/COFF image can execute on this system, either natively
  or via emulation/interpretation. In the latter case, the PeCoffEmu member
  of the LOADED_IMAGE_PRIVATE_DATA struct pointer is populated with a pointer
  to the emulator protocol that supports this image.

  @param[in, out]   Image         LOADED_IMAGE_PRIVATE_DATA struct pointer

  @retval           TRUE          The image is supported
  @retval           FALSE         The image is not supported

**/
STATIC
BOOLEAN
CoreIsImageTypeSupported (
  IN OUT LOADED_IMAGE_PRIVATE_DATA       *Image,
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT *ImageContext
  )
{
  LIST_ENTRY      *Link;
  EMULATOR_ENTRY  *Entry;

  for (Link = GetFirstNode (&mAvailableEmulators);
       !IsNull (&mAvailableEmulators, Link);
       Link = GetNextNode (&mAvailableEmulators, Link))
  {
    Entry = BASE_CR (Link, EMULATOR_ENTRY, Link);
    if (Entry->MachineType != UefiImageGetMachine (ImageContext)) {
      continue;
    }

    if (Entry->Emulator->IsImageSupported (
                           Entry->Emulator,
                           UefiImageGetSubsystem (ImageContext),
                           Image->Info.FilePath
                           ))
    {
      Image->PeCoffEmu = Entry->Emulator;
      return TRUE;
    }
  }

  return EFI_IMAGE_MACHINE_TYPE_SUPPORTED (UefiImageGetMachine (ImageContext)) ||
         EFI_IMAGE_MACHINE_CROSS_TYPE_SUPPORTED (UefiImageGetMachine (ImageContext));
}

/**
  Loads, relocates, and invokes a PE/COFF image

  @param  BootPolicy              If TRUE, indicates that the request originates
                                  from the boot manager, and that the boot
                                  manager is attempting to load FilePath as a
                                  boot selection.
  @param  Image                   PE image to be loaded
  @param  DstBuffer               The buffer to store the image
  @param  EntryPoint              A pointer to the entry point
  @param  Attribute               The bit mask of attributes to set for the load
                                  PE image

  @retval EFI_SUCCESS             The file was loaded, relocated, and invoked
  @retval EFI_OUT_OF_RESOURCES    There was not enough memory to load and
                                  relocate the PE/COFF file
  @retval EFI_INVALID_PARAMETER   Invalid parameter
  @retval EFI_BUFFER_TOO_SMALL    Buffer for image is too small

**/
EFI_STATUS
CoreLoadPeImage (
  IN     BOOLEAN                          BootPolicy,
  IN     LOADED_IMAGE_PRIVATE_DATA        *Image,
  IN     EFI_PHYSICAL_ADDRESS             *DstBuffer   OPTIONAL,
  OUT    EFI_PHYSICAL_ADDRESS             *EntryPoint  OPTIONAL,
  IN     UINT32                           Attribute,
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *ImageContext
  )
{
  EFI_STATUS                        Status;
  BOOLEAN                           DstBufAlocated;
  UINT32                            ImageSize;
  UINT32                            ImageAlignment;
  UINT64                            ValueInSectionHeader;
  UINT32                            DstBufPages;
  UINT32                            DstBufSize;
  EFI_MEMORY_TYPE                   ImageCodeMemoryType;
  EFI_MEMORY_TYPE                   ImageDataMemoryType;
  UEFI_IMAGE_LOADER_RUNTIME_CONTEXT *RelocationData;
  EFI_PHYSICAL_ADDRESS              BufferAddress;
  UINT32                            RelocDataSize;

  RelocationData = NULL;

  if (!CoreIsImageTypeSupported (Image, ImageContext)) {
    //
    // The PE/COFF loader can support loading image types that can be executed.
    // If we loaded an image type that we can not execute return EFI_UNSUPPORTED.
    //
    DEBUG ((
      DEBUG_ERROR,
      "Image type %s can't be loaded on %s UEFI system.\n",
      GetMachineTypeName (UefiImageGetMachine (ImageContext)),
      mDxeCoreImageMachineTypeName
      ));

    return EFI_UNSUPPORTED;
  }

  //
  // Set EFI memory type based on ImageType
  //
  switch (UefiImageGetSubsystem (ImageContext)) {
    case EFI_IMAGE_SUBSYSTEM_EFI_APPLICATION:
      ImageCodeMemoryType = EfiLoaderCode;
      ImageDataMemoryType = EfiLoaderData;
      break;
    case EFI_IMAGE_SUBSYSTEM_EFI_BOOT_SERVICE_DRIVER:
      ImageCodeMemoryType = EfiBootServicesCode;
      ImageDataMemoryType = EfiBootServicesData;
      break;
    case EFI_IMAGE_SUBSYSTEM_EFI_RUNTIME_DRIVER:
    case EFI_IMAGE_SUBSYSTEM_SAL_RUNTIME_DRIVER:
      ImageCodeMemoryType = EfiRuntimeServicesCode;
      ImageDataMemoryType = EfiRuntimeServicesData;
      break;
  default:
    DEBUG ((DEBUG_INFO, "Unsupported type %d\n", UefiImageGetSubsystem (ImageContext)));
    return EFI_UNSUPPORTED;
  }

  ImageSize      = UefiImageGetImageSize (ImageContext);
  DstBufPages    = EFI_SIZE_TO_PAGES (ImageSize);
  DstBufSize     = EFI_PAGES_TO_SIZE (DstBufPages);
  ImageAlignment = UefiImageGetSegmentAlignment (ImageContext);

  BufferAddress = 0;
  //
  // Allocate memory of the correct memory type aligned on the required image boundary
  //
  DstBufAlocated = FALSE;
  if (*DstBuffer == 0) {
    //
    // Allocate Destination Buffer as caller did not pass it in
    //
    Image->NumberOfPages = DstBufPages;

    //
    // If the image relocations have not been stripped, then load at any address.
    // Otherwise load at the address at which it was linked.
    //
    // Memory below 1MB should be treated reserved for CSM and there should be
    // no modules whose preferred load addresses are below 1MB.
    //
    Status = EFI_OUT_OF_RESOURCES;
    //
    // If Loading Module At Fixed Address feature is enabled, the module should be loaded to
    // a specified address.
    //
    if (PcdGet64 (PcdLoadModuleAtFixAddressEnable) != 0 ) {
      Status = UefiImageGetFixedAddress (ImageContext, &ValueInSectionHeader);
      if (RETURN_ERROR (Status)) {
        return Status;
      }

      Status = GetUefiImageFixLoadingAssignedAddress (&BufferAddress, ValueInSectionHeader, DstBufSize);

      if (!EFI_ERROR (Status))  {
        if (BufferAddress != UefiImageGetBaseAddress (ImageContext) && UefiImageGetRelocsStripped (ImageContext)) {
          Status = EFI_UNSUPPORTED;
          DEBUG ((EFI_D_INFO|EFI_D_LOAD, "LOADING MODULE FIXED ERROR: Loading module at fixed address failed since relocs have been stripped.\n"));
        }
      } else {
        //
        // If the code memory is not ready, invoke CoreAllocatePage with AllocateAnyPages to load the driver.
        //
        DEBUG ((DEBUG_INFO|DEBUG_LOAD, "LOADING MODULE FIXED ERROR: Loading module at fixed address failed since specified memory is not available.\n"));
      }
    }
    if (EFI_ERROR (Status)) {
      BufferAddress = UefiImageGetBaseAddress (ImageContext);
      if ((BufferAddress >= 0x100000) || UefiImageGetRelocsStripped (ImageContext)) {
        Status = AllocatePagesEx (
                   AllocateAddress,
                   ImageCodeMemoryType,
                   DstBufPages,
                   &BufferAddress
                   );
      }

      if (EFI_ERROR (Status) && !UefiImageGetRelocsStripped (ImageContext)) {
        Status = AllocateAlignedPagesEx (
                   AllocateAnyPages,
                   ImageCodeMemoryType,
                   DstBufPages,
                   ImageAlignment,
                   &BufferAddress
                   );
      }
    }

    if (EFI_ERROR (Status)) {
      ASSERT (FALSE);
      return Status;
    }

    DstBufAlocated = TRUE;
    *DstBuffer     = BufferAddress;
  } else {
    //
    // Caller provided the destination buffer
    //

    if (UefiImageGetRelocsStripped (ImageContext) && (BufferAddress != *DstBuffer)) {
      //
      // If the image relocations were stripped, and the caller provided a
      // destination buffer address that does not match the address that the
      // image is linked at, then the image cannot be loaded.
      //
      ASSERT (FALSE);
      return EFI_INVALID_PARAMETER;
    }

    if ((Image->NumberOfPages != 0) &&
        (Image->NumberOfPages <
         DstBufPages))
    {
      Image->NumberOfPages = DstBufPages;
      ASSERT (FALSE);
      return EFI_BUFFER_TOO_SMALL;
    }

    Image->NumberOfPages = DstBufPages;
    BufferAddress        = *DstBuffer;
  }

  Image->ImageBasePage = BufferAddress;

  //
  // If this is a Runtime Driver, then allocate memory for the FixupData that
  // is used to relocate the image when SetVirtualAddressMap() is called. The
  // relocation is done by the Runtime AP.
  //
  RelocDataSize = 0;
  if ((Attribute & EFI_LOAD_PE_IMAGE_ATTRIBUTE_RUNTIME_REGISTRATION) != 0) {
    if (UefiImageGetSubsystem (ImageContext) == EFI_IMAGE_SUBSYSTEM_EFI_RUNTIME_DRIVER) {
      if (UefiImageGetRelocsStripped (ImageContext)) {
        ASSERT (FALSE);
        Status = RETURN_UNSUPPORTED;
        goto Done;
      }
      Status = UefiImageLoaderGetRuntimeContextSize (ImageContext, &RelocDataSize);
      if (EFI_ERROR (Status)) {
        ASSERT (FALSE);
        goto Done;
      }
      RelocationData = AllocateRuntimeZeroPool (RelocDataSize);
      if (RelocationData == NULL) {
        ASSERT (FALSE);
        Status = EFI_OUT_OF_RESOURCES;
        goto Done;
      }
    }
  }

  //
  // Load the image from the file into the allocated memory
  //
  Status = UefiImageLoadImageForExecution (
             ImageContext,
             (VOID *)(UINTN)BufferAddress,
             DstBufSize,
             RelocationData,
             RelocDataSize
             );
  if (EFI_ERROR (Status)) {
    ASSERT (FALSE);
    goto Done;
  }

  //
  // Copy the machine type from the context to the image private data.
  //
  Image->Machine = UefiImageGetMachine (ImageContext);

  //
  // Get the image entry point.
  //
  Image->EntryPoint = (EFI_IMAGE_ENTRY_POINT)(UefiImageLoaderGetImageEntryPoint (ImageContext));

  //
  // Fill in the image information for the Loaded Image Protocol
  //
  Image->Type               = UefiImageGetSubsystem (ImageContext);
  Image->Info.ImageBase     = (VOID *)(UINTN)BufferAddress;
  Image->Info.ImageSize     = ImageSize;
  Image->Info.ImageCodeType = ImageCodeMemoryType;
  Image->Info.ImageDataType = ImageDataMemoryType;
  if ((Attribute & EFI_LOAD_PE_IMAGE_ATTRIBUTE_RUNTIME_REGISTRATION) != 0) {
    if (UefiImageGetSubsystem (ImageContext) == EFI_IMAGE_SUBSYSTEM_EFI_RUNTIME_DRIVER) {
      //
      // Make a list off all the RT images so we can let the RT AP know about them.
      //
      Image->RuntimeData = AllocateRuntimePool (sizeof (EFI_RUNTIME_IMAGE_ENTRY));
      if (Image->RuntimeData == NULL) {
        goto Done;
      }

      Image->RuntimeData->ImageBase      = Image->Info.ImageBase;
      Image->RuntimeData->ImageSize      = (UINT64)(Image->Info.ImageSize);
      Image->RuntimeData->RelocationData = RelocationData;
      Image->RuntimeData->Handle         = Image->Handle;
      InsertTailList (&gRuntime->ImageHead, &Image->RuntimeData->Link);
      InsertImageRecord (Image, ImageContext);
    }
  }

  //
  // Fill in the entry point of the image if it is available
  //
  if (EntryPoint != NULL) {
    *EntryPoint = UefiImageLoaderGetImageEntryPoint (ImageContext);
  }

  UINT32 Hiioff;
  UINT32 Hiisize;
  Status = UefiImageGetHiiDataRva (ImageContext, &Hiioff, &Hiisize);
  if (Status != RETURN_NOT_FOUND) {
    ASSERT_EFI_ERROR (Status);
  }
  if (!EFI_ERROR (Status)) {
    Image->HiiData = (VOID *)((UINTN)BufferAddress + Hiioff);
  }

  //
  // Print the load address and the PDB file name if it is available
  //

  DEBUG_CODE_BEGIN ();

  CHAR8 EfiFileName[256];

  DEBUG ((DEBUG_INFO | DEBUG_LOAD,
         "Loading driver at 0x%11p EntryPoint=0x%11p \n",
         (VOID *)(UINTN)BufferAddress,
           FUNCTION_ENTRY_POINT (UefiImageLoaderGetImageEntryPoint (ImageContext))));

    Status = UefiImageGetModuleNameFromSymbolsPath (
             ImageContext,
             EfiFileName,
             sizeof (EfiFileName)
             );

  //
  // Print Module Name by Pdb file path.
  //
  if (!EFI_ERROR (Status)) {
    DEBUG ((DEBUG_INFO | DEBUG_LOAD, "%a", EfiFileName));
  }
  DEBUG ((DEBUG_INFO | DEBUG_LOAD, "\n"));

  DEBUG_CODE_END ();

  return EFI_SUCCESS;

Done:

  //
  // Free memory.
  //

  if (DstBufAlocated) {
    ZeroMem ((VOID *)(UINTN)BufferAddress, EFI_PAGES_TO_SIZE (Image->NumberOfPages));
    FreeAlignedPages ((VOID *)(UINTN)BufferAddress, Image->NumberOfPages);
    Image->ImageBasePage = 0;
  }

  if (RelocationData != NULL) {
    CoreFreePool (RelocationData);
  }

  return Status;
}

/**
  Get the image's private data from its handle.

  @param  ImageHandle             The image handle

  @return Return the image private data associated with ImageHandle.

**/
LOADED_IMAGE_PRIVATE_DATA *
CoreLoadedImageInfo (
  IN EFI_HANDLE  ImageHandle
  )
{
  EFI_STATUS                 Status;
  EFI_LOADED_IMAGE_PROTOCOL  *LoadedImage;
  LOADED_IMAGE_PRIVATE_DATA  *Image;

  Status = CoreHandleProtocol (
             ImageHandle,
             &gEfiLoadedImageProtocolGuid,
             (VOID **)&LoadedImage
             );
  if (!EFI_ERROR (Status)) {
    Image = LOADED_IMAGE_PRIVATE_DATA_FROM_THIS (LoadedImage);
  } else {
    DEBUG ((DEBUG_LOAD, "CoreLoadedImageInfo: Not an ImageHandle %p\n", ImageHandle));
    Image = NULL;
  }

  return Image;
}

/**
  Unloads EFI image from memory.

  @param  Image                   EFI image
  @param  FreePage                Free allocated pages

**/
VOID
CoreUnloadAndCloseImage (
  IN LOADED_IMAGE_PRIVATE_DATA  *Image,
  IN BOOLEAN                    FreePage
  )
{
  EFI_STATUS                           Status;
  UINTN                                HandleCount;
  EFI_HANDLE                           *HandleBuffer;
  UINTN                                HandleIndex;
  EFI_GUID                             **ProtocolGuidArray;
  UINTN                                ArrayCount;
  UINTN                                ProtocolIndex;
  EFI_OPEN_PROTOCOL_INFORMATION_ENTRY  *OpenInfo;
  UINTN                                OpenInfoCount;
  UINTN                                OpenInfoIndex;

  HandleBuffer      = NULL;
  ProtocolGuidArray = NULL;

  UnregisterMemoryProfileImage (Image->Info.FilePath, Image->ImageBasePage);

  if (Image->PeCoffEmu != NULL) {
    //
    // If the PE/COFF Emulator protocol exists we must unregister the image.
    //
    Image->PeCoffEmu->UnregisterImage (Image->PeCoffEmu, (UINTN) Image->Info.ImageBase);
  }

  //
  // Unload image, free Image->ImageContext->ModHandle
  //
  // FIXME:
  //PeCoffUnloadImage (&Image->ImageContext);

  //
  // Free our references to the image handle
  //
  if (Image->Handle != NULL) {
    Status = CoreLocateHandleBuffer (
               AllHandles,
               NULL,
               NULL,
               &HandleCount,
               &HandleBuffer
               );
    if (!EFI_ERROR (Status)) {
      for (HandleIndex = 0; HandleIndex < HandleCount; ++HandleIndex) {
        Status = CoreProtocolsPerHandle (
                   HandleBuffer[HandleIndex],
                   &ProtocolGuidArray,
                   &ArrayCount
                   );
        if (!EFI_ERROR (Status)) {
          for (ProtocolIndex = 0; ProtocolIndex < ArrayCount; ++ProtocolIndex) {
            Status = CoreOpenProtocolInformation (
                       HandleBuffer[HandleIndex],
                       ProtocolGuidArray[ProtocolIndex],
                       &OpenInfo,
                       &OpenInfoCount
                       );
            if (!EFI_ERROR (Status)) {
              for (OpenInfoIndex = 0; OpenInfoIndex < OpenInfoCount; ++OpenInfoIndex) {
                if (OpenInfo[OpenInfoIndex].AgentHandle == Image->Handle) {
                  Status = CoreCloseProtocol (
                             HandleBuffer[HandleIndex],
                             ProtocolGuidArray[ProtocolIndex],
                             Image->Handle,
                             OpenInfo[OpenInfoIndex].ControllerHandle
                             );
                }
              }

              if (OpenInfo != NULL) {
                CoreFreePool (OpenInfo);
              }
            }
          }

          if (ProtocolGuidArray != NULL) {
            CoreFreePool (ProtocolGuidArray);
          }
        }
      }

      if (HandleBuffer != NULL) {
        CoreFreePool (HandleBuffer);
      }
    }

    CoreRemoveDebugImageInfoEntry (Image->Handle);

    Status = CoreUninstallProtocolInterface (
               Image->Handle,
               &gEfiLoadedImageDevicePathProtocolGuid,
               Image->LoadedImageDevicePath
               );

    Status = CoreUninstallProtocolInterface (
               Image->Handle,
               &gEfiLoadedImageProtocolGuid,
               &Image->Info
               );

    if (Image->HiiData != NULL) {
      Status = CoreUninstallProtocolInterface (
                 Image->Handle,
                 &gEfiHiiPackageListProtocolGuid,
                 Image->HiiData
                 );
    }
  }

  if (Image->RuntimeData != NULL) {
    if (Image->RuntimeData->Link.ForwardLink != NULL) {
      //
      // Remove the Image from the Runtime Image list as we are about to Free it!
      //
      RemoveEntryList (&Image->RuntimeData->Link);
      RemoveImageRecord (Image->RuntimeData);
    }

    CoreFreePool (Image->RuntimeData);
  }

  //
  // Done with the Image structure
  //
  if (Image->FixupData != NULL) {
    CoreFreePool (Image->FixupData);
  }

  //
  // Free the Image from memory
  //
  if ((Image->ImageBasePage != 0) && FreePage) {
    UnprotectUefiImage (&Image->Info, Image->LoadedImageDevicePath);
    // FIXME: SecureZeroMem; instruction pattern to trap?
    ZeroMem ((VOID *)(UINTN)Image->ImageBasePage, EFI_PAGES_TO_SIZE (Image->NumberOfPages));
    CoreFreePages (Image->ImageBasePage, Image->NumberOfPages);
  }

  if (Image->Info.FilePath != NULL) {
    CoreFreePool (Image->Info.FilePath);
  }

  if (Image->LoadedImageDevicePath != NULL) {
    CoreFreePool (Image->LoadedImageDevicePath);
  }

  CoreFreePool (Image);
}

/**
  Loads an EFI image into memory and returns a handle to the image.

  @param  BootPolicy              If TRUE, indicates that the request originates
                                  from the boot manager, and that the boot
                                  manager is attempting to load FilePath as a
                                  boot selection.
  @param  ParentImageHandle       The caller's image handle.
  @param  FilePath                The specific file path from which the image is
                                  loaded.
  @param  SourceBuffer            If not NULL, a pointer to the memory location
                                  containing a copy of the image to be loaded.
  @param  SourceSize              The size in bytes of SourceBuffer.
  @param  DstBuffer               The buffer to store the image
  @param  NumberOfPages           If not NULL, it inputs a pointer to the page
                                  number of DstBuffer and outputs a pointer to
                                  the page number of the image. If this number is
                                  not enough,  return EFI_BUFFER_TOO_SMALL and
                                  this parameter contains the required number.
  @param  ImageHandle             Pointer to the returned image handle that is
                                  created when the image is successfully loaded.
  @param  EntryPoint              A pointer to the entry point
  @param  Attribute               The bit mask of attributes to set for the load
                                  PE image

  @retval EFI_SUCCESS             The image was loaded into memory.
  @retval EFI_NOT_FOUND           The FilePath was not found.
  @retval EFI_INVALID_PARAMETER   One of the parameters has an invalid value.
  @retval EFI_BUFFER_TOO_SMALL    The buffer is too small
  @retval EFI_UNSUPPORTED         The image type is not supported, or the device
                                  path cannot be parsed to locate the proper
                                  protocol for loading the file.
  @retval EFI_OUT_OF_RESOURCES    Image was not loaded due to insufficient
                                  resources.
  @retval EFI_LOAD_ERROR          Image was not loaded because the image format was corrupt or not
                                  understood.
  @retval EFI_DEVICE_ERROR        Image was not loaded because the device returned a read error.
  @retval EFI_ACCESS_DENIED       Image was not loaded because the platform policy prohibits the
                                  image from being loaded. NULL is returned in *ImageHandle.
  @retval EFI_SECURITY_VIOLATION  Image was loaded and an ImageHandle was created with a
                                  valid EFI_LOADED_IMAGE_PROTOCOL. However, the current
                                  platform policy specifies that the image should not be started.

**/
EFI_STATUS
CoreLoadImageCommon (
  IN  BOOLEAN                   BootPolicy,
  IN  EFI_HANDLE                ParentImageHandle,
  IN  EFI_DEVICE_PATH_PROTOCOL  *FilePath,
  IN  VOID                      *SourceBuffer       OPTIONAL,
  IN  UINTN                     SourceSize,
  IN  EFI_PHYSICAL_ADDRESS      DstBuffer           OPTIONAL,
  IN OUT UINTN                  *NumberOfPages      OPTIONAL,
  OUT EFI_HANDLE                *ImageHandle,
  OUT EFI_PHYSICAL_ADDRESS      *EntryPoint         OPTIONAL,
  IN  UINT32                    Attribute
  )
{
  LOADED_IMAGE_PRIVATE_DATA       *Image;
  LOADED_IMAGE_PRIVATE_DATA       *ParentImage;
  IMAGE_FILE_HANDLE               FHand;
  EFI_STATUS                      Status;
  EFI_STATUS                      SecurityStatus;
  EFI_HANDLE                      DeviceHandle;
  UINT32                          AuthenticationStatus;
  EFI_DEVICE_PATH_PROTOCOL        *OriginalFilePath;
  EFI_DEVICE_PATH_PROTOCOL        *HandleFilePath;
  EFI_DEVICE_PATH_PROTOCOL        *InputFilePath;
  EFI_DEVICE_PATH_PROTOCOL        *Node;
  UINTN                           FilePathSize;
  BOOLEAN                         ImageIsFromFv;
  BOOLEAN                         ImageIsFromLoadFile;
  UEFI_IMAGE_LOADER_IMAGE_CONTEXT ImageContext;
  UINT8                           ImageOrigin;

  SecurityStatus = EFI_SUCCESS;

  ASSERT (gEfiCurrentTpl < TPL_NOTIFY);
  ParentImage = NULL;
  Image       = NULL;

  //
  // The caller must pass in a valid ParentImageHandle
  //
  if ((ImageHandle == NULL) || (ParentImageHandle == NULL)) {
    return EFI_INVALID_PARAMETER;
  }

  ParentImage = CoreLoadedImageInfo (ParentImageHandle);
  if (ParentImage == NULL) {
    DEBUG ((DEBUG_LOAD|DEBUG_ERROR, "LoadImageEx: Parent handle not an image handle\n"));
    return EFI_INVALID_PARAMETER;
  }

  ZeroMem (&FHand, sizeof (IMAGE_FILE_HANDLE));
  FHand.Signature      = IMAGE_FILE_HANDLE_SIGNATURE;
  OriginalFilePath     = FilePath;
  InputFilePath        = FilePath;
  HandleFilePath       = FilePath;
  DeviceHandle         = NULL;
  Status               = EFI_SUCCESS;
  AuthenticationStatus = 0;
  ImageIsFromFv        = FALSE;
  ImageIsFromLoadFile  = FALSE;

  //
  // If the caller passed a copy of the file, then just use it
  //
  if (SourceBuffer != NULL) {
    FHand.Source     = SourceBuffer;
    FHand.SourceSize = SourceSize;
    Status           = CoreLocateDevicePath (&gEfiDevicePathProtocolGuid, &HandleFilePath, &DeviceHandle);
    if (EFI_ERROR (Status)) {
      DeviceHandle = NULL;
    }

    if (SourceSize > 0) {
      if (DeviceHandle != NULL) {
        Status = CoreOpenProtocol (
                   DeviceHandle,
                   &gEfiFirmwareVolume2ProtocolGuid,
                   NULL,
                   NULL,
                   NULL,
                   EFI_OPEN_PROTOCOL_TEST_PROTOCOL
                   );
        ImageIsFromFv = !EFI_ERROR (Status);
      }

      Status = EFI_SUCCESS;
    } else {
      Status = EFI_LOAD_ERROR;
    }
  } else {
    if (FilePath == NULL) {
      return EFI_INVALID_PARAMETER;
    }

    //
    // Try to get the image device handle by checking the match protocol.
    //
    Node   = NULL;
    Status = CoreLocateDevicePath (&gEfiFirmwareVolume2ProtocolGuid, &HandleFilePath, &DeviceHandle);
    if (!EFI_ERROR (Status)) {
      ImageIsFromFv = TRUE;
      ImageOrigin   = UefiImageOriginFv;
    } else {
      HandleFilePath = FilePath;
      Status         = CoreLocateDevicePath (&gEfiSimpleFileSystemProtocolGuid, &HandleFilePath, &DeviceHandle);
      if (EFI_ERROR (Status)) {
        if (!BootPolicy) {
          HandleFilePath = FilePath;
          Status         = CoreLocateDevicePath (&gEfiLoadFile2ProtocolGuid, &HandleFilePath, &DeviceHandle);
        }

        if (EFI_ERROR (Status)) {
          HandleFilePath = FilePath;
          Status         = CoreLocateDevicePath (&gEfiLoadFileProtocolGuid, &HandleFilePath, &DeviceHandle);
          if (!EFI_ERROR (Status)) {
            ImageIsFromLoadFile = TRUE;
            Node                = HandleFilePath;
          }
        }
      }

      ImageOrigin = UefiImageOriginOptionROM;
    }

    //
    // Get the source file buffer by its device path.
    //
    FHand.Source = GetFileBufferByFilePath (
                     BootPolicy,
                     FilePath,
                     &FHand.SourceSize,
                     &AuthenticationStatus
                     );
    if (FHand.Source == NULL) {
      Status = EFI_NOT_FOUND;
    } else {
      FHand.FreeBuffer = TRUE;
      if (ImageIsFromLoadFile) {
        //
        // LoadFile () may cause the device path of the Handle be updated.
        //
        OriginalFilePath = AppendDevicePath (DevicePathFromHandle (DeviceHandle), Node);
      }
    }
  }

  if (EFI_ERROR (Status)) {
    goto Done;
  }

  if (gBdsStarted) {
    ImageOrigin = UefiImageOriginUserImage;
  }

  //
  // Get information about the image being loaded
  //
  Status = UefiImageInitializeContextPreHash (
             &ImageContext,
             FHand.Source,
             (UINT32) FHand.SourceSize,
             ImageIsFromFv ? UEFI_IMAGE_SOURCE_FV : UEFI_IMAGE_SOURCE_NON_FV,
             ImageOrigin
             );
  if (EFI_ERROR (Status)) {
    if ((ImageOrigin != UefiImageOriginUserImage) && (Status != EFI_NOT_STARTED)) {
      CpuDeadLoop ();
    }

    goto Done;
  }

  // FIXME: Context
  if (gSecurity2 != NULL) {
    //
    // Verify File Authentication through the Security2 Architectural Protocol
    //
    SecurityStatus = gSecurity2->FileAuthentication (
                                   gSecurity2,
                                   OriginalFilePath,
                                   &ImageContext,
                                   sizeof (ImageContext),
                                   BootPolicy
                                   );
    if (!EFI_ERROR (SecurityStatus) && ImageIsFromFv) {
      //
      // When Security2 is installed, Security Architectural Protocol must be published.
      //
      ASSERT (gSecurity != NULL);

      //
      // Verify the Authentication Status through the Security Architectural Protocol
      // Only on images that have been read using Firmware Volume protocol.
      //
      SecurityStatus = gSecurity->FileAuthenticationState (
                                    gSecurity,
                                    AuthenticationStatus,
                                    OriginalFilePath
                                    );
    }
  } else if ((gSecurity != NULL) && (OriginalFilePath != NULL)) {
    //
    // Verify the Authentication Status through the Security Architectural Protocol
    //
    SecurityStatus = gSecurity->FileAuthenticationState (
                                  gSecurity,
                                  AuthenticationStatus,
                                  OriginalFilePath
                                  );
  }

  //
  // Check Security Status.
  //
  if (EFI_ERROR (SecurityStatus) && (SecurityStatus != EFI_SECURITY_VIOLATION)) {
    if (SecurityStatus == EFI_ACCESS_DENIED) {
      //
      // Image was not loaded because the platform policy prohibits the image from being loaded.
      // It's the only place we could meet EFI_ACCESS_DENIED.
      //
      *ImageHandle = NULL;
    }

    Status = SecurityStatus;
    goto Done;
  }

  Status = UefiImageInitializeContextPostHash (&ImageContext);
  if (EFI_ERROR (Status)) {
    if (ImageOrigin != UefiImageOriginUserImage) {
      CpuDeadLoop ();
    }

    goto Done;
  }

  //
  // Allocate a new image structure
  //
  Image = AllocateZeroPool (sizeof (LOADED_IMAGE_PRIVATE_DATA));
  if (Image == NULL) {
    Status = EFI_OUT_OF_RESOURCES;
    goto Done;
  }

  //
  // Pull out just the file portion of the DevicePath for the LoadedImage FilePath
  //
  FilePath = OriginalFilePath;
  if (DeviceHandle != NULL) {
    Status = CoreHandleProtocol (DeviceHandle, &gEfiDevicePathProtocolGuid, (VOID **)&HandleFilePath);
    if (!EFI_ERROR (Status)) {
      FilePathSize = GetDevicePathSize (HandleFilePath) - sizeof (EFI_DEVICE_PATH_PROTOCOL);
      FilePath     = (EFI_DEVICE_PATH_PROTOCOL *)(((UINT8 *)FilePath) + FilePathSize);
    }
  }

  //
  // Initialize the fields for an internal driver
  //
  Image->Signature         = LOADED_IMAGE_PRIVATE_DATA_SIGNATURE;
  Image->Info.SystemTable  = gST;
  Image->Info.DeviceHandle = DeviceHandle;
  Image->Info.Revision     = EFI_LOADED_IMAGE_PROTOCOL_REVISION;
  Image->Info.FilePath     = DuplicateDevicePath (FilePath);
  Image->Info.ParentHandle = ParentImageHandle;

  if (NumberOfPages != NULL) {
    Image->NumberOfPages = *NumberOfPages;
  } else {
    Image->NumberOfPages = 0;
  }

  //
  // Install the protocol interfaces for this image
  // don't fire notifications yet
  //
  Status = CoreInstallProtocolInterfaceNotify (
             &Image->Handle,
             &gEfiLoadedImageProtocolGuid,
             EFI_NATIVE_INTERFACE,
             &Image->Info,
             FALSE
             );
  if (EFI_ERROR (Status)) {
    goto Done;
  }

  //
  // Load the image.  If EntryPoint is Null, it will not be set.
  //
  EFI_PHYSICAL_ADDRESS LoadAddress = DstBuffer;
  Status = CoreLoadPeImage (BootPolicy, Image, &LoadAddress, EntryPoint, Attribute, &ImageContext);
  if (EFI_ERROR (Status)) {
    if ((Status == EFI_BUFFER_TOO_SMALL) || (Status == EFI_OUT_OF_RESOURCES)) {
      if (NumberOfPages != NULL) {
        *NumberOfPages = Image->NumberOfPages;
      }
    }

    goto Done;
  }

  if (NumberOfPages != NULL) {
    *NumberOfPages = Image->NumberOfPages;
  }

  //
  // Register the image in the Debug Image Info Table if the attribute is set
  //
  if ((Attribute & EFI_LOAD_PE_IMAGE_ATTRIBUTE_DEBUG_IMAGE_INFO_TABLE_REGISTRATION) != 0) {
    CoreNewDebugImageInfoEntry (&Image->Info, Image->Handle, &ImageContext);
  }

  //
  // Reinstall loaded image protocol to fire any notifications
  //
  Status = CoreReinstallProtocolInterface (
             Image->Handle,
             &gEfiLoadedImageProtocolGuid,
             &Image->Info,
             &Image->Info
             );
  if (EFI_ERROR (Status)) {
    goto Done;
  }

  //
  // If DevicePath parameter to the LoadImage() is not NULL, then make a copy of DevicePath,
  // otherwise Loaded Image Device Path Protocol is installed with a NULL interface pointer.
  //
  if (OriginalFilePath != NULL) {
    Image->LoadedImageDevicePath = DuplicateDevicePath (OriginalFilePath);
  }

  //
  // Install Loaded Image Device Path Protocol onto the image handle of a PE/COFE image
  //
  Status = CoreInstallProtocolInterface (
             &Image->Handle,
             &gEfiLoadedImageDevicePathProtocolGuid,
             EFI_NATIVE_INTERFACE,
             Image->LoadedImageDevicePath
             );
  if (EFI_ERROR (Status)) {
    goto Done;
  }

  if (Image->HiiData != NULL) {
    Status = CoreInstallProtocolInterface (
               &Image->Handle,
               &gEfiHiiPackageListProtocolGuid,
               EFI_NATIVE_INTERFACE,
               Image->HiiData
               );
    if (EFI_ERROR (Status)) {
      goto Done;
    }
  }

  Status = EFI_SUCCESS;
  ProtectUefiImage (&Image->Info, ImageOrigin, &ImageContext, &Image->IsUserImage, &Image->IsRing3EntryPoint);

  RegisterMemoryProfileImage (
    Image->LoadedImageDevicePath,
    (UefiImageGetSubsystem (&ImageContext) == EFI_IMAGE_SUBSYSTEM_EFI_APPLICATION ? EFI_FV_FILETYPE_APPLICATION : EFI_FV_FILETYPE_DRIVER),
    &ImageContext
    );

  //
  // Success.  Return the image handle
  //
  *ImageHandle = Image->Handle;

Done:
  //
  // All done accessing the source file
  // If we allocated the Source buffer, free it
  //
  if (FHand.FreeBuffer) {
    CoreFreePool (FHand.Source);
  }

  if (OriginalFilePath != InputFilePath) {
    CoreFreePool (OriginalFilePath);
  }

  //
  // There was an error.  If there's an Image structure, free it
  //
  if (EFI_ERROR (Status)) {
    if (Image != NULL) {
      CoreUnloadAndCloseImage (Image, (BOOLEAN)(DstBuffer == 0));
      Image = NULL;
    }
  } else if (EFI_ERROR (SecurityStatus)) {
    Status = SecurityStatus;
  }

  //
  // Track the return status from LoadImage.
  //
  if (Image != NULL) {
    Image->LoadImageStatus = Status;
  }

  return Status;
}

/**
  Loads an EFI image into memory and returns a handle to the image.

  @param  BootPolicy              If TRUE, indicates that the request originates
                                  from the boot manager, and that the boot
                                  manager is attempting to load FilePath as a
                                  boot selection.
  @param  ParentImageHandle       The caller's image handle.
  @param  FilePath                The specific file path from which the image is
                                  loaded.
  @param  SourceBuffer            If not NULL, a pointer to the memory location
                                  containing a copy of the image to be loaded.
  @param  SourceSize              The size in bytes of SourceBuffer.
  @param  ImageHandle             Pointer to the returned image handle that is
                                  created when the image is successfully loaded.

  @retval EFI_SUCCESS             The image was loaded into memory.
  @retval EFI_NOT_FOUND           The FilePath was not found.
  @retval EFI_INVALID_PARAMETER   One of the parameters has an invalid value.
  @retval EFI_UNSUPPORTED         The image type is not supported, or the device
                                  path cannot be parsed to locate the proper
                                  protocol for loading the file.
  @retval EFI_OUT_OF_RESOURCES    Image was not loaded due to insufficient
                                  resources.
  @retval EFI_LOAD_ERROR          Image was not loaded because the image format was corrupt or not
                                  understood.
  @retval EFI_DEVICE_ERROR        Image was not loaded because the device returned a read error.
  @retval EFI_ACCESS_DENIED       Image was not loaded because the platform policy prohibits the
                                  image from being loaded. NULL is returned in *ImageHandle.
  @retval EFI_SECURITY_VIOLATION  Image was loaded and an ImageHandle was created with a
                                  valid EFI_LOADED_IMAGE_PROTOCOL. However, the current
                                  platform policy specifies that the image should not be started.

**/
EFI_STATUS
EFIAPI
CoreLoadImage (
  IN BOOLEAN                   BootPolicy,
  IN EFI_HANDLE                ParentImageHandle,
  IN EFI_DEVICE_PATH_PROTOCOL  *FilePath,
  IN VOID                      *SourceBuffer   OPTIONAL,
  IN UINTN                     SourceSize,
  OUT EFI_HANDLE               *ImageHandle
  )
{
  EFI_STATUS  Status;
  EFI_HANDLE  Handle;

  PERF_LOAD_IMAGE_BEGIN (NULL);

  Status = CoreLoadImageCommon (
             BootPolicy,
             ParentImageHandle,
             FilePath,
             SourceBuffer,
             SourceSize,
             (EFI_PHYSICAL_ADDRESS)(UINTN)NULL,
             NULL,
             ImageHandle,
             NULL,
             EFI_LOAD_PE_IMAGE_ATTRIBUTE_RUNTIME_REGISTRATION | EFI_LOAD_PE_IMAGE_ATTRIBUTE_DEBUG_IMAGE_INFO_TABLE_REGISTRATION
             );

  Handle = NULL;
  if (!EFI_ERROR (Status)) {
    //
    // ImageHandle will be valid only Status is success.
    //
    Handle = *ImageHandle;
  }

  PERF_LOAD_IMAGE_END (Handle);

  return Status;
}

VOID *
EFIAPI
AllocateRing3CopyPages (
  IN VOID    *MemoryCore,
  IN UINT32  MemoryCoreSize
  )
{
  VOID  *MemoryRing3;

  MemoryRing3 = AllocatePages (EFI_SIZE_TO_PAGES (MemoryCoreSize));
  if (MemoryRing3 == NULL) {
    return NULL;
  }

  CopyMem (MemoryRing3, MemoryCore, MemoryCoreSize);

  SetUefiImageMemoryAttributes ((UINTN)MemoryRing3, EFI_PAGES_TO_SIZE (EFI_SIZE_TO_PAGES (MemoryCoreSize)), EFI_MEMORY_USER);

  return MemoryRing3;
}

VOID
EFIAPI
InitializeRing3 (
  IN EFI_HANDLE                 ImageHandle,
  IN LOADED_IMAGE_PRIVATE_DATA  *Image
  )
{
  VOID                    *BaseOfStack;
  VOID                    *TopOfStack;
  UINTN                   SizeOfStack;
  UINT64                  Msr;
  IA32_CR4                Cr4;
  IA32_EFLAGS32           Eflags;
  UINT32                  Ebx;
  UINT32                  Edx;
  MSR_IA32_EFER_REGISTER  MsrEfer;

  Ebx = 0;
  Edx = 0;

  //
  // Set Ring3 EntryPoint and BootServices.
  //
  mRing3Data = AllocateRing3CopyPages ((VOID *)Image->Info.SystemTable, sizeof (RING3_DATA));

  Image->Status = Image->EntryPoint (ImageHandle, (EFI_SYSTEM_TABLE *)mRing3Data);

  gRing3EntryPoint = mRing3Data->EntryPoint;

  mRing3Data->SystemTable.BootServices = mRing3Data->BootServices;

  //
  // Forbid supervisor-mode accesses to any user-mode pages.
  // SMEP and SMAP must be supported.
  //
  AsmCpuidEx (0x07, 0x0, NULL, &Ebx, NULL, NULL);
  //
  // SYSCALL and SYSRET must be also supported.
  //
  AsmCpuidEx (0x80000001, 0x0, NULL, NULL, NULL, &Edx);
  if (((Ebx & BIT20) != 0) && ((Ebx & BIT7) != 0) && ((Edx & BIT11) != 0)) {
    Cr4.UintN     = AsmReadCr4 ();
    Cr4.Bits.SMAP = 1;
    Cr4.Bits.SMEP = 1;
    AsmWriteCr4 (Cr4.UintN);

    Eflags.UintN   = AsmReadEflags ();
    Eflags.Bits.AC = 0;
    //
    // Allow user image to access ports.
    //
    Eflags.Bits.IOPL = 3;
    AsmWriteEflags (Eflags.UintN);
    //
    // Enable SYSCALL and SYSRET.
    //
    MsrEfer.Uint64   = AsmReadMsr64 (MSR_IA32_EFER);
    MsrEfer.Bits.SCE = 1;
    AsmWriteMsr64 (MSR_IA32_EFER, MsrEfer.Uint64);
  }

  SizeOfStack = EFI_SIZE_TO_PAGES (USER_STACK_SIZE) * EFI_PAGE_SIZE;

  //
  // Allocate 128KB for the Core SysCall Stack.
  //
  BaseOfStack = AllocatePages (EFI_SIZE_TO_PAGES (USER_STACK_SIZE));
  ASSERT (BaseOfStack != NULL);

  //
  // Compute the top of the allocated stack. Pre-allocate a UINTN for safety.
  //
  TopOfStack = (VOID *)((UINTN)BaseOfStack + SizeOfStack - CPU_STACK_ALIGNMENT);
  TopOfStack = ALIGN_POINTER (TopOfStack, CPU_STACK_ALIGNMENT);

  gCoreSysCallStackTop = TopOfStack;

  SetUefiImageMemoryAttributes ((UINTN)BaseOfStack, SizeOfStack, EFI_MEMORY_XP);
  DEBUG ((DEBUG_ERROR, "Core: gCoreSysCallStackTop = %p\n", gCoreSysCallStackTop));

  //
  // Allocate 128KB for the User Stack.
  //
  BaseOfStack = AllocatePages (EFI_SIZE_TO_PAGES (USER_STACK_SIZE));
  ASSERT (BaseOfStack != NULL);

  //
  // Compute the top of the allocated stack. Pre-allocate a UINTN for safety.
  //
  TopOfStack = (VOID *)((UINTN)BaseOfStack + SizeOfStack - CPU_STACK_ALIGNMENT);
  TopOfStack = ALIGN_POINTER (TopOfStack, CPU_STACK_ALIGNMENT);

  gRing3CallStackTop = TopOfStack;

  SetUefiImageMemoryAttributes ((UINTN)BaseOfStack, SizeOfStack, EFI_MEMORY_XP | EFI_MEMORY_USER);
  DEBUG ((DEBUG_ERROR, "Core: gRing3CallStackTop = %p\n", gRing3CallStackTop));

  //
  // Initialize MSR_IA32_STAR and MSR_IA32_LSTAR for SYSCALL and SYSRET.
  //
  Msr = ((((UINT64)RING3_CODE64_SEL - 16) << 16) | (UINT64)RING0_CODE64_SEL) << 32;
  AsmWriteMsr64 (MSR_IA32_STAR, Msr);

  Msr = (UINT64)(UINTN)CoreBootServices;
  AsmWriteMsr64 (MSR_IA32_LSTAR, Msr);
}

/**
  Transfer control to a loaded image's entry point.

  @param  ImageHandle             Handle of image to be started.
  @param  ExitDataSize            Pointer of the size to ExitData
  @param  ExitData                Pointer to a pointer to a data buffer that
                                  includes a Null-terminated string,
                                  optionally followed by additional binary data.
                                  The string is a description that the caller may
                                  use to further indicate the reason for the
                                  image's exit.

  @retval EFI_INVALID_PARAMETER   Invalid parameter
  @retval EFI_OUT_OF_RESOURCES    No enough buffer to allocate
  @retval EFI_SECURITY_VIOLATION  The current platform policy specifies that the image should not be started.
  @retval EFI_SUCCESS             Successfully transfer control to the image's
                                  entry point.

**/
EFI_STATUS
EFIAPI
CoreStartImage (
  IN EFI_HANDLE  ImageHandle,
  OUT UINTN      *ExitDataSize,
  OUT CHAR16     **ExitData  OPTIONAL
  )
{
  EFI_STATUS                 Status;
  LOADED_IMAGE_PRIVATE_DATA  *Image;
  LOADED_IMAGE_PRIVATE_DATA  *LastImage;
  UINT64                     HandleDatabaseKey;
  UINTN                      SetJumpFlag;
  EFI_HANDLE                 Handle;
  UINT64                     Attributes;

  Handle = ImageHandle;

  Image = CoreLoadedImageInfo (ImageHandle);
  if ((Image == NULL) ||  Image->Started) {
    return EFI_INVALID_PARAMETER;
  }

  if (EFI_ERROR (Image->LoadImageStatus)) {
    return Image->LoadImageStatus;
  }

  DEBUG ((DEBUG_WARN, "Starting driver at %lu\n", Image->Info.ImageBase));

  //
  // The image to be started must have the machine type supported by DxeCore.
  //
  if (!EFI_IMAGE_MACHINE_TYPE_SUPPORTED (Image->Machine) &&
      (Image->PeCoffEmu == NULL))
  {
    //
    // Do not ASSERT here, because image might be loaded via EFI_IMAGE_MACHINE_CROSS_TYPE_SUPPORTED
    // But it can not be started.
    //
    DEBUG ((EFI_D_ERROR, "Image type %s can't be started ", GetMachineTypeName(Image->Machine)));
    DEBUG ((EFI_D_ERROR, "on %s UEFI system.\n", mDxeCoreImageMachineTypeName));
    return EFI_UNSUPPORTED;
  }

  if (Image->PeCoffEmu != NULL) {
    Status = Image->PeCoffEmu->RegisterImage (
                                 Image->PeCoffEmu,
                                 (UINTN) Image->Info.ImageBase,
                                 Image->Info.ImageSize,
                                 &Image->EntryPoint
                                 );
    if (EFI_ERROR (Status)) {
      DEBUG ((
        DEBUG_LOAD | DEBUG_ERROR,
        "CoreLoadPeImage: Failed to register foreign image with emulator - %r\n",
        Status
        ));
      return Status;
    }
  }

  PERF_START_IMAGE_BEGIN (Handle);

  //
  // Push the current start image context, and
  // link the current image to the head.   This is the
  // only image that can call Exit()
  //
  HandleDatabaseKey = CoreGetHandleDatabaseKey ();
  LastImage         = mCurrentImage;
  mCurrentImage     = Image;
  Image->Tpl        = gEfiCurrentTpl;

  //
  // Set long jump for Exit() support
  // JumpContext must be aligned on a CPU specific boundary.
  // Overallocate the buffer and force the required alignment
  //
  Image->JumpBuffer = AllocatePool (sizeof (BASE_LIBRARY_JUMP_BUFFER) + BASE_LIBRARY_JUMP_BUFFER_ALIGNMENT);
  if (Image->JumpBuffer == NULL) {
    //
    // Image may be unloaded after return with failure,
    // then ImageHandle may be invalid, so use NULL handle to record perf log.
    //
    PERF_START_IMAGE_END (NULL);

    //
    // Pop the current start image context
    //
    mCurrentImage = LastImage;

    return EFI_OUT_OF_RESOURCES;
  }

  Image->JumpContext = ALIGN_POINTER (Image->JumpBuffer, BASE_LIBRARY_JUMP_BUFFER_ALIGNMENT);

  SetJumpFlag = SetJump (Image->JumpContext);
  //
  // The initial call to SetJump() must always return 0.
  // Subsequent calls to LongJump() cause a non-zero value to be returned by SetJump().
  //
  if (SetJumpFlag == 0) {
    //
    // Call the image's entry point
    //
    Image->Started = TRUE;

    if (Image->IsRing3EntryPoint) {
      InitializeRing3 (ImageHandle, Image);
    } else if (Image->IsUserImage) {
      gCpu->GetMemoryAttributes (gCpu, (EFI_PHYSICAL_ADDRESS)Image->EntryPoint, &Attributes);
      ASSERT ((Attributes & EFI_MEMORY_USER) != 0);

      //
      // Necessary fix for ProcessLibraryConstructorList() -> DxeCcProbeLibConstructor()
      //
      SetUefiImageMemoryAttributes (
        FixedPcdGet32 (PcdOvmfWorkAreaBase),
        FixedPcdGet32 (PcdOvmfWorkAreaSize),
        EFI_MEMORY_XP | EFI_MEMORY_USER
        );

      Image->Status = GoToRing3 (
                        2,
                        (VOID *)Image->EntryPoint,
                        ImageHandle,
                        mRing3Data
                        );
    } else {
      Image->Status = Image->EntryPoint (ImageHandle, Image->Info.SystemTable);
    }

    //
    // Add some debug information if the image returned with error.
    // This make the user aware and check if the driver image have already released
    // all the resource in this situation.
    //
    DEBUG_CODE_BEGIN ();
    if (EFI_ERROR (Image->Status)) {
      DEBUG ((DEBUG_ERROR, "Error: Image at %11p start failed: %r\n", Image->Info.ImageBase, Image->Status));
    }

    DEBUG_CODE_END ();

    //
    // If the image returns, exit it through Exit()
    //
    CoreExit (ImageHandle, Image->Status, 0, NULL);
  }

  //
  // Image has completed.  Verify the tpl is the same
  //
  ASSERT (Image->Tpl == gEfiCurrentTpl);
  if (Image->Tpl != gEfiCurrentTpl) {
    CoreRestoreTpl (Image->Tpl);
  }

  CoreFreePool (Image->JumpBuffer);

  //
  // Pop the current start image context
  //
  mCurrentImage = LastImage;

  //
  // UEFI Specification - StartImage() - EFI 1.10 Extension
  // To maintain compatibility with UEFI drivers that are written to the EFI
  // 1.02 Specification, StartImage() must monitor the handle database before
  // and after each image is started. If any handles are created or modified
  // when an image is started, then EFI_BOOT_SERVICES.ConnectController() must
  // be called with the Recursive parameter set to TRUE for each of the newly
  // created or modified handles before StartImage() returns.
  //
  if (Image->Type != EFI_IMAGE_SUBSYSTEM_EFI_APPLICATION) {
    CoreConnectHandlesByKey (HandleDatabaseKey);
  }

  //
  // Handle the image's returned ExitData
  //
  DEBUG_CODE_BEGIN ();
  if ((Image->ExitDataSize != 0) || (Image->ExitData != NULL)) {
    DEBUG ((DEBUG_LOAD, "StartImage: ExitDataSize %d, ExitData %p", (UINT32)Image->ExitDataSize, Image->ExitData));
    if (Image->ExitData != NULL) {
      DEBUG ((DEBUG_LOAD, " (%s)", Image->ExitData));
    }

    DEBUG ((DEBUG_LOAD, "\n"));
  }

  DEBUG_CODE_END ();

  //
  //  Return the exit data to the caller
  //
  if ((ExitData != NULL) && (ExitDataSize != NULL)) {
    *ExitDataSize = Image->ExitDataSize;
    *ExitData     = Image->ExitData;
  } else {
    //
    // Caller doesn't want the exit data, free it
    //
    CoreFreePool (Image->ExitData);
    Image->ExitData = NULL;
  }

  //
  // Save the Status because Image will get destroyed if it is unloaded.
  //
  Status = Image->Status;

  //
  // If the image returned an error, or if the image is an application
  // unload it
  //
  if (EFI_ERROR (Image->Status) || (Image->Type == EFI_IMAGE_SUBSYSTEM_EFI_APPLICATION)) {
    CoreUnloadAndCloseImage (Image, TRUE);
    //
    // ImageHandle may be invalid after the image is unloaded, so use NULL handle to record perf log.
    //
    Handle = NULL;
  }

  //
  // Done
  //
  PERF_START_IMAGE_END (Handle);
  return Status;
}

/**
  Terminates the currently loaded EFI image and returns control to boot services.

  @param  ImageHandle             Handle that identifies the image. This
                                  parameter is passed to the image on entry.
  @param  Status                  The image's exit code.
  @param  ExitDataSize            The size, in bytes, of ExitData. Ignored if
                                  ExitStatus is EFI_SUCCESS.
  @param  ExitData                Pointer to a data buffer that includes a
                                  Null-terminated Unicode string, optionally
                                  followed by additional binary data. The string
                                  is a description that the caller may use to
                                  further indicate the reason for the image's
                                  exit.

  @retval EFI_INVALID_PARAMETER   Image handle is NULL or it is not current
                                  image.
  @retval EFI_SUCCESS             Successfully terminates the currently loaded
                                  EFI image.
  @retval EFI_ACCESS_DENIED       Should never reach there.
  @retval EFI_OUT_OF_RESOURCES    Could not allocate pool

**/
EFI_STATUS
EFIAPI
CoreExit (
  IN EFI_HANDLE  ImageHandle,
  IN EFI_STATUS  Status,
  IN UINTN       ExitDataSize,
  IN CHAR16      *ExitData  OPTIONAL
  )
{
  LOADED_IMAGE_PRIVATE_DATA  *Image;
  EFI_TPL                    OldTpl;

  //
  // Prevent possible reentrance to this function
  // for the same ImageHandle
  //
  OldTpl = CoreRaiseTpl (TPL_NOTIFY);

  Image = CoreLoadedImageInfo (ImageHandle);
  if (Image == NULL) {
    Status = EFI_INVALID_PARAMETER;
    goto Done;
  }

  if (!Image->Started) {
    //
    // The image has not been started so just free its resources
    //
    CoreUnloadAndCloseImage (Image, TRUE);
    Status = EFI_SUCCESS;
    goto Done;
  }

  //
  // Image has been started, verify this image can exit
  //
  if (Image != mCurrentImage) {
    DEBUG ((DEBUG_LOAD|DEBUG_ERROR, "Exit: Image is not exitable image\n"));
    Status = EFI_INVALID_PARAMETER;
    goto Done;
  }

  //
  // Set status
  //
  Image->Status = Status;

  //
  // If there's ExitData info, move it
  //
  if (ExitData != NULL) {
    Image->ExitDataSize = ExitDataSize;
    Image->ExitData     = AllocatePool (Image->ExitDataSize);
    if (Image->ExitData == NULL) {
      Status = EFI_OUT_OF_RESOURCES;
      goto Done;
    }

    CopyMem (Image->ExitData, ExitData, Image->ExitDataSize);
  }

  CoreRestoreTpl (OldTpl);
  //
  // return to StartImage
  //
  LongJump (Image->JumpContext, (UINTN)-1);

  //
  // If we return from LongJump, then it is an error
  //
  ASSERT (FALSE);
  Status = EFI_ACCESS_DENIED;
Done:
  CoreRestoreTpl (OldTpl);
  return Status;
}

/**
  Unloads an image.

  @param  ImageHandle             Handle that identifies the image to be
                                  unloaded.

  @retval EFI_SUCCESS             The image has been unloaded.
  @retval EFI_UNSUPPORTED         The image has been started, and does not support
                                  unload.
  @retval EFI_INVALID_PARAMETER   ImageHandle is not a valid image handle.

**/
EFI_STATUS
EFIAPI
CoreUnloadImage (
  IN EFI_HANDLE  ImageHandle
  )
{
  EFI_STATUS                 Status;
  LOADED_IMAGE_PRIVATE_DATA  *Image;

  Image = CoreLoadedImageInfo (ImageHandle);
  if (Image == NULL ) {
    //
    // The image handle is not valid
    //
    Status = EFI_INVALID_PARAMETER;
    goto Done;
  }

  if (Image->Started) {
    //
    // The image has been started, request it to unload.
    //
    Status = EFI_UNSUPPORTED;
    if (Image->Info.Unload != NULL) {
      Status = Image->Info.Unload (ImageHandle);
    }
  } else {
    //
    // This Image hasn't been started, thus it can be unloaded
    //
    Status = EFI_SUCCESS;
  }

  if (!EFI_ERROR (Status)) {
    //
    // if the Image was not started or Unloaded O.K. then clean up
    //
    CoreUnloadAndCloseImage (Image, TRUE);
  }

Done:
  return Status;
}
