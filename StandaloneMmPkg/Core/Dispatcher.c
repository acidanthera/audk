/** @file
  MM Driver Dispatcher.

  Step #1 - When a FV protocol is added to the system every driver in the FV
            is added to the mDiscoveredList. The Before, and After Depex are
            pre-processed as drivers are added to the mDiscoveredList. If an Apriori
            file exists in the FV those drivers are added to the
            mScheduledQueue. The mFwVolList is used to make sure a
            FV is only processed once.

  Step #2 - Dispatch. Remove driver from the mScheduledQueue and load and
            start it. After mScheduledQueue is drained check the
            mDiscoveredList to see if any item has a Depex that is ready to
            be placed on the mScheduledQueue.

  Step #3 - Adding to the mScheduledQueue requires that you process Before
            and After dependencies. This is done recursively as the call to add
            to the mScheduledQueue checks for Before Depexes and recursively
            adds all Before Depexes. It then adds the item that was passed in
            and then processess the After dependencies by recursively calling
            the routine.

  Dispatcher Rules:
  The rules for the dispatcher are similar to the DXE dispatcher.

  The rules for DXE dispatcher are in chapter 10 of the DXE CIS. Figure 10-3
  is the state diagram for the DXE dispatcher

  Depex - Dependency Expresion.

  Copyright (c) 2014, Hewlett-Packard Development Company, L.P.
  Copyright (c) 2009 - 2014, Intel Corporation. All rights reserved.<BR>
  Copyright (c) 2016 - 2021, Arm Limited. All rights reserved.<BR>

  SPDX-License-Identifier: BSD-2-Clause-Patent

**/

#include "ProcessorBind.h"
#include "StandaloneMmCore.h"

//
// MM Dispatcher Data structures
//
#define KNOWN_FWVOL_SIGNATURE  SIGNATURE_32('k','n','o','w')

typedef struct {
  UINTN                         Signature;
  LIST_ENTRY                    Link;      // mFwVolList
  EFI_FIRMWARE_VOLUME_HEADER    *FwVolHeader;
} KNOWN_FWVOL;

//
// Function Prototypes
//

/**
  Insert InsertedDriverEntry onto the mScheduledQueue. To do this you
  must add any driver with a before dependency on InsertedDriverEntry first.
  You do this by recursively calling this routine. After all the Before Depexes
  are processed you can add InsertedDriverEntry to the mScheduledQueue.
  Then you can add any driver with an After dependency on InsertedDriverEntry
  by recursively calling this routine.

  @param  InsertedDriverEntry   The driver to insert on the ScheduledLink Queue

**/
VOID
MmInsertOnScheduledQueueWhileProcessingBeforeAndAfter (
  IN  EFI_MM_DRIVER_ENTRY  *InsertedDriverEntry
  );

//
// The Driver List contains one copy of every driver that has been discovered.
// Items are never removed from the driver list. List of EFI_MM_DRIVER_ENTRY
//
LIST_ENTRY  mDiscoveredList = INITIALIZE_LIST_HEAD_VARIABLE (mDiscoveredList);

//
// Queue of drivers that are ready to dispatch. This queue is a subset of the
// mDiscoveredList.list of EFI_MM_DRIVER_ENTRY.
//
LIST_ENTRY  mScheduledQueue = INITIALIZE_LIST_HEAD_VARIABLE (mScheduledQueue);

//
// List of firmware volume headers whose containing firmware volumes have been
// parsed and added to the mFwDriverList.
//
LIST_ENTRY  mFwVolList = INITIALIZE_LIST_HEAD_VARIABLE (mFwVolList);

//
// Flag for the MM Dispacher.  TRUE if dispatcher is executing.
//
BOOLEAN  gDispatcherRunning = FALSE;

//
// Flag for the MM Dispacher.  TRUE if there is one or more MM drivers ready to be dispatched
//
BOOLEAN  gRequestDispatch = FALSE;

STATIC
RETURN_STATUS
InternalProtectMmImage (
  IN OUT UEFI_IMAGE_LOADER_IMAGE_CONTEXT  *ImageContext
  )
{
  UEFI_IMAGE_RECORD       *ImageRecord;
  UINTN                   SectionAddress;
  UINT32                  SectionIndex;

  if (UefiImageGetSegmentAlignment (ImageContext) < EFI_PAGE_SIZE) {
    // FIXME: PCD to abort loading?
    //
    // The sections need to be at least 4 KB aligned, since that is the
    // granularity at which we can tighten permissions. So just clear the
    // noexec permissions on the entire region.
    //
    DEBUG ((DEBUG_WARN,
      "%a: Image at 0x%lx has SectionAlignment < 4 KB (%lu)\n",
      __FUNCTION__, UefiImageLoaderGetImageAddress (ImageContext), UefiImageGetSegmentAlignment (ImageContext)));

    ASSERT ((UefiImageLoaderGetImageAddress (ImageContext) & (EFI_PAGE_SIZE - 1)) == 0);

    ClearMemoryRegionNoExec (
      UefiImageLoaderGetImageAddress (ImageContext),
      ALIGN_VALUE (UefiImageGetImageSize (ImageContext), EFI_PAGE_SIZE)
      );

    return RETURN_SUCCESS;
  }

  ImageRecord = UefiImageLoaderGetImageRecord (ImageContext);
  if (ImageRecord == NULL) {
    return RETURN_OUT_OF_RESOURCES;
  }
  //
  // Images are loaded into RW memory, thus only +X and -W need to be handled.
  //
  SectionAddress = ImageRecord->StartAddress;
  for (SectionIndex = 0; SectionIndex < ImageRecord->NumSegments; ++ SectionIndex) {
    DEBUG ((DEBUG_INFO,
      "%a: Mapping segment of image at 0x%lx with %s-%s permissions and size 0x%x\n",
      __FUNCTION__, SectionAddress,
      (ImageRecord->Segments[SectionIndex].Attributes & EFI_MEMORY_RO) != 0 ? "RO" : "RW",
      (ImageRecord->Segments[SectionIndex].Attributes & EFI_MEMORY_XP) != 0 ? "XN" : "X",
      ImageRecord->Segments[SectionIndex].Size));

    // FIXME: What about their return values?
    if ((ImageRecord->Segments[SectionIndex].Attributes & EFI_MEMORY_RO) != 0) {
      SetMemoryRegionReadOnly (
        SectionAddress,
        ImageRecord->Segments[SectionIndex].Size
        );
    }

    if ((ImageRecord->Segments[SectionIndex].Attributes & EFI_MEMORY_XP) == 0) {
      ClearMemoryRegionNoExec (
        SectionAddress,
        ImageRecord->Segments[SectionIndex].Size
        );
    }

    SectionAddress += ImageRecord->Segments[SectionIndex].Size;
  }

  FreePool (ImageRecord);

  return RETURN_SUCCESS;
}

/**
  Loads an EFI image into SMRAM.

  @param  DriverEntry             EFI_MM_DRIVER_ENTRY instance
  @param  ImageContext            Allocated ImageContext to be filled out by this function

  @return EFI_STATUS

**/
EFI_STATUS
EFIAPI
MmLoadImage (
  IN OUT EFI_MM_DRIVER_ENTRY           *DriverEntry,
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *ImageContext
  )
{
  UINT32      ImageSize;
  UINT32      ImageAlignment;
  EFI_STATUS  Status;
  VOID        *DstBuffer;
  UINT32      DstBufferPages;
  UINT32      DstBufferSize;

  DEBUG ((DEBUG_INFO, "MmLoadImage - %g\n", &DriverEntry->FileName));

  if (ImageContext == NULL) {
    return EFI_INVALID_PARAMETER;
  }

  Status = EFI_SUCCESS;

  //
  // Get information about the image being loaded
  //
  Status = UefiImageInitializeContext (ImageContext, DriverEntry->Pe32Data, DriverEntry->Pe32DataSize);
  if (EFI_ERROR (Status)) {
    return Status;
  }

  ImageSize      = UefiImageGetImageSize (ImageContext);
  DstBufferPages = EFI_SIZE_TO_PAGES (ImageSize);
  DstBufferSize  = EFI_PAGES_TO_SIZE (DstBufferPages);
  ImageAlignment = UefiImageGetSegmentAlignment (ImageContext);

  DstBuffer = AllocateAlignedCodePages (DstBufferPages, ImageAlignment);
  if (DstBuffer == NULL) {
    return EFI_OUT_OF_RESOURCES;
  }

  //
  // Load the image to our new buffer
  //
  Status = UefiImageLoadImageForExecution (ImageContext, DstBuffer, DstBufferSize, NULL, 0);
  if (EFI_ERROR (Status)) {
    FreeAlignedPages (DstBuffer, DstBufferPages);
    return Status;
  }

  //
  // Save Image EntryPoint in DriverEntry
  //
  DriverEntry->ImageEntryPoint = UefiImageLoaderGetImageEntryPoint (ImageContext);
  DriverEntry->ImageBuffer     = (UINTN)DstBuffer;
  DriverEntry->NumberOfPage    = DstBufferPages;

  //
  // Fill in the remaining fields of the Loaded Image Protocol instance.
  // Note: ImageBase is an SMRAM address that can not be accessed outside of SMRAM if SMRAM window is closed.
  //
  DriverEntry->LoadedImage.Revision     = EFI_LOADED_IMAGE_PROTOCOL_REVISION;
  DriverEntry->LoadedImage.ParentHandle = NULL;
  DriverEntry->LoadedImage.SystemTable  = NULL;
  DriverEntry->LoadedImage.DeviceHandle = NULL;
  DriverEntry->LoadedImage.FilePath     = NULL;

  DriverEntry->LoadedImage.ImageBase     = DstBuffer;
  DriverEntry->LoadedImage.ImageSize     = ImageSize;
  DriverEntry->LoadedImage.ImageCodeType = EfiRuntimeServicesCode;
  DriverEntry->LoadedImage.ImageDataType = EfiRuntimeServicesData;

  //
  // Install Loaded Image protocol into MM handle database for the MM Driver
  //
  MmInstallProtocolInterface (
    &DriverEntry->ImageHandle,
    &gEfiLoadedImageProtocolGuid,
    EFI_NATIVE_INTERFACE,
    &DriverEntry->LoadedImage
    );

  InternalProtectMmImage (ImageContext);

  //
  // Print the load address and the PDB file name if it is available
  //
  DEBUG_CODE_BEGIN ();

  CHAR8  EfiFileName[256];

  DEBUG ((
    DEBUG_INFO | DEBUG_LOAD,
    "Loading MM driver at 0x%11p EntryPoint=0x%11p ",
    DstBuffer,
    FUNCTION_ENTRY_POINT (UefiImageLoaderGetImageEntryPoint (ImageContext))
    ));

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

  return Status;
}

/**
  Preprocess dependency expression and update DriverEntry to reflect the
  state of  Before and After dependencies. If DriverEntry->Before
  or DriverEntry->After is set it will never be cleared.

  @param  DriverEntry           DriverEntry element to update .

  @retval EFI_SUCCESS           It always works.

**/
EFI_STATUS
MmPreProcessDepex (
  IN EFI_MM_DRIVER_ENTRY  *DriverEntry
  )
{
  UINT8  *Iterator;

  Iterator               = DriverEntry->Depex;
  DriverEntry->Dependent = TRUE;

  if (*Iterator == EFI_DEP_BEFORE) {
    DriverEntry->Before = TRUE;
  } else if (*Iterator == EFI_DEP_AFTER) {
    DriverEntry->After = TRUE;
  }

  if (DriverEntry->Before || DriverEntry->After) {
    CopyMem (&DriverEntry->BeforeAfterGuid, Iterator + 1, sizeof (EFI_GUID));
  }

  return EFI_SUCCESS;
}

/**
  Read Depex and pre-process the Depex for Before and After. If Section Extraction
  protocol returns an error via ReadSection defer the reading of the Depex.

  @param  DriverEntry           Driver to work on.

  @retval EFI_SUCCESS           Depex read and preprossesed
  @retval EFI_PROTOCOL_ERROR    The section extraction protocol returned an error
                                and  Depex reading needs to be retried.
  @retval Error                 DEPEX not found.

**/
EFI_STATUS
MmGetDepexSectionAndPreProccess (
  IN EFI_MM_DRIVER_ENTRY  *DriverEntry
  )
{
  EFI_STATUS  Status;

  //
  // Data already read
  //
  if (DriverEntry->Depex == NULL) {
    Status = EFI_NOT_FOUND;
  } else {
    Status = EFI_SUCCESS;
  }

  if (EFI_ERROR (Status)) {
    if (Status == EFI_PROTOCOL_ERROR) {
      //
      // The section extraction protocol failed so set protocol error flag
      //
      DriverEntry->DepexProtocolError = TRUE;
    } else {
      //
      // If no Depex assume depend on all architectural protocols
      //
      DriverEntry->Depex              = NULL;
      DriverEntry->Dependent          = TRUE;
      DriverEntry->DepexProtocolError = FALSE;
    }
  } else {
    //
    // Set Before and After state information based on Depex
    // Driver will be put in Dependent state
    //
    MmPreProcessDepex (DriverEntry);
    DriverEntry->DepexProtocolError = FALSE;
  }

  return Status;
}

/**
  This is the main Dispatcher for MM and it exits when there are no more
  drivers to run. Drain the mScheduledQueue and load and start a PE
  image for each driver. Search the mDiscoveredList to see if any driver can
  be placed on the mScheduledQueue. If no drivers are placed on the
  mScheduledQueue exit the function.

  @retval EFI_SUCCESS           All of the MM Drivers that could be dispatched
                                have been run and the MM Entry Point has been
                                registered.
  @retval EFI_NOT_READY         The MM Driver that registered the MM Entry Point
                                was just dispatched.
  @retval EFI_NOT_FOUND         There are no MM Drivers available to be dispatched.
  @retval EFI_ALREADY_STARTED   The MM Dispatcher is already running

**/
EFI_STATUS
MmDispatcher (
  VOID
  )
{
  EFI_STATUS                    Status;
  LIST_ENTRY                    *Link;
  EFI_MM_DRIVER_ENTRY           *DriverEntry;
  BOOLEAN                       ReadyToRun;
  BOOLEAN                       PreviousMmEntryPointRegistered;
  PE_COFF_LOADER_IMAGE_CONTEXT  ImageContext;

  DEBUG ((DEBUG_INFO, "MmDispatcher\n"));

  if (!gRequestDispatch) {
    DEBUG ((DEBUG_INFO, "  !gRequestDispatch\n"));
    return EFI_NOT_FOUND;
  }

  if (gDispatcherRunning) {
    DEBUG ((DEBUG_INFO, "  gDispatcherRunning\n"));
    //
    // If the dispatcher is running don't let it be restarted.
    //
    return EFI_ALREADY_STARTED;
  }

  gDispatcherRunning = TRUE;

  do {
    //
    // Drain the Scheduled Queue
    //
    DEBUG ((DEBUG_INFO, "  Drain the Scheduled Queue\n"));
    while (!IsListEmpty (&mScheduledQueue)) {
      DriverEntry = CR (
                      mScheduledQueue.ForwardLink,
                      EFI_MM_DRIVER_ENTRY,
                      ScheduledLink,
                      EFI_MM_DRIVER_ENTRY_SIGNATURE
                      );
      DEBUG ((DEBUG_INFO, "  DriverEntry (Scheduled) - %g\n", &DriverEntry->FileName));

      //
      // Load the MM Driver image into memory. If the Driver was transitioned from
      // Untrusted to Scheduled it would have already been loaded so we may need to
      // skip the LoadImage
      //
      if (DriverEntry->ImageHandle == NULL) {
        Status = MmLoadImage (DriverEntry, &ImageContext);

        //
        // Update the driver state to reflect that it's been loaded
        //
        if (EFI_ERROR (Status)) {
          //
          // The MM Driver could not be loaded, and do not attempt to load or start it again.
          // Take driver from Scheduled to Initialized.
          //
          DriverEntry->Initialized = TRUE;
          DriverEntry->Scheduled   = FALSE;
          RemoveEntryList (&DriverEntry->ScheduledLink);

          //
          // If it's an error don't try the StartImage
          //
          continue;
        }
      }

      DriverEntry->Scheduled   = FALSE;
      DriverEntry->Initialized = TRUE;
      RemoveEntryList (&DriverEntry->ScheduledLink);

      //
      // Cache state of MmEntryPointRegistered before calling entry point
      //
      PreviousMmEntryPointRegistered = mMmEntryPointRegistered;

      //
      // For each MM driver, pass NULL as ImageHandle
      //
      DEBUG ((DEBUG_INFO, "StartImage - 0x%x (Standalone Mode)\n", DriverEntry->ImageEntryPoint));
      Status = ((MM_IMAGE_ENTRY_POINT)(UINTN)DriverEntry->ImageEntryPoint)(DriverEntry->ImageHandle, &gMmCoreMmst);
      if (EFI_ERROR (Status)) {
        DEBUG ((DEBUG_INFO, "StartImage Status - %r\n", Status));

        // we need to unload the image before we free the pages. On some architectures (e.g. x86), this is a no-op, but
        // on others (e.g. AARCH64) this will remove the image memory protections set on the region so that when the
        // memory is freed, it has the default attributes set and can be used generically
        PeCoffLoaderUnloadImage (&ImageContext);
        MmFreePages (DriverEntry->ImageBuffer, DriverEntry->NumberOfPage);
        if (DriverEntry->ImageHandle != NULL) {
          MmUninstallProtocolInterface (
            DriverEntry->ImageHandle,
            &gEfiLoadedImageProtocolGuid,
            &DriverEntry->LoadedImage
            );
        }
      }

      if (!PreviousMmEntryPointRegistered && mMmEntryPointRegistered) {
        if (FeaturePcdGet (PcdRestartMmDispatcherOnceMmEntryRegistered)) {
          //
          // Return immediately if the MM Entry Point was registered by the MM
          // Driver that was just dispatched. The MM IPL will reinvoke the MM
          // Core Dispatcher. This is required so MM Mode may be enabled as soon
          // as all the dependent MM Drivers for MM Mode have been dispatched.
          // Once the MM Entry Point has been registered, then MM Mode will be
          // used.
          //
          gRequestDispatch   = TRUE;
          gDispatcherRunning = FALSE;
          return EFI_NOT_READY;
        }
      }
    }

    //
    // Search DriverList for items to place on Scheduled Queue
    //
    DEBUG ((DEBUG_INFO, "  Search DriverList for items to place on Scheduled Queue\n"));
    ReadyToRun = FALSE;
    for (Link = mDiscoveredList.ForwardLink; Link != &mDiscoveredList; Link = Link->ForwardLink) {
      DriverEntry = CR (Link, EFI_MM_DRIVER_ENTRY, Link, EFI_MM_DRIVER_ENTRY_SIGNATURE);
      DEBUG ((DEBUG_INFO, "  DriverEntry (Discovered) - %g\n", &DriverEntry->FileName));

      if (DriverEntry->DepexProtocolError) {
        //
        // If Section Extraction Protocol did not let the Depex be read before retry the read
        //
        Status = MmGetDepexSectionAndPreProccess (DriverEntry);
      }

      if (DriverEntry->Dependent) {
        if (MmIsSchedulable (DriverEntry)) {
          MmInsertOnScheduledQueueWhileProcessingBeforeAndAfter (DriverEntry);
          ReadyToRun = TRUE;
        }
      }
    }
  } while (ReadyToRun);

  //
  // If there is no more MM driver to dispatch, stop the dispatch request
  //
  DEBUG ((DEBUG_INFO, "  no more MM driver to dispatch, stop the dispatch request\n"));
  gRequestDispatch = FALSE;
  for (Link = mDiscoveredList.ForwardLink; Link != &mDiscoveredList; Link = Link->ForwardLink) {
    DriverEntry = CR (Link, EFI_MM_DRIVER_ENTRY, Link, EFI_MM_DRIVER_ENTRY_SIGNATURE);
    DEBUG ((DEBUG_INFO, "  DriverEntry (Discovered) - %g\n", &DriverEntry->FileName));

    if (!DriverEntry->Initialized) {
      //
      // We have MM driver pending to dispatch
      //
      gRequestDispatch = TRUE;
      break;
    }
  }

  gDispatcherRunning = FALSE;

  return EFI_SUCCESS;
}

/**
  Insert InsertedDriverEntry onto the mScheduledQueue. To do this you
  must add any driver with a before dependency on InsertedDriverEntry first.
  You do this by recursively calling this routine. After all the Before Depexes
  are processed you can add InsertedDriverEntry to the mScheduledQueue.
  Then you can add any driver with an After dependency on InsertedDriverEntry
  by recursively calling this routine.

  @param  InsertedDriverEntry   The driver to insert on the ScheduledLink Queue

**/
VOID
MmInsertOnScheduledQueueWhileProcessingBeforeAndAfter (
  IN  EFI_MM_DRIVER_ENTRY  *InsertedDriverEntry
  )
{
  LIST_ENTRY           *Link;
  EFI_MM_DRIVER_ENTRY  *DriverEntry;

  //
  // Process Before Dependency
  //
  for (Link = mDiscoveredList.ForwardLink; Link != &mDiscoveredList; Link = Link->ForwardLink) {
    DriverEntry = CR (Link, EFI_MM_DRIVER_ENTRY, Link, EFI_MM_DRIVER_ENTRY_SIGNATURE);
    if (DriverEntry->Before && DriverEntry->Dependent && (DriverEntry != InsertedDriverEntry)) {
      DEBUG ((DEBUG_DISPATCH, "Evaluate MM DEPEX for FFS(%g)\n", &DriverEntry->FileName));
      DEBUG ((DEBUG_DISPATCH, "  BEFORE FFS(%g) = ", &DriverEntry->BeforeAfterGuid));
      if (CompareGuid (&InsertedDriverEntry->FileName, &DriverEntry->BeforeAfterGuid)) {
        //
        // Recursively process BEFORE
        //
        DEBUG ((DEBUG_DISPATCH, "TRUE\n  END\n  RESULT = TRUE\n"));
        MmInsertOnScheduledQueueWhileProcessingBeforeAndAfter (DriverEntry);
      } else {
        DEBUG ((DEBUG_DISPATCH, "FALSE\n  END\n  RESULT = FALSE\n"));
      }
    }
  }

  //
  // Convert driver from Dependent to Scheduled state
  //

  InsertedDriverEntry->Dependent = FALSE;
  InsertedDriverEntry->Scheduled = TRUE;
  InsertTailList (&mScheduledQueue, &InsertedDriverEntry->ScheduledLink);

  //
  // Process After Dependency
  //
  for (Link = mDiscoveredList.ForwardLink; Link != &mDiscoveredList; Link = Link->ForwardLink) {
    DriverEntry = CR (Link, EFI_MM_DRIVER_ENTRY, Link, EFI_MM_DRIVER_ENTRY_SIGNATURE);
    if (DriverEntry->After && DriverEntry->Dependent && (DriverEntry != InsertedDriverEntry)) {
      DEBUG ((DEBUG_DISPATCH, "Evaluate MM DEPEX for FFS(%g)\n", &DriverEntry->FileName));
      DEBUG ((DEBUG_DISPATCH, "  AFTER FFS(%g) = ", &DriverEntry->BeforeAfterGuid));
      if (CompareGuid (&InsertedDriverEntry->FileName, &DriverEntry->BeforeAfterGuid)) {
        //
        // Recursively process AFTER
        //
        DEBUG ((DEBUG_DISPATCH, "TRUE\n  END\n  RESULT = TRUE\n"));
        MmInsertOnScheduledQueueWhileProcessingBeforeAndAfter (DriverEntry);
      } else {
        DEBUG ((DEBUG_DISPATCH, "FALSE\n  END\n  RESULT = FALSE\n"));
      }
    }
  }
}

/**
  Return TRUE if the firmware volume has been processed, FALSE if not.

  @param  FwVolHeader           The header of the firmware volume that's being
                                tested.

  @retval TRUE                  The firmware volume denoted by FwVolHeader has
                                been processed
  @retval FALSE                 The firmware volume denoted by FwVolHeader has
                                not yet been processed

**/
BOOLEAN
FvHasBeenProcessed (
  IN EFI_FIRMWARE_VOLUME_HEADER  *FwVolHeader
  )
{
  LIST_ENTRY   *Link;
  KNOWN_FWVOL  *KnownFwVol;

  for (Link = mFwVolList.ForwardLink;
       Link != &mFwVolList;
       Link = Link->ForwardLink)
  {
    KnownFwVol = CR (Link, KNOWN_FWVOL, Link, KNOWN_FWVOL_SIGNATURE);
    if (KnownFwVol->FwVolHeader == FwVolHeader) {
      return TRUE;
    }
  }

  return FALSE;
}

/**
  Remember that the firmware volume denoted by FwVolHeader has had its drivers
  placed on mDiscoveredList. This function adds entries to mFwVolList. Items
  are never removed/freed from mFwVolList.

  @param  FwVolHeader           The header of the firmware volume that's being
                                processed.

**/
VOID
FvIsBeingProcessed (
  IN EFI_FIRMWARE_VOLUME_HEADER  *FwVolHeader
  )
{
  KNOWN_FWVOL  *KnownFwVol;

  DEBUG ((DEBUG_INFO, "FvIsBeingProcessed - 0x%08x\n", FwVolHeader));

  KnownFwVol = AllocatePool (sizeof (KNOWN_FWVOL));
  if (KnownFwVol == NULL) {
    ASSERT (FALSE);
    return;
  }

  KnownFwVol->Signature   = KNOWN_FWVOL_SIGNATURE;
  KnownFwVol->FwVolHeader = FwVolHeader;
  InsertTailList (&mFwVolList, &KnownFwVol->Link);
}

/**
  Add an entry to the mDiscoveredList. Allocate memory to store the DriverEntry,
  and initialise any state variables. Read the Depex from the FV and store it
  in DriverEntry. Pre-process the Depex to set the Before and After state.
  The Discovered list is never freed and contains booleans that represent the
  other possible MM driver states.

  @param [in]   FwVolHeader     Pointer to the formware volume header.
  @param [in]   Pe32Data        Pointer to the PE data.
  @param [in]   Pe32DataSize    Size of the PE data.
  @param [in]   Depex           Pointer to the Depex info.
  @param [in]   DepexSize       Size of the Depex info.
  @param [in]   DriverName      Name of driver to add to mDiscoveredList.

  @retval EFI_SUCCESS           If driver was added to the mDiscoveredList.
**/
EFI_STATUS
MmAddToDriverList (
  IN EFI_FIRMWARE_VOLUME_HEADER  *FwVolHeader,
  IN VOID                        *Pe32Data,
  IN UINT32                      Pe32DataSize,
  IN VOID                        *Depex,
  IN UINTN                       DepexSize,
  IN EFI_GUID                    *DriverName
  )
{
  EFI_MM_DRIVER_ENTRY  *DriverEntry;

  DEBUG ((DEBUG_INFO, "MmAddToDriverList - %g (0x%08x)\n", DriverName, Pe32Data));

  //
  // Create the Driver Entry for the list. ZeroPool initializes lots of variables to
  // NULL or FALSE.
  //
  DriverEntry = AllocateZeroPool (sizeof (EFI_MM_DRIVER_ENTRY));
  ASSERT (DriverEntry != NULL);

  DriverEntry->Signature = EFI_MM_DRIVER_ENTRY_SIGNATURE;
  CopyGuid (&DriverEntry->FileName, DriverName);
  DriverEntry->FwVolHeader  = FwVolHeader;
  DriverEntry->Pe32Data     = Pe32Data;
  DriverEntry->Pe32DataSize = Pe32DataSize;
  DriverEntry->Depex        = Depex;
  DriverEntry->DepexSize    = DepexSize;

  MmGetDepexSectionAndPreProccess (DriverEntry);

  InsertTailList (&mDiscoveredList, &DriverEntry->Link);
  gRequestDispatch = TRUE;

  return EFI_SUCCESS;
}

/**
  Event notification that is fired MM IPL to dispatch the previously discovered MM drivers.

  @param[in]       DispatchHandle  The unique handle assigned to this handler by MmiHandlerRegister().
  @param[in]       Context         Points to an optional handler context which was specified when the
                                   handler was registered.
  @param[in, out]  CommBuffer      A pointer to a collection of data in memory that will
                                   be conveyed from a non-MM environment into an MM environment.
  @param[in, out]  CommBufferSize  The size of the CommBuffer.

  @return EFI_SUCCESS              Dispatcher is executed.

**/
EFI_STATUS
EFIAPI
MmDriverDispatchHandler (
  IN     EFI_HANDLE  DispatchHandle,
  IN     CONST VOID  *Context         OPTIONAL,
  IN OUT VOID        *CommBuffer      OPTIONAL,
  IN OUT UINTN       *CommBufferSize  OPTIONAL
  )
{
  EFI_STATUS  Status;

  DEBUG ((DEBUG_INFO, "MmDriverDispatchHandler\n"));

  //
  // Execute the MM Dispatcher on MM drivers that have been discovered
  // previously but not dispatched.
  //
  Status = MmDispatcher ();

  //
  // Check to see if CommBuffer and CommBufferSize are valid
  //
  if ((CommBuffer != NULL) && (CommBufferSize != NULL)) {
    if (*CommBufferSize > sizeof (EFI_STATUS)) {
      //
      // Set the status of MmDispatcher to CommBuffer
      //
      *(EFI_STATUS *)CommBuffer = Status;
    }
  }

  MmCoreInitializeMemoryAttributesTable ();

  MmiHandlerUnRegister (DispatchHandle);

  //
  // Free shadowed MM Fvs
  //
  MmFreeShadowedFvs ();

  return EFI_SUCCESS;
}

/**
  Traverse the discovered list for any drivers that were discovered but not loaded
  because the dependency expressions evaluated to false.

**/
VOID
MmDisplayDiscoveredNotDispatched (
  VOID
  )
{
  LIST_ENTRY           *Link;
  EFI_MM_DRIVER_ENTRY  *DriverEntry;

  for (Link = mDiscoveredList.ForwardLink; Link != &mDiscoveredList; Link = Link->ForwardLink) {
    DriverEntry = CR (Link, EFI_MM_DRIVER_ENTRY, Link, EFI_MM_DRIVER_ENTRY_SIGNATURE);
    if (DriverEntry->Dependent) {
      DEBUG ((DEBUG_LOAD, "MM Driver %g was discovered but not loaded!!\n", &DriverEntry->FileName));
    }
  }
}
