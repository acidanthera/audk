/** @file

  Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause

**/

#include <Chipset/AArch64.h>
#include <Guid/EarlyPL011BaseAddress.h>
#include <Library/ArmLib.h>
#include <Library/DefaultExceptionHandlerLib.h>

#include "DxeMain.h"

STATIC UINTN  mCoreSp;
UINTN         gUartBaseAddress;

EFI_STATUS
EFIAPI
ArmCallRing3 (
  IN RING3_CALL_DATA *Data,
  IN VOID            *StackPointer,
  IN VOID            *EntryPoint,
  IN VOID            *SysCallStack,
  IN VOID            *CoreStack
  );

VOID
EFIAPI
ReturnToCore (
  IN EFI_STATUS Status,
  IN UINTN      CoreSp
  );

VOID
EFIAPI
ArmSetPan (
  VOID
  );

VOID
EFIAPI
ArmClearPan (
  VOID
  );

STATIC
EFI_STATUS
EFIAPI
SysCallBootService (
  IN  UINT8  Type,
  IN  VOID   *CoreRbp,
  IN  VOID   *UserRsp
  )
{
  EFI_STATUS              Status;
  EFI_PHYSICAL_ADDRESS    Physical;

  if (Type == SysCallReturnToCore) {
    ReturnToCore (*(EFI_STATUS *)CoreRbp, mCoreSp);
  }

  Status = CoreAllocatePages (
             AllocateAnyPages,
             EfiRing3MemoryType,
             EFI_SIZE_TO_PAGES (9 * sizeof (UINTN)),
             &Physical
             );
  if (EFI_ERROR (Status)) {
    return Status;
  }

  DisableSMAP ();
  CopyMem ((VOID *)((UINTN)Physical + sizeof (UINTN)), (VOID *)UserRsp, 8 * sizeof (UINTN));

  SetUefiImageMemoryAttributes (
    gUartBaseAddress,
    EFI_PAGE_SIZE,
    EFI_MEMORY_XP
    );
  EnableSMAP ();

  Status = CallBootService (
             Type,
             (CORE_STACK *)CoreRbp,
             (RING3_STACK *)(UINTN)Physical
             );

  SetUefiImageMemoryAttributes (
    gUartBaseAddress,
    EFI_PAGE_SIZE,
    EFI_MEMORY_XP | EFI_MEMORY_USER
    );

  CoreFreePages (Physical, EFI_SIZE_TO_PAGES (9 * sizeof (UINTN)));

  return Status;
}

VOID
EFIAPI
InitializeMsr (
  IN OUT EFI_CONFIGURATION_TABLE *Table,
  IN     UINTN                   NumberOfEntries
  )
{
  UINTN                    Tcr;
  UINTN                    Index;
  EARLY_PL011_BASE_ADDRESS *UartBase;
  EFI_PHYSICAL_ADDRESS     Physical;
  EFI_HOB_GENERIC_HEADER   *Ring3Hob;
  UINT16                   HobLength;
  EFI_STATUS               Status;
  //
  // If HCR_EL2.NV is 1 and the current Exception level is EL1,
  // then EL1 read accesses to the CurrentEL register return a value of 0x2 in bits[3:2].
  // CurrentEL == 1 -> HCR_EL2.NV == 0
  //
  // If stage 1 is enabled and stage 1 Base permissions use Direct permissions,
  // then GCS access is not permitted and UnprivGCS and PrivGCS are not present.
  //
  // Disable Hierarchical permissions just in case.
  //
  Tcr = ArmGetTCR ();
  Tcr |= TCR_EL1_HPD0_MASK | TCR_EL1_HPD1_MASK;
  ArmSetTCR (Tcr);
  //
  // Problem 1: Uart is memory maped.
  //
  for (Index = 0; Index < NumberOfEntries; ++Index) {
    if (CompareGuid (&gEfiHobListGuid, &(Table[Index].VendorGuid))) {
      UartBase         = GET_GUID_HOB_DATA (Table[Index].VendorTable);
      gUartBaseAddress = UartBase->DebugAddress;
      //
      // Copy Hob into Ring3.
      //
      Status = CoreAllocatePages (
                 AllocateAnyPages,
                 EfiRing3MemoryType,
                 1,
                 &Physical
                 );
      if (EFI_ERROR (Status)) {
        DEBUG ((DEBUG_ERROR, "Core: Failed to allocate memory for Ring3Hob.\n"));
        ASSERT (FALSE);
      }
      DEBUG ((DEBUG_ERROR, "UartBaseAddress = %p.\n", gUartBaseAddress));

      Ring3Hob = (EFI_HOB_GENERIC_HEADER *)(UINTN)Physical;

      HobLength = (UINT16)((sizeof (EFI_HOB_GUID_TYPE) + sizeof (EARLY_PL011_BASE_ADDRESS) + 0x7) & (~0x7));

      Ring3Hob->HobType = EFI_HOB_TYPE_GUID_EXTENSION;
      Ring3Hob->HobLength = HobLength;
      Ring3Hob->Reserved  = 0;

      CopyGuid (&((EFI_HOB_GUID_TYPE *)Ring3Hob)->Name, &gEarlyPL011BaseAddressGuid);

      Ring3Hob = (EFI_HOB_GENERIC_HEADER *)((UINTN)Ring3Hob + HobLength);

      Ring3Hob->HobType   = EFI_HOB_TYPE_END_OF_HOB_LIST;
      Ring3Hob->HobLength = sizeof (EFI_HOB_GENERIC_HEADER);
      Ring3Hob->Reserved  = 0;

      Table[Index].VendorTable = (VOID *)(UINTN)Physical;
      UartBase                 = GET_GUID_HOB_DATA (Table[Index].VendorTable);
      UartBase->DebugAddress   = gUartBaseAddress;
    }
  }

  if (ArmHasPan ()) {
    //
    // Enable Privileged Access Never feature.
    //
    ArmSetPan ();
  } else {
    DEBUG ((DEBUG_ERROR, "Core: Failed to initialize MSRs for Ring3.\n"));
    ASSERT (FALSE);
  }

  InitializeSysCallHandler ((VOID *)SysCallBootService);
}

VOID
EFIAPI
DisableSMAP (
  VOID
  )
{
  ArmClearPan ();
}

VOID
EFIAPI
EnableSMAP (
  VOID
  )
{
  ArmSetPan ();
}

EFI_STATUS
EFIAPI
CallRing3 (
  IN RING3_CALL_DATA *Data
  )
{
  return ArmCallRing3 (Data, gRing3CallStackTop, gRing3EntryPoint, gCoreSysCallStackTop, &mCoreSp);
}
