/** @file

  Copyright (c) 2024, Mikhail Krichanov. All rights reserved.

  Copyright (C) Red Hat

  SPDX-License-Identifier: BSD-2-Clause-Patent

**/

#include <Guid/EarlyPL011BaseAddress.h>
#include <Library/BaseMemoryLib.h>
#include <Library/PcdLib.h>
#include <Library/PL011UartLib.h>

UINTN  mDebugLibFdtPL011UartAddress;

EFI_STATUS
EFIAPI
DebugLibFdtPL011UartUserConstructor (
  IN EFI_HANDLE        ImageHandle,
  IN EFI_SYSTEM_TABLE  *SystemTable
  )
{
  UINTN  Index;

  mDebugLibFdtPL011UartAddress = 0;

  for (Index = 0; Index < SystemTable->NumberOfTableEntries; ++Index) {
    if (CompareGuid (&gEarlyPL011BaseAddressGuid, &(SystemTable->ConfigurationTable[Index].VendorGuid))) {
      mDebugLibFdtPL011UartAddress = (UINTN)SystemTable->ConfigurationTable[Index].VendorTable;
      return EFI_SUCCESS;
    }
  }

  return EFI_NOT_FOUND;
}

/**
  (Copied from SerialPortWrite() in "MdePkg/Include/Library/SerialPortLib.h" at
  commit c4547aefb3d0, with the Buffer non-nullity assertion removed:)

  Write data from buffer to serial device.

  Writes NumberOfBytes data bytes from Buffer to the serial device.
  The number of bytes actually written to the serial device is returned.
  If the return value is less than NumberOfBytes, then the write operation failed.
  If NumberOfBytes is zero, then return 0.

  @param  Buffer           Pointer to the data buffer to be written.
  @param  NumberOfBytes    Number of bytes to written to the serial device.

  @retval 0                NumberOfBytes is 0.
  @retval >0               The number of bytes written to the serial device.
                           If this value is less than NumberOfBytes, then the write operation failed.
**/
UINTN
DebugLibFdtPL011UartWrite (
  IN UINT8  *Buffer,
  IN UINTN  NumberOfBytes
  )
{
  EFI_STATUS          Status;
  UINT64              BaudRate;
  UINT32              ReceiveFifoDepth;
  EFI_PARITY_TYPE     Parity;
  UINT8               DataBits;
  EFI_STOP_BITS_TYPE  StopBits;

  if (mDebugLibFdtPL011UartAddress == 0) {
    return 0;
  }

  BaudRate         = (UINTN)FixedPcdGet64 (PcdUartDefaultBaudRate);
  ReceiveFifoDepth = 0; // Use the default value for Fifo depth
  Parity           = (EFI_PARITY_TYPE)FixedPcdGet8 (PcdUartDefaultParity);
  DataBits         = FixedPcdGet8 (PcdUartDefaultDataBits);
  StopBits         = (EFI_STOP_BITS_TYPE)FixedPcdGet8 (PcdUartDefaultStopBits);

  Status = PL011UartInitializePort (
             mDebugLibFdtPL011UartAddress,
             FixedPcdGet32 (PL011UartClkInHz),
             &BaudRate,
             &ReceiveFifoDepth,
             &Parity,
             &DataBits,
             &StopBits
             );
  if (EFI_ERROR (Status)) {
    return 0;
  }

  return PL011UartWrite (mDebugLibFdtPL011UartAddress, Buffer, NumberOfBytes);
}
