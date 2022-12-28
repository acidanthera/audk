#ifndef UE_SUPPORT_H_
#define UE_SUPPORT_H_

#include <Library/UeImageLib.h>
#include <Library/UefiImageLib.h>

UEFI_IMAGE_RECORD *
UefiImageLoaderGetImageRecordUe (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context
  );

RETURN_STATUS
UefiImageDebugLocateImageUe (
  OUT UE_LOADER_IMAGE_CONTEXT  *Context,
  IN  UINTN                    Address
  );

RETURN_STATUS
UefiImageGetFixedAddressUe (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context,
  OUT    UINT64                   *Address
  );

RETURN_STATUS
UefiImageDebugPrintSegmentsUe (
  IN OUT UE_LOADER_IMAGE_CONTEXT  *Context
  );

#endif // UE_SUPPORT_H_
