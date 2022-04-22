#include <Base.h>

#include <Library/PeCoffLib.h>
#include <Library/CacheMaintenanceLib.h>

RETURN_STATUS
PeCoffLoadImageForExecution (
  IN OUT PE_COFF_LOADER_IMAGE_CONTEXT  *Context,
  OUT    VOID                          *Destination,
  IN     UINT32                        DestinationSize,
  OUT PE_COFF_RUNTIME_CONTEXT          *RelocationData OPTIONAL,
  IN  UINT32                           RelocationDataSize
  )
{
  RETURN_STATUS Status;
  UINTN         BaseAddress;
  UINTN         SizeOfImage;

  Status = PeCoffLoadImage (Context, Destination, DestinationSize);
  if (RETURN_ERROR (Status)) {
    return Status;
  }

  BaseAddress = PeCoffLoaderGetDestinationAddress (Context);
  Status = PeCoffRelocateImage (
    Context,
    BaseAddress,
    RelocationData,
    RelocationDataSize
    );
  if (RETURN_ERROR (Status)) {
    return Status;
  }

  SizeOfImage = PeCoffGetSizeOfImage (Context);
  //
  // Flush the instruction cache so the image data is written before we execute it
  //
  InvalidateInstructionCacheRange ((VOID *) BaseAddress, SizeOfImage);

  return RETURN_SUCCESS;
}
