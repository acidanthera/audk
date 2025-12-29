/**
  Initialize the state information for the CPU Architectural Protocol.

  @retval EFI_SUCCESS           Thread can be successfully created
  @retval EFI_OUT_OF_RESOURCES  Can not allocate protocol data structure
  @retval EFI_DEVICE_ERROR      Can not create the thread
**/
EFI_STATUS
InitializeCpu (
  VOID
  )
{
  return EFI_SUCCESS;
}

/**
  Initialize Multi-processor support.

**/
VOID
InitializeMpSupport (
  VOID
  )
{
}
