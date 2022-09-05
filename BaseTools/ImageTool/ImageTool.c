#include "ImageTool.h"

image_tool_image_info_t mImageInfo;

static
EFI_STATUS
PeToUe (
	IN const char *PeName,
  IN const char *UeName
  )
{
  void       *Pe;
  uint32_t   PeSize;
  void       *Ue;
  uint32_t   UeSize;
  bool       Result;
  image_tool_image_info_t Image;

  Pe = UserReadFile (PeName, &PeSize);
  if (Pe == NULL) {
    return EFI_ABORTED;
  }

  Result = ToolContextConstructPe (&Image, Pe, PeSize);

  free(Pe);
  Pe = NULL;

  if (!Result) {
    return EFI_ABORTED;
  }

  Result = CheckToolImage (&Image);
  if (!Result) {
    ToolImageDestruct (&Image);
    return EFI_ABORTED;
  }

  Result = ImageConvertToXip (&Image);
  if (!Result) {
    ToolImageDestruct (&Image);
    return EFI_ABORTED;
  }

  Ue = ToolImageEmitUe (&Image, &UeSize);

  if (Ue == NULL) {
    ToolImageDestruct (&Image);
    return EFI_ABORTED;
  }

  ToolImageDestruct (&Image);

  /*UE_LOADER_IMAGE_CONTEXT UeContext;
  EFI_STATUS Status = UeInitializeContext(&UeContext, Ue, UeSize);
  printf("UE status - %llu\n", Status);*/

  UserWriteFile (UeName, Ue, UeSize);

  free (Ue);
  Ue = NULL;

  return EFI_SUCCESS;
}

static
EFI_STATUS
ElfToIntermediateToPe (
	IN const char *ElfName,
	IN const char *PeName,
  IN const char *ModuleType
  )
{
	EFI_STATUS Status;
	void       *Pe;
  uint32_t   PeSize;

	assert (ElfName    != NULL);
	assert (PeName     != NULL);
	assert (ModuleType != NULL);

	Status = ElfToIntermediate (ElfName, ModuleType);
	if (EFI_ERROR (Status)) {
		return Status;
	}

  Pe = ToolImageEmitPe (&mImageInfo, &PeSize);
  if (Pe == NULL) {
    ToolImageDestruct (&mImageInfo);
    return EFI_ABORTED;
  }

  ToolImageDestruct (&mImageInfo);

  UserWriteFile (PeName, Pe, PeSize);

  free (Pe);

  return EFI_SUCCESS;
}

int main (int argc, char *argv[])
{
  EFI_STATUS Status;

  if (strcmp (argv[4], "ElfToPe") == 0) {
		// Status = ElfToPe (argv[1], argv[2], argv [3]);
    Status = ElfToIntermediateToPe (argv[1], argv[2], argv [3]);
    if (EFI_ERROR (Status)) {
      raise ();
      return -1;
    }
  } else if (strcmp (argv[4], "PeToUe") == 0) {
    Status = PeToUe (argv[1], argv[2]);
    if (EFI_ERROR (Status)) {
      raise ();
      return -1;
    }
  }

  return 0;
}
