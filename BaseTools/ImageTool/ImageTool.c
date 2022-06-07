#include "ImageTool.h"

int main (int argc, char *argv[])
{
  void     *Pe;
  uint32_t PeSize;
  void     *Ue;
  uint32_t UeSize;
  bool     Result;
  image_tool_image_info_t Image;

  ElfToPe (argv[1], "Pe.efi");

  Pe = UserReadFile ("Pe.efi", &PeSize);
  if (Pe == NULL) {
    raise();
    return -1;
  }

  Result = ToolContextConstructPe(&Image, Pe, PeSize);

  free(Pe);
  Pe = NULL;

  if (!Result) {
    raise();
    return -1;
  }

  Result = CheckToolImage(&Image);
  if (!Result) {
    ToolImageDestruct(&Image);
    raise();
    return -1;
  }

  Result = ImageConvertToXip(&Image);
  if (!Result) {
    ToolImageDestruct(&Image);
    raise();
    return -1;
  }

  Ue = ToolImageEmitUe(&Image, &UeSize);

  if (Ue == NULL) {
    ToolImageDestruct(&Image);
    raise();
    return -1;
  }

  ToolImageDestruct(&Image);

  /*UE_LOADER_IMAGE_CONTEXT UeContext;
  EFI_STATUS Status = UeInitializeContext(&UeContext, Ue, UeSize);
  printf("UE status - %llu\n", Status);*/

  UserWriteFile(argv[2], Ue, UeSize);

  free(Ue);
  Ue = NULL;

  return 0;
}
