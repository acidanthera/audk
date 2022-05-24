#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include <assert.h>
#include <string.h>

#include <stdio.h>

#include <Base.h>

#include <IndustryStandard/PeImage2.h>
#include <IndustryStandard/UeImage.h>

#include <Library/UeImageLib.h>

#include "../MdePkg/Library/BasePeCoffLib2/BaseOverflow.h"

#include "ImageTool.h"

#include <UserFile.h>

void *ToolImageEmitPe(
  const image_tool_image_info_t *Image,
  uint32_t                      *FileSize
  );
void *ToolImageEmitUe(image_tool_image_info_t *Image, uint32_t *FileSize);
bool ToolContextConstructPe(image_tool_image_info_t *Image, const void *File, size_t FileSize);
bool CheckToolImage(image_tool_image_info_t *Image);

int main(void)
{
  uint32_t PeSize;
  void *Pe = UserReadFile("Pe.efi", &PeSize);
  if (Pe == NULL) {
    raise();
    return -1;
  }

  image_tool_image_info_t Image;
  bool Result = ToolContextConstructPe(&Image, Pe, PeSize);

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

  uint32_t UeSize;
  void *Ue = ToolImageEmitUe(&Image, &UeSize);

  if (Ue == NULL) {
    ToolImageDestruct(&Image);
    raise();
    return -1;
  }

  ToolImageDestruct(&Image);

  /*UE_LOADER_IMAGE_CONTEXT UeContext;
  EFI_STATUS Status = UeInitializeContext(&UeContext, Ue, UeSize);
  printf("UE status - %llu\n", Status);*/

  UserWriteFile("Ue.efi", Ue, UeSize);

  free(Ue);
  Ue = NULL;

  return 0;
}
