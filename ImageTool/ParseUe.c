#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include <assert.h>
#include <string.h>

#include <Base.h>

#include <IndustryStandard/UeImage.h>

#include <Library/UeImageLib.h>

#include "../MdePkg/Library/BasePeCoffLib2/BaseOverflow.h"

#include "ImageTool.h"

typedef struct {
  UE_LOADER_IMAGE_CONTEXT Lib;
} image_tool_context_ue;

image_tool_context_ue *ToolContextConstructUe(void *File, size_t FileSize)
{
  assert(File != NULL || FileSize == 0);

  if (FileSize > MAX_UINT32) {
    return NULL;
  }

  image_tool_context_ue *Context = calloc(1, sizeof(image_tool_context_ue));
  if (Context == NULL) {
    return NULL;
  }

  RETURN_STATUS Status = UeInitializeContext(
    &Context->Lib,
    File,
    (UINT32) FileSize
    );
  if (RETURN_ERROR(Status)) {
    free(Context);
    return NULL;
  }

  return Context;
}

void ToolContextDestructUe(image_tool_context_ue *Context)
{
  assert(Context != NULL);
  free(Context);
}

void ToolImageInitializeUe(
  image_tool_context_ue   *Context,
  image_tool_image_info_t *Image
  )
{
  assert(Context != NULL);
  assert(Image != NULL);
}
