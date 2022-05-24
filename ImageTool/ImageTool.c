#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include <assert.h>

#include <stdio.h>

#include <Base.h>

#include <IndustryStandard/PeImage2.h>
#include <IndustryStandard/UeImage.h>

#include <Library/UeImageLib.h>

#include "ImageTool.h"

#include <UserFile.h>

void ToolImageDestruct(image_tool_image_info_t *image)
{
  assert(image != NULL);
  free(image);
}

void *ToolImageEmitUe(image_tool_image_info_t *Image, uint32_t *FileSize);
image_tool_image_info_t *ToolContextConstructPe(void *File, size_t FileSize);

void ImageShrinkSegments(image_tool_segment_info_t *SegmentInfo)
{
  assert(SegmentInfo != NULL);

  for (uint64_t Index = 0; Index < SegmentInfo->NumSegments; ++Index) {
    image_tool_segment_t *Segment = SegmentInfo->Segments + Index;
    if (Segment->ImageSize < Segment->DataSize) {
      Segment->DataSize = Segment->ImageSize;
    }

    for (; Segment->DataSize > 0; --Segment->DataSize) {
      if (Segment->Data[Segment->DataSize - 1] != 0) {
        break;
      }
    }
  }
}

const image_tool_segment_t *ImageGetSegmentByAddress(
  const image_tool_segment_info_t *SegmentInfo,
  uint64_t                        Address
  )
{
  assert(SegmentInfo != NULL);

  for (uint64_t Index = 0; Index < SegmentInfo->NumSegments; ++Index) {
    if (SegmentInfo->Segments[Index].ImageAddress <= Address
     && Address < SegmentInfo->Segments[Index].ImageAddress + SegmentInfo->Segments[Index].ImageSize) {
      return &SegmentInfo->Segments[Index];
    }
  }

  return NULL;
}

void ImageDebugRelocs(image_tool_image_info_t *Image)
{
  assert(Image != NULL);

  image_tool_reloc_info_t *RelocInfo = &Image->RelocInfo;

  uint64_t WRelocs = 0;

  for (uint64_t Index = 0; Index < RelocInfo->NumRelocs; ++Index) {
    const image_tool_segment_t *Segment = ImageGetSegmentByAddress(
      &Image->SegmentInfo,
      RelocInfo->Relocs[Index].Target
      );
    if (Segment == NULL) {
      assert(false);
      continue;
    }

    if (Segment->Write) {
      printf("!!! writable reloc at %lx !!!\n", RelocInfo->Relocs[Index].Target);
      ++WRelocs;
    }
  }

  printf("!!! %lu relocs to writable segments !!!\n", WRelocs);
}

int main(void)
{
  uint32_t PeSize;
  void *Pe = UserReadFile("Pe.efi", &PeSize);
  if (Pe == NULL) {
    raise();
    return -1;
  }

  image_tool_image_info_t *Image = ToolContextConstructPe(Pe, PeSize);
  if (Image == NULL) {
    raise();
    return -1;
  }

  ImageShrinkSegments(&Image->SegmentInfo);

  ImageDebugRelocs(Image);

  uint32_t UeSize;
  void *Ue = ToolImageEmitUe(Image, &UeSize);
  if (Ue == NULL) {
    raise();
    return -1;
  }

  UE_LOADER_IMAGE_CONTEXT UeContext;
  EFI_STATUS Status = UeInitializeContext(&UeContext, Ue, UeSize);
  printf("UE status - %llu\n", Status);

  UserWriteFile("Ue.efi", Ue, UeSize);

  return 0;
}
