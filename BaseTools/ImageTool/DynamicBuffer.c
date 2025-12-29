#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>

#include <Base.h>

#include <Library/BaseOverflowLib.h>

#include "ImageTool.h"
#include "DynamicBuffer.h"

#ifndef IMAGE_TOOL_DYNAMIC_BUFFER_GROWTH
#define IMAGE_TOOL_DYNAMIC_BUFFER_GROWTH  0x1000
#endif // IMAGE_TOOL_DYNAMIC_BUFFER_GROWTH

void
ImageToolBufferInit (
  image_tool_dynamic_buffer  *Buffer
  )
{
  memset (Buffer, 0, sizeof (*Buffer));
}

static
uint32_t
ImageToolBufferExpand (
  image_tool_dynamic_buffer  *Buffer,
  uint32_t                   Size
  )
{
  bool      Overflow;
  uint32_t  NewAllocatedSize;
  uint8_t   *NewMemory;
  uint32_t  Offset;

  assert (Buffer->DataSize <= Buffer->AllocatedSize);
  assert (IS_ALIGNED (Buffer->AllocatedSize, IMAGE_TOOL_DYNAMIC_BUFFER_GROWTH));

  if (Buffer->AllocatedSize - Buffer->DataSize < Size) {
    Overflow = BaseOverflowAlignUpU32 (
                 Size,
                 IMAGE_TOOL_DYNAMIC_BUFFER_GROWTH,
                 &NewAllocatedSize
                 );
    if (Overflow) {
      DEBUG_RAISE ();
      return MAX_UINT32;
    }

    Overflow = BaseOverflowAddU32 (
                 NewAllocatedSize,
                 Buffer->AllocatedSize,
                 &NewAllocatedSize
                 );
    if (Overflow) {
      DEBUG_RAISE ();
      return MAX_UINT32;
    }

    NewMemory = AllocatePool (NewAllocatedSize);
    if (NewMemory == NULL) {
      DEBUG_RAISE ();
      return MAX_UINT32;
    }

    if (Buffer->Memory != NULL) {
      memmove (NewMemory, Buffer->Memory, Buffer->DataSize);
      FreePool (Buffer->Memory);
    }

    memset (
      NewMemory + Buffer->DataSize,
      0,
      NewAllocatedSize - Buffer->DataSize
      );

    Buffer->Memory        = NewMemory;
    Buffer->AllocatedSize = NewAllocatedSize;
  }

  Offset            = Buffer->DataSize;
  Buffer->DataSize += Size;

  return Offset;
}

void
ImageToolBufferRead (
  void                             *Data,
  uint32_t                         Size,
  const image_tool_dynamic_buffer  *Buffer,
  uint32_t                         Offset
  )
{
  assert (Offset + Size > Offset);
  assert (Offset + Size <= Buffer->DataSize);

  memmove (Data, &Buffer->Memory[Offset], Size);
}

void
ImageToolBufferWrite (
  image_tool_dynamic_buffer  *Buffer,
  uint32_t                   Offset,
  const void                 *Data,
  uint32_t                   Size
  )
{
  assert (Offset + Size > Offset);
  assert (Offset + Size <= Buffer->DataSize);

  memmove (&Buffer->Memory[Offset], Data, Size);
}

uint32_t
ImageToolBufferAppend (
  image_tool_dynamic_buffer  *Buffer,
  const void                 *Data,
  uint32_t                   Size
  )
{
  uint32_t  Offset;

  Offset = ImageToolBufferExpand (Buffer, Size);
  if (Offset != MAX_UINT32) {
    memmove (&Buffer->Memory[Offset], Data, Size);
  }

  return Offset;
}

uint32_t
ImageToolBufferAppendReserve (
  image_tool_dynamic_buffer  *Buffer,
  uint32_t                   Size
  )
{
  uint32_t  Offset;

  Offset = ImageToolBufferExpand (Buffer, Size);
  if (Offset != MAX_UINT32) {
    memset (&Buffer->Memory[Offset], 0, Size);
  }

  return Offset;
}

uint32_t
ImageToolBufferAppendReserveAlign (
  image_tool_dynamic_buffer  *Buffer,
  uint32_t                   Alignment
  )
{
  assert (IS_POW2 (Alignment));

  return ImageToolBufferAppendReserve (
           Buffer,
           ALIGN_VALUE_ADDEND (ImageToolBufferGetSize (Buffer), Alignment)
           );
}

void *
ImageToolBufferGetPointer (
  const image_tool_dynamic_buffer  *Buffer,
  uint32_t                         Offset
  )
{
  assert (Offset < Buffer->DataSize);

  return &Buffer->Memory[Offset];
}

uint32_t
ImageToolBufferGetSize (
  const image_tool_dynamic_buffer  *Buffer
  )
{
  return Buffer->DataSize;
}

void *
ImageToolBufferDump (
  uint32_t                   *Size,
  image_tool_dynamic_buffer  *Buffer
  )
{
  void      *Data;
  uint32_t  DataSize;

  // LCOV_EXCL_START
  if (Buffer->Memory == NULL) {
    return NULL;
  }

  // LCOV_EXCL_STOP

  DataSize = ImageToolBufferGetSize (Buffer);

  Data = AllocateCopyPool (DataSize, Buffer->Memory);
  if (Data == NULL) {
    return NULL;
  }

  *Size = DataSize;

  return Data;
}

void
ImageToolBufferFree (
  image_tool_dynamic_buffer  *Buffer
  )
{
  if (Buffer->Memory != NULL) {
    FreePool (Buffer->Memory);
  }

  ImageToolBufferInit (Buffer);
}
