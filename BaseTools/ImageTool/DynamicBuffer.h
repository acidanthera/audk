#ifndef DYNAMIC_BUFFER_H
#define DYNAMIC_BUFFER_H

#include <stdint.h>

typedef struct {
  uint32_t  AllocatedSize;
  uint32_t  DataSize;
  uint8_t   *Memory;
} image_tool_dynamic_buffer;

void
ImageToolBufferInit (
  image_tool_dynamic_buffer  *Buffer
  );

uint32_t
ImageToolBufferAppend (
  image_tool_dynamic_buffer  *Buffer,
  const void                 *Data,
  uint32_t                   Size
  );

uint32_t
ImageToolBufferAppendReserve (
  image_tool_dynamic_buffer  *Buffer,
  uint32_t                   Size
  );

uint32_t
ImageToolBufferAppendReserveAlign (
  image_tool_dynamic_buffer  *Buffer,
  uint32_t                   Alignment
  );

void
ImageToolBufferRead (
  void                             *Data,
  uint32_t                         Size,
  const image_tool_dynamic_buffer  *Buffer,
  uint32_t                         Offset
  );

void
ImageToolBufferWrite (
  image_tool_dynamic_buffer  *Buffer,
  uint32_t                   Offset,
  const void                 *Data,
  uint32_t                   Size
  );

void *
ImageToolBufferGetPointer (
  const image_tool_dynamic_buffer  *Buffer,
  uint32_t                         Offset
  );

uint32_t
ImageToolBufferGetSize (
  const image_tool_dynamic_buffer  *Buffer
  );

void *
ImageToolBufferDump (
  uint32_t                   *Size,
  image_tool_dynamic_buffer  *Buffer
  );

void
ImageToolBufferFree (
  image_tool_dynamic_buffer  *Buffer
  );

#endif // DYNAMIC_BUFFER_H
