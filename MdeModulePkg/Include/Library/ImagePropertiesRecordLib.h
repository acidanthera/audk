/** @file

  Provides definitions and functionality for manipulating IMAGE_PROPERTIES_RECORD.

  Copyright (c) 2016 - 2018, Intel Corporation. All rights reserved.<BR>
  Copyright (c) Microsoft Corporation.
  SPDX-License-Identifier: BSD-2-Clause-Patent

**/

#ifndef IMAGE_PROPERTIES_RECORD_SUPPORT_LIB_H_
#define IMAGE_PROPERTIES_RECORD_SUPPORT_LIB_H_

#include <Library/UefiImageLib.h>

/**
  Split the original memory map and add more entries to describe PE code
  and data sections for each image in the input ImageRecordList.

  NOTE: This function assumes PE code/data section are page aligned.
  NOTE: This function assumes there are enough entries for the new memory map.

  |         |      |      |      |      |      |         |
  | 4K PAGE | DATA | CODE | DATA | CODE | DATA | 4K PAGE |
  |         |      |      |      |      |      |         |
  Assume the above memory region is the result of one split memory map descriptor. It's unlikely
  that a linker will orient an image this way, but the caller must assume the worst case scenario.
  This image layout example contains code sections oriented in a way that maximizes the number of
  descriptors which would be required to describe each section. To ensure we have enough space
  for every descriptor of the broken up memory map, the caller must assume that every image will
  have the maximum number of code sections oriented in a way which maximizes the number of data
  sections with unrelated memory regions flanking each image within a single descriptor.

  Given an image record list, the caller should use the following formula when allocating extra descriptors:
  NumberOfAdditionalDescriptors = (MemoryMapSize / DescriptorSize) +
                                    ((2 * <Most Code Segments in a Single Image> + 3) * <Number of Images>)

  @param[in, out] MemoryMapSize                   IN:   The size, in bytes, of the old memory map before the split.
                                                  OUT:  The size, in bytes, of the used descriptors of the split
                                                        memory map
  @param[in, out] MemoryMap                       IN:   A pointer to the buffer containing the current memory map.
                                                        This buffer must have enough space to accomodate the "worst case"
                                                        scenario where every image in ImageRecordList needs a new descriptor
                                                        to describe its code and data sections.
                                                  OUT:  A pointer to the updated memory map with separated image section
                                                        descriptors.
  @param[in]      DescriptorSize                  The size, in bytes, of an individual EFI_MEMORY_DESCRIPTOR.
  @param[in]      ImageRecordList                 A list of IMAGE_PROPERTIES_RECORD entries used when searching
                                                  for an image record contained by the memory range described in
                                                  EFI memory map descriptors.
  @param[in]      NumberOfAdditionalDescriptors   The number of unused descriptors at the end of the input MemoryMap.
                                                  The formula in the description should be used to calculate this value.

  @retval EFI_SUCCESS                             The memory map was successfully split.
  @retval EFI_INVALID_PARAMETER                   MemoryMapSize, MemoryMap, or ImageRecordList was NULL.
**/
EFI_STATUS
EFIAPI
SplitTable (
  IN OUT UINTN                  *MemoryMapSize,
  IN OUT EFI_MEMORY_DESCRIPTOR  *MemoryMap,
  IN     UINTN                  DescriptorSize,
  IN     LIST_ENTRY             *ImageRecordList,
  IN     UINTN                  NumberOfAdditionalDescriptors
  );

/**
  Deleted an image properties record. The function will also call
  RemoveEntryList() on each code segment and the input ImageRecord before
  freeing each pool.

  @param[in]      ImageRecord             The IMAGE_PROPERTIES_RECORD to delete
**/
VOID
EFIAPI
DeleteImagePropertiesRecord (
  IN  UEFI_IMAGE_RECORD  *ImageRecord
  );

#endif
