/** @file
  Support routines for memory allocation routines based on SMM Core internal functions,
  with memory profile support.

  The PI System Management Mode Core Interface Specification only allows the use
  of EfiRuntimeServicesCode and EfiRuntimeServicesData memory types for memory
  allocations as the SMRAM space should be reserved after BDS phase.  The functions
  in the Memory Allocation Library use EfiBootServicesData as the default memory
  allocation type.  For this SMM specific instance of the Memory Allocation Library,
  EfiRuntimeServicesData is used as the default memory type for all allocations.
  In addition, allocation for the Reserved memory types are not supported and will
  always return NULL.

  Copyright (c) 2006 - 2018, Intel Corporation. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-2-Clause-Patent

**/

//
// The required functions are defined by PiSmmCore itself.
//
