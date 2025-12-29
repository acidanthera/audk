/** @file

  Unified linker script for GCC, CLANG based builds

  Copyright (c) 2023, Mikhail Krichanov. All rights reserved.<BR>
  Copyright (c) 2010 - 2021, Intel Corporation. All rights reserved.<BR>
  Copyright (c) 2015, Linaro Ltd. All rights reserved.<BR>
  (C) Copyright 2016 Hewlett Packard Enterprise Development LP<BR>

  SPDX-License-Identifier: BSD-2-Clause-Patent

**/

PHDRS {
  text      PT_LOAD     FLAGS(5);  /* R_X */
  data      PT_LOAD     FLAGS(6);  /* RW_ */
}

SECTIONS {

  . = ALIGNED_PE_HEADER_SIZE;

  .text : ALIGN(CONSTANT(MAXPAGESIZE)) {
    *(.text .text.* .stub .gnu.linkonce.t.*)
    *(.rodata .rodata.* .data.rel.ro .data.rel.ro.* .gnu.linkonce.r.*)
    *(.got .got.*)

    /*
     * The contents of AutoGen.c files are mostly constant from the POV of the
     * program, but most of it ends up in .data or .bss by default since few of
     * the variable definitions that get emitted are declared as CONST.
     * Unfortunately, we cannot pull it into the .text section entirely, since
     * patchable PCDs are also emitted here, but we can at least move all of the
     * emitted GUIDs here.
     */
    *:AutoGen.obj(.data.g*Guid)
  } :text

  .data : ALIGN(CONSTANT(MAXPAGESIZE)) {
    *(.data .data.* .gnu.linkonce.d.*)
    *(.bss .bss.*)
  } :data

  .hii : ALIGN(CONSTANT(MAXPAGESIZE)) {
    KEEP (*(.hii))
  }

  .eh_frame : ALIGN(CONSTANT(MAXPAGESIZE)) {
    KEEP (*(.eh_frame))
  }

  .rela (INFO) : {
    *(.rela .rela.*)
  }

  .build-id (INFO) : { *(.note.gnu.build-id) }

  /DISCARD/ : {
    *(.note.GNU-stack)
    *(.interp)
    *(.dynsym)
    *(.dynstr)
    *(.hash .gnu.hash)
    *(.comment)
    *(COMMON)
    *(.dynamic)
    *(.ARM.exidx .ARM.exidx.*)
  }
}
