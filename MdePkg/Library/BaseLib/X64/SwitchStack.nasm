;------------------------------------------------------------------------------
; Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
; SPDX-License-Identifier: BSD-3-Clause
;
; Copyright (c) 2006 - 2008, Intel Corporation. All rights reserved.<BR>
; SPDX-License-Identifier: BSD-2-Clause-Patent
;
; Module Name:
;
;   SwitchStack.Asm
;
; Abstract:
;
;------------------------------------------------------------------------------

    DEFAULT REL
    SECTION .text

;------------------------------------------------------------------------------
; Routine Description:
;
;   Routine for switching stacks with 2 parameters
;
; Arguments:
;
;   (rcx) EntryPoint    - Entry point with new stack.
;   (rdx) Context1      - Parameter1 for entry point.
;   (r8)  Context2      - Parameter2 for entry point.
;   (r9)  NewStack      - The pointer to new stack.
;
; Returns:
;
;   None
;
;------------------------------------------------------------------------------
global ASM_PFX(InternalSwitchStack)
ASM_PFX(InternalSwitchStack):
    mov     rax, rcx
    mov     rcx, rdx
    mov     rdx, r8
    ;
    ; Reserve space for register parameters (rcx, rdx, r8 & r9) on the stack,
    ; in case the callee wishes to spill them.
    ;
    lea     rsp, [r9 - 0x20]
    call    rax

;------------------------------------------------------------------------------
; Routine Description:
;
;   Routine for transfering control to user image with 2 parameters
;
; Arguments:
;
;   (rcx) EntryPoint    - Entry point with new stack.
;   (rdx) Context1      - Parameter1 for entry point.
;   (r8)  Context2      - Parameter2 for entry point.
;   (r9)  NewStack      - The pointer to new stack.
;On stack CodeSelector  - Segment selector for code.
;On stack DataSelector  - Segment selector for data.
;
; Returns:
;
;   None
;
;------------------------------------------------------------------------------
global ASM_PFX(InternalEnterUserImage)
ASM_PFX(InternalEnterUserImage):
    ; Set Data selectors
    mov     rax, [rsp + 8*6]
    or      rax, 3H ; RPL = 3

    mov     ds, ax
    mov     es, ax
    mov     fs, ax
    mov     gs, ax

    ; Save Code selector
    mov     r10, [rsp + 8*5]
    or      r10, 3H ; RPL = 3

    ; Prepare stack before swithcing
    push    rax     ;  ss
    push    r9      ;  rsp
    push    r10     ;  cs
    push    rcx     ;  rip

    ; Save 2 parameters
    mov     rcx, rdx
    mov     rdx, r8

    ; Pass control to user image
    retfq

;------------------------------------------------------------------------------
; typedef enum {
;   SysCallReadMemory         = 0,
;   SysCallAllocateRing3Pages = 1,
;   SysCallAllocateCoreCopy   = 2,
;   SysCallLocateProtocol     = 3,
;   SysCallOpenProtocol       = 4,
;   SysCallMax
; } SYS_CALL_TYPE;
;------------------------------------------------------------------------------

%define READ_MEMORY           0
%define ALLOCATE_RING3_PAGES  1
%define ALLOCATE_CORE_COPY    2
%define LOCATE_PROTOCOL       3
%define OPEN_PROTOCOL         4

%macro CallSysRet 0
    ; Prepare SYSRET arguments.
    pop     rcx

    ; Switch from Core to User data segment selectors.
    pop     r11

o16 mov     ds, r11
o16 mov     es, r11
o16 mov     fs, r11
o16 mov     gs, r11

    ; Restore RFLAGS in R11 for SYSRET.
    pushfq
    pop     r11

    ; Switch to User Stack.
    pop     rbp
    pop     rdx
    mov     rsp, rdx

    ; SYSCALL saves RFLAGS into R11 and the RIP of the next instruction into RCX.
o64 sysret
    ; SYSRET copies the value in RCX into RIP and loads RFLAGS from R11.
%endmacro

%macro DisableSMAP 0
    pushfq
    pop     r10
    or      r10, 0x40000 ; Set AC (bit 18)
    push    r10
    popfq
%endmacro

%macro EnableSMAP 0
    pushfq
    pop     r10
    and     r10, ~0x40000 ; Clear AC (bit 18)
    push    r10
    popfq
%endmacro

;------------------------------------------------------------------------------
; UINTN
; EFIAPI
; CoreBootServices (
;   IN  UINT8  Type,
;   IN  UINTN  FunctionAddress,
;   ...
;   );
;
;   (rcx) RIP of the next instruction saved by SYSCALL in SysCall().
;   (rdx) FunctionAddress.
;   (r8)  Argument 1 of the called function.
;   (r9)  Argument 2 of the called function.
;   (r10) Type.
;   (r11) RFLAGS saved by SYSCALL in SysCall().
;On stack Argument 3, 4, ...
;------------------------------------------------------------------------------
global ASM_PFX(CoreBootServices)
ASM_PFX(CoreBootServices):
    ; Save User data segment selector temporarily in R11.
    mov     r11, ds

    ; Switch from User to Core data segment selectors.
    mov     ax, ss
    mov     ds, ax
    mov     es, ax
    mov     fs, ax
    mov     gs, ax

    ; Save User Stack pointers and switch to Core SysCall Stack.
    mov     rax, [ASM_PFX(gCoreSysCallStackTop)]
    sub     rax, 8
    mov     [rax], rsp
    mov     rsp, rax

    push    rbp
    mov     rbp, rsp

    ; Save User data segment selector on Core SysCall Stack.
    push    r11

    ; Save FunctionAddress in R11 as it will be called later.
    mov     r11, rdx

    ; Save return address for SYSRET.
    push    rcx

    cmp     r10, READ_MEMORY
    je      readMemory

    cmp     r10, ALLOCATE_RING3_PAGES
    je      allocateRing3Pages

    cmp     r10, ALLOCATE_CORE_COPY
    je      allocateCoreCopy

    cmp     r10, LOCATE_PROTOCOL
    je      locateProtocol

    cmp     r10, OPEN_PROTOCOL
    je      openProtocol

;------------------------------------------------------------------------------
; UINTN
; ReadMemory (
;   IN UINTN Address
;   );
readMemory:
    mov    rax, [rdx]

    CallSysRet

;------------------------------------------------------------------------------
; EFI_STATUS
; AllocateRing3Pages (
;   IN UINTN     NumberOfPages,
;   IN OUT VOID  **Memory
;   );
allocateRing3Pages:
    ; Save User (VOID **)Memory on Core SysCall Stack.
    push    r9

    ; Replace arguments according to UEFI calling convention.
    mov     rcx, r8
    ; Allocate space for (VOID *)Memory on Core SysCall Stack.
    sub     rsp, 8
    mov     rdx, rsp

    ; Call Boot Service by FunctionAddress.
    call    [r11]

    DisableSMAP

    ; Copy (VOID *)Memory from Core SysCall Stack to User Stack.
    pop     rdx
    pop     r9
    mov     [r9], rdx

    EnableSMAP

    CallSysRet

;------------------------------------------------------------------------------
; VOID *
; AllocateCoreCopy (
;   IN UINTN       AllocationSize,
;   IN CONST VOID  *Buffer
;   );
allocateCoreCopy:
    DisableSMAP

    ; Replace arguments according to UEFI calling convention.
    mov     rcx, r8
    mov     rdx, r9

    ; Call Boot Service by FunctionAddress.
    call    [r11]

    EnableSMAP

    CallSysRet

;------------------------------------------------------------------------------
; EFI_STATUS
; LocateProtocol (
;   IN  EFI_GUID  *Protocol,
;   IN  VOID      *Registration  OPTIONAL,
;   OUT VOID      **Interface
;   );
locateProtocol:
    ; Replace arguments according to UEFI calling convention.
    mov     rcx, r8
    mov     rdx, r9
    ; Allocate space for (VOID *)Interface on Core SysCall Stack.
    sub     rsp, 8
    mov     r8, rsp

    ; Call Boot Service by FunctionAddress.
    call    [r11]

    DisableSMAP

    ; Copy (VOID *)Interface from Core SysCall Stack to User Stack.
    pop     rcx
    mov     rdx, [rbp + 8]   ; rdx = User rsp
    mov     [rdx + 8*5], rcx ; 5th argument of SysCall (SysCallLocateProtocol)

    EnableSMAP

    CallSysRet

;------------------------------------------------------------------------------
; EFI_STATUS
; OpenProtocol (
;   IN  EFI_HANDLE  UserHandle,
;   IN  EFI_GUID    *Protocol,
;   OUT VOID        **Interface  OPTIONAL,
;   IN  EFI_HANDLE  ImageHandle,
;   IN  EFI_HANDLE  ControllerHandle,
;   IN  UINT32      Attributes
;   );
openProtocol:
    ; Replace arguments according to UEFI calling convention.
    mov     rcx, r8          ; UserHandle
    mov     rdx, r9          ; Protocol
    ; Allocate space for (VOID *)Interface on Core SysCall Stack.
    sub     rsp, 8
    mov     r8, rsp          ; Interface

    DisableSMAP

    ; Copy ImageHandle, ControllerHandle, Attributes from User Stack to Core SysCall Stack.
    mov     rax, [rbp + 8]   ; rax = User rsp
    mov     r9, [rax + 8*8]  ; Attributes - 8th argument of SysCall (SysCallOpenProtocol)
    push    r9
    mov     r9, [rax + 8*7]  ; ControllerHandle - 7th argument of SysCall (SysCallOpenProtocol)
    push    r9
    mov     r9, [rax + 8*6]  ; ImageHandle - 6th argument of SysCall (SysCallOpenProtocol)

    EnableSMAP

    ; Step over first 4 arguments, which are passed through registers.
    sub     rsp, 8*4

    ; Call Boot Service by FunctionAddress.
    call    [r11]

    DisableSMAP

    ; Copy (VOID *)Interface from Core SysCall Stack to User Stack.
    add     rsp, 8*6
    pop     rcx
    mov     rdx, [rbp + 8]   ; rdx = User rsp
    mov     [rdx + 8*5], rcx ; 5th argument of SysCall (SysCallOpenProtocol)

    EnableSMAP

    CallSysRet

SECTION .data

global ASM_PFX(gCoreSysCallStackTop)
ASM_PFX(gCoreSysCallStackTop):
    resq 1
