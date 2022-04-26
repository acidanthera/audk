# Verified EDK II image loader

This branch demonstrates the integration of a new image loader designed with the help of formal methods into the EDK II infrastructure.

## Introduction

The image loader is one of the central components of the firmware core and the trust base. Every image part of an UEFI system, including platform drivers from the primary firmware storage, Option ROMs from external hardware, and OS loaders from arbitrary storage, is verified and loaded by this library. Clearly it is a key component to ensure platform reliability and software compatibility, and can only be modified with great care. It also is an essential piece of security technologies such as Secure Boot and Measured Boot.

![image](LoaderFlow.png)

Unfortunately, over the years, the current EDK II image loader has been subject to bug reports affecting platform reliability, some of which have been unresolved to date. Please refer to the TianoCore BugZilla and especially discussions on the edk2-devel mailing list for further reading. Due to the incremental changes to the existing solution over the years, the state of a sound solution has been lost, and it has become a maintenance burden that is hard to fix and further advance incrementally. At the same time, the demand on not only tested but proven security has become more important in the recent times.

The usage of formal methods to design the new solution greatly helped restore the state of a truly sound solution, resolving many issues regarding inter-API guarantees and image acceptance. Many new abstractions have been introduced, external code has been centralized, and the overall flexibility has been improved, to hopefully aid future developers to extend the codebase more easily. Beyond that, the formal model guarantees that security-wise there have been no regressions, but even potential improvements.

## Issues of the current solution
* High level of maintenance cost due to convoluted function contracts
* Error-prone design promoting the introduction of code bugs
* Multiple real-world bugs affecting reliability, partially unaddressed for years

## Benefits of the new solution
* Fixes all known reported BZs on image loader reliability
* Formal methods guarantee a high level of reliability and security
* Improved design eases future maintenance and extension
* Architecture-independent image processing (e.g. for emulation)
* Possibility for more granular section permissions (e.g. read-only)

## Benefits of the formal methods involved
* Complete proof arithmetic cannot overflow (excluding intentional modulo arithmetic)
* Mostly complete proof memory accesses are safe (requires axioms)
* Complete proof of image compliance verification
* Complete proof of loading correctness
* Mostly complete proof of relocation application (end state cannot be easily described)

## Current progress, future goals, and further notes
* OVMF boots to Shell with SMM and Secure Boot enabled
* Extended support for image protection has been implemented
* Not all packages build or have been fully ported
* Not all features have been implemented, e.g. debug support and RISC-V
* Not all security requirements are met, i.e. due to insufficient APIs
* Not all problematic coding conventions have been fully resolved
* There are unrelated changes present to help testing and validation
* Build compatibility for out-of-tree packages is still absent

## BZs fixed by integrating the new image loader
* https://bugzilla.tianocore.org/show_bug.cgi?id=1999
* https://bugzilla.tianocore.org/show_bug.cgi?id=3329
* https://bugzilla.tianocore.org/show_bug.cgi?id=1860
* https://bugzilla.tianocore.org/show_bug.cgi?id=2120

## BZs easier to address by integrating the new image loader
* https://bugzilla.tianocore.org/show_bug.cgi?id=3326
* https://bugzilla.tianocore.org/show_bug.cgi?id=3331
