# PE/COFF loader designed with formal methods

This branch demonstrates the integration of a new PE/COFF loader designed with the help of formal methods into the EDK II infrastructure.

## Introduction

The PE/COFF loader is one of the central components of the firmware core and its trust base. Every Image part of an UEFI system, including platform drivers from the primary firmware storage, Option ROMs from external hardware, and OS loaders from arbitrary storage, is verified and loaded by this library. Clearly it is a key component to ensure platform reliability and software compatibility, and can only be modified with great care. It also is an essential component for security technologies such as Secure Boot and Measured Boot.

![image](LoaderFlow.png)

Unfortunately, over the years, the current solution has been subject to bug reports affecting platform reliability, some of which have been unresolved to date. Please refer to the TianoCore BugZilla and especially discussions on the edk2-devel mailing list for further reading. Due to the incremental changes to the existing solution over the years, the state of a sound solution has been lost, and it has become a maintenance burden that is hard to fix and further advance incrementally. At the same time, the demand on not only tested but proven security has become more important in the recent times.

The usage of formal methods to design the new solution greatly helped restore the state of a truly sound solution, resolving many issues regarding inter-API guarantees and Image format validation. Many new abstractions have been introduced, external code has been centralized, and the overall flexibility has been improved, to hopefully aid developers to extend the codebase more easily in the future. Beyond that, the formal model ensures a high level of confidence that security-wise there have been no regressions, and there might even be potential improvements.

Please also refer to the new work-in-progress documentation available at [MdePkg/Library/BasePeCoffLib2/Documentation.md](MdePkg/Library/BasePeCoffLib2/Documentation.md)

## Further abstraction

The new solution has been implemented as a new library class in MdePkg. ``PeCoffLib2`` features a new API that allows for a more resilient and a more flexible caller design. Most notably, all Image operations have been integrated into the API design rather than the callers accessing the library context and duplicating certain work. ``PeCoffLib`` remains intact as deprecated API to support legacy code during the transition period.

To increase platform flexibility, a new layer of abstraction is introduced in the form of the library class ``UefiImageLib``, which can be found at [MdePkg/Include/Library/UefiImageLib.h](MdePkg/Include/Library/UefiImageLib.h). Currently, it is a subset of the APIs provided by ``PeCoffLib2`` that is expected to be compatible with most other common executable formats, plus a few convenience functions. As part of the proposal, the instance ``UefiImageLibPeCoff`` is provided, which is basically a shim for ``PeCoffLib2``. In the future, instances to support other file formats can be introduced without having to integrate them across the entire EDK II tree.

## Issues of the current solution
* High level of maintenance cost due to convoluted function contracts
* Error-prone design promoting the introduction of code bugs
* Multiple real-world bugs affecting reliability, some unaddressed for years
* A lot of duplicate caller-side code that decreases the flexibility of porting and integration (e.g. Image permissions in PEI)
* Dependency on Image re-parsing for production code

## Benefits of the new solution
* Fixes all known reported BugZilla tickets on PE/COFF loader reliability
* Formal methods increase confidence in a high level of reliability and security
* Improved design eases future maintenance and extension
* Architecture-independent Image processing (e.g. for emulation)
* Support for more granular Image section permissions (e.g. read-only)

## Benefits of the formal methods involved
* Complete proof arithmetic cannot overflow (excluding intentional modulo arithmetic)
* Mostly complete proof memory accesses are safe (requires axioms)
* Complete proof of Image format compliance verification
* Complete proof of Image loading
* Mostly complete proof of Image relocation (final memory state cannot be easily described)

## Further notes about the formal approach
* A snapshot of the new PE/COFF loader code will be provided with annotations and proving results
* The snapshot will not be current and updating the old code is out of the scope of this project, however the functional changes should be manageable to review
* We are currently investigating whether deploying the proving environment as a Docker container is feasible
* There may be aids to compare the updates over the last fully verified state (e.g. stripped versions of the code with diffs)
* If accepted, the new PE/COFF loader code should be developed further without updating the formal annotations, but with thorough review of important invariants and sufficient documentation

## Current progress, future goals, and further notes
* OVMF boots to Shell with SMM and Secure Boot enabled
* Linux EmulatorPkg boots
* Extended support for Image protection has been implemented
* FFS and DebugTable enhancements have been implemented
* Not all features have been implemented, e.g. RISC-V support
* There are unrelated changes present to help testing and validation
* Specified interfaces need adjustments (e.g. security architectural protocol)
* Some validation is still absent

## BZs fixed by integrating the new PE/COFF loader
* https://bugzilla.tianocore.org/show_bug.cgi?id=1860
* https://bugzilla.tianocore.org/show_bug.cgi?id=1999
* https://bugzilla.tianocore.org/show_bug.cgi?id=2120
* https://bugzilla.tianocore.org/show_bug.cgi?id=3329
* More to be added shortly...

## BZs easier to address by integrating the new PE/COFF loader
* https://bugzilla.tianocore.org/show_bug.cgi?id=3326
* https://bugzilla.tianocore.org/show_bug.cgi?id=3331
* More to be added shortly...
