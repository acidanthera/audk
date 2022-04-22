# Verified EDK II image loader

This branch demonstrates the integration of a new, formally verified image loader into the EDK II infrastructure.

## Introduction

The image loader is one of the central components of the firmware core and the trust base. Every image part of an UEFI system, including platform drivers from the primary firmware storage, Option ROMs from external hardware, and OS loaders from arbitrary storage, are verified and loaded by this library. It's an essential piece of security technologies such as Secure Boot and Measured Boot, in a way that their effectivity strictly depends on the validation work done by the image loader.

![image](LoaderFlow.png)

As even images from untrusted user media are loaded into the UEFI execution environment with no fewer permissions than the trusted platform drivers (ex. SMM), the previously mentioned technologies are absolutely crucial to guarantee the security of the platform. Unfortunately, over the years, the current EDK II image loader has been subject to many bug reports affecting reliability and security, which have been unresolved to date. Please refer to the TianoCore BugZilla and "Further reading" for further information.

## Issues of the current solution
* High level of maintenance debt due to convoluted function contracts
* Error-prone design promoting the introduction of vulnerabilities such as TOC/TOU
* Multiple real-world bugs affecting reliability and security, unaddressed for years

## Benefits of the new solution
* Fixes all known reported BZs on image loader reliability and security
* Formal methods guarantee a high level of reliability
* Improved design eases future maintenance and extension
* Architecture-independent image processing (e.g. for emulation)
* Possibility for more granular section permissions (e.g. read-only)

## Benefits of the formal methods involved
* Complete proof arithmetic cannot overflow (ex. intentional modulo arithmetic)
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

## BZs fixed by integrating the new loader
* https://bugzilla.tianocore.org/show_bug.cgi?id=1957
* https://bugzilla.tianocore.org/show_bug.cgi?id=1990
* https://bugzilla.tianocore.org/show_bug.cgi?id=1993
* https://bugzilla.tianocore.org/show_bug.cgi?id=1999
* https://bugzilla.tianocore.org/show_bug.cgi?id=3328
* https://bugzilla.tianocore.org/show_bug.cgi?id=3329

## BZs made easier to address by integrating the new loader
* https://bugzilla.tianocore.org/show_bug.cgi?id=2120
* https://bugzilla.tianocore.org/show_bug.cgi?id=3326
* https://bugzilla.tianocore.org/show_bug.cgi?id=3331

## BZs that require further discussion
* https://bugzilla.tianocore.org/show_bug.cgi?id=1860
* https://bugzilla.tianocore.org/show_bug.cgi?id=2213

Please note that the list of BZs is not comprehensive regarding all issues of the current image loader. For further reading, please refer to section 2 of the publication "Securing the EDK II Image Loader".

## Further reading
* https://github.com/mhaeuser/ISPRASOpen-SecurePE
* M. Häuser and V. Cheptsov, "Securing the EDK II Image Loader," 2020 Ivannikov Ispras Open Conference (ISPRAS), 2020, pp. 16-25, doi: 10.1109/ISPRAS51486.2020.00010. (preprint: https://arxiv.org/abs/2012.05471)