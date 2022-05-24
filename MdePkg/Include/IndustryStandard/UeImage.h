/** @file
  Definitions of the UEFI Executable file format.

  Copyright (c) 2021, Marvin Häuser. All rights reserved.<BR>

  SPDX-License-Identifier: BSD-2-Clause-Patent
**/

#ifndef UE_IMAGE_H_
#define UE_IMAGE_H_

//
// UEFI Executable segment definitions.
//
// NOTE: To guarantee all data is sufficiently aligned, no matter what it is,
//       all UE segments are at least 8 Byte aligned in the UE memory space.
//       This leaves the bottom 3 Bits unused for valid values. Use them to
//       indicate the UE segment permissions.
//

///
/// The alignment, in Bytes, of each UE segment in the UE memory space.
///
#define UE_SEGMENT_ALIGNMENT  8U

///
/// Definition of an UEFI Executable segment header.
///
typedef struct {
  ///
  /// Information about the UE segment in the UE memory space.
  ///
  /// [Bit 0]     Indicates whether the UE segment is read-protected.
  /// [Bit 1]     Indicates whether the UE segment is execute-protected.
  /// [Bit 2]     Indicates whether the UE segment is write-protected.
  /// [Bits 31:3] The size, in 8 Byte units, of the UE segment in the UE memory
  ///             space.
  ///
  UINT32 ImageInfo;
  ///
  /// The size, in Bytes, of the UE segment in the UE raw file.
  ///
  UINT32 FileSize;
} UE_SEGMENT;

#define UE_SEGMENT_INFO_RP  BIT0
#define UE_SEGMENT_INFO_XP  BIT1
#define UE_SEGMENT_INFO_RO  BIT2

STATIC_ASSERT (
  sizeof (UE_SEGMENT) == 8 && ALIGNOF (UE_SEGMENT) == 4,
  "The UE segment definition does not meet the specification."
  );

///
/// Definition of an UEFI Executable XIP segment header.
///
typedef struct {
  ///
  /// Information about the UE segment in the UE memory space.
  ///
  /// [Bit 0]     Indicates whether the UE segment is read-protected.
  /// [Bit 1]     Indicates whether the UE segment is execute-protected.
  /// [Bit 2]     Indicates whether the UE segment is write-protected.
  /// [Bits 31:3] The size, in 8 Byte units, of the UE segment in the UE memory
  ///             space.
  ///
  UINT32 ImageInfo;
} UE_SEGMENT_XIP;

STATIC_ASSERT (
  sizeof (UE_SEGMENT_XIP) == 4 && ALIGNOF (UE_SEGMENT_XIP) == 4,
  "The UE XIP segment definition does not meet the specification."
  );

STATIC_ASSERT (
  OFFSET_OF (UE_SEGMENT, ImageInfo) == OFFSET_OF (UE_SEGMENT_XIP, ImageInfo),
  "The UE and UE XIP segment definitions do not align."
  );

/**
  Retrieve the UE segment memory permissions.

  @param[in] ImageInfo  The UE segment memory information.
**/
#define UE_SEGMENT_PERMISSIONS(ImageInfo) ((ImageInfo) & 0x00000007U)

/**
  Retrieve the size, in Bytes, of the UE segment in the UE memory space.

  @param[in] ImageInfo  The UE segment image information.
**/
#define UE_SEGMENT_SIZE(ImageInfo)        ((ImageInfo) & 0xFFFFFFF8U)

STATIC_ASSERT (
  IS_ALIGNED (UE_SEGMENT_SIZE (0xFFFFFFFF), UE_SEGMENT_ALIGNMENT),
  "The UE segment size definition does not meet the specification."
  );

//
// UEFI Executable section definitions.
//
// NOTE: To guarantee all data is sufficiently aligned, no matter what it is,
//       all UE sections are at least 8 Byte aligned.
//
//       UE sections are identified by ID and can be omitted to save space.
//
//       UE sections are ordered by ID to allow efficient lookups.
//
//       UE relocation table will likely be close to PE/COFF.
//
//       UE HII support needs discussion, REF: https://bugzilla.tianocore.org/show_bug.cgi?id=557
//
//       UE certificate table will likely be a stripped version of PE/COFF.
//
//       UE sections are not loaded into the UE memory space as their data is
//       only required by the loader.
//
//       UE section Bit 2 is reserved in case more UE section IDs are required
//       in the future. If it is set, an extended structure should be used.
//

///
/// The alignment, in Bytes, of each UE section in the UE raw file.
///
#define UE_SECTION_ALIGNMENT  8U

///
/// Definition of UE section identifiers.
///
enum {
  UeSectionIdRelocTable = 0x00U,
  UeSectionIdDebugTable = 0x01U,
  UeSectionIdHiiTable   = 0x02U
};

//
// Definition of an UE section header.
//
typedef struct {
  ///
  /// Information about the UE section.
  ///
  /// [Bits 1:0]  The identifier of the UE section.
  /// [Bit 2]     Reserved for future usage. Must be set to 0.
  /// [Bits 31:3] The size, in 8 Byte units, of the UE section in the UE raw
  ///             file.
  ///
  UINT32 FileInfo;
} UE_SECTION;

STATIC_ASSERT (
  sizeof (UE_SECTION) == 4 && ALIGNOF (UE_SECTION) == 4,
  "The UE section definition does not meet the specification."
  );

/**
  Retrieves the UE section identifier.

  @param[in] FileInfo  The UE section raw file information.
**/
#define UE_SECTION_ID(FileInfo)   ((FileInfo) & 0x00000003U)

/**
  Retrieves the size, in Bytes, of the UE section in the UE raw file.

  @param[in] FileInfo  The UE section raw file information.
**/
#define UE_SECTION_SIZE(FileInfo) ((FileInfo) & 0xFFFFFFF8U)

STATIC_ASSERT (
  IS_ALIGNED (UE_SECTION_SIZE (0xFFFFFFFF), UE_SECTION_ALIGNMENT),
  "The UE section size definition does not meet the specification."
  );

//
// UEFI Executable relocation table definitions.
//
// NOTE: The rest of the definitions should be close to PE/COFF.
//       PE/COFF SizeOfBlock allows for a lot more relocations, however forcing
//       4 KB blocks still allows for one relocation per Byte with this design.
//

///
/// Definition of the UEFI Executable relocation identifiers.
///
enum {
  UeRelocRel32     = 0x00U,
  UeRelocRel64     = 0x01U,
  UeRelocArmMov32t = 0x02U
};

#define UE_RELOCATION_BLOCK_ALIGNMENT   4U

#define UE_RELOCATION_BLOCK_MAX_RELOCS  4095U

///
/// Definition of an UEFI Executable relocation block.
///
typedef struct {
  ///
  /// Information about the UE relocation block.
  ///
  /// [Bits 11:0]  The amount of relocations of the UE relocation block.
  /// [Bits 31:12] The base address, in 4 KB units, of the UE relocation block.
  ///
  UINT32 BlockInfo;
  ///
  /// The relocations of the UE relocation block.
  ///
  /// [Bits 11:0]  The offset of the UE relocation in the UE relocation block.
  /// [Bits 31:12] The type of the UE relocation.
  ///
  UINT16 RelocInfo[];
} UE_RELOCATION_BLOCK;

STATIC_ASSERT (
  sizeof (UE_RELOCATION_BLOCK) == 4 && ALIGNOF (UE_RELOCATION_BLOCK) == UE_RELOCATION_BLOCK_ALIGNMENT,
  "The UE relocation block definition does not meet the specification."
  );

STATIC_ASSERT (
  ALIGNOF (UE_RELOCATION_BLOCK) <= UE_SECTION_ALIGNMENT,
  "The UE relocation block definition does not meet the specification."
  );

STATIC_ASSERT (
  OFFSET_OF (UE_RELOCATION_BLOCK, RelocInfo) == sizeof (UE_RELOCATION_BLOCK),
  "The UE relocation block definition does not meet the specification."
  );

/**
  Retrieves the target offset of the UE relocation.

  @param[in] RelocInfo  The UE relocation information.
**/
#define UE_RELOC_OFFSET(RelocInfo) ((RelocInfo) & 0x0FFFU)

/**
  Retrieves the type of the UE relocation.

  @param[in] RelocInfo  The UE relocation information.
**/
#define UE_RELOC_TYPE(RelocInfo)   ((RelocInfo) >> 12U)

/**
  Retrieves the amount of relocations in the UE relocation block.

  @param[in] BlockInfo  The UE relocation block information.
**/
#define UE_RELOC_BLOCK_NUM(BlockInfo)     ((BlockInfo) & 0x00000FFFU)

/**
  Retrieves the base address of the UE relocation block.

  @param[in] BlockInfo  The UE relocation block information.
**/
#define UE_RELOC_BLOCK_ADDRESS(BlockInfo) ((BlockInfo) & 0xFFFFF000U)

//
// UEFI Executable debug table definitions.
//
// NOTE: The UE symbols base address offset is required for conversion of
//       PE/COFF Images that have their first section start after the end of the
//       Image headers. As PDBs cannot easily be rebased, store the offset.
//

///
/// Definition of an UEFI Executable segment name.
///
typedef UINT8 UE_SEGMENT_NAME[8];

STATIC_ASSERT (
  sizeof (UE_SEGMENT_NAME) == 8 && ALIGNOF (UE_SEGMENT_NAME) == 1,
  "The UE segment name definition does not meet the specification."
  );

///
/// Definition of an UEFI Executable section header.
///
typedef struct {
  ///
  /// The offset to be added to the UE base address in order to retrieve the
  /// UE symbols base address.
  /// FIXME: Can we rely on equal layouts for all source file formats?
  ///
  INT16           SymbolsBaseOffset;
  //
  // Reserved for future usage. Must be set to 0.
  //
  UINT8           Reserved;
  ///
  /// The size, in Bytes, of the UE symbols path.
  ///
  UINT8           SymbolsPathSize;
  ///
  /// The UE symbols path.
  ///
  UINT8           SymbolsPath[];
  ///
  /// The UE segment name table. In the same order as the UE segment table.
  ///
//UE_SEGMENT_NAME SegmentNames[];
} UE_DEBUG_TABLE;

///
/// The minimum size, in Bytes, of the UE debug table.
///
#define MIN_SIZE_OF_UE_DEBUG_TABLE  OFFSET_OF (UE_DEBUG_TABLE, SymbolsPath)

/**
  Retrieves the segment name table of an UE debug table.

  @param[in] DebugTable  The UE debug table.
**/
#define UE_DEBUG_TABLE_SEGMENT_NAMES(DebugTable)               \
  (CONST UE_SEGMENT_NAME *) (                                  \
    (DebugTable)->SymbolsPath + (DebugTable)->SymbolsPathSize  \
    )

STATIC_ASSERT (
  sizeof (UE_DEBUG_TABLE) == 4 && ALIGNOF (UE_DEBUG_TABLE) == 2,
  "The UE debug table definition does not meet the specification."
  );

STATIC_ASSERT (
  ALIGNOF (UE_DEBUG_TABLE) <= UE_SECTION_ALIGNMENT,
  "The UE debug table definition is misaligned."
  );

STATIC_ASSERT (
  OFFSET_OF (UE_DEBUG_TABLE, SymbolsPath) == sizeof (UE_DEBUG_TABLE),
  "The UE relocation block definition does not meet the specification."
  );

//
// UEFI Executable header definitions.
//
// NOTE: The UE segment alignment is stored as shift exponent to save up to
//       3 Bytes. This also guarantees it to be a power fo two.
//
//       UE fixed-address loading needs reconsideration.
//
//       The UE header can be contained in a separate FFS section to save space.
//
//       The UE segment table overlaps the UE header padding. However, as there
//       must always be at least one segment, the padding can be ignored.
//
//       The index of the last UE segment is stored over the number of segments
//       to avoid the check against 0, and to allow for one more segment.
//
//       The remaining reserved fields may be used to indicate revision.
//
//       The certificate table is not stored as an UE section to both omit its
//       size from the headers (allows for multi-step-signing without having to
//       hash the certificate table size), and to allow immediate hashing.
//
//       The UE XIP header omits all data that can be derived from platform
//       constraints. This header is not guaranteed to be backwards-compatible.
//

///
/// The signature of an UEFI Executable header.
///
#define UE_HEADER_SIGNATURE  SIGNATURE_16 ('U', 'E')

#define UE_HEADER_FLAG_RELOCS_STRIPPED  BIT7

///
/// Definition of the UEFI Executable machine identifiers.
///
enum {
  UeMachineI386          = 0x00U,
  UeMachineEbc           = 0x01U,
  UeMachineX64           = 0x02U,
  UeMachineArmThumbMixed = 0x03U,
  UeMachineArm64         = 0x04U,
  UeMachineRiscV32       = 0x05U,
  UeMachineRiscV64       = 0x06U,
  UeMachineRiscV128      = 0x07U
};

///
/// Definition of the UEFI Executable subsystem identifiers.
///
enum {
  UeSubsystemEfiApplication        = 0x00U,
  UeSubsystemEfiBootServicesDriver = 0x01U,
  UeSubsystemEfiRuntimeDriver      = 0x02U,
  UeSubsystemSalRuntimeDriver      = 0x03U,
};

///
/// Definition of an UEFI Executable header.
///
typedef struct {
  ///
  /// The signature to identify the UE raw file format. Must match 'UE'.
  ///
  UINT16     Signature;
  ///
  /// [Bits 7:0] Reserved for future usage. Must be set to 0.
  ///
  UINT8      Reserved;
  ///
  /// Information about the UE Image.
  ///
  /// [Bits 4:0] The shift exponent for the UE segment alignment in Bytes.
  /// [Bits 6:5] Reserved for future usage. Must be set to 0.
  /// [Bit 7]    Indicates whether the UE relocation table has been stripped.
  ///
  UINT8      ImageInfo;
  ///
  /// The index of the last segment in the UE segment table.
  ///
  UINT8      LastSegmentIndex;
  ///
  /// The number of sections in the UE section table.
  ///
  UINT8      NumSections;
  ///
  /// Indicates the subsystem identifier the UE targets.
  ///
  UINT8      Subsystem;
  ///
  /// Indicates the machine identifier the UE targets.
  ///
  UINT8      Machine;
  ///
  /// Indicates the UE preferred load address.
  ///
  UINT64     PreferredAddress;
  ///
  /// Indicates the offset of the UE entry point in the UE memory space.
  ///
  UINT32     EntryPointAddress;
  ///
  /// Extended information about the UE Image.
  ///
  /// [Bits 2:0]  Reserved for future usage. Must be set to 0.
  /// [Bits 31:3] The size, in 8 Byte units, of the unsigned UE raw file. If the
  ///             UE raw file size is larger than this value, the appended data
  ///             is the UE certificate table.
  ///
  UINT32     ImageInfo2;
  ///
  /// The UE segment table. It contains all data of the UE memory space.
  ///
  /// All UE segments are contiguous in the UE memory space.
  /// The offset of the first UE segment in the UE memory space is 0.
  ///
  /// All UE segments are contiguous in the UE raw file.
  /// The offset of the first UE segment in the UE raw file is the end of the
  /// UEFI Executable header in the UE raw file.
  ///
  UE_SEGMENT Segments[];
  ///
  /// The UE section table. It contains data useful for UE loading.
  ///
  /// All UE sections are contiguous in the UE raw file.
  /// The offset of the first UE section in the UE raw file is the end of the
  /// last UE segment in the UE raw file.
  ///
  /// All UE sections are ordered by their UE section identifier.
  ///
//UE_SECTION Sections[];
} UE_HEADER;

///
/// The minimum size, in Bytes, of a valid UE header.
///
#define MIN_SIZE_OF_UE_HEADER  \
  (OFFSET_OF (UE_HEADER, Segments) + sizeof (UE_SEGMENT))

STATIC_ASSERT (
  sizeof (UE_HEADER) == 24 && ALIGNOF (UE_HEADER) == 8,
  "The UE header definition does not meet the specification."
  );

STATIC_ASSERT (
  ALIGNOF (UE_SEGMENT) <= ALIGNOF (UE_SECTION),
  "The UE header definition is misaligned."
  );

STATIC_ASSERT (
  OFFSET_OF (UE_HEADER, Segments) == sizeof (UE_HEADER),
  "The UE header definition does not meet the specification."
  );

/**
  Retrieves the UE segment alignment, in Bytes, as a power of two.

  @param[in] ImageInfo  The UE header image information.
**/
#define UE_HEADER_ALIGNMENT(ImageInfo) ((UINT32) 1U << ((ImageInfo) & 0x1FU))

/**
  Retrieves the 8 Byte aligned unsigned UE raw file size.
  If the UE raw file size is larger than this value, the appended data is the UE
  certificate table.
  @param[in] ImageInfo2  The UE header image information.
**/
#define UE_HEADER_UNSIGNED_SIZE(ImageInfo2) ((ImageInfo2) & 0xFFFFFFF8U)

STATIC_ASSERT (
  IS_ALIGNED (UE_HEADER_UNSIGNED_SIZE (0xFFFFFFFF), UE_SECTION_ALIGNMENT),
  "The unsigned UE raw file size definition does not meet the specification."
  );

///
/// Definition of an UEFI Executable XIP header.
///
typedef struct {
  ///
  /// [Bits 7:0] Reserved for future usage. Must be set to 0.
  ///
  UINT8          Reserved;
  ///
  /// Information about the UE Image.
  ///
  /// [Bits 4:0] The shift exponent for the UE segment alignment.
  /// [Bits 6:5] Reserved for future usage. Must be set to 0.
  /// [Bit 7]    Indicates whether the UE relocation table has been stripped.
  ///
  UINT8          ImageInfo;
  ///
  /// The index of the last segment in the UE segment table.
  ///
  UINT8          LastSegmentIndex;
  ///
  /// The number of sections in the UE section table.
  ///
  UINT8          NumSections;
  ///
  /// Indicates the offset of the UE entry point in the UE memory space.
  ///
  UINT32         EntryPointAddress;
  ///
  /// The UE segment table. It contains all data of the UE memory space.
  ///
  /// All UE segments are contiguous in the UE memory space.
  /// The offset of the first UE segment in the UE memory space is 0.
  ///
  /// The UE segments are stored separately in XIP memory.
  ///
  UE_SEGMENT_XIP Segments[];
  ///
  /// The UE section table. It contains data useful for UE loading.
  ///
  /// All UE sections are contiguous in the UE raw file.
  /// The offset of the first UE section in the UE raw file is the end of the
  /// UEFI Executable XIP header in the UE raw file.
  ///
  /// All UE sections are ordered by their UE section identifier.
  ///
//UE_SECTION     Sections[];
} UE_HEADER_XIP;

///
/// The minimum size, in Bytes, of a valid UE XIP header.
///
#define MIN_SIZE_OF_UE_HEADER_XIP  \
  (OFFSET_OF (UE_HEADER_XIP, Segments) + sizeof (UE_SEGMENT_XIP))

STATIC_ASSERT (
  sizeof (UE_HEADER_XIP) == 8 && ALIGNOF (UE_HEADER_XIP) == 4,
  "The UE XIP header definition does not meet the specification."
  );

STATIC_ASSERT (
  ALIGNOF (UE_SEGMENT_XIP) <= ALIGNOF (UE_SECTION),
  "The UE XIP header definition is misaligned."
  );

STATIC_ASSERT (
  OFFSET_OF (UE_HEADER_XIP, Segments) == sizeof (UE_HEADER_XIP),
  "The UE XIP header definition does not meet the specification."
  );

#endif // UE_IMAGE_H_
