/** @file
  Definitions of the UE certificate store format.

  Copyright (c) 2021, Marvin Häuser. All rights reserved.<BR>

  SPDX-License-Identifier: BSD-2-Clause-Patent
**/

#ifndef UE_CERT_STORE_H_
#define UE_CERT_STORE_H_

///
/// Definition of an UE certificate (PKCS).
///
typedef struct {
  ///
  /// The UE certificate (PKCS) information.
  ///
  /// [Bits 23:0]  The size, in Bytes, of TbsData.
  /// [Bits 31:24] Reserved for future usage. Must be set to 0.
  ///
  UINT32 Info;
  ///
  /// The size, in Bytes, of Signature.
  ///
  UINT32 SignatureSize;
  ///
  /// The ASN.1 DER encoded X.509 tbsCertificate field.
  ///
  UINT8  TbsData[];
  ///
  /// The signature of TbsData, signed by the certificate identified by
  /// TbsData.issuer, with the algorithm identified by SignatureAlgorithm. Its
  /// size is strictly defined by the signature algorithm.
  ///
//UINT8  Signature[];
} UE_CERT_PKCS;

/**
  Retrieves the size, in Bytes, of TbsData of an UE certificate (PKCS).

  @param[in] Info  The UE certificate (PKCS) information.
**/
#define UE_CERT_PKCS_TBS_SIZE(Info)  ((Info) & 0x00FFFFFFU)

STATIC_ASSERT (
  sizeof (UE_CERT_PKCS) == 8 && ALIGNOF (UE_CERT_PKCS) == 4,
  "The UE certificate (PKCS) definition does not meet the specification."
  );

STATIC_ASSERT (
  OFFSET_OF (UE_CERT_PKCS, TbsData) == sizeof (UE_CERT_PKCS),
  "The UE certificate (PKCS) definition does not meet the specification."
  );

///
/// Definition of the UE certificate (minimal RSA) purpose identifiers.
///
enum {
  UeCertMinRsaPurposeExecutable = 0x00U,
  UeCertMinRsaPurposeVariables  = 0x01U,
  UeCertMinRsaPurposeConfig     = 0x02U
};

///
/// Definition of an UE certificate (minimal RSA).
/// The RSA exponent is always 65537.
///
typedef struct {
  ///
  /// The certificate subject identifier GUID.
  ///
  GUID   SubjectId;
  ///
  /// [Bits 28:0]  The time the certificate expires. It is calculated by:
  ///              S + M * 60 + H * 3600 + D * 86400 + m * 2678400 + Y * 32140800, with
  ///                S [0,59]: The number of full seconds into the current minute,
  ///                M [0,59]: The number of full minutes into the current hour,
  ///                H [0,23]: The number of full hours into the current day,
  ///                D [0,30]: The number of full days into the current month,
  ///                m [0,11]: The number of full months into the current year,
  ///                Y [0,16]: The number of full years since 2021.
  /// [Bits 29:31] Reserved for future usage. Must be set to 0.
  ///
  UINT32 ExpiryTime;
  ///
  /// [Bits 1:0] The purpose identifier of the certificate.
  /// [Bits 7:1] Reserved for future usage. Must be set to 0.
  ///
  UINT8  Purpose;
  ///
  /// Reserved for future usage. Must be set to 0.
  ///
  UINT8  Reserved;
  ///
  /// [Bits 11:0]  The size, in 8 Byte units, of the RSA modulus.
  /// [Bits 15:12] Reserved for future usage. Must be set to 0.
  ///
  UINT16 NumQwords;
  ///
  /// The Montgomery Inverse in the 64-bit space: -1 / N[0] mod 2^64.
  ///
  UINT64 N0Inv;
  ///
  /// The RSA parameters. If the number of significant Bits is less than the
  /// number of available Bits, the remaining Bits must be set to 0. Storage
  /// happens in reverse byte order.
  ///
  /// [0 .. 8 * NumQwords)              The RSA key.
  /// [8 * NumQwords .. 16 * NumQwords) Montgomery R^2 mod N.
  ///
  UINT8  Data[];
} UE_CERT_MIN_RSA;

STATIC_ASSERT (
  sizeof (UE_CERT_MIN_RSA) == 32 && ALIGNOF (UE_CERT_MIN_RSA) == 8,
  "The UE certificate (minimal RSA) definition does not meet the specification."
  );

STATIC_ASSERT (
  OFFSET_OF (UE_CERT_MIN_RSA, Data) == sizeof (UE_CERT_MIN_RSA),
  "The UE certificate (minimal RSA) definition does not meet the specification."
  );

STATIC_ASSERT (
  IS_ALIGNED (OFFSET_OF (UE_CERT_MIN_RSA, Data), ALIGNOF (UINT64)),
  "The UE certificate (minimal RSA) definition does not meet the specification."
  );

///
/// Definition of the UE certificate store types.
///
enum {
  UeCertChainTypePkcs = 0x00
};

///
/// The alignment, in Bytes, of each UE certificate chain in the UE certificate
/// store.
///
#define UE_CERT_CHAIN_ALIGNMENT  8U

///
/// Definition of an UE certificate chain.
///
typedef struct {
  ///
  /// The signature algorithm used to sign the data.
  ///
  GUID   Algorithm;
  ///
  /// The UE certificate chain information.
  ///
  /// [Bit 0]      If set, the certificate chain is empty and the data may be
  ///              directly signed by a trusted certificate. In this case,
  ///              instead of a certificate chain structure, the type-specific
  ///              issuer information is stored.
  /// [Bits 2:1]   Reserved for future usage. Must be set to 0.
  /// [Bits 23:3]  The size, in Bytes, of this UE certificate chain, or of the
  ///              type-specific issuer information.
  /// [Bit 24]     The type of the UE certificate store.
  /// [Bits 31:25] Reserved for future usage. Must be set to 0.
  ///
  UINT32 Info;
  ///
  /// The size, in Bytes, of Signature.
  ///
  UINT32 SignatureSize;
  ///
  /// The signature of the signed data, signed by the first certificate of the
  /// chain, with the algorithm identified by SignatureAlgorithm. Its size is
  /// strictly defined by the signature algorithm.
  ///
  UINT8  Signature[];
  ///
  /// The certficate chain. The first certificate signs the data.
  ///
//UE_CERT Chain[];
} UE_CERT_CHAIN;

/**
  Retrieves whether the UE certificate chain is routed, i.e. whether there is
  no chain of certificates but a type-specific issuer identifier for the trusted
  certificate that signs the data.

  @param[in] Info  The UE certificate chain information.
**/
#define UE_CERT_CHAIN_ROOTED(Info)  ((Info) & 0x00000001U)

/**
  Retrieves the size, in Bytes, of the UE certificate chain.

  @param[in] Info  The UE certificate chain information.
**/
#define UE_CERT_CHAIN_SIZE(Info)    ((Info) & 0x00FFFFF8U)

/**
  Retrieves the type of the UE certificate chain.

  @param[in] Info  The UE certificate chain information.
**/
#define UE_CERT_CHAIN_TYPE(Info)    (((Info) & 0x1000000U) >> 24U)

STATIC_ASSERT (
  IS_ALIGNED (UE_CERT_CHAIN_SIZE (0xFFFFFFFF), UE_CERT_CHAIN_ALIGNMENT),
  "The UE certificate chain definition does not meet the specification."
  );

STATIC_ASSERT (
  sizeof (UE_CERT_CHAIN) == 24 && ALIGNOF (UE_CERT_CHAIN) == 4,
  "The UE certificate chain definition does not meet the specification."
  );

STATIC_ASSERT (
  OFFSET_OF (UE_CERT_CHAIN, Signature) == sizeof (UE_CERT_CHAIN),
  "The UE certificate chain definition does not meet the specification."
  );

#endif // UE_CERT_STORE_H_
