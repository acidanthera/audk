/** @file
  This library is BaseCrypto SHA256 hash instance.
  It can be registered to BaseCrypto router, to serve as hash engine.

Copyright (c) 2013 - 2018, Intel Corporation. All rights reserved. <BR>
SPDX-License-Identifier: BSD-2-Clause-Patent

**/

#include <PiPei.h>
#include <Library/BaseLib.h>
#include <Library/BaseMemoryLib.h>
#include <Library/Tpm2CommandLib.h>
#include <Library/DebugLib.h>
#include <Library/BaseCryptLib.h>
#include <Library/MemoryAllocationLib.h>
#include <Library/HashLib.h>

/**
  The function set SHA256 to digest list.

  @param DigestList   digest list
  @param Sha256Digest SHA256 digest
**/
VOID
Tpm2SetSha256ToDigestList (
  IN TPML_DIGEST_VALUES  *DigestList,
  IN UINT8               *Sha256Digest
  )
{
  DigestList->count              = 1;
  DigestList->digests[0].hashAlg = TPM_ALG_SHA256;
  CopyMem (
    DigestList->digests[0].digest.sha256,
    Sha256Digest,
    SHA256_DIGEST_SIZE
    );
}

/**
  Start hash sequence.

  @param HashHandle Hash handle.

  @retval EFI_SUCCESS          Hash sequence start and HandleHandle returned.
  @retval EFI_OUT_OF_RESOURCES No enough resource to start hash.
**/
BOOLEAN
EFIAPI
Sha256HashInit (
  OUT VOID           **HashHandle
  )
{
  VOID   *Sha256Ctx;
  UINTN  CtxSize;

  CtxSize   = Sha256GetContextSize ();
  Sha256Ctx = AllocatePool (CtxSize);
  ASSERT (Sha256Ctx != NULL);

  Sha256Init (Sha256Ctx);

  *HashHandle = Sha256Ctx;

  return TRUE;
}

/**
  Update hash sequence data.

  @param HashHandle    Hash handle.
  @param DataToHash    Data to be hashed.
  @param DataToHashLen Data size.

  @retval EFI_SUCCESS     Hash sequence updated.
**/
BOOLEAN
EFIAPI
Sha256HashUpdate (
  IN VOID           *HashHandle,
  IN CONST VOID     *DataToHash,
  IN UINTN        DataToHashLen
  )
{
  Sha256Update (HashHandle, DataToHash, DataToHashLen);

  return TRUE;
}

/**
  Complete hash sequence complete.

  @param HashHandle    Hash handle.
  @param DigestList    Digest list.

  @retval EFI_SUCCESS     Hash sequence complete and DigestList is returned.
**/
BOOLEAN
EFIAPI
Sha256HashFinal (
  IN VOID                *HashHandle,
  OUT TPML_DIGEST_VALUES  *DigestList
  )
{
  UINT8  Digest[SHA256_DIGEST_SIZE];

  Sha256Final (HashHandle, Digest);

  FreePool (HashHandle);

  Tpm2SetSha256ToDigestList (DigestList, Digest);

  return TRUE;
}

HASH_INTERFACE  mSha256InternalHashInstance = {
  HASH_ALGORITHM_SHA256_GUID,
  Sha256HashInit,
  Sha256HashUpdate,
  Sha256HashFinal,
};

/**
  The function register SHA256 instance.

  @retval EFI_SUCCESS   SHA256 instance is registered, or system does not support register SHA256 instance
**/
EFI_STATUS
EFIAPI
HashInstanceLibSha256Constructor (
  VOID
  )
{
  EFI_STATUS  Status;

  Status = RegisterHashInterfaceLib (&mSha256InternalHashInstance);
  if ((Status == EFI_SUCCESS) || (Status == EFI_UNSUPPORTED)) {
    //
    // Unsupported means platform policy does not need this instance enabled.
    //
    return EFI_SUCCESS;
  }

  return Status;
}
