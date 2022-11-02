/** @file
  This library is BaseCrypto SHA384 hash instance.
  It can be registered to BaseCrypto router, to serve as hash engine.

Copyright (c) 2018, Intel Corporation. All rights reserved. <BR>
SPDX-License-Identifier: BSD-2-Clause-Patent

**/

#include <PiPei.h>

#include <Library/BaseLib.h>
#include <Library/BaseMemoryLib.h>
#include <Library/DebugLib.h>
#include <Library/BaseCryptLib.h>
#include <Library/MemoryAllocationLib.h>
#include <Library/HashLib.h>

/**
  The function set SHA384 to digest list.

  @param DigestList   digest list
  @param Sha384Digest SHA384 digest
**/
VOID
Tpm2SetSha384ToDigestList (
  IN TPML_DIGEST_VALUES  *DigestList,
  IN UINT8               *Sha384Digest
  )
{
  DigestList->count              = 1;
  DigestList->digests[0].hashAlg = TPM_ALG_SHA384;
  CopyMem (
    DigestList->digests[0].digest.sha384,
    Sha384Digest,
    SHA384_DIGEST_SIZE
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
Sha384HashInit (
  OUT VOID           **HashHandle
  )
{
  VOID   *Sha384Ctx;
  UINTN  CtxSize;

  CtxSize   = Sha384GetContextSize ();
  Sha384Ctx = AllocatePool (CtxSize);
  ASSERT (Sha384Ctx != NULL);

  Sha384Init (Sha384Ctx);

  *HashHandle = Sha384Ctx;

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
Sha384HashUpdate (
  IN VOID           *HashHandle,
  IN CONST VOID     *DataToHash,
  IN UINTN        DataToHashLen
  )
{
  Sha384Update (HashHandle, DataToHash, DataToHashLen);

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
Sha384HashFinal (
  IN VOID                *HashHandle,
  OUT TPML_DIGEST_VALUES  *DigestList
  )
{
  UINT8  Digest[SHA384_DIGEST_SIZE];

  Sha384Final (HashHandle, Digest);

  FreePool (HashHandle);

  Tpm2SetSha384ToDigestList (DigestList, Digest);

  return TRUE;
}

HASH_INTERFACE  mSha384InternalHashInstance = {
  HASH_ALGORITHM_SHA384_GUID,
  Sha384HashInit,
  Sha384HashUpdate,
  Sha384HashFinal,
};

/**
  The function register SHA384 instance.

  @retval EFI_SUCCESS   SHA384 instance is registered, or system does not support register SHA384 instance
**/
EFI_STATUS
EFIAPI
HashInstanceLibSha384Constructor (
  VOID
  )
{
  EFI_STATUS  Status;

  Status = RegisterHashInterfaceLib (&mSha384InternalHashInstance);
  if ((Status == EFI_SUCCESS) || (Status == EFI_UNSUPPORTED)) {
    //
    // Unsupported means platform policy does not need this instance enabled.
    //
    return EFI_SUCCESS;
  }

  return Status;
}
