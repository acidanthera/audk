/** @file
  BaseCrypto SM3 hash instance library.
  It can be registered to BaseCrypto router, to serve as hash engine.

  Copyright (c) 2013 - 2019, Intel Corporation. All rights reserved.<BR>
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
  The function set SM3 to digest list.

  @param DigestList   digest list
  @param Sm3Digest    SM3 digest
**/
VOID
Tpm2SetSm3ToDigestList (
  IN TPML_DIGEST_VALUES  *DigestList,
  IN UINT8               *Sm3Digest
  )
{
  DigestList->count              = 1;
  DigestList->digests[0].hashAlg = TPM_ALG_SM3_256;
  CopyMem (
    DigestList->digests[0].digest.sm3_256,
    Sm3Digest,
    SM3_256_DIGEST_SIZE
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
Sm3HashInit (
  OUT VOID           **HashHandle
  )
{
  VOID   *Sm3Ctx;
  UINTN  CtxSize;

  CtxSize = Sm3GetContextSize ();
  Sm3Ctx  = AllocatePool (CtxSize);
  if (Sm3Ctx == NULL) {
    return FALSE;
  }

  Sm3Init (Sm3Ctx);

  *HashHandle = Sm3Ctx;

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
Sm3HashUpdate (
  IN VOID           *HashHandle,
  IN CONST VOID     *DataToHash,
  IN UINTN        DataToHashLen
  )
{
  Sm3Update (HashHandle, DataToHash, DataToHashLen);

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
Sm3HashFinal (
  IN VOID                *HashHandle,
  OUT TPML_DIGEST_VALUES  *DigestList
  )
{
  UINT8  Digest[SM3_256_DIGEST_SIZE];

  Sm3Final (HashHandle, Digest);

  FreePool (HashHandle);

  Tpm2SetSm3ToDigestList (DigestList, Digest);

  return TRUE;
}

HASH_INTERFACE  mSm3InternalHashInstance = {
  HASH_ALGORITHM_SM3_256_GUID,
  Sm3HashInit,
  Sm3HashUpdate,
  Sm3HashFinal,
};

/**
  The function register SM3 instance.

  @retval EFI_SUCCESS   SM3 instance is registered, or system dose not support register SM3 instance
**/
EFI_STATUS
EFIAPI
HashInstanceLibSm3Constructor (
  VOID
  )
{
  EFI_STATUS  Status;

  Status = RegisterHashInterfaceLib (&mSm3InternalHashInstance);
  if ((Status == EFI_SUCCESS) || (Status == EFI_UNSUPPORTED)) {
    //
    // Unsupported means platform policy does not need this instance enabled.
    //
    return EFI_SUCCESS;
  }

  return Status;
}
