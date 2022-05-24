#include <Base.h>

#include <IndustryStandard/UeCertStore.h>

#include <Library/DebugLib.h>

#include "../Library/BasePeCoffLib2/BaseOverflow.h"

typedef struct {
  CONST UE_CERT_CHAIN *CertStore;
  UINT32              CertStoreSize;
} UE_CS_CONTEXT;

RETURN_STATUS
UeCsInitializeContext (
  OUT UE_CS_CONTEXT  *Context,
  IN  CONST VOID     *Buffer,
  IN  UINT32         BufferSize
  )
{
  ASSERT (Context != NULL);
  ASSERT (Buffer != NULL || BufferSize == 0);

  if (sizeof (UE_CERT_CHAIN) > BufferSize) {
    DEBUG_RAISE ();
    return RETURN_UNSUPPORTED;
  }

  Context->CertStore     = Buffer;
  Context->CertStoreSize = BufferSize;
  return RETURN_SUCCESS;
}

RETURN_STATUS
UeGetFirstCertChain (
  IN OUT UE_CS_CONTEXT  *Context,
  IN OUT UE_CERT_CHAIN  **CertChain
  )
{
  ASSERT (Context != NULL);
  ASSERT (CertChain != NULL);
}

RETURN_STATUS
UeGetNextCertChain (
  IN OUT UE_CS_CONTEXT  *Context,
  IN OUT UE_CERT_CHAIN  **CertChain
  )
{
  ASSERT (Context != NULL);
  ASSERT (CertChain != NULL);
}

STATIC
RETURN_STATUS
InternalValidatePkcsCertChain (
  IN OUT UE_CS_CONTEXT  *Context,
  IN OUT UE_CERT_CHAIN  *CertChain,
  IN     UINT32         RemainingSize
  )
{
  BOOLEAN            Overflow;
  CONST UE_CERT_PKCS *Certs;
  UINT32             CertChainPayloadSize;
  UINT32             CertChainChainSize;
  UINT32             CertSize;

  ASSERT (Context != NULL);
  ASSERT (CertChain != NULL);
  ASSERT (UE_CERT_CHAIN_TYPE (CertChain->Info) == UeCertChainTypePkcs);

  Overflow = BaseOverflowSubU32 (
               RemainingSize,
               sizeof (UE_CERT_CHAIN),
               &RemainingSize
               );
  if (Overflow) {
    DEBUG_RAISE ();
    return RETURN_UNSUPPORTED;
  }

  CertChainChainSize = UE_CERT_CHAIN_SIZE (CertChain->Info);

  Overflow = BaseOverflowAddU32 (
               CertChain->SignatureSize,
               CertChainChainSize,
               &CertChainPayloadSize
               );
  if (Overflow) {
    DEBUG_RAISE ();
    return RETURN_UNSUPPORTED;
  }

  if (CertChainPayloadSize > RemainingSize) {
    DEBUG_RAISE ();
    return RETURN_UNSUPPORTED;
  }

  Certs = CertChain->Signature + CertChain->SignatureSize;
}

RETURN_STATUS
UeValidateCertChain (
  IN OUT UE_CS_CONTEXT  *Context,
  IN OUT UE_CERT_CHAIN  *CertChain
  )
{
  ASSERT (Context != NULL);
  ASSERT (CertChain != NULL);
}
