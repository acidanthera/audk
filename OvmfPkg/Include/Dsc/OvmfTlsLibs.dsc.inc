##
#    SPDX-License-Identifier: BSD-2-Clause-Patent
##

[LibraryClasses]
  IntrinsicLib|MdePkg/Library/IntrinsicLib/IntrinsicLib.inf
!if $(NETWORK_TLS_ENABLE) == TRUE
!if $(FD_SIZE_IN_KB) < 4096
  OpensslLib|CryptoPkg/Library/OpensslLib/OpensslLib.inf
!else
  OpensslLib|CryptoPkg/Library/OpensslLib/OpensslLibFull.inf
!endif
  TlsLib|CryptoPkg/Library/TlsLib/TlsLib.inf
!else
  OpensslLib|CryptoPkg/Library/OpensslLib/OpensslLibCrypto.inf
!endif
