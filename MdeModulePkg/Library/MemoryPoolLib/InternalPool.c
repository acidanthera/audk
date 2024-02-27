/** @file
  DXE Core functions necessary for pool management functions.

  Copyright (c) 2024, Mikhail Krichanov. All rights reserved.
  SPDX-License-Identifier: BSD-3-Clause

**/

#include <Library/UefiBootServicesTableLib.h>
#include <Library/UefiLib.h>

/**
  Initialize a basic mutual exclusion lock.   Each lock
  provides mutual exclusion access at it's task priority
  level.  Since there is no-premption (at any TPL) or
  multiprocessor support, acquiring the lock only consists
  of raising to the locks TPL.

  @param  Lock               The EFI_LOCK structure to initialize

  @retval EFI_SUCCESS        Lock Owned.
  @retval EFI_ACCESS_DENIED  Reentrant Lock Acquisition, Lock not Owned.

**/
EFI_STATUS
CoreAcquireLockOrFail (
  IN EFI_LOCK  *Lock
  )
{
  return EfiAcquireLockOrFail (Lock);
}

/**
  Raising to the task priority level of the mutual exclusion
  lock, and then acquires ownership of the lock.

  @param  Lock               The lock to acquire

  @return Lock owned

**/
VOID
CoreAcquireLock (
  IN EFI_LOCK  *Lock
  )
{
  EfiAcquireLock (Lock);
}

/**
  Releases ownership of the mutual exclusion lock, and
  restores the previous task priority level.

  @param  Lock               The lock to release

  @return Lock unowned

**/
VOID
CoreReleaseLock (
  IN EFI_LOCK  *Lock
  )
{
  EfiReleaseLock (Lock);
}
