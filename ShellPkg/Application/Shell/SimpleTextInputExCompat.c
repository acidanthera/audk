/** @file
  SimpleTextInputEx Protocol Compatibility Implementation for Shell
  
  Provides EFI 1.1 compatibility by implementing SimpleTextInputEx protocol
  as a wrapper around the standard SimpleTextInput protocol.
  
  Copyright (c) 2025, Enhanced Shell Compatibility Layer
   All rights reserved.
  
  SPDX-License-Identifier: BSD-2-Clause-Patent
**/

#include "Shell.h"

// Global variables for compatibility protocol
STATIC EFI_SIMPLE_TEXT_INPUT_EX_PROTOCOL  *mOriginalSimpleTextInputEx = NULL;
STATIC EFI_SIMPLE_TEXT_INPUT_EX_PROTOCOL   mCompatSimpleTextInputEx;

/**
  Compatibility implementation of ReadKeyStrokeEx that falls back to ReadKeyStroke.
  
  @param  This                 Protocol instance pointer.
  @param  KeyData              A pointer to a buffer that is filled in with the keystroke 
                               state data for the key that was pressed.
  
  @retval EFI_SUCCESS          The keystroke information was returned.
  @retval EFI_NOT_READY        There was no keystroke data available.
  @retval EFI_DEVICE_ERROR     The keystroke information was not returned due to 
                               hardware errors.
**/
STATIC
EFI_STATUS
EFIAPI
CompatReadKeyStrokeEx (
  IN  EFI_SIMPLE_TEXT_INPUT_EX_PROTOCOL  *This,
  OUT EFI_KEY_DATA                       *KeyData
  )
{
  EFI_STATUS  Status;
  
  if (KeyData == NULL) {
    return EFI_INVALID_PARAMETER;
  }
  
  // Clear the KeyData structure
  ZeroMem (KeyData, sizeof (EFI_KEY_DATA));
  
  // Try to read from the standard SimpleTextInput protocol
  Status = gST->ConIn->ReadKeyStroke (gST->ConIn, &KeyData->Key);
  
  if (!EFI_ERROR (Status)) {
    // Set default shift state (no modifiers detected on EFI 1.1)
    KeyData->KeyState.KeyShiftState  = 0;
    KeyData->KeyState.KeyToggleState = 0;
    
    DEBUG ((DEBUG_INFO, "Shell SimpleTextInputEx Compat: Key processed - Unicode=0x%04x, Scan=0x%04x, ShiftState=0x%08x\n",
            KeyData->Key.UnicodeChar, KeyData->Key.ScanCode, KeyData->KeyState.KeyShiftState));
  }
  
  return Status;
}

/**
  Compatibility implementation of SetState (does nothing on EFI 1.1).
  
  @param  This                 Protocol instance pointer.
  @param  KeyToggleState       A pointer to the EFI_KEY_TOGGLE_STATE to set the 
                               state for the input device.
                               
  @retval EFI_SUCCESS          The device state was set successfully.
  @retval EFI_UNSUPPORTED      The device does not support the ability to have its state set.
**/
STATIC
EFI_STATUS
EFIAPI
CompatSetState (
  IN EFI_SIMPLE_TEXT_INPUT_EX_PROTOCOL  *This,
  IN EFI_KEY_TOGGLE_STATE               *KeyToggleState
  )
{
  DEBUG ((DEBUG_INFO, "Shell SimpleTextInputEx Compat: SetState called (silently succeeding on EFI 1.1)\n"));
  
  // Always return success to prevent calling applications from failing
  // EFI 1.1 systems don't support toggle state, but we pretend we do
  // to maintain compatibility with applications that expect this to work
  return EFI_SUCCESS;
}

/**
  Compatibility implementation of RegisterKeyNotify (does nothing on EFI 1.1).
  
  @param  This                 Protocol instance pointer.
  @param  KeyData              A pointer to a buffer that defines the keystroke 
                               information for the notification function.
  @param  KeyNotificationFunction Points to the function to be called when the key 
                               sequence is typed in the specified input device.
  @param  NotifyHandle         Points to the unique handle assigned to the registered notification.                        
                               
  @retval EFI_SUCCESS          The notification function was registered successfully.
  @retval EFI_OUT_OF_RESOURCES Failed to allocate memory for the dummy handle.
**/
STATIC
EFI_STATUS
EFIAPI
CompatRegisterKeyNotify (
  IN EFI_SIMPLE_TEXT_INPUT_EX_PROTOCOL  *This,
  IN EFI_KEY_DATA                       *KeyData,
  IN EFI_KEY_NOTIFY_FUNCTION            KeyNotificationFunction,
  OUT VOID                              **NotifyHandle
  )
{
  // Not supported on EFI 1.1 systems, but return success with unique handle
  // to avoid breaking applications that expect this to work
  if (NotifyHandle != NULL) {
    // Allocate a unique dummy handle (1 byte is sufficient)
    *NotifyHandle = AllocateZeroPool (1);
    if (*NotifyHandle == NULL) {
      DEBUG ((DEBUG_ERROR, "Shell SimpleTextInputEx Compat: Failed to allocate dummy notify handle\n"));
      return EFI_OUT_OF_RESOURCES;
    }
  }

  DEBUG ((DEBUG_INFO, "Shell SimpleTextInputEx Compat: RegisterKeyNotify returning success with unique dummy handle (EFI 1.1 limitation)\n"));
  return EFI_SUCCESS;
}

/**
  Compatibility implementation of UnregisterKeyNotify (does nothing on EFI 1.1).
  
  @param  This                 Protocol instance pointer.
  @param  NotificationHandle   The handle of the notification function being unregistered.
  
  @retval EFI_SUCCESS          The notification function was unregistered successfully.
  @retval EFI_INVALID_PARAMETER The NotificationHandle is not valid.
**/
STATIC
EFI_STATUS
EFIAPI
CompatUnregisterKeyNotify (
  IN EFI_SIMPLE_TEXT_INPUT_EX_PROTOCOL  *This,
  IN VOID                               *NotificationHandle
  )
{
  // Not supported on EFI 1.1 systems, but validate and free the handle to avoid misuse
  if (NotificationHandle == NULL) {
    DEBUG ((DEBUG_WARN, "Shell SimpleTextInputEx Compat: NULL NotificationHandle passed to UnregisterKeyNotify\n"));
    return EFI_INVALID_PARAMETER;
  }

  // Free the dummy handle that was allocated in RegisterKeyNotify
  FreePool (NotificationHandle);
  DEBUG ((DEBUG_INFO, "Shell SimpleTextInputEx Compat: Freed dummy handle and returning success (EFI 1.1 limitation)\n"));
  return EFI_SUCCESS;
}

/**
  Reset implementation wrapper for SimpleTextInputEx compatibility.
  
  @param  This                     Protocol instance pointer.
  @param  ExtendedVerification     Indicates that the driver may perform a more
                                   exhaustive verification operation of the device
                                   during reset.
  
  @retval EFI_SUCCESS              The device was reset.
  @retval EFI_DEVICE_ERROR         The device is not functioning properly and could
                                   not be reset.
**/
STATIC
EFI_STATUS
EFIAPI
CompatReset (
  IN EFI_SIMPLE_TEXT_INPUT_EX_PROTOCOL  *This,
  IN BOOLEAN                            ExtendedVerification
  )
{
  return gST->ConIn->Reset (gST->ConIn, ExtendedVerification);
}

/**
  Install SimpleTextInputEx compatibility protocol on the console input handle.
  This function checks if SimpleTextInputEx is already available, and if not,
  installs a compatibility version that wraps SimpleTextInput.
  
  @retval EFI_SUCCESS          Protocol installed successfully or already present
  @retval Others               Installation failed
**/
EFI_STATUS
InstallSimpleTextInputExCompat (
  VOID
  )
{
  EFI_STATUS                         Status;
  EFI_SIMPLE_TEXT_INPUT_EX_PROTOCOL  *NativeSimpleTextInputEx = NULL;
  
  // Check if SimpleTextInputEx is already available
  Status = gBS->HandleProtocol (
                  gST->ConsoleInHandle,
                  &gEfiSimpleTextInputExProtocolGuid,
                  (VOID **)&NativeSimpleTextInputEx
                  );
                  
  if (!EFI_ERROR (Status)) {
    // Protocol already exists, no need for compatibility
    mOriginalSimpleTextInputEx = NativeSimpleTextInputEx;
    DEBUG ((DEBUG_INFO, "Shell SimpleTextInputEx: Native protocol found, compatibility not needed\n"));
    return EFI_SUCCESS;
  }
  
  DEBUG ((DEBUG_INFO, "Shell SimpleTextInputEx: Native protocol not found, installing compatibility layer\n"));
  
  // Initialize the compatibility protocol structure
  mCompatSimpleTextInputEx.Reset               = CompatReset;
  mCompatSimpleTextInputEx.ReadKeyStrokeEx     = CompatReadKeyStrokeEx;
  mCompatSimpleTextInputEx.WaitForKeyEx        = gST->ConIn->WaitForKey; // Reuse the same event
  mCompatSimpleTextInputEx.SetState            = CompatSetState;
  mCompatSimpleTextInputEx.RegisterKeyNotify   = CompatRegisterKeyNotify;
  mCompatSimpleTextInputEx.UnregisterKeyNotify = CompatUnregisterKeyNotify;
  
  // Install the compatibility protocol on the console input handle
  Status = gBS->InstallProtocolInterface (
                  &gST->ConsoleInHandle,
                  &gEfiSimpleTextInputExProtocolGuid,
                  EFI_NATIVE_INTERFACE,
                  &mCompatSimpleTextInputEx
                  );
                  
  if (EFI_ERROR (Status)) {
    DEBUG ((DEBUG_ERROR, "Shell SimpleTextInputEx Compat: Failed to install protocol - %r\n", Status));
    return Status;
  }
  
  DEBUG ((DEBUG_INFO, "Shell SimpleTextInputEx Compat: Successfully installed compatibility protocol\n"));
  return EFI_SUCCESS;
}

/**
  Uninstall SimpleTextInputEx compatibility protocol.
  This should be called during shell cleanup.
  
  @retval EFI_SUCCESS          Protocol uninstalled successfully
  @retval Others               Uninstallation failed
**/
EFI_STATUS
UninstallSimpleTextInputExCompat (
  VOID
  )
{
  EFI_STATUS  Status;
  
  // Only uninstall if we installed the compatibility version
  if (mOriginalSimpleTextInputEx != NULL) {
    // Native protocol was present, nothing to uninstall
    return EFI_SUCCESS;
  }
  
  Status = gBS->UninstallProtocolInterface (
                  gST->ConsoleInHandle,
                  &gEfiSimpleTextInputExProtocolGuid,
                  &mCompatSimpleTextInputEx
                  );
                  
  if (EFI_ERROR (Status)) {
    DEBUG ((DEBUG_WARN, "Shell SimpleTextInputEx Compat: Failed to uninstall protocol - %r\n", Status));
  } else {
    DEBUG ((DEBUG_INFO, "Shell SimpleTextInputEx Compat: Successfully uninstalled compatibility protocol\n"));
  }
  
  return Status;
}
