# Current states of packages

| Name | Architectures | Targets | Compilable | Tested |
| :--- | :-----------: | :-----: | :--------: | :----: |
| $${\color{lightblue}ArmPkg/}$$ |
| ArmPkg.dsc | ARM AARCH64 | DEBUG RELEASE NOOPT | GCC5 CLANGDWARF | ❌ |
| Drivers/ArmCrashDumpDxe/ArmCrashDumpDxe.dsc | AARCH64 | DEBUG | ❓ | ❌ |
| $${\color{lightblue}ArmPlatformPkg/}$$ |
| ArmPlatformPkg.dsc | ARM AARCH64 | DEBUG RELEASE NOOPT | GCC5 CLANGDWARF | ❌ |
| $${\color{lightblue}ArmVirtPkg/}$$ |
| ArmVirtCloudHv.dsc | ARM AARCH64 | DEBUG RELEASE NOOPT | ❓ | ❌ |
| ArmVirtKvmTool.dsc | ARM AARCH64 | DEBUG RELEASE | ❓ | ❌ |
| ArmVirtQemu.dsc | ARM AARCH64 | DEBUG RELEASE NOOPT | GCC5 CLANGDWARF | ✔ |
| ArmVirtQemuKernel.dsc | ARM AARCH64 | DEBUG RELEASE NOOPT | ❓ | ❌ |
| ArmVirtXen.dsc | ARM AARCH64 | DEBUG RELEASE NOOPT | ❓ | ❌ |
| $${\color{lightblue}CryptoPkg/}$$ |
| CryptoPkg.dsc | IA32 X64 ARM AARCH64 RISCV64 LOONGARCH64 | DEBUG RELEASE NOOPT | ❓ | ❌ |
| Test/CryptoPkgHostUnitTest.dsc | IA32 X64 | NOOPT | ❓ | ❌ |
| $${\color{lightblue}DynamicTablesPkg/}$$ |
| DynamicTablesPkg.dsc | ARM AARCH64 | DEBUG RELEASE NOOPT | ❓ | ❌ |
| $${\color{lightblue}EmbeddedPkg/}$$ |
| EmbeddedPkg.dsc | IA32 X64 ARM AARCH64 | DEBUG RELEASE NOOPT | ❓ | ❌ |
| $${\color{lightblue}EmulatorPkg/}$$ |
| EmulatorPkg.dsc | IA32 X64 | DEBUG RELEASE NOOPT | ❓ | ❌ |
| $${\color{lightblue}Ext4Pkg/}$$ |
| Ext4Pkg.dsc | IA32 X64 EBC ARM AARCH64 RISCV64 | DEBUG RELEASE NOOPT | GCC5 CLANGDWARF CLANGPDB VS2019 XCODE5 | ❌ |
| $${\color{lightblue}FatPkg/}$$ |
| FatPkg.dsc | IA32 X64 EBC ARM AARCH64 RISCV64 LOONGARCH64 | DEBUG RELEASE NOOPT | GCC5 CLANGDWARF CLANGPDB VS2019 XCODE5 | ❌ |
| $${\color{lightblue}FmpDevicePkg/}$$ |
| FmpDevicePkg.dsc | IA32 X64 ARM AARCH64 RISCV64 LOONGARCH64 | DEBUG RELEASE NOOPT | ❓ | ❌ |
| Test/FmpDeviceHostPkgTest.dsc | IA32 X64 | NOOPT | ❓ | ❌ |
| $${\color{lightblue}IntelFsp2Pkg/}$$ |
| IntelFsp2Pkg.dsc | IA32 X64 | DEBUG RELEASE NOOPT | GCC5 CLANGDWARF CLANGPDB VS2019 XCODE5 | ❌ |
| Tools/Tests/QemuFspPkg.dsc | IA32 X64 | DEBUG RELEASE | ❓ | ❌ |
| $${\color{lightblue}IntelFsp2WrapperPkg/}$$ |
| IntelFsp2WrapperPkg.dsc | IA32 X64 | DEBUG RELEASE NOOPT | GCC5 CLANGDWARF CLANGPDB VS2019 XCODE5 | ❌ |
| $${\color{lightblue}MdeModulePkg/}$$ |
| MdeModulePkg.dsc | IA32 X64 EBC ARM AARCH64 RISCV64 LOONGARCH64 | DEBUG RELEASE NOOPT | GCC5 CLANGDWARF CLANGPDB VS2019 XCODE5 | ❌ |
| Test/MdeModulePkgHostTest.dsc | IA32 X64 | NOOPT | ❓ | ❌ |
| $${\color{lightblue}MdePkg/}$$ |
| MdePkg.dsc | IA32 X64 EBC ARM AARCH64 RISCV64 LOONGARCH64 | DEBUG RELEASE NOOPT | GCC5 CLANGDWARF CLANGPDB VS2019 XCODE5 | ❌ |
| Test/MdePkgHostTest.dsc | IA32 X64 | NOOPT | ❓ | ❌ |
| $${\color{lightblue}NetworkPkg/}$$ |
| NetworkPkg.dsc | IA32 X64 EBC ARM AARCH64 RISCV64 LOONGARCH64 | DEBUG RELEASE NOOPT | GCC5 CLANGDWARF CLANGPDB VS2019 XCODE5 | ❌ |
| $${\color{lightblue}OvmfPkg/}$$ |
| OvmfPkgIa32.dsc | IA32 | DEBUG RELEASE NOOPT | GCC5 CLANGDWARF CLANGPDB VS2019 XCODE5 | ✔ |
| OvmfPkgIa32X64.dsc | IA32 X64 | DEBUG RELEASE NOOPT | GCC5 CLANGDWARF CLANGPDB VS2019 XCODE5 | ✔ |
| OvmfPkgX64.dsc | X64 | DEBUG RELEASE NOOPT | GCC5 CLANGDWARF CLANGPDB VS2019 XCODE5 | ✔ |
| OvmfXen.dsc | X64 | DEBUG RELEASE NOOPT | ❓ | ❌ |
| AmdSev/AmdSevX64.dsc | X64 | DEBUG RELEASE NOOPT | ❓ | ❌ |
| Bhyve/BhyveX64.dsc | X64 | DEBUG RELEASE NOOPT | ❓ | ❌ |
| CloudHv/CloudHvX64.dsc | X64 | DEBUG RELEASE NOOPT | ❓ | ❌ |
| IntelTdx/IntelTdxX64.dsc | X64 | DEBUG RELEASE NOOPT | ❓ | ❌ |
| Microvm/MicrovmX64.dsc | X64 | DEBUG RELEASE NOOPT | ❓ | ❌ |
| RiscVVirt/RiscVVirtQemu.dsc | RISCV64 | DEBUG RELEASE NOOPT | ❓ | ❌ |
| $${\color{lightblue}PcAtChipsetPkg/}$$ |
| PcAtChipsetPkg.dsc | IA32 X64 | DEBUG RELEASE NOOPT | ❓ | ❌ |
| $${\color{lightblue}PrmPkg/}$$ |
| PrmPkg.dsc | IA32 X64 AARCH64 | DEBUG RELEASE NOOPT | ❓ | ❌ |
| Test/PrmPkgHostTest.dsc | IA32 X64 | NOOPT | ❓ | ❌ |
| $${\color{lightblue}RedfishPkg/}$$ |
| RedfishPkg.dsc | IA32 X64 ARM AARCH64 RISCV64 | DEBUG RELEASE NOOPT | ❓ | ❌ |
| $${\color{lightblue}SecurityPkg/}$$ |
| SecurityPkg.dsc | IA32 X64 EBC ARM AARCH64 RISCV64 LOONGARCH64 | DEBUG RELEASE NOOPT | GCC CLANGDWARF CLANGPDB VS2019 XCODE5 | ❌ |
| Test/SecurityPkgHostTest.dsc | IA32 X64 | NOOPT | ❓ | ❌ |
| $${\color{lightblue}ShellPkg/}$$ |
| ShellPkg.dsc | IA32 X64 EBC ARM AARCH64 RISCV64 LOONGARCH64 | DEBUG RELEASE NOOPT | ❓ | ❌ |
| $${\color{lightblue}SignedCapsulePkg/}$$ |
| SignedCapsulePkg.dsc | IA32 X64 ARM AARCH64 | DEBUG RELEASE NOOPT | ❓ | ❌ |
| $${\color{lightblue}SourceLevelDebugPkg/}$$ |
| SourceLevelDebugPkg.dsc | IA32 X64 | DEBUG RELEASE NOOPT | ❓ | ❌ |
| $${\color{lightblue}StandaloneMmPkg/}$$ |
| StandaloneMmPkg.dsc | X64 ARM AARCH64 | DEBUG RELEASE | ❓ | ❌ |
| $${\color{lightblue}UefiCpuPkg/}$$ |
| UefiCpuPkg.dsc | IA32 X64 | DEBUG RELEASE NOOPT | GCC5 CLANGDWARF CLANGPDB VS2019 XCODE5 | ❌ |
| Test/UefiCpuPkgHostTest.dsc | IA32 X64 | NOOPT | ❓ | ❌ |
| $${\color{lightblue}UefiPayloadPkg/}$$ |
| UefiPayloadPkg.dsc | IA32 X64 | DEBUG RELEASE NOOPT | GCC5 CLANGDWARF CLANGPDB VS2019 XCODE5 | ❌ |
| $${\color{lightblue}UnitTestFrameworkPkg/}$$ |
| UnitTestFrameworkPkg.dsc | IA32 X64 ARM AARCH64 RISCV64 LOONGARCH64 | DEBUG RELEASE NOOPT | GCC5 CLANGDWARF CLANGPDB VS2019 XCODE5 | ❌ |
| Test/UnitTestFrameworkPkgHostTest.dsc | IA32 X64 | NOOPT | ❓ | ❌ |
