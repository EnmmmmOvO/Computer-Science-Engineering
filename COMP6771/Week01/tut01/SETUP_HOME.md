# Setting up the environment at Home (i.e. not VLAB)

## Notes

* **Do not run this on VLAB. See [SETUP.md][vlab] for this.**
* While we maintain a best-effort approach to helping you set up at home, this is not officially
  supported, and we may be unable to help you in some cirucmstances.

## Philosophy

There is very little benefit for most users of the course to swap out of VLAB, especially given the short duration of the course and often stable internet connections.

However some users may have unstable internet connections that encourage them to complete work locally. While we support local installs on Linux, and generally support it on Windows, some users will only be able to solve this problem by using a Virtual Machine as an alternative to VLab. While this isn't ideal, it's simply too difficult to support such a wide array of operating systems.

**The only platform we officially support is VLAB. We will however, try our best to support your home set-up.**

## Practically "Supported" operating systems

The steps to install at home are known to work on the following distributions. We have workarounds
for folks wanting to use a different home system below.

* Debian 10
* Ubuntu 18.04 or later
* Ubuntu 18.04 or later via [Windows Subsystem for Linux 2][wsl] (requires Windows 10 Update 2004)

Note that using WSL1 will not suffice for our exact toolchain, as it prevents one of the tools we use from working.

### What this means on different systems

* If you are using **Mac OSX**, you will need to download VMWare Player and install Ubuntu 18.04 in the Virtual Machine. Once you boot up the virtual machine, you can follow the instructions below as if you were using Ubuntu
* If you are using **Linux** natively, specifically Debian 10 or Ubuntu 18.04, you can simply open a terminal and follow the instructions below.
* If you are using **Windows**, you can follow the instructions to [enable WSL2 for windows](https://docs.microsoft.com/en-us/windows/wsl/install-win10) and then install *Ubuntu 18.04* from the Microsoft Store. This will allow you to use an Ubuntu 18.04 shell on windows, and you can complete the instructions below.

## Installing the required software

One of the advantages of VLAB is that _everything_ is pre-installed for you, and you only need to
add the things that are local to your repository. Since that security has been removed, we'll need
to manually install a bunch of programs.

## Editor

Please install [Visual Studio Code][1].

## Installing the toolchain

Run the following from the tutorial directory:
```bash
$ sudo bash config/tools/apt-install.sh root
$ bash config/tools/install-vscode.sh
```

**Note: you may sometimes be required to update these packages. This is done using:**

```
apt update && apt upgrade -y
```

## Next steps

From here on, you can follow the steps in [SETUP.md][vlab], as if it were your own computer. The only difference will be that once you select your toolkit you need to select `COMP6771 (Home Setup)` instead of the VLAB option.

## Alternate routes

### I don't use/can't get one of the supported operating systems

That's fine! Many operating systems now support [Docker][4], and there's also a supported Docker
image. You can find the supported Docker script in [config/ci/Dockerfile][5]. While you could
install Ubuntu using a virtual machine, the Docker approach is far more lightweight, and will
yield the same system for everyone (so if you encounter a problem, it can be more-easily reproduced
and fixed).

### I want to use a different editor

Sure! Modern C++ tooling tends to integrate well with many editors; particularly the tooling that
we'll be using. Your tooling should support:

* `clangd` integration
* CMake integration
* LLDB integration
* WSL integration (if running on Windows)

### I want to use WSL1

This is possible, but you'll need to use GDB instead of LLDB. LLDB is better suited to C++ than GDB,
which is why we use it, but GDB is a reasonable backup. Your experience won't be as pleasant as the
LLDB experience, so it's worth reconsidering WSL2.

### I'm using WSL and things aren't working like they were on VLAB

That probably means you haven't activated all the extensions in WSL mode. To fix that, open the
Extensions window (`Ctrl + Shift + X`) and [config/tools/vscode-extensions.ps1][4]. Enable the
extensions in that file for WSL (there's a button that will say "Install on WSL").

### My editor didn't change to the Material theme like it did on VLAB

That's okay. We decided not to override your preferred theme. If you'd like to re-enable it, press
`Ctrl+K Ctrl+T`, type "Material Theme", and press Enter. You may also like to play around with the
other themes and see which ones you like!

[vlab]: SETUP.md
[wsl]: https://docs.microsoft.com/en-us/windows/wsl/install-win10
[1]: https://code.visualstudio.com/
[3]: config/tools/install-vscode.sh
[4]: config/tools/vscode-extensions.ps1
[5]: config/tools/ci/Dockerfile
[6]: config/ci/Dockerfile
[7]: config/tools/install-vcpkg-linux.sh

