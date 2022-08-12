#!/bin/bash

if `grep -qEi "Microsoft|WSL" /proc/version`; then
	echo "$0: Detected Windows Subsystem for Linux. Please run ./install-extensions.ps1 in a PowerShell terminal instead of this script."
	exit 1
fi

function install_vscode {
	if `which code`; then
		return 0
	fi

	if `grep -qEi 'Ubuntu|Debian' /etc/issue`; then
		curl https://packages.microsoft.com/keys/microsoft.asc | gpg --dearmor > packages.microsoft.gpg
		sudo install -o root -g root -m 644 packages.microsoft.gpg /usr/share/keyrings/
		sudo sh -c 'echo "deb [arch=amd64 signed-by=/usr/share/keyrings/packages.microsoft.gpg] https://packages.microsoft.com/repos/vscode stable main" > /etc/apt/sources.list.d/vscode.list'
		sudo apt-get install -y apt-transport-https
		sudo apt-get update
		sudo apt-get install -y code
		rm ./packages.microsoft.gpg
	elif `grep -qEi '(Red Hat)|Fedora|CentOS|SUSE' /etc/issue`; then
		sudo rpm --import https://packages.microsoft.com/keys/microsoft.asc
		sudo sh -c 'echo -e "[code]\nname=Visual Studio Code\nbaseurl=https://packages.microsoft.com/yumrepos/vscode\nenabled=1\ngpgcheck=1\ngpgkey=https://packages.microsoft.com/keys/microsoft.asc" > /etc/yum.repos.d/vscode.repo'
		if `grep -qEi 'SUSE' /etc/issue`; then
			sudo zypper refresh
			sudo zypper install code
		else
			sudo dnf check-update
			sudo dnf install code
		fi
	elif `grep -qEi 'Arch' /etc/issue`; then
		echo "$0: Visual Studio Code is installed on Arch Linux via the Arch User Repository (AUR), which this script doesn't yet support."
		echo "$0: You can find the tarball at https://aur.archlinux.org/packages/visual-studio-code-bin."
		echo "$0: For more information, please see https://wiki.archlinux.org/index.php/Arch_User_Repository#Build_and_install_the_package."
		echo "$0: Once you've manually installed VS Code, re-run this script to install the extensions."
	fi
}

install_vscode                                                    && \
code --install-extension eamodio.gitlens                          && \
code --install-extension Equinusocio.vsc-material-theme           && \
code --install-extension equinusocio.vsc-material-theme-icons     && \
code --install-extension helgardrichard.helium-icon-theme         && \
code --install-extension j-zeppenfeld.tab-indent-space-align      && \
code --install-extension llvm-vs-code-extensions.vscode-clangd    && \
code --install-extension ms-vscode.cmake-tools                    && \
code --install-extension twxs.cmake                               && \
code --install-extension vadimcn.vscode-lldb                      &&
code --install-extension webfreak.debug
