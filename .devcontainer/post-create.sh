#!/bin/bash

# Exit on error
set -e

echo "Starting Lean installation script..."

# Install Lean using the official elan installer
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- --default-toolchain none -y

# Add elan to the PATH for this and future terminal sessions
echo 'export PATH="$HOME/.elan/bin:$PATH"' >> ~/.bashrc
export PATH="$HOME/.elan/bin:$PATH"

echo "Elan installed. Setting default toolchain..."

# Set the default Lean toolchain (as specified in your lean-toolchain file)
elan toolchain install $(cat /workspaces/hyperlocal/lean-toolchain)
elan default $(cat /workspaces/hyperlocal/lean-toolchain)

echo "Toolchain set. Getting mathlib cache..."

# Navigate to the workspace and get the mathlib cache
cd /workspaces/hyperlocal
lake exe cache get

echo "Lean setup complete!"
