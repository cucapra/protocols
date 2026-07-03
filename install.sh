#!/usr/bin/env bash

# Set exit code to non-zero if any command / any command in a pipeline fails 
set -euo pipefail

OS="$(uname -s)"

# Install package manager 
# Homebrew if MacOS, or apt-get if on Linux (e.g. Gorgonzola/Havarti)
if [[ "$OS" == "Darwin" ]]; then
    if ! command -v brew &>/dev/null; then
        echo "Installing Homebrew..."
        /bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"
        if [[ -f /opt/homebrew/bin/brew ]]; then
            eval "$(/opt/homebrew/bin/brew shellenv)"
        fi
    else
        echo "Homebrew already installed: $(brew --version | head -1)"
    fi
elif [[ "$OS" == "Linux" ]]; then
    if ! command -v apt-get &>/dev/null; then
        echo "ERROR: apt-get not found" >&2
        exit 1
    fi
    echo "Updating apt package lists..."
    sudo apt-get update -q
else
    echo "ERROR: Unsupported OS $OS" >&2
    exit 1
fi

# Install Rust via Rustup
if ! command -v cargo &>/dev/null; then
    echo "Installing Rust via rustup..."
    curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
    # shellcheck source=/dev/null
    source "$HOME/.cargo/env"
else
    echo "Cargo already installed: $(cargo --version)"
fi

# Check that Rust version matches current version requirement in cargo.toml (1.88)
REQUIRED_RUST="1.88"
CURRENT_RUST=$(rustc --version | awk '{print $2}')
if [[ "$(printf '%s\n' "$REQUIRED_RUST" "$CURRENT_RUST" | sort -V | head -1)" != "$REQUIRED_RUST" ]]; then
    echo "Rust $CURRENT_RUST is older than required version $REQUIRED_RUST, updating..."
    rustup update stable
fi

# Install uv (for Python dependencies / virtual environments)
if ! command -v uv &>/dev/null; then
    echo "Installing uv..."
    if [[ "$OS" == "Darwin" ]]; then
        brew install uv
    else
        curl -LsSf https://astral.sh/uv/install.sh | sh
        export PATH="$HOME/.local/bin:$PATH"
    fi
else
    echo "uv already installed: $(uv --version)"
fi

# Install just (for running Justfiles)
if ! command -v just &>/dev/null; then
    echo "Installing just..."
    if [[ "$OS" == "Darwin" ]]; then
        brew install just
    else
        cargo install just
    fi
else
    echo "just already installed: $(just --version)"
fi

# Install Yosys (for interpreter)
if ! command -v yosys &>/dev/null; then
    echo "Installing yosys..."
    if [[ "$OS" == "Darwin" ]]; then
        brew install yosys
    else
        sudo apt-get install -y yosys
    fi
else
    echo "yosys already installed: $(yosys --version 2>&1 | head -1)"
fi

# Install Nikil's fork of Runt
if ! command -v runt &>/dev/null; then
    echo "Installing our fork of runt..."
    cargo install --git https://github.com/Nikil-Shyamsunder/runt.git
else
    echo "runt already installed: $(runt --version 2>&1 | head -1)"
fi

echo "Syncing Python dependencies..."
uv sync

echo -e "\nAll dependencies installed. Run 'just test' to check tests pass."
