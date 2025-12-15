#!/bin/bash

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

MODEL_NAME="qwen30:4b"

# echo "Setting up autoformalization environment..."

# if [ ! -d "venv" ]; then
#     echo "Creating virtual environment..."
#     python3 -m venv .venv
# fi

# echo "Activating virtual environment..."
# source .venv/bin/activate

# echo "Installing dependencies..."
# pip install --quiet --upgrade pip
# pip install --quiet -r requirements.txt

echo ""
echo "Checking Ollama installation..."
if ! command -v ollama &> /dev/null; then
    echo "Error: Ollama not found"
    echo "Install with: brew install ollama"
    exit 1
fi

echo ""
echo "=" | tr '=' '\n' | head -80 | tr '\n' '='
echo ""
echo "Setup complete. Starting autoformalization tool..."
echo "=" | tr '=' '\n' | head -80 | tr '\n' '='
echo ""

python autoformalize_ollama.py

if [ -n "$OLLAMA_PID" ]; then
    echo "Stopping Ollama server..."
    kill $OLLAMA_PID 2>/dev/null || true
fi

deactivate
