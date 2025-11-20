#!/bin/bash

# Setup script for CPSC 510 Logical Foundations of Computing

echo "🚀 Setting up CPSC 510 Logical Foundations of Computing..."

# Check if Python 3 is available
if ! command -v python3 &> /dev/null; then
    echo "❌ Python 3 is required but not installed."
    exit 1
fi

# Create virtual environment if it doesn't exist
if [ ! -d ".venv" ]; then
    echo "📦 Creating virtual environment..."
    python3 -m venv .venv
    echo "✅ Virtual environment created"
else
    echo "✅ Virtual environment already exists"
fi

# Activate virtual environment
echo "🔧 Activating virtual environment..."
source .venv/bin/activate

# Upgrade pip
echo "⬆️  Upgrading pip..."
pip install --upgrade pip

# Install Jupyter Book version 2 (latest version 2.x)
echo "📚 Installing Jupyter Book version 2..."
pip install "jupyter-book>=2.0.0,<3.0.0"

# Install other dependencies if requirements.txt exists
if [ -f "requirements.txt" ]; then
    echo "📦 Installing additional dependencies from requirements.txt..."
    pip install -r requirements.txt
fi

# Verify installation
echo "✅ Verifying installation..."
python3 -c "import jupyterbook; print('✅ Jupyter Book installed successfully')" 2>/dev/null || echo "⚠️  Jupyter Book verification failed, but installation may still work"

echo ""
echo "🎉 Setup complete!"
echo ""
echo "Next steps:"
echo "1. Activate the virtual environment: source .venv/bin/activate"
echo "2. Build the book: jupyter-book build ."
echo "3. View locally: open _build/html/index.html"
echo "4. Deploy: ghp-import -n -p -f _build/html"
echo ""
echo "📚 Book URL: https://leap-at-chapman.github.io/CPSC-510-Logical-Foundations-of-Computing/intro.html"
