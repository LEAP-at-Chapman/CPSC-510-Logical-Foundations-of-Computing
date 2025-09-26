#!/bin/bash

# Setup script for CPSC 510 Logical Foundations of Computing

echo "🚀 Setting up CPSC 510 Logical Foundations of Computing..."

# Check if Python 3 is available
if ! command -v python3 &> /dev/null; then
    echo "❌ Python 3 is required but not installed."
    exit 1
fi

# Check if pip is available
if ! command -v pip &> /dev/null; then
    echo "❌ pip is required but not installed."
    exit 1
fi

# Install dependencies
echo "📦 Installing dependencies..."
pip install -r requirements.txt

# Verify installation
echo "✅ Verifying installation..."
python3 -c "import jupyterbook; print('✅ Jupyter Book installed successfully')" 2>/dev/null || echo "⚠️  Jupyter Book verification failed, but installation may still work"
python3 -c "import z3; print('✅ Z3 solver installed successfully')"

echo ""
echo "🎉 Setup complete!"
echo ""
echo "Next steps:"
echo "1. Build the book: jupyter-book build ."
echo "2. View locally: open _build/html/index.html"
echo "3. Deploy: ghp-import -n -p -f _build/html"
echo ""
echo "📚 Book URL: https://leap-at-chapman.github.io/CPSC-510-Logical-Foundations-of-Computing/intro.html"
