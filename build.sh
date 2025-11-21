#!/bin/bash

# Build script that restores content folder from main branch before building

set -e

echo "🔨 Building Jupyter Book..."

# Get current branch
CURRENT_BRANCH=$(git branch --show-current)
echo "Current branch: $CURRENT_BRANCH"

# Fetch latest changes
echo "📥 Fetching latest changes..."
git fetch origin main

# Checkout content folder from main branch
echo "📂 Restoring content folder from main branch..."
if [ -d "content" ]; then
    # If content exists but is ignored, remove it first
    if git check-ignore -q content/ 2>/dev/null; then
        echo "⚠️  Content folder exists and is ignored. Removing..."
        rm -rf content
    else
        echo "⚠️  Content folder exists. Backing up..."
        if [ -d "content.backup" ]; then
            rm -rf content.backup
        fi
        mv content content.backup
    fi
fi

# Restore content from main (force checkout even if in .gitignore)
git checkout origin/main -- content/ 2>/dev/null || {
    # If checkout fails (e.g., content is in .gitignore), force it
    echo "⚠️  Standard checkout failed, forcing restore..."
    git show origin/main:content/ > /dev/null 2>&1 || {
        echo "❌ Error: content folder not found in main branch"
        exit 1
    }
    # Use git archive to extract content folder
    git archive origin/main content/ | tar -x
}

# Build the book
echo "📚 Building Jupyter Book..."
jupyter-book build .

# Optionally clean up the content folder after build
# Uncomment the next lines if you want to remove content after building
# echo "🧹 Cleaning up content folder..."
# rm -rf content/
# if [ -d "content.backup" ]; then
#     mv content.backup content
# fi

echo "✅ Build complete!"
echo "📖 Open the book: open _build/html/index.html"

