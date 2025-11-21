
#!/bin/bash

# Script to manually sync content folder from main branch into jupyter-v2 branch

set -e

echo "🔄 Syncing content folder from main branch into jupyter-v2..."

# Get current branch
CURRENT_BRANCH=$(git branch --show-current)
echo "Current branch: $CURRENT_BRANCH"

# Fetch latest changes
echo "📥 Fetching latest changes..."
git fetch origin

# Checkout jupyter-v2 branch and ensure it's up to date
echo "🔀 Checking out jupyter-v2 branch..."
if git show-ref --verify --quiet refs/heads/jupyter-v2; then
    git checkout jupyter-v2
    echo "📥 Pulling latest jupyter-v2 changes..."
    git pull origin jupyter-v2 --no-edit || echo "⚠️  Pull had issues, continuing..."
else
    git checkout -b jupyter-v2 origin/jupyter-v2
fi

# Merge only the content folder from main into jupyter-v2
echo "🔀 Merging content folder from main into jupyter-v2..."
if git checkout origin/main -- content/; then
    echo "✅ Content folder restored from main!"
    
    # Check if there are any changes to commit
    if git diff --staged --quiet; then
        echo "ℹ️  No changes to content folder (already up to date)"
    else
        # Commit only the content folder changes
        git add content/
        git commit -m "Sync content folder from main branch" || {
            echo "⚠️  No changes to commit (content already synced)"
        }
        
        # Ask if user wants to push
        read -p "Push changes to remote? (y/n) " -n 1 -r
        echo
        if [[ $REPLY =~ ^[Yy]$ ]]; then
            echo "📤 Pushing to remote..."
            git push origin jupyter-v2
            echo "✅ Sync complete!"
        else
            echo "ℹ️  Changes committed locally but not pushed. Run 'git push origin jupyter-v2' when ready."
        fi
    fi
else
    echo "❌ Failed to restore content folder from main"
    exit 1
fi

# Optionally return to original branch
if [ "$CURRENT_BRANCH" != "jupyter-v2" ]; then
    read -p "Return to $CURRENT_BRANCH branch? (y/n) " -n 1 -r
    echo
    if [[ $REPLY =~ ^[Yy]$ ]]; then
        git checkout "$CURRENT_BRANCH"
        echo "✅ Returned to $CURRENT_BRANCH"
    fi
fi

