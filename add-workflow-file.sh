#!/bin/bash

# Helper script to add the workflow file to GitHub
# This is needed because Personal Access Tokens require 'workflow' scope to push workflow files

REPO_URL="https://github.com/LEAP-at-Chapman/CPSC-510-Logical-Foundations-of-Computing"
BRANCH="jupyter-v2"
FILE_PATH=".github/workflows/sync-main-to-jupyter-v2.yml"

echo "📋 Instructions to add the workflow file:"
echo ""
echo "The workflow file cannot be pushed via git because your Personal Access Token"
echo "needs the 'workflow' scope. Here are your options:"
echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""
echo "OPTION 1: Add via GitHub Web Interface (Easiest)"
echo ""
echo "1. Open this URL in your browser:"
echo "   ${REPO_URL}/new/${BRANCH}?filename=${FILE_PATH}"
echo ""
echo "2. Copy and paste the contents of:"
echo "   .github/workflows/sync-main-to-jupyter-v2.yml"
echo ""
echo "3. Click 'Commit new file'"
echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""
echo "OPTION 2: Update Your Personal Access Token"
echo ""
echo "1. Go to: https://github.com/settings/tokens"
echo "2. Edit your token"
echo "3. Check the 'workflow' scope"
echo "4. Update your git credentials"
echo "5. Then run: git add .github/workflows/sync-main-to-jupyter-v2.yml"
echo "6. Then run: git commit -m 'Add auto-sync workflow'"
echo "7. Then run: git push origin jupyter-v2"
echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

# Try to open the URL if on macOS
if [[ "$OSTYPE" == "darwin"* ]]; then
    read -p "Open the GitHub web interface now? (y/n) " -n 1 -r
    echo
    if [[ $REPLY =~ ^[Yy]$ ]]; then
        open "${REPO_URL}/new/${BRANCH}?filename=${FILE_PATH}"
        echo ""
        echo "✅ Opened in browser. The file contents are below for easy copy-paste:"
        echo ""
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
        echo ""
        cat .github/workflows/sync-main-to-jupyter-v2.yml
        echo ""
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
    fi
fi

