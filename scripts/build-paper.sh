#!/bin/bash
# Build paper from LaTeX with proper cross-references

set -e

cd "$(dirname "$0")/.."

echo "📄 Building PDF from LaTeX"
echo "=========================="
echo ""

if [ ! -f "paper/read-or-x-clean.tex" ]; then
    echo "❌ Error: paper/read-or-x-clean.tex not found"
    exit 1
fi

cd paper

echo "Pass 1/3: Initial compilation..."
pdflatex -interaction=nonstopmode read-or-x-clean.tex > /dev/null 2>&1 || true

echo "Pass 2/3: Bibliography..."
bibtex read-or-x-clean > /dev/null 2>&1 || true

echo "Pass 3/3: Cross-references..."
pdflatex -interaction=nonstopmode read-or-x-clean.tex > /dev/null 2>&1 || true
pdflatex -interaction=nonstopmode read-or-x-clean.tex > /dev/null 2>&1 || true

echo ""
if [ -f "read-or-x-clean.pdf" ]; then
    echo "✅ PDF built successfully!"
    echo "   Location: paper/read-or-x-clean.pdf"
    echo "   Size: $(ls -lh read-or-x-clean.pdf | awk '{print $5}')"

    # Count pages if pdfinfo available
    if command -v pdfinfo &> /dev/null; then
        PAGES=$(pdfinfo read-or-x-clean.pdf 2>/dev/null | grep Pages | awk '{print $2}')
        echo "   Pages: $PAGES"
    fi
else
    echo "❌ Error: PDF was not generated"
    echo "   Check paper/read-or-x-clean.log for errors"
    exit 1
fi
