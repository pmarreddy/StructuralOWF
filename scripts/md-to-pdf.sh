#!/bin/bash
# Complete pipeline: markdown → LaTeX → PDF

set -e

cd "$(dirname "$0")/.."

echo "📄 Full Pipeline: Markdown → LaTeX → PDF"
echo "========================================="
echo ""

# Check for pandoc
if ! command -v pandoc &> /dev/null; then
    echo "❌ Error: pandoc not found"
    echo "Install with: brew install pandoc"
    exit 1
fi

# Check source file
if [ ! -f "paper/read-or-x.md" ]; then
    echo "❌ Error: paper/read-or-x.md not found"
    exit 1
fi

# Step 1: Markdown → LaTeX (with Unicode filter)
echo "Step 1/2: Converting Markdown → LaTeX..."
cd paper

pandoc read-or-x.md \
    -f gfm \
    --lua-filter=../scripts/tools/unicode-to-math.lua \
    -o read-or-x-clean.tex \
    --standalone \
    -V geometry:margin=1in \
    -V fontsize=10pt \
    -V colorlinks=true

echo "  ✓ LaTeX generated: read-or-x-clean.tex"

# Step 1.5: Fix Unicode characters that Pandoc missed
echo "  ✓ Fixing Unicode characters..."
../scripts/tools/fix-unicode-in-tex.sh read-or-x-clean.tex > /dev/null

# Step 2: LaTeX → PDF (3 passes)
echo ""
echo "Step 2/2: Compiling LaTeX → PDF..."

pdflatex -interaction=nonstopmode read-or-x-clean.tex > /dev/null 2>&1 || true
echo "  ✓ Pass 1/3"

bibtex read-or-x-clean > /dev/null 2>&1 || true
echo "  ✓ Bibliography"

pdflatex -interaction=nonstopmode read-or-x-clean.tex > /dev/null 2>&1 || true
echo "  ✓ Pass 2/3"

pdflatex -interaction=nonstopmode read-or-x-clean.tex > /dev/null 2>&1 || true
echo "  ✓ Pass 3/3"

# Summary
echo ""
echo "========================================="
if [ -f "read-or-x-clean.pdf" ]; then
    echo "✅ Complete pipeline successful!"
    echo ""
    echo "Output:"
    echo "  LaTeX: paper/read-or-x-clean.tex"
    echo "  PDF:   paper/read-or-x-clean.pdf"
    echo ""
    ls -lh read-or-x-clean.pdf

    if command -v pdfinfo &> /dev/null; then
        PAGES=$(pdfinfo read-or-x-clean.pdf 2>/dev/null | grep Pages | awk '{print $2}')
        echo "  Pages: $PAGES"
    fi
else
    echo "❌ PDF generation failed"
    echo "Check paper/read-or-x-clean.log for errors"
    exit 1
fi
