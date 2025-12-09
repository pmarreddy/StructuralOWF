# Build Workflow

## 📋 Full Pipeline: Markdown → LaTeX → PDF

### Quick Start

```bash
# Edit markdown
vim paper/read-or-x.md

# Build everything (md → tex → pdf)
make md-to-pdf
```

### What Happens

```
paper/read-or-x.md
    ↓ (Pandoc + unicode-to-math.lua filter)
paper/read-or-x-clean.tex
    ↓ (pdflatex × 3 + bibtex)
paper/read-or-x-clean.pdf ✅
```

---

## 🛠️ Build Commands

### Full Pipeline (Recommended)
```bash
make md-to-pdf
```
- Converts markdown → LaTeX (with Unicode symbols)
- Compiles LaTeX → PDF (3 passes)
- Handles bibliography

### Just PDF (if .tex already exists)
```bash
make pdf-from-latex
```
- Compiles existing LaTeX → PDF
- Skips markdown conversion

### Quick Single Pass
```bash
make paper
```
- Fast compilation (no cross-references)

---

## 📁 File Locations

### Source (edit these)
- `paper/read-or-x.md` - Markdown source (editable)
- `paper/read-or-x-clean.tex` - Generated LaTeX (auto-generated)

### Tools
- `paper/tools/unicode-to-math.lua` - Pandoc filter for Unicode

### Output (generated)
- `paper/read-or-x-clean.pdf` - Final PDF (gitignored)

---

## 🔧 Scripts

### Using Make
```bash
make md-to-pdf      # Full pipeline
make pdf-from-latex # LaTeX → PDF only
make clean          # Clean artifacts
```

### Using Scripts Directly
```bash
./scripts/md-to-pdf.sh      # Full pipeline
./scripts/build-paper.sh    # LaTeX → PDF only
```

---

## ⚙️ Requirements

### For Full Pipeline (md-to-pdf)
- pandoc (install: `brew install pandoc`)
- pdflatex (install: `brew install --cask mactex`)
- bibtex (included with LaTeX)

### For LaTeX Only (pdf-from-latex)
- pdflatex
- bibtex

---

## 💡 Workflow Tips

### Normal Workflow
1. Edit `paper/read-or-x.md`
2. Run `make md-to-pdf`
3. View `paper/read-or-x-clean.pdf`

### Quick Edits to LaTeX
1. Edit `paper/read-or-x-clean.tex` directly
2. Run `make pdf-from-latex`
3. View `paper/read-or-x-clean.pdf`

**Note**: If you edit `.tex` directly, changes will be **overwritten** next time you run `make md-to-pdf`!

---

## 🎯 Summary

| Command | Input | Output | Use When |
|---------|-------|--------|----------|
| `make md-to-pdf` | `.md` | `.pdf` | Updated markdown |
| `make pdf-from-latex` | `.tex` | `.pdf` | LaTeX already exists |
| `make paper` | `.tex` | `.pdf` | Quick preview |
| `make clean` | - | - | Clean build artifacts |
