# Quick Reference - Build Commands

## 🚀 Building the Paper

### Method 1: Using Make (Recommended)

```bash
# From repository root
make pdf-from-latex
```

This runs 3 LaTeX passes for proper cross-references and bibliography.

### Method 2: Using Script

```bash
# From repository root
./scripts/build-paper.sh
```

### Method 3: Direct LaTeX

```bash
cd paper
pdflatex read-or-x-clean.tex
bibtex read-or-x-clean
pdflatex read-or-x-clean.tex
pdflatex read-or-x-clean.tex
```

## 🏗️ Building Lean

```bash
# From repository root
make lean

# Or directly
cd lean && lake build
```

## 🧹 Cleaning

```bash
# Clean all build artifacts
make clean

# Clean Lean only
cd lean && lake clean

# Clean paper artifacts only
cd paper && rm -f *.aux *.log *.out *.toc *.bbl *.blg
```

## 📊 All Make Targets

```bash
make lean          # Build Lean formalization
make paper         # Build paper (single pass)
make pdf-from-latex # Build PDF with references (3 passes)
make clean         # Remove all build artifacts
make help          # Show help
```

## 📁 Output Locations

- **Lean build**: `.build/` and `lean/.lake/` (gitignored)
- **Paper PDF**: `paper/read-or-x-clean.pdf` (gitignored)
- **Paper logs**: `paper/*.log` (gitignored)

---

**Tip**: Always use `make pdf-from-latex` or `./scripts/build-paper.sh` for the paper - they handle cross-references correctly!
