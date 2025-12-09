.PHONY: all lean paper pdf-from-latex md-to-pdf clean help

all: lean

lean:
	@echo "Building Lean formalization..."
	@cd lean && lake build

paper:
	@echo "Building paper (single pass)..."
	@cd paper && pdflatex -interaction=nonstopmode read-or-x-clean.tex

pdf-from-latex:
	@echo "📄 Building PDF from LaTeX (3 passes for references)..."
	@cd paper && pdflatex -interaction=nonstopmode read-or-x-clean.tex > /dev/null 2>&1 || true
	@echo "   Pass 1/3 complete"
	@cd paper && bibtex read-or-x-clean > /dev/null 2>&1 || true
	@echo "   Bibliography processed"
	@cd paper && pdflatex -interaction=nonstopmode read-or-x-clean.tex > /dev/null 2>&1 || true
	@echo "   Pass 2/3 complete"
	@cd paper && pdflatex -interaction=nonstopmode read-or-x-clean.tex > /dev/null 2>&1 || true
	@echo "   Pass 3/3 complete"
	@echo ""
	@if [ -f paper/read-or-x-clean.pdf ]; then \
		echo "✅ PDF generated: paper/read-or-x-clean.pdf"; \
		ls -lh paper/read-or-x-clean.pdf; \
	else \
		echo "❌ PDF generation failed - check paper/read-or-x-clean.log"; \
	fi

md-to-pdf:
	@echo "📄 Full pipeline: Markdown → LaTeX → PDF"
	@./scripts/md-to-pdf.sh

clean:
	@echo "Cleaning build artifacts..."
	@rm -rf .build/
	@cd lean && lake clean
	@rm -f paper/*.aux paper/*.log paper/*.out paper/*.toc paper/*.bbl paper/*.blg
	@echo "✓ Clean complete"

help:
	@echo "Available targets:"
	@echo "  make lean          - Build Lean formalization"
	@echo "  make paper         - Build paper (single pass)"
	@echo "  make pdf-from-latex - Build PDF from existing LaTeX (3 passes)"
	@echo "  make md-to-pdf     - Full pipeline: Markdown → LaTeX → PDF"
	@echo "  make clean         - Remove build artifacts"
	@echo "  make help          - Show this help"
	@echo ""
	@echo "Recommended workflow:"
	@echo "  1. Edit: paper/read-or-x.md"
	@echo "  2. Build: make md-to-pdf"
