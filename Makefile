SHELL := /bin/bash

PAPER_DIR := paper
BUILD_DIR := $(PAPER_DIR)/build
OUTPUT_PDF := $(PAPER_DIR)/output/rank-role-uncertainty.pdf
LEAN_DIR := lean
SCRIPTS_DIR := scripts

LATEXMK := latexmk
LATEXMK_FLAGS := -pdf -interaction=nonstopmode -halt-on-error -file-line-error -outdir=build

.PHONY: all pdf figures lean test clean

all: figures lean test pdf

pdf:
	@mkdir -p $(BUILD_DIR) $(PAPER_DIR)/output
	cd $(PAPER_DIR) && $(LATEXMK) $(LATEXMK_FLAGS) main.tex
	cp $(BUILD_DIR)/main.pdf $(OUTPUT_PDF)
	@pdfinfo $(OUTPUT_PDF) | grep -E 'Pages|Title|Author' || true

figures:
	@mkdir -p $(PAPER_DIR)/data $(PAPER_DIR)/figures
	python3 $(SCRIPTS_DIR)/run_simulations.py
	python3 $(SCRIPTS_DIR)/generate_figures.py
	@$(MAKE) -s tikz-figures

tikz-figures:
	@for tex in $(PAPER_DIR)/figures/*.tex; do \
		[ -e "$$tex" ] || continue; \
		base=$$(basename "$$tex" .tex); \
		mkdir -p $(BUILD_DIR)/tikz; \
		pdflatex -interaction=nonstopmode -halt-on-error -output-directory=$(BUILD_DIR)/tikz "$$tex" >/dev/null; \
		cp "$(BUILD_DIR)/tikz/$$base.pdf" "$(PAPER_DIR)/figures/$$base.pdf"; \
		pdf2svg "$(PAPER_DIR)/figures/$$base.pdf" "$(PAPER_DIR)/figures/$$base.svg"; \
	done

lean:
	cd $(LEAN_DIR) && lake build

test:
	python3 -m unittest discover -s tests -v

clean:
	rm -rf $(BUILD_DIR)
	find $(SCRIPTS_DIR) -name '__pycache__' -type d -exec rm -rf {} + 2>/dev/null || true
