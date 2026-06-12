# Build the arXiv preprint. Prefers latexmk, falls back to pdflatex+bibtex,
# and finally to tectonic (which runs its own bibtex pass automatically).
MAIN := main

LATEXMK  := $(shell command -v latexmk 2>/dev/null)
PDFLATEX := $(shell command -v pdflatex 2>/dev/null)
TECTONIC := $(shell command -v tectonic 2>/dev/null)

.PHONY: all clean distclean

all: $(MAIN).pdf

$(MAIN).pdf: $(MAIN).tex references.bib
ifdef LATEXMK
	latexmk -pdf -interaction=nonstopmode $(MAIN).tex
else ifdef PDFLATEX
	pdflatex -interaction=nonstopmode $(MAIN).tex
	bibtex $(MAIN)
	pdflatex -interaction=nonstopmode $(MAIN).tex
	pdflatex -interaction=nonstopmode $(MAIN).tex
else ifdef TECTONIC
	tectonic $(MAIN).tex
else
	$(error No TeX engine found: install latexmk, pdflatex, or tectonic)
endif

clean:
	rm -f $(MAIN).aux $(MAIN).bbl $(MAIN).blg $(MAIN).log $(MAIN).out \
	      $(MAIN).toc $(MAIN).fls $(MAIN).fdb_latexmk $(MAIN).synctex.gz

distclean: clean
	rm -f $(MAIN).pdf
