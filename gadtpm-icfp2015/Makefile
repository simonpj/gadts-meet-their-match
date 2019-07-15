# .SUFFIXES: .tex .pdf
# .PHONY: all clean distclean FORCE

export TEXINPUTS := .:./Styles//:${TEXINPUTS}
export BSTINPUTS := .:./Styles//:${BSTINPUTS}
export SHELL := /bin/bash

all: main extended

main:
	lhs2TeX --verb gadtpm.lhs >gadtpm.tex
	pdflatex gadtpm
	bibtex   gadtpm
	pdflatex gadtpm
	pdflatex gadtpm

extended:
	lhs2TeX --verb gadtpm_ext.lhs >gadtpm_ext.tex
	pdflatex gadtpm_ext
	bibtex   gadtpm_ext
	pdflatex gadtpm_ext
	pdflatex gadtpm_ext

clean:
	$(RM) *.dvi *.aux *.log *.bbl *.blg *.toc *.out *.fls *.haux *.fdb_latexmk *~

distclean: clean
	$(RM) gadtpm.tex
	$(RM) gadtpm.pdf
	$(RM) gadtpm_ext.tex
	$(RM) gadtpm_ext.pdf


