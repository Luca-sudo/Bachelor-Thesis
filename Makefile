SOURCES = $(wildcard chapters/*.tex misc/*.tex)
IMAGES = $(wildcard images/*)

thesis.pdf: thesis.tex literature/literature.bib $(SOURCES) $(IMAGES)
	latexmk -pdf -file-line-error -halt-on-error -interaction=nonstopmode -shell-escape $<

clean:
	latexmk -C

.PHONY: clean
