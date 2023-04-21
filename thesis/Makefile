.PHONY: default clean

SRC_TEX := \
	preamble.tex\
	title.tex\
	chapters/introduction.tex\
	chapters/program-transformations.tex\
	chapters/binding-representation.tex\
	chapters/de-bruijn.tex\
	chapters/co-de-bruijn.tex\
	chapters/generic-co-de-bruijn.tex

default: thesis.pdf

chapters/de-bruijn.tex : chapters/de-bruijn.lagda custom.fmt
	lhs2TeX --agda --poly -o $@ $<

chapters/co-de-bruijn.tex : chapters/co-de-bruijn.lagda custom.fmt
	lhs2TeX --agda --poly -o $@ $<

chapters/generic-co-de-bruijn.tex : chapters/generic-co-de-bruijn.lagda custom.fmt
	lhs2TeX --agda --poly -o $@ $<

thesis.tex : thesis.lagda custom.fmt
	lhs2TeX --agda --poly -o $@ $<

thesis.pdf: thesis.tex ${SRC_TEX} ../correct-optimisations.bib
	latexmk -pdf $<

clean:
	rm -f chapters/*.aux
	rm -f chapters/{de-bruijn,co-de-bruijn,generic-co-de-bruijn}.tex
	rm -f *.{aux,bbl,blg,dvi,fdb_latexmk,fls,log,out,ptb,toc,xcp}
	rm -f thesis.pdf
