.PHONY: default clean

default: thesis.pdf

thesis.tex : thesis.lagda custom.fmt
	lhs2TeX --agda --poly -o $@ $<

thesis.pdf: thesis.tex ../correct-optimisations.bib
	latexmk -pdf $<

clean:
	rm -f *.{aux,bbl,blg,dvi,fdb_latexmk,fls,log,out,ptb,toc,xcp}
	rm -f thesis.tex
	rm -f thesis.pdf
