.PHONY: default clean

default: thesis-proposal.pdf

thesis-proposal.tex : thesis-proposal.lagda custom.fmt
	lhs2TeX --agda --poly -o $@ $<

thesis-proposal.pdf: thesis-proposal.tex ../correct-optimisations.bib
	latexmk -pdf $<

clean:
	rm -f *.{aux,bbl,blg,dvi,fdb_latexmk,fls,log,out,ptb,toc,xcp}
	rm -f thesis-proposal.tex
	rm -f thesis-proposal.pdf
