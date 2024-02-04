.PHONY: default clean

default: correct-optimisations.pdf

correct-optimisations.tex : correct-optimisations.lagda custom.fmt
	lhs2TeX --agda --poly -o $@ $<

correct-optimisations.pdf: correct-optimisations.tex ../correct-optimisations.bib
	latexmk -pdf $<

clean:
	rm -f *.{aux,bbl,blg,dvi,fdb_latexmk,fls,log,out,ptb,toc,xcp}
	rm -f correct-optimisations.tex
	rm -f correct-optimisations.pdf
