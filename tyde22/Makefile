.PHONY: default clean

default: ext-abstract.pdf

%.tex : %.lagda custom.fmt
	lhs2TeX --agda --poly -o $@ $<

# TODO: temporary working directory
%.pdf: %.tex ../correct-optimisations.bib
	latexmk -pdf $<

clean:
	rm -f *.{aux,bbl,blg,dvi,fdb_latexmk,fls,log,out,ptb,toc,xcp}
	rm -f ext-abstract.tex
	rm -f ext-abstract.pdf
