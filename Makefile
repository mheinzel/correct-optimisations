.PHONY: default clean check

default: tyde-ext-abstract.pdf

# Should import everything important
check: check-Examples

check-%: src/%.agda
	agda $<

%.tex : %.lagda %.fmt
	lhs2TeX --agda --poly -o $@ $<

# TODO: temporary working directory
%.pdf: %.tex correct-optimisations.bib
	latexmk -pdf $<

clean:
	rm -f src/*.agdai *.agda~
	rm -f *.{aux,bbl,blg,dvi,fdb_latexmk,fls,log,out,ptb,toc,xcp}
	rm -f tyde-ext-abstract.tex
	rm -f tyde-ext-abstract.pdf
