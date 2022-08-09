.PHONY: default clean check

default: tyde-ext-abstract.pdf

# Should import everything important
check: check-Examples

check-%: src/%.agda
	agda $<

# TODO: temporary working directory
tyde-ext-abstract.pdf: tyde-ext-abstract.tex correct-optimisations.bib
	latexmk -pdf tyde-ext-abstract.tex

clean:
	rm -f src/*.agdai *.agda~
	rm -f *.{aux,bbl,blg,dvi,fdb_latexmk,fls,log,out,ptb,toc,xcp}
	rm -f tyde-ext-abstract.pdf
