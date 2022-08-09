.PHONY: all clean check

all: check tyde-ext-abstract.pdf

check:
	agda src/Examples.lagda

# TODO: temporary working directory
tyde-ext-abstract.pdf: tyde-ext-abstract.tex correct-optimisations.bib
	latexmk -pdf tyde-ext-abstract.tex

clean:
	rm -f src/*.agdai *.agda~
	rm -f *.{aux,bbl,blg,dvi,fdb_latexmk,fls,log,out,ptb,toc,xcp}
	rm -f tyde-ext-abstract.pdf
