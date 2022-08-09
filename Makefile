.PHONY: all clean check

all: check tyde-ext-abstract.pdf

check:
	agda src/Examples.lagda

# TODO: temporary working directory
tyde-ext-abstract.pdf: tyde-ext-abstract.tex correct-optimisations.bib
	pdflatex tyde-ext-abstract
	bibtex tyde-ext-abstract
	pdflatex tyde-ext-abstract
	pdflatex tyde-ext-abstract

clean:
	rm -f src/*.agdai *.agda~
	rm -f *.{aux,bbl,blg,log,out,ptb,toc}
	rm -f tyde-ext-abstract.pdf
