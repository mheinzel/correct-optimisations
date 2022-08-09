.PHONY: all clean check icfp-tyde-abstract

all: check icfp-tyde-abstract.pdf

check:
	agda src/Examples.lagda

# TODO: temporary working directory
icfp-tyde-abstract.pdf: icfp-tyde-abstract.tex correct-optimisations.bib
	pdflatex icfp-tyde-abstract
	bibtex icfp-tyde-abstract
	pdflatex icfp-tyde-abstract
	pdflatex icfp-tyde-abstract

clean:
	rm -f src/*.agdai *.agda~
	rm -f *.{aux,bbl,blg,log,out,ptb,toc}
	rm -f icfp-tyde-abstract.pdf
