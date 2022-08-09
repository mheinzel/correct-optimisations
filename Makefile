.PHONY: all clean icfp-tyde-abstract

all: icfp-tyde-abstract

icfp-tyde-abstract: latex/icfp-tyde-abstract.pdf

latex/icfp-tyde-abstract.pdf: latex/icfp-tyde-abstract.tex latex/bibliography.bib
	cd latex; pdflatex icfp-tyde-abstract
	cd latex; bibtex icfp-tyde-abstract
	cd latex; pdflatex icfp-tyde-abstract
	cd latex; pdflatex icfp-tyde-abstract

clean:
	rm -f *.agdai *.agda~
	rm -f latex/*.{aux,bbl,blg,log,out,ptb,toc}
	rm -f latex/icfp-tyde-abstract.pdf
