.PHONY: default clean

default: ext-abstract.pdf slides.pdf

ext-abstract.tex : ext-abstract.lagda custom.fmt
	lhs2TeX --agda --poly -o $@ $<

ext-abstract.pdf: ext-abstract.tex ../correct-optimisations.bib
	latexmk -pdf $<

slides.pdf: slides.md include/beamer-template.tex
	pandoc -t beamer slides.md -o slides.pdf --slide-level=2 --pdf-engine=xelatex --template include/beamer-template.tex --table-of-contents

clean:
	rm -f *.{aux,bbl,blg,dvi,fdb_latexmk,fls,log,out,ptb,toc,xcp}
	rm -f ext-abstract.tex
	rm -f ext-abstract.pdf
	rm -f slides.pdf
