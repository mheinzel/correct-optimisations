.PHONY: default clean

all: slides.pdf slides-extended.pdf

%.pdf: %.md include/beamer-template.tex
	pandoc -t beamer $< -o $@ --slide-level=2 --pdf-engine=xelatex --template include/beamer-template.tex --table-of-contents

clean:
	rm -f *.{aux,bbl,blg,dvi,fdb_latexmk,fls,log,out,ptb,toc,xcp}
	rm -f slides.pdf slides-extended.pdf
