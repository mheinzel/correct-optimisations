report.pdf: report.tex latex/agda.sty latex/*.tex
	pdflatex report.tex
	pdflatex report.tex

latex/Lang.tex: Lang.lagda
	agda --latex Lang.lagda

.PHONY: clean
clean:
	rm -f *.log *.aux report.pdf
