report.pdf: report.tex latex/Recursion.tex latex/Lang.tex latex/Subset.tex latex/Live.tex
	pdflatex report.tex
	pdflatex report.tex

latex/Lang.tex: Lang.lagda
	agda --latex Lang.lagda

latex/Subset.tex: Subset.lagda Lang.lagda
	agda --latex Subset.lagda

latex/Recursion.tex: Recursion.lagda Lang.lagda Subset.lagda
	agda --latex Recursion.lagda

latex/Live.tex: Live.lagda Lang.lagda Subset.lagda Recursion.lagda
	agda --latex Live.lagda

.PHONY: clean
clean:
	rm -f *.log *.aux latex/*.tex latex/agda.sty report.pdf
