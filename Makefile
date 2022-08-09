AGDA = agda

GEN_DIR = latex/generated
GEN_TEX_FILES = $(GEN_DIR)/Recursion.tex $(GEN_DIR)/Lang.tex $(GEN_DIR)/Subset.tex $(GEN_DIR)/Live.tex $(GEN_DIR)/Examples.tex

.PHONY: all clean project-report icfp-tyde-abstract

all: project-report icfp-tyde-abstract

project-report: latex/project-report.pdf
icfp-tyde-abstract: latex/icfp-tyde-abstract.pdf

latex/project-report.pdf: latex/project-report.tex latex/agda.sty latex/bibliography.bib $(GEN_TEX_FILES)
	cd latex; pdflatex project-report
	cd latex; bibtex project-report
	cd latex; pdflatex project-report
	cd latex; pdflatex project-report

latex/icfp-tyde-abstract.pdf: latex/icfp-tyde-abstract.tex latex/bibliography.bib
	cd latex; pdflatex icfp-tyde-abstract
	cd latex; bibtex icfp-tyde-abstract
	cd latex; pdflatex icfp-tyde-abstract
	cd latex; pdflatex icfp-tyde-abstract

$(GEN_DIR)/Lang.tex: Lang.lagda
	$(AGDA) --latex-dir=$(GEN_DIR) --latex Lang.lagda

$(GEN_DIR)/Subset.tex: Subset.lagda Lang.lagda
	$(AGDA) --latex-dir=$(GEN_DIR) --latex Subset.lagda

$(GEN_DIR)/Recursion.tex: Recursion.lagda Lang.lagda Subset.lagda
	$(AGDA) --latex-dir=$(GEN_DIR) --latex Recursion.lagda

$(GEN_DIR)/Live.tex: Live.lagda Lang.lagda Subset.lagda Recursion.lagda
	$(AGDA) --latex-dir=$(GEN_DIR) --latex Live.lagda

$(GEN_DIR)/Examples.tex: Examples.lagda Live.lagda Lang.lagda Subset.lagda Recursion.lagda
	$(AGDA) --latex-dir=$(GEN_DIR) --latex Examples.lagda

clean:
	rm -f *.agdai *.agda~
	rm -f latex/*.{aux,bbl,blg,log,out,ptb,toc}
	rm -f latex{project-report,icfp-tyde-abstract}.pdf
	rm -f $(GEN_DIR)/*
