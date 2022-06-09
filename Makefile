AGDA = agda

GEN_DIR = latex/generated
GEN_TEX_FILES = $(GEN_DIR)/Recursion.tex $(GEN_DIR)/Lang.tex $(GEN_DIR)/Subset.tex $(GEN_DIR)/Live.tex

.PHONY: all clean project-report icfp-tyde-abstract icfp-src-abstract

all: project-report icfp-tyde-abstract icfp-src-abstract

project-report: latex/project-report.pdf
icfp-tyde-abstract: latex/icfp-tyde-abstract.pdf
icfp-src-abstract: latex/icfp-src-abstract.pdf

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

latex/icfp-src-abstract.pdf: latex/icfp-src-abstract.tex latex/bibliography.bib
	cd latex; pdflatex icfp-src-abstract
	cd latex; bibtex icfp-src-abstract
	cd latex; pdflatex icfp-src-abstract
	cd latex; pdflatex icfp-src-abstract

$(GEN_DIR)/Lang.tex: Lang.lagda
	$(AGDA) --latex-dir=$(GEN_DIR) --latex Lang.lagda

$(GEN_DIR)/Subset.tex: Subset.lagda Lang.lagda
	$(AGDA) --latex-dir=$(GEN_DIR) --latex Subset.lagda

$(GEN_DIR)/Recursion.tex: Recursion.lagda Lang.lagda Subset.lagda
	$(AGDA) --latex-dir=$(GEN_DIR) --latex Recursion.lagda

$(GEN_DIR)/Live.tex: Live.lagda Lang.lagda Subset.lagda Recursion.lagda
	$(AGDA) --latex-dir=$(GEN_DIR) --latex Live.lagda

clean:
	rm -f *.agdai *.agda~
	rm -f latex/*.{aux,bbl,blg,log,out,pdf,ptb,toc}
	rm -f $(GEN_DIR)/*
