GEN_DIR = report/generated

.PHONY: all clean

all: report/report.pdf

report/report.pdf: report/report.tex $(GEN_DIR)/Recursion.tex $(GEN_DIR)/Lang.tex $(GEN_DIR)/Subset.tex $(GEN_DIR)/Live.tex report/agda.sty report/report.bib
	cd report; pdflatex report
	cd report; bibtex report
	cd report; pdflatex report
	cd report; pdflatex report

$(GEN_DIR)/Lang.tex: Lang.lagda
	agda --latex-dir=$(GEN_DIR) --latex Lang.lagda

$(GEN_DIR)/Subset.tex: Subset.lagda Lang.lagda
	agda --latex-dir=$(GEN_DIR) --latex Subset.lagda

$(GEN_DIR)/Recursion.tex: Recursion.lagda Lang.lagda Subset.lagda
	agda --latex-dir=$(GEN_DIR) --latex Recursion.lagda

$(GEN_DIR)/Live.tex: Live.lagda Lang.lagda Subset.lagda Recursion.lagda
	agda --latex-dir=$(GEN_DIR) --latex Live.lagda

clean:
	rm -f *.agdai *.agda~
	rm -f report/*.log report/*.aux report/*.toc report/*.ptb
	rm -f $(GEN_DIR)/*
	rm -f report/report.pdf
