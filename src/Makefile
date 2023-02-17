GOAL= main-icfp23-pearl
TARGET_MODULES= ST-finite-nonbranching ST-recursive
TARGET_FILES= agdamacros.tex unicodeletters.tex $(addprefix $(PREFIX)/, $(addsuffix .tex, $(TARGET_MODULES)))
PREFIX= latex

$(GOAL).pdf: $(GOAL).tex $(TARGET_FILES)
	pdflatex  --synctex=1 -interaction=nonstopmode $(GOAL)

$(PREFIX)/%.tex: %.lagda
	agda --latex --only-scope-checking $<
