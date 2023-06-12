GOAL= main-icfp23-pearl
TARGET_MODULES= ST-finite-nonbranching ST-recursive ST-monadic ST-indexed-contextfree ST-multichannel \
	EX-multichannel ST-multichannel-finite-branching-recursion Channels Utils
TARGET_FILES= agdamacros.tex unicodeletters.tex $(addprefix $(PREFIX)/, $(addsuffix .tex, $(TARGET_MODULES)))
PREFIX= latex

ZIPFILES= README.md Makefile $(addsuffix .lagda, $(TARGET_MODULES)) Control/Concurrent/UntypedChannel.hs
ZIPGOAL= supplement-icfp23.zip

ARXIVGOAL= $(GOAL).zip

AECGOAL= $(GOAL)-aec.zip

$(GOAL).pdf: $(GOAL).tex $(TARGET_FILES)
	pdflatex  --synctex=1 -interaction=nonstopmode $(GOAL)

$(PREFIX)/%.tex: %.lagda
	agda --latex --only-scope-checking $<

$(ZIPGOAL): $(ZIPFILES)
	zip $@ $^

$(ARXIVGOAL): $(GOAL).tex $(GOAL).bbl $(TARGET_FILES) acmart.cls agda.sty ACM-Reference-Format.bst
	zip $@ $^

.PHONY: all type-check clean
all: $(GOAL).pdf $(ZIPGOAL)

### clean up

clean:
	$(RM) -f EX-multichannel
	$(RM) -rf MAlonzo
	$(RM) -f *.agdai

### type checking

type-check:
	for src in $(addsuffix .lagda, $(TARGET_MODULES)) ; do \
		echo '***' checking $$src ; \
		agda $$src; \
	done

### executables

EX-multichannel: EX-multichannel.lagda
	agda --compile $^
