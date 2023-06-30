GOAL= main-icfp23-pearl
TARGET_MODULES= ST-finite-nonbranching ST-recursive ST-monadic ST-indexed-contextfree ST-multichannel \
	EX-multichannel ST-multichannel-finite-branching ST-multichannel-finite-branching-recursion Channels Utils
TARGET_FILES= agdamacros.tex unicodeletters.tex $(addprefix $(PREFIX)/, $(addsuffix .tex, $(TARGET_MODULES)))
PREFIX= latex

ZIPFILES= README.md Makefile $(addsuffix .lagda, $(TARGET_MODULES)) Control/Concurrent/UntypedChannel.hs
ZIPGOAL= supplement-icfp23.zip

ARXIVGOAL= $(GOAL).zip

AECGOAL= $(GOAL)-aec.zip
