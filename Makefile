ARTIFACT= README.md src/supplement-icfp23.zip

.PHONY: all

all:
	cd src; $(MAKE) supplement-icfp23.zip
	$(MAKE) artifact-icfp23.zip

artifact-icfp23.zip: Makefile $(ARTIFACT)
	zip $@ $^
