include src/variables.mk

ARTIFACT= README.md $(addprefix src/, $(ZIPFILES))

.PHONY: artifact

artifact:
	$(MAKE) artifact-icfp23.zip

artifact-icfp23.zip: Makefile $(ARTIFACT)
	zip $@ $^
