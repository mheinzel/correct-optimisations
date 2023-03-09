AGDA_FILES:=$(shell find src -name "*.agda" -type f | sed 's|\./||g' | sort)
AGDA_OUTPUT:=$(patsubst %.agda,%.agdai,$(AGDA_FILES))

.PHONY: default check clean

default: check

check: $(AGDA_OUTPUT)

src/%.agdai: src/%.agda $(AGDA_FILES)
	agda $<

clean:
	rm -f $(shell find src -name "*.agdai")
