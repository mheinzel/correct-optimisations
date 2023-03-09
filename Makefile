AGDA_FILES:=$(shell find src -name "*.agda" -type f | sed 's|\./||g' | sort)
AGDA_OUTPUT:=$(patsubst %.agda,%.agdai,$(AGDA_FILES))

.PHONY: default check clean

default: check

# TODO: this keeps looping?
check: $(AGDA_OUTPUT)

src/%.agdai: src/%.agda $(AGDA_FILES)
	agda $<

clean:
	rm -f $(shell find -name "*.agdai")
	rm -f $(shell find -name "*~")
	$(MAKE) -C generic-syntax-simple clean
	$(MAKE) -C thesis                clean
	$(MAKE) -C thesis-proposal       clean
	$(MAKE) -C tyde22                clean
