AGDA_FILES:=$(shell find src -name "*.agda" -type f | sed 's|\./||g' | sort)

.PHONY: default check clean

default: check

check: $(AGDA_Files)
	agda src/Everything.agda

clean:
	rm -f $(shell find -name "*.agdai")
	rm -f $(shell find -name "*~")
	$(MAKE) -C thesis          clean
	$(MAKE) -C thesis-proposal clean
	$(MAKE) -C tyde22          clean
