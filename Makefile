.PHONY: default compile clean

default: compile

check: src/Examples.agdai

src/%.agdai: src/%.agda src/*.agda
	agda $<

clean:
	rm -f src/*.agdai src/*.agda~ src/#*#
	$(MAKE) -C thesis          clean
	$(MAKE) -C thesis-proposal clean
	$(MAKE) -C tyde22          clean
