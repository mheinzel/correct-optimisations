.PHONY: default compile clean

default: compile

compile: src/Live.agdai

# TODO: support other agda files
src/Live.agdai: src/*.agda
	agda src/Live.agda

clean:
	rm -f src/*.agdai src/*.agda~ src/#*#
	$(MAKE) -C thesis-proposal clean
	$(MAKE) -C tyde22          clean
