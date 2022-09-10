.PHONY: default tyde22 clean

default: tyde22

tyde22:
	cd tyde22; $(MAKE)

clean:
	rm -f src/*.agdai src/*.agda~
	cd tyde22; $(MAKE) clean
