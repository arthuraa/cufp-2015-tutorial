COQSPLIT = ~/src/sf/tools/coqsplit

ALL = redblack-full.v redblack-short.v

all: $(ALL)

redblack-full.v: redblack.v
	$(COQSPLIT) foo < $< > $@

redblack-short.v: redblack.v
	$(COQSPLIT) foo -terse < $< > $@

.PHONY: clean

clean:
	rm $(ALL)
