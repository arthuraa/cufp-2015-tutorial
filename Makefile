COQSPLIT = ~/src/sf/tools/coqsplit

ALL = list_basics.full.v list_basics.short.v list_basics.sol.v \
	redblack.full.v redblack.short.v redblack.sol.v

all: $(ALL)

list_basics.full.v: list_basics.v
	$(COQSPLIT) foo < $< > $@

list_basics.short.v: list_basics.v
	$(COQSPLIT) foo -terse < $< > $@

list_basics.sol.v: list_basics.v
	$(COQSPLIT) foo -solutions < $< > $@

redblack.full.v: redblack.v
	$(COQSPLIT) foo < $< > $@

redblack.short.v: redblack.v
	$(COQSPLIT) foo -terse < $< > $@

redblack.sol.v: redblack.v
	$(COQSPLIT) foo -solutions < $< > $@

.PHONY: clean

clean:
	rm $(ALL)
