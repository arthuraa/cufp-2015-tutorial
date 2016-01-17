COQSPLIT = ./coqsplit

V = list_basics.full.v list_basics.short.v list_basics.sol.v \
	redblack.full.v redblack.short.v redblack.sol.v

all: $(V)

list_basics.full.v: list_basics.v coqsplit
	$(COQSPLIT) < $< > $@

list_basics.short.v: list_basics.v coqsplit
	$(COQSPLIT) -terse < $< > $@

list_basics.sol.v: list_basics.v coqsplit
	$(COQSPLIT) -solutions < $< > $@

redblack.full.v: redblack.v coqsplit
	$(COQSPLIT) < $< > $@

redblack.short.v: redblack.v coqsplit
	$(COQSPLIT) -terse < $< > $@

redblack.sol.v: redblack.v coqsplit
	$(COQSPLIT) -solutions < $< > $@

coqsplit: coqsplit.ml
	ocamlc.opt coqsplit.ml -o coqsplit

.PHONY: clean

clean:
	rm $(V) coqsplit coqsplit.cmo coqsplit.cmi
