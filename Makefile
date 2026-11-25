ROCQ ?= rocq

.PHONY: all clean

all:
	$(ROCQ) makefile -f _RocqProject -o Makefile.rocq
	+$(MAKE) -f Makefile.rocq

clean:
	+@if test -f Makefile.rocq; then $(MAKE) -f Makefile.rocq clean; fi
