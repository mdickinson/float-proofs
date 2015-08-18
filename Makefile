MODULES := rearrange_tactic remedial floor_and_ceiling is_multiple_of \
	round qpos twopower cobinade twopower_tactics binary_float \
	rounding separation_results next_up binade
VS := $(MODULES:%=%.v)

.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile  $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
