DIRNAME := results
TOOLS := rpg-stela rpgsolve-syn sweap sweap-noacc
OTHER_TOOLS := temos raboniel rpgsolve
TIMEOUT := 1200

.PHONY: all others everything clean clean-aux $(tools)

all: $(TOOLS)

others: $(OTHER_TOOLS)

everything: all others

clean: clean-aux
	-rm -rf $(DIRNAME)/
	-rm -rf logs/*.log
	-rm benchmarks/scripts/log-*

clean-aux:
	-rm -rf benchmarks/raboniel/*.t
	-rm -rf benchmarks/raboniel/*.tsl
	-rm -rf benchmarks/raboniel/*.py
	-rm -rf benchmarks/raboniel/*.t_R*.tlsf
	-rm -rf benchmarks/raboniel/*.t_R*.kiss
	-rm -rf benchmarks/raboniel/finite/*.t
	-rm -rf benchmarks/raboniel/finite/*.tsl
	-rm -rf benchmarks/raboniel/finite/*.py
	-rm -rf benchmarks/raboniel/finite/*.t_R*.tlsf
	-rm -rf benchmarks/raboniel/finite/*.t_R*.kiss

$(TOOLS) $(OTHER_TOOLS): %: $(addsuffix -0, $(addprefix $(DIRNAME)/out-, %))

# Force sweap tools to run in sequence
$(DIRNAME)/out-sweap-noacc-0: $(DIRNAME)/out-sweap-0

$(DIRNAME)/out-%-0: | $(DIRNAME)
	@rm benchmarks/scripts/out-$*-* 2>/dev/null || true
	benchmarks/scripts/run-$*.sh $(TIMEOUT)
	mv benchmarks/scripts/out-$*-* $(DIRNAME)/out-$*-0

$(DIRNAME):
	@mkdir -p $(DIRNAME)

