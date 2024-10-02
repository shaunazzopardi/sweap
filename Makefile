DIRNAME := results
TOOLS := rpg-stela rpgsolve rpgsolve-syn sweap sweap-noacc
OTHER_TOOLS := temos raboniel
TIMEOUT := 1200

.PHONY: all others everything clean $(tools)

all: $(TOOLS)

others: $(OTHER_TOOLS)

everything: all others

clean:
	-rm -rf $(DIRNAME)/

$(TOOLS) $(OTHER_TOOLS): %: $(addsuffix -0, $(addprefix $(DIRNAME)/out-, %))

# Force sweap tools to run in sequence
$(DIRNAME)/out-sweap-noacc-0: $(DIRNAME)/out-sweap-0

$(DIRNAME)/out-%-0: | $(DIRNAME)
	@rm benchmarks/scripts/out-$*-* 2>/dev/null || true
	benchmarks/scripts/run-$*.sh $(TIMEOUT)
	mv benchmarks/scripts/out-$*-* $(DIRNAME)/out-$*-0

$(DIRNAME):
	@mkdir -p $(DIRNAME)

