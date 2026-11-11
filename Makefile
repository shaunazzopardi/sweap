# Force bash as the shell
SHELL := $(shell which bash)
# Shortnames we give to the tools
SWEAP_ALL := sweap-strix sweap-dual sweap-issy sweap-issy-dual sweap-rpg sweap-rpg-dual sweap-tsl sweap-tsl-dual sweap-semml
ISSY3_ALL := issy3 issy3-rpg issy3-tsl 
TOOLS := $(SWEAP_ALL) $(ISSY3_ALL)
# Timeout for each benchmark, in seconds
TIMEOUT := 600

# Directory that contains this Makefile
ROOT_DIR := $(dir $(realpath $(firstword $(MAKEFILE_LIST))))

BENCH_DIR := /benchmarks

.PHONY: all clean clean-timeouts confirm setup tables plots count $(TOOLS)

# Paths to benchmark files
SWEAP_BENCHS :=		$(basename $(wildcard $(BENCH_DIR)/sweap/*.prog))
SWEAP_BENCHS +=		$(basename $(wildcard $(BENCH_DIR)/sweap/tacas16/*.prog))
SWEAP_BENCHS +=		$(basename $(wildcard $(BENCH_DIR)/sweap/cav24/*.prog))
SWEAP_BENCHS +=		$(basename $(wildcard $(BENCH_DIR)/sweap/isola24/*.prog))
SWEAP_BENCHS +=		$(basename $(wildcard $(BENCH_DIR)/sweap/popl24/*.prog))
SWEAP_BENCHS +=		$(basename $(wildcard $(BENCH_DIR)/sweap/popl25/*.prog))
SWEAP_BENCHS +=		$(basename $(wildcard $(BENCH_DIR)/sweap/popl25/basic/*.prog))
SWEAP_BENCHS +=		$(basename $(wildcard $(BENCH_DIR)/sweap/popl25/limitations/*.prog))
SWEAP_BENCHS +=		$(basename $(wildcard $(BENCH_DIR)/sweap/popl25/misc/*.prog))
SWEAP_BENCHS +=		$(basename $(wildcard $(BENCH_DIR)/sweap/popl25/robot-missions/*.prog))
SWEAP_BENCHS +=		$(basename $(wildcard $(BENCH_DIR)/sweap/popl25/tasks/*.prog))
SWEAP_BENCHS +=		$(basename $(wildcard $(BENCH_DIR)/sweap/popl25/thermostat/*.prog))
SWEAP_BENCHS +=		$(basename $(wildcard $(BENCH_DIR)/sweap/full-ltl/*.prog))
SWEAP_BENCHS +=		$(basename $(wildcard $(BENCH_DIR)/sweap/full-ltl/hard/*.prog))
RPG_BENCHS :=		$(basename $(wildcard $(BENCH_DIR)/rpgsolve/*.rpg))
RABONIEL_BENCHS :=	$(basename $(wildcard $(BENCH_DIR)/raboniel/*.tslmt))
TSLMT2RPG_BENCHS :=	$(basename $(wildcard $(BENCH_DIR)/tslmt2rpg/*.tslmt))

ISSY_BENCHS :=		$(basename $(wildcard $(BENCH_DIR)/issy/*.issy))
ISSY_BENCHS +=		$(basename $(wildcard $(BENCH_DIR)/issy/balancers/*.issy))
ISSY_BENCHS +=		$(basename $(wildcard $(BENCH_DIR)/issy/buechi/*.issy))
ISSY_BENCHS +=		$(basename $(wildcard $(BENCH_DIR)/issy/counters/*.issy))
ISSY_BENCHS +=		$(basename $(wildcard $(BENCH_DIR)/issy/example/*.issy))
ISSY_BENCHS +=		$(basename $(wildcard $(BENCH_DIR)/issy/parity/*.issy))
ISSY_BENCHS +=		$(basename $(wildcard $(BENCH_DIR)/issy/system-level/*.issy))

ISSY_BENCHS +=		$(basename $(wildcard $(BENCH_DIR)/issy/tacas26/*.issy))
ISSY_BENCHS +=		$(basename $(wildcard $(BENCH_DIR)/issy/tacas26/verification/*.issy))

SWEAP_STRIX_LOGS :=		$(addsuffix .sweap-strix.log, 		$(SWEAP_BENCHS))
SWEAP_DUAL_LOGS :=		$(addsuffix .sweap-dual.log, 		$(SWEAP_BENCHS))
SWEAP_STRIX_DUAL_LOGS :=$(addsuffix .sweap-strix-dual.log,	$(SWEAP_BENCHS))
SWEAP_SEMML_LOGS :=		$(addsuffix .sweap-semml.log, 		$(SWEAP_BENCHS))
SWEAP_RPG_LOGS :=		$(addsuffix .sweap-rpg.log, 		$(RPG_BENCHS))
SWEAP_RPG_DUAL_LOGS :=	$(addsuffix .sweap-rpg-dual.log, 	$(RPG_BENCHS))
SWEAP_TSL_LOGS :=		$(addsuffix .sweap-tsl.log, 		$(RABONIEL_BENCHS))
SWEAP_TSL_DUAL_LOGS :=	$(addsuffix .sweap-tsl-dual.log, 	$(RABONIEL_BENCHS))
SWEAP_ISSY_LOGS :=		$(addsuffix .sweap-issy.log, 		$(ISSY_BENCHS))
SWEAP_ISSY_DUAL_LOGS :=	$(addsuffix .sweap-issy-dual.log, 	$(ISSY_BENCHS))

ISSY3_LOGS :=			$(addsuffix .issy3.log,				$(ISSY_BENCHS))
ISSY3_RPG_LOGS :=		$(addsuffix .issy3-rpg.log,			$(RPG_BENCHS))
ISSY3_TSL_LOGS :=		$(addsuffix .issy3-tsl.log,			$(TSLMT2RPG_BENCHS))

# Tool command-line invocation
$(SWEAP_STRIX_LOGS): cmd = 	python3 src/main.py --synthesise --synthesis_backend strix --p
$(SWEAP_SEMML_LOGS): cmd = 	python3 src/main.py --synthesise --synthesis_backend semml --p
$(SWEAP_DUAL_LOGS): cmd =	python3 src/main.py --synthesise --dual --workers 1 --synthesis_backend semml --p
$(SWEAP_STRIX_DUAL_LOGS): cmd =	python3 src/main.py --synthesise --dual --workers 1 --synthesis_backend strix --p
$(SWEAP_RPG_LOGS): cmd = 	python3 src/main.py --synthesise --synthesis_backend semml --rpg
$(SWEAP_RPG_DUAL_LOGS): cmd = 	python3 src/main.py --synthesise --dual --workers 1 --synthesis_backend semml --rpg
$(SWEAP_TSL_LOGS): cmd = 	python3 src/main.py --synthesise --synthesis_backend semml --tsl
$(SWEAP_TSL_DUAL_LOGS): cmd =	python3 src/main.py --synthesise --dual --workers 1 --synthesis_backend semml --tsl
$(SWEAP_ISSY_LOGS): cmd = 	python3 src/main.py --synthesise --synthesis_backend semml --issy
$(SWEAP_ISSY_DUAL_LOGS): cmd = 	python3 src/main.py --synthesise --dual --workers 1 --synthesis_backend semml --issy
$(ISSY3_LOGS): cmd =		issy-bin --synt --caller-z3 /usr/bin/z3-4.15.1 --caller-muval /usr/bin/call-muval --caller-aut /usr/local/bin/ltl2tgba --issy
$(ISSY3_RPG_LOGS): cmd =	issy-bin --synt --caller-z3 /usr/bin/z3-4.15.1 --caller-muval /usr/bin/call-muval --caller-aut /usr/local/bin/ltl2tgba --rpg
$(ISSY3_TSL_LOGS): cmd =	issy-bin --synt --caller-z3 /usr/bin/z3-4.15.1 --caller-muval /usr/bin/call-muval --caller-aut /usr/local/bin/ltl2tgba --tslmt


# paths that the tool needs in $PATH
path = $(ROOT_DIR)/binaries:$(ROOT_DIR)/binaries/CPAchecker-2.3-unix/scripts

# Set up environment variables, create temporary log file, record start time
define HEADER
	export PYTHONPATH=src/ ;\
	export PATH=$(path):$$PATH ;\
	export LOGFILE=$$(mktemp tmp-bench.XXXXXXX.log) ;\
	echo "[$$(date)] timeout $(TIMEOUT) $(cmd) $<" >> $$LOGFILE ;\
	starttime=`date +%s%N`
endef

# Record return code and elapsed time, move log file to its final location
define FOOTER
	exitcode=$$? ;\
	endtime=`date +%s%N` ;\
	echo >> $$LOGFILE ;\
	echo >> $$LOGFILE ;\
	echo $$exitcode >> $$LOGFILE ;\
	echo $$(((endtime - starttime)/1000000)) >> $$LOGFILE ;\
	mv $$LOGFILE $@
endef

all: $(TOOLS)

sweap-strix:		$(SWEAP_STRIX_LOGS)
sweap-semml:		$(SWEAP_SEMML_LOGS)
sweap-dual:			$(SWEAP_DUAL_LOGS)
sweap-strix-dual:	$(SWEAP_STRIX_DUAL_LOGS)
sweap-rpg:			$(SWEAP_RPG_LOGS)
sweap-rpg-dual:		$(SWEAP_RPG_DUAL_LOGS)
sweap-tsl:			$(SWEAP_TSL_LOGS)
sweap-tsl-dual:		$(SWEAP_TSL_DUAL_LOGS)
sweap-issy:			$(SWEAP_ISSY_LOGS)
sweap-issy-dual:	$(SWEAP_ISSY_DUAL_LOGS)

issy3:		$(ISSY3_LOGS)
issy3-rpg:	$(ISSY3_RPG_LOGS)
issy3-tsl:	$(ISSY3_TSL_LOGS)


################################################################################
# Here are the core commands that run a tool on a benchmark <bench>.<ext>
# and record all output into <bench>.<tool>.log
# The log also contains the exact command line, the return code,
# and the execution time (in ms)

$(SWEAP_STRIX_LOGS): %.sweap-strix.log: %.prog
	@echo "$(cmd) $< $(TIMEOUT)"
	@$(HEADER) ; timeout $(TIMEOUT) $(cmd) $< >> $$LOGFILE 2>&1 ; $(FOOTER)

$(SWEAP_DUAL_LOGS): %.sweap-dual.log: %.prog
	@echo "$(cmd) $< $(TIMEOUT)"
	@$(HEADER) ; timeout $(TIMEOUT) $(cmd) $< >> $$LOGFILE 2>&1 ; $(FOOTER)

$(SWEAP_STRIX_DUAL_LOGS): %.sweap-strix-dual.log: %.prog
	@echo "$(cmd) $< $(TIMEOUT)"
	@$(HEADER) ; timeout $(TIMEOUT) $(cmd) $< >> $$LOGFILE 2>&1 ; $(FOOTER)

$(SWEAP_SEMML_LOGS): %.sweap-semml.log: %.prog
	@echo "$(cmd) $< $(TIMEOUT)"
	@$(HEADER) ; timeout $(TIMEOUT) $(cmd) $< >> $$LOGFILE 2>&1 ; $(FOOTER)

$(SWEAP_RPG_LOGS): %.sweap-rpg.log: %.rpg
	@echo "$(cmd) $< $(TIMEOUT)"
	@$(HEADER) ; timeout $(TIMEOUT) $(cmd) $< >> $$LOGFILE 2>&1 ; $(FOOTER)

$(SWEAP_RPG_DUAL_LOGS): %.sweap-rpg-dual.log: %.rpg
	@echo "$(cmd) $< $(TIMEOUT)"
	@$(HEADER) ; timeout $(TIMEOUT) $(cmd) $< >> $$LOGFILE 2>&1 ; $(FOOTER)

$(SWEAP_TSL_LOGS): %.sweap-tsl.log: %.tslmt
	@echo "$(cmd) $< $(TIMEOUT)"
	@$(HEADER) ; timeout $(TIMEOUT) $(cmd) $< >> $$LOGFILE 2>&1 ; $(FOOTER)

$(SWEAP_TSL_DUAL_LOGS): %.sweap-tsl-dual.log: %.tslmt
	@echo "$(cmd) $< $(TIMEOUT)"
	@$(HEADER) ; timeout $(TIMEOUT) $(cmd) $< >> $$LOGFILE 2>&1 ; $(FOOTER)

$(SWEAP_ISSY_LOGS): %.sweap-issy.log: %.issy
	@echo "$(cmd) $< $(TIMEOUT)"
	@$(HEADER) ; timeout $(TIMEOUT) $(cmd) $< >> $$LOGFILE 2>&1 ; $(FOOTER)

$(SWEAP_ISSY_DUAL_LOGS): %.sweap-issy-dual.log: %.issy
	@echo "$(cmd) $< $(TIMEOUT)"
	@$(HEADER) ; timeout $(TIMEOUT) $(cmd) $< >> $$LOGFILE 2>&1 ; $(FOOTER)

$(ISSY3_LOGS): %.issy3.log : %.issy
	@echo "$(cmd) $< $(TIMEOUT)"
	@$(HEADER) ; timeout $(TIMEOUT) $(cmd) $< >> $$LOGFILE 2>&1 ; $(FOOTER)

$(ISSY3_RPG_LOGS): %.issy3-rpg.log : %.rpg
	@echo "$(cmd) $< $(TIMEOUT)"
	@$(HEADER) ; timeout $(TIMEOUT) $(cmd) $< >> $$LOGFILE 2>&1 ; $(FOOTER)

$(ISSY3_TSL_LOGS): %.issy3-tsl.log : %.tslmt
	@echo "$(cmd) $< $(TIMEOUT)"
	@$(HEADER) ; timeout $(TIMEOUT) $(cmd) $< >> $$LOGFILE 2>&1 ; $(FOOTER)


################################################################################

################################################################################
# Cleanup commands
clean: confirm
	@echo "Cleaning up all logs..."
	@find $(BENCH_DIR)/ -iname "*.*.log" -delete || true

clean-timeouts: confirm
	@echo "Cleaning up logs for experiments that timed out..."
	-@find $(BENCH_DIR)/ -iname "*.*.log" | xargs tail -n2 | grep -B1 -e '^124$$' -e '^255$$' | grep "==>" | xargs rm -v 2>/dev/null || true

confirm:
	@echo -n "Are you sure? [y/N] " && read ans && [ $${ans:-N} = y ]
################################################################################

tables:
	($(BENCH_DIR)/scripts/process_logs.py $(BENCH_DIR) | tee $(BENCH_DIR)/results/results.csv) 2> >(tee $(BENCH_DIR)/results/stats.csv)

plots:
	$(BENCH_DIR)/scripts/scatter.py $(BENCH_DIR)/results/results.csv sweap-pf sweap-strix > $(BENCH_DIR)/results/table_sweap-pf_sweap-strix.tex
	$(BENCH_DIR)/scripts/scatter.py $(BENCH_DIR)/results/results.csv sweap-issy-pf issy3 > $(BENCH_DIR)/results/table_sweap-issy-pf_issy3.tex
	$(BENCH_DIR)/scripts/scatter.py $(BENCH_DIR)/results/results.csv sweap-rpg-pf issy3-rpg > $(BENCH_DIR)/results/table_sweap-rpg-pf_issy3-rpg.tex
	$(BENCH_DIR)/scripts/scatter.py $(BENCH_DIR)/results/results.csv sweap-tsl-pf issy3-tsl > $(BENCH_DIR)/results/table_sweap-tsl-pf_issy3-tsl.tex

count:
	@echo -n "sweap: " && echo $(SWEAP_BENCHS) | wc -w
	@echo -n "issy: " && echo $(ISSY_BENCHS) | wc -w
	@echo -n "rpg: " && echo $(RPG_BENCHS) | wc -w
	@echo -n "tslmt: " && echo $(TSLMT2RPG_BENCHS) | wc -w

setup:
	cp -r $(ROOT_DIR)/benchmarks/* $(BENCH_DIR)
