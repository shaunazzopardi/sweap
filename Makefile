# Shortnames we give to the tools
SWEAP_ALL := sweap-strix sweap-dual sweap-issy sweap-issy-dual sweap-rpg sweap-rpg-dual sweap-tsl sweap-tsl-dual sweap-semml
ISSY2_ALL := issy2 issy2-rpg issy2-tsl 
TOOLS := $(SWEAP_ALL) $(ISSY2_ALL)
# Timeout for each benchmark, in seconds
TIMEOUT := 600

# Directory that contains this Makefile
ROOT_DIR := $(dir $(realpath $(firstword $(MAKEFILE_LIST))))

.PHONY: all clean clean-timeouts confirm check-ulimit tables plots count $(TOOLS)

# Paths to benchmark files
SWEAP_BENCHS :=		$(basename $(wildcard benchmarks/sweap/*.prog))
SWEAP_BENCHS +=		$(basename $(wildcard benchmarks/sweap/tacas16/*.prog))
SWEAP_BENCHS +=		$(basename $(wildcard benchmarks/sweap/cav24/*.prog))
SWEAP_BENCHS +=		$(basename $(wildcard benchmarks/sweap/isola24/*.prog))
SWEAP_BENCHS +=		$(basename $(wildcard benchmarks/sweap/popl24/*.prog))
SWEAP_BENCHS +=		$(basename $(wildcard benchmarks/sweap/popl25/*.prog))
SWEAP_BENCHS +=		$(basename $(wildcard benchmarks/sweap/popl25/basic/*.prog))
SWEAP_BENCHS +=		$(basename $(wildcard benchmarks/sweap/popl25/limitations/*.prog))
SWEAP_BENCHS +=		$(basename $(wildcard benchmarks/sweap/popl25/misc/*.prog))
SWEAP_BENCHS +=		$(basename $(wildcard benchmarks/sweap/popl25/robot-missions/*.prog))
SWEAP_BENCHS +=		$(basename $(wildcard benchmarks/sweap/popl25/tasks/*.prog))
SWEAP_BENCHS +=		$(basename $(wildcard benchmarks/sweap/popl25/thermostat/*.prog))
SWEAP_BENCHS +=		$(basename $(wildcard benchmarks/sweap/full-ltl/*.prog))
SWEAP_BENCHS +=		$(basename $(wildcard benchmarks/sweap/full-ltl/hard/*.prog))
RPG_BENCHS :=		$(basename $(wildcard benchmarks/rpgsolve/*.rpg))
RABONIEL_BENCHS :=	$(basename $(wildcard benchmarks/raboniel/*.tslmt))
TSLMT2RPG_BENCHS :=	$(basename $(wildcard benchmarks/tslmt2rpg/*.tslmt))

ISSY_BENCHS :=		$(basename $(wildcard benchmarks/issy/*.issy))
ISSY_BENCHS +=		$(basename $(wildcard benchmarks/issy/balancers/*.issy))
ISSY_BENCHS +=		$(basename $(wildcard benchmarks/issy/buechi/*.issy))
ISSY_BENCHS +=		$(basename $(wildcard benchmarks/issy/counters/*.issy))
ISSY_BENCHS +=		$(basename $(wildcard benchmarks/issy/example/*.issy))
ISSY_BENCHS +=		$(basename $(wildcard benchmarks/issy/parity/*.issy))
ISSY_BENCHS +=		$(basename $(wildcard benchmarks/issy/system-level/*.issy))


SWEAP_STRIX_LOGS :=		$(addsuffix .sweap-strix.log, 		$(SWEAP_BENCHS))
SWEAP_DUAL_LOGS :=		$(addsuffix .sweap-dual.log, 		$(SWEAP_BENCHS))
SWEAP_SEMML_LOGS :=		$(addsuffix .sweap-semml.log, 		$(SWEAP_BENCHS))
SWEAP_RPG_LOGS :=		$(addsuffix .sweap-rpg.log, 		$(RPG_BENCHS))
SWEAP_RPG_DUAL_LOGS :=	$(addsuffix .sweap-rpg-dual.log, 	$(RPG_BENCHS))
SWEAP_TSL_LOGS :=		$(addsuffix .sweap-tsl.log, 		$(RABONIEL_BENCHS))
SWEAP_TSL_DUAL_LOGS :=	$(addsuffix .sweap-tsl-dual.log, 	$(RABONIEL_BENCHS))
SWEAP_ISSY_LOGS :=		$(addsuffix .sweap-issy.log, 		$(ISSY_BENCHS))
SWEAP_ISSY_DUAL_LOGS :=	$(addsuffix .sweap-issy-dual.log, 	$(ISSY_BENCHS))

ISSY2_LOGS :=			$(addsuffix .issy2.log,				$(ISSY_BENCHS))
ISSY2_RPG_LOGS :=		$(addsuffix .issy2-rpg.log,			$(RPG_BENCHS))
ISSY2_TSL_LOGS :=		$(addsuffix .issy2-tsl.log,			$(TSLMT2RPG_BENCHS))


# Tool command-line invocation
$(SWEAP_STRIX_LOGS): cmd = 		python3 src/main.py --synthesise --synthesis_backend strix --p
$(SWEAP_SEMML_LOGS): cmd = 		python3 src/main.py --synthesise --synthesis_backend semml --p
$(SWEAP_DUAL_LOGS): cmd =		python3 src/main.py --synthesise --dual --synthesis_backend semml --p
$(SWEAP_RPG_LOGS): cmd = 		python3 src/main.py --synthesise --synthesis_backend semml --rpg
$(SWEAP_RPG_DUAL_LOGS): cmd = 	python3 src/main.py --synthesise --dual --synthesis_backend semml --rpg
$(SWEAP_TSL_LOGS): cmd = 		python3 src/main.py --synthesise --synthesis_backend semml --tsl
$(SWEAP_TSL_DUAL_LOGS): cmd =	python3 src/main.py --synthesise --dual --synthesis_backend semml --tsl
$(SWEAP_ISSY_LOGS): cmd = 		python3 src/main.py --synthesise --synthesis_backend semml --issy
$(SWEAP_ISSY_DUAL_LOGS): cmd = 	python3 src/main.py --synthesise --dual --synthesis_backend semml --issy
$(ISSY2_LOGS): cmd =			apptainer exec issy2.sif issy --pruning 2 --synt <
$(ISSY2_RPG_LOGS): cmd =		apptainer exec issy2.sif issy --pruning 2 --synt --rpg <
$(ISSY2_TSL_LOGS): cmd =		apptainer exec issy2.sif issy --pruning 2 --synt --tslmt <


# paths that the tool needs in $PATH
path = binaries:binaries/CPAchecker-2.3-unix/scripts

# Set up environment variables, create temporary log file, record start time
define HEADER
	export PYTHONPATH=src/ ;\
	export PATH=$(path):$$PATH ;\
	export LOGFILE=$$(mktemp tmp-bench.XXXXXXX.log) ;\
	echo "[$$(date)] timeout $(TIMEOUT) $(cmd) $<" >> $$LOGFILE ;\
	echo "git commit:" `git rev-parse --short HEAD` >> $$LOGFILE ;\
	starttime=`date +%s%N`
endef

# Record return code and elapsed time, move log file to its final location
define FOOTER
	exitcode=$$? ;\
	endtime=`date +%s%N` ;\
	echo $$exitcode >> $$LOGFILE ;\
	echo $$(((endtime - starttime)/1000000)) >> $$LOGFILE ;\
	mv $$LOGFILE $(ROOT_DIR)/$@
endef

all: $(TOOLS)

sweap-strix:	check-ulimit $(SWEAP_STRIX_LOGS)
sweap-semml:	$(SWEAP_SEMML_LOGS) # SemML does not work well under ulimit
sweap-dual:		$(SWEAP_DUAL_LOGS)
sweap-rpg:		$(SWEAP_RPG_LOGS)
sweap-rpg-dual:	$(SWEAP_RPG_DUAL_LOGS)
sweap-tsl:		$(SWEAP_TSL_LOGS)
sweap-tsl-dual:	$(SWEAP_TSL_DUAL_LOGS)
sweap-issy:		$(SWEAP_ISSY_LOGS)
sweap-issy-dual:	$(SWEAP_ISSY_DUAL_LOGS)

issy2:		check-ulimit $(ISSY2_LOGS)	
issy2-rpg:	check-ulimit $(ISSY2_RPG_LOGS)
issy2-tsl:	check-ulimit $(ISSY2_TSL_LOGS)


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

$(ISSY2_LOGS): %.issy2.log : %.issy
	@echo "$(cmd) $< $(TIMEOUT)"
	@$(HEADER) ; timeout $(TIMEOUT) $(cmd) $< >> $$LOGFILE 2>&1 ; $(FOOTER)

$(ISSY2_RPG_LOGS): %.issy2-rpg.log : %.rpg
	@echo "$(cmd) $< $(TIMEOUT)"
	@$(HEADER) ; timeout $(TIMEOUT) $(cmd) $< >> $$LOGFILE 2>&1 ; $(FOOTER)

$(ISSY2_TSL_LOGS): %.issy2-tsl.log : %.tslmt
	@echo "$(cmd) $< $(TIMEOUT)"
	@$(HEADER) ; timeout $(TIMEOUT) $(cmd) $< >> $$LOGFILE 2>&1 ; $(FOOTER)


################################################################################

################################################################################
# Cleanup commands
clean: confirm
	@echo "Cleaning up all logs..."
	@find benchmarks/ -iname "*.*.log" -delete || true

clean-timeouts: confirm
	@echo "Cleaning up logs for experiments that timed out..."
	-@find benchmarks/ -iname "*.*.log" | xargs tail -n2 | grep -B1 -e '^124$$' -e '^255$$' | grep "==>" | xargs rm -v 2>/dev/null || true

confirm:
	@echo -n "Are you sure? [y/N] " && read ans && [ $${ans:-N} = y ]
################################################################################

ULIM := $(shell ulimit -v)

# Checks whether a memory limit has been set
check-ulimit:
ifeq ("$(ULIM)", "unlimited")
	@echo -n "memory unlimited! Are you sure? [y/N] " && read ans && [ $${ans:-N} = y ]
endif


tables:
	(benchmarks/scripts/process_logs.py benchmarks | tee benchmarks/results/results.csv) 2> >(tee benchmarks/results/stats.csv)

plots:
	cd benchmarks/scripts; \
	./cactus.py ../results/results.csv

count:
	@echo -n "sweap: " && echo $(SWEAP_BENCHS) | wc -w
	@echo -n "issy: " && echo $(ISSY_BENCHS) | wc -w
	@echo -n "rpg: " && echo $(RPG_BENCHS) | wc -w
	@echo -n "tslmt: " && echo $(TSLMT2RPG_BENCHS) | wc -w

