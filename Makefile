# Shortnames we give to the tools
TOOLS := rpgsolve rpgsolve-syn rpg-stela sweap sweap-lazy sweap-nobin tslmt2rpg tslmt2rpg-syn sweap-rpg sweap-tsl sweap-semml issy-rpg sweap-dual issy-tsl sweap-issy issy
# Timeout for each benchmark, in seconds
TIMEOUT := 600

# Directory that contains this Makefile
ROOT_DIR := $(dir $(realpath $(firstword $(MAKEFILE_LIST))))

.PHONY: all others everything clean clean-aux clean-timeouts confirm check-ulimit tables plots count $(TOOLS)

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
SWEAP_BENCHS +=		$(basename $(wildcard benchmarks/sweap/non-det-inputs/*.prog))
SWEAP_BENCHS +=		$(basename $(wildcard benchmarks/sweap/non-det-inputs/cav24/*.prog))
SWEAP_BENCHS +=		$(basename $(wildcard benchmarks/sweap/non-det-inputs/popl25/basic/*.prog))
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


SWEAP_LOGS :=			$(addsuffix .sweap.log, 			$(SWEAP_BENCHS))
SWEAP_DUAL_LOGS :=		$(addsuffix .sweap-dual.log, 		$(SWEAP_BENCHS))
SWEAP_SEMML_LOGS :=		$(addsuffix .sweap-semml.log, 		$(SWEAP_BENCHS))
SWEAP_RPG_LOGS :=		$(addsuffix .sweap-rpg.log, 		$(RPG_BENCHS))
SWEAP_TSL_LOGS :=		$(addsuffix .sweap-tsl.log, 		$(RABONIEL_BENCHS))
SWEAP_ISSY_LOGS :=		$(addsuffix .sweap-issy.log, 		$(ISSY_BENCHS))
ISSY_LOGS :=			$(addsuffix .issy.log, 				$(ISSY_BENCHS))
ISSY_RPG_LOGS :=		$(addsuffix .issy-rpg.log,			$(RPG_BENCHS))
ISSY_TSL_LOGS :=		$(addsuffix .issy-tsl.log,			$(TSLMT2RPG_BENCHS))

ALL_LOGS := $(SWEAP_LOGS) $(SWEAP_DUAL_LOGS) $(SWEAP_SEMML_LOGS) $(SWEAP_RPG_LOGS) $(SWEAP_TSL_LOGS) $(SWEAP_ISSY_LOGS) $(ISSY_LOGS) $(ISSY_RPG_LOGS) $(ISSY_TSL_LOGS)


SWEAP_LAZY_LOGS :=		$(addsuffix .sweap-lazy.log, 		$(SWEAP_BENCHS))
SWEAP_NOBIN_LOGS :=		$(addsuffix .sweap-nobin.log,       $(SWEAP_BENCHS))
RPG_STELA_LOGS :=		$(addsuffix .rpg-stela.log,			$(RPG_BENCHS))
RPG_SYN_LOGS :=			$(addsuffix .rpgsolve-syn.log,		$(RPG_BENCHS))
RPG_LOGS :=				$(addsuffix .rpgsolve.log,			$(RPG_BENCHS))
TSLMT2RPG_LOGS :=		$(addsuffix .tslmt2rpg.log,			$(TSLMT2RPG_BENCHS))
TSLMT2RPG_SYN_LOGS :=	$(addsuffix .tslmt2rpg-syn.log,		$(TSLMT2RPG_BENCHS))

# Tool command-line invocation
$(SWEAP_LOGS): cmd = 			python3 src/main.py --synthesise --synthesis_backend strix --p
$(SWEAP_DUAL_LOGS): cmd =		python3 src/main.py --synthesise --dual --synthesis_backend semml --p
$(SWEAP_SEMML_LOGS): cmd = 		python3 src/main.py --synthesise --synthesis_backend semml --p
$(SWEAP_RPG_LOGS): cmd = 		python3 src/main.py --synthesise --synthesis_backend semml --rpg
$(SWEAP_TSL_LOGS): cmd = 		python3 src/main.py --synthesise --synthesis_backend semml --tsl
$(SWEAP_ISSY_LOGS): cmd = 		python3 src/main.py --synthesise --synthesis_backend semml --issy
$(ISSY_LOGS): cmd =			rm -rf /home/luca.di.stefano/.local/libpod/tmp && podman run --timeout $(TIMEOUT) --rm -i issy-runner /usr/bin/issy --pruning 2 --synt <
$(ISSY_RPG_LOGS): cmd =			rm -rf /home/luca.di.stefano/.local/libpod/tmp && podman run --timeout $(TIMEOUT) --rm -i issy-runner /usr/bin/issy --pruning 2 --synt --rpg <
$(ISSY_TSL_LOGS): cmd =			rm -rf /home/luca.di.stefano/.local/libpod/tmp && podman run --timeout $(TIMEOUT) --rm -i issy-runner /usr/bin/issy --pruning 2 --synt --tslmt <


$(SWEAP_LAZY_LOGS): cmd =		python3 src/main.py --synthesise --lazy --p
$(SWEAP_NOBIN_LOGS): cmd =		python3 src/main.py --synthesise --no_binary_enc --p
$(RPG_STELA_LOGS): cmd = 		rpg-stela solve --enable-no-pruning <
$(RPG_SYN_LOGS): cmd =			rpgsolve --generate-program --disable-log <
$(RPG_LOGS): cmd =				rpgsolve --disable-log <
$(TSLMT2RPG_LOGS): cmd =		run-pruned.sh
$(TSLMT2RPG_SYN_LOGS): cmd =	run-pruned-syn.sh

# paths that the tool needs in $PATH
path =				binaries
$(SWEAP_LOGS) : path =		binaries:binaries/CPAchecker-2.3-unix/scripts
$(SWEAP_LAZY_LOGS): path =	binaries:binaries/CPAchecker-2.3-unix/scripts
$(SWEAP_DUAL_LOGS): path =	binaries:binaries/CPAchecker-2.3-unix/scripts
$(SWEAP_RPG_LOGS): path =	binaries:binaries/CPAchecker-2.3-unix/scripts
$(SWEAP_TSL_LOGS): path =	binaries:binaries/CPAchecker-2.3-unix/scripts
$(SWEAP_ISSY_LOGS): path =	binaries:binaries/CPAchecker-2.3-unix/scripts
$(SWEAP_SEMML_LOGS): path =	binaries:binaries/CPAchecker-2.3-unix/scripts
$(RPG_SYN_LOGS): path =		binaries/z3-4-8:binaries
$(TSLMT2RPG_LOGS): path =	binaries/z3-4-8:binaries
$(TSLMT2RPG_SYN_LOGS): path =	binaries/z3-4-8:binaries

# Set up environment variables, create temporary log file, record start time
define HEADER
	export PYTHONPATH=src/ ;\
	export PATH=$(path):$$PATH ;\
	export LOGFILE=$$(mktemp tmp-bench.XXXXXXX.log) ;\
	echo "timeout $(TIMEOUT) $(cmd) $<" >> $$LOGFILE ;\
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

all: sweap sweap-rpg sweap-tsl sweap-semml
everything: all sweap-nobin

sweap:			check-ulimit $(SWEAP_LOGS)
sweap-dual:		$(SWEAP_DUAL_LOGS)
sweap-semml:	$(SWEAP_SEMML_LOGS) # SemML does not work well under ulimit
sweap-rpg:		$(SWEAP_RPG_LOGS)
sweap-tsl:		$(SWEAP_TSL_LOGS)
sweap-issy:		$(SWEAP_ISSY_LOGS)

issy:		check-ulimit $(ISSY_LOGS)	
issy-rpg:	check-ulimit $(ISSY_RPG_LOGS)
issy-tsl:	check-ulimit $(ISSY_TSL_LOGS)

sweap-lazy:		check-ulimit $(SWEAP_LAZY_LOGS)
sweap-nobin:	check-ulimit $(SWEAP_NOBIN_LOGS)
rpg-stela:      check-ulimit $(RPG_STELA_LOGS)
rpgsolve-syn:   check-ulimit $(RPG_SYN_LOGS)
rpgsolve:       check-ulimit $(RPG_LOGS)
tslmt2rpg:      check-ulimit $(TSLMT2RPG_LOGS)
tslmt2rpg-syn:  check-ulimit $(TSLMT2RPG_SYN_LOGS)


################################################################################
# Here are the core commands that run a tool on a benchmark <bench>.<ext>
# and record all output into <bench>.<tool>.log
# The log also contains the exact command line, the return code,
# and the execution time (in ms)

$(SWEAP_LOGS): %.sweap.log: %.prog
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

$(SWEAP_TSL_LOGS): %.sweap-tsl.log: %.tslmt
	@echo "$(cmd) $< $(TIMEOUT)"
	@$(HEADER) ; timeout $(TIMEOUT) $(cmd) $< >> $$LOGFILE 2>&1 ; $(FOOTER)

$(SWEAP_ISSY_LOGS): %.sweap-issy.log: %.issy
	@echo "$(cmd) $< $(TIMEOUT)"
	@$(HEADER) ; timeout $(TIMEOUT) $(cmd) $< >> $$LOGFILE 2>&1 ; $(FOOTER)

$(SWEAP_LAZY_LOGS): %.sweap-lazy.log: %.prog
	@echo "$(cmd) $< $(TIMEOUT)"
	@$(HEADER) ; timeout $(TIMEOUT) $(cmd) $< >> $$LOGFILE 2>&1 ; $(FOOTER)

$(SWEAP_NOBIN_LOGS): %.sweap-nobin.log: %.prog
	@echo "$(cmd) $< $(TIMEOUT)"
	@$(HEADER) ; timeout $(TIMEOUT) $(cmd) $< >> $$LOGFILE 2>&1 ; $(FOOTER)

$(RPG_STELA_LOGS): %.rpg-stela.log : %.rpg
	@echo "$(cmd) $< $(TIMEOUT)"
	@$(HEADER) ; timeout $(TIMEOUT) $(cmd) $< >> $$LOGFILE 2>&1 ; $(FOOTER)

$(RPG_SYN_LOGS): %.rpgsolve-syn.log : %.rpg
	@echo "$(cmd) $< $(TIMEOUT)"
	@$(HEADER) ; timeout $(TIMEOUT) $(cmd) $< >> $$LOGFILE 2>&1 ; $(FOOTER)

$(RPG_LOGS): %.rpgsolve.log : %.rpg
	@echo "$(cmd) $< $(TIMEOUT)"
	@$(HEADER) ; timeout $(TIMEOUT) $(cmd) $< >> $$LOGFILE 2>&1 ; $(FOOTER)

$(ISSY_LOGS): %.issy.log : %.issy
	@echo "$(cmd) $< $(TIMEOUT)"
	@$(HEADER) ; timeout $(TIMEOUT) $(cmd) $< >> $$LOGFILE 2>&1 ; $(FOOTER)

$(ISSY_RPG_LOGS): %.issy-rpg.log : %.rpg
	@echo "$(cmd) $< $(TIMEOUT)"
	@$(HEADER) ; timeout $(TIMEOUT) $(cmd) $< >> $$LOGFILE 2>&1 ; $(FOOTER)

$(ISSY_TSL_LOGS): %.issy-tsl.log : %.tslmt
	@echo "$(cmd) $< $(TIMEOUT)"
	@$(HEADER) ; timeout $(TIMEOUT) $(cmd) $< >> $$LOGFILE 2>&1 ; $(FOOTER)

$(TSLMT2RPG_LOGS): %.tslmt2rpg.log : %.tslmt
	@echo "$(cmd) $< $(TIMEOUT)"
	@$(HEADER) ; timeout $(TIMEOUT) $(cmd) $< >> $$LOGFILE 2>&1 ; $(FOOTER)

$(TSLMT2RPG_SYN_LOGS): %.tslmt2rpg-syn.log : %.tslmt
	@echo "$(cmd) $< $(TIMEOUT)"
	@$(HEADER) ; timeout $(TIMEOUT) $(cmd) $< >> $$LOGFILE 2>&1 ; $(FOOTER)

################################################################################

################################################################################
# Cleanup commands
clean: clean-aux
	@echo "Cleaning up all logs..."
	@find
	-@rm $(SWEAP_LOGS) 2>/dev/null || true
	-@rm $(SWEAP_SEMML_LOGS) 2>/dev/null || true
	-@rm $(SWEAP_RPG_LOGS) 2>/dev/null || true
	-@rm $(SWEAP_TSL_LOGS) 2>/dev/null || true
	-@rm $(SWEAP_ISSY_LOGS) 2>/dev/null || true
	-@rm $(SWEAP_LAZY_LOGS) 2>/dev/null || true
	-@rm $(RPG_STELA_LOGS) 2>/dev/null || true
	-@rm $(TSLMT2RPG_LOGS) 2>/dev/null || true
	-@rm $(TSLMT2RPG_SYN_LOGS) 2>/dev/null || true
	-@rm $(ISSY_RPG_LOGS) 2>/dev/null || true

clean-aux: confirm
	@echo "Cleaning up auxiliary files..."
	-@rm -rf benchmarks/raboniel/*.t 2>/dev/null || true
	-@rm -rf benchmarks/raboniel/*.tsl 2>/dev/null || true
	-@rm -rf benchmarks/raboniel/*.py 2>/dev/null || true
	-@rm -rf benchmarks/raboniel/*.t_R*.tlsf 2>/dev/null || true
	-@rm -rf benchmarks/raboniel/*.t_R*.kiss 2>/dev/null || true

clean-timeouts: confirm
	@echo "Cleaning up logs for experiments that timed out..."
	-@find benchmarks/ -iname "*.log" | xargs tail -n2 | grep -B1 -e '^124$$' -e '^255$$' | grep "==>" | xargs rm -v 2>/dev/null || true
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
	benchmarks/scripts/process_logs.py benchmarks > >(tee benchmarks/results/results.csv) 2> >(tee benchmarks/results/stats.csv)

plots:
	cd benchmarks/scripts; \
	./cactus.py ../results/results.csv

count:
	@echo -n "sweap: " && echo $(SWEAP_BENCHS) | wc -w
	@echo -n "issy: " && echo $(ISSY_BENCHS) | wc -w
	@echo -n "rpg: " && echo $(RPG_BENCHS) | wc -w
	@echo -n "tslmt: " && echo $(TSLMT2RPG_BENCHS) | wc -w

