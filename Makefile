# Shortnames we give to the tools
TOOLS := raboniel rpgsolve rpgsolve-syn rpg-stela sweap sweap-noac sweap-nobin temos tslmt2rpg tslmt2rpg-syn
# Timeout for each benchmark, in seconds
TIMEOUT := 1200

# Directory that contains this Makefile
ROOT_DIR := $(dir $(realpath $(firstword $(MAKEFILE_LIST))))

.PHONY: all others everything clean clean-aux clean-timeouts confirm check-ulimit tables plots $(TOOLS)

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
TEMOS_BENCHS := 	$(basename $(wildcard benchmarks/temos/*.tslt))
TSLMT2RPG_BENCHS :=	$(basename $(wildcard benchmarks/tslmt2rpg/*.tslmt))


SWEAP_LOGS :=			$(addsuffix .sweap.log, 			$(SWEAP_BENCHS))
SWEAP_LAZY_LOGS :=		$(addsuffix .sweap-noacc.log, 		$(SWEAP_BENCHS))
SWEAP_NOBIN_LOGS :=		$(addsuffix .sweap-nobin.log,       $(SWEAP_BENCHS))
RPG_STELA_LOGS :=		$(addsuffix .rpg-stela.log,			$(RPG_BENCHS))
RPG_SYN_LOGS :=			$(addsuffix .rpgsolve-syn.log,		$(RPG_BENCHS))
RPG_LOGS :=				$(addsuffix .rpgsolve.log,			$(RPG_BENCHS))
RABONIEL_LOGS :=		$(addsuffix .raboniel.log,			$(RABONIEL_BENCHS))
TEMOS_LOGS :=			$(addsuffix .temos.log,				$(TEMOS_BENCHS))
TSLMT2RPG_LOGS :=		$(addsuffix .tslmt2rpg.log,			$(TSLMT2RPG_BENCHS))
TSLMT2RPG_SYN_LOGS :=	$(addsuffix .tslmt2rpg-syn.log,		$(TSLMT2RPG_BENCHS))

# Tool command-line invocation
$(SWEAP_LOGS): cmd = 			python3 src/main.py --synthesise --p
$(SWEAP_LAZY_LOGS): cmd =		python3 src/main.py --synthesise --lazy --p
$(SWEAP_NOBIN_LOGS): cmd =		python3 src/main.py --synthesise --no_binary_enc --p
$(RPG_STELA_LOGS): cmd = 		rpg-stela solve --enable-no-pruning <
$(RPG_SYN_LOGS): cmd =			rpgsolve --generate-program --disable-log <
$(RPG_LOGS): cmd =				rpgsolve --disable-log <
$(RABONIEL_LOGS): cmd =			./raboniel --spec
$(TEMOS_LOGS): cmd = 			temos.sh
$(TSLMT2RPG_LOGS): cmd =		run-pruned.sh
$(TSLMT2RPG_SYN_LOGS): cmd =	run-pruned-syn.sh

# paths that the tool needs in $PATH
path =							binaries
$(SWEAP_LOGS) : path =			binaries:binaries/CPAchecker-2.3-unix/scripts
$(SWEAP_LAZY_LOGS): path =		binaries:binaries/CPAchecker-2.3-unix/scripts
$(RPG_SYN_LOGS): path =			binaries/z3-4-8:binaries
$(TSLMT2RPG_LOGS): path =		binaries/z3-4-8:binaries
$(TSLMT2RPG_SYN_LOGS): path =	binaries/z3-4-8:binaries
# Because Raboniel will run from binaries/
$(RABONIEL_LOGS): path = 		.

# Set up environment variables, create temporary log file, record start time
define HEADER
	export PYTHONPATH=src/ ;\
	export PATH=$(path):$$PATH ;\
	export FILE=$$(mktemp --suffix .log) ;\
	echo "timeout $(TIMEOUT) $(cmd) $<" >> $$FILE ;\
	starttime=`date +%s%N`
endef

# Record return code and elapsed time, move log file to its final location
define FOOTER
	exitcode=$$? ;\
	endtime=`date +%s%N` ;\
	echo $$exitcode >> $$FILE ;\
	echo $$(((endtime - starttime)/1000000)) >> $$FILE ;\
	mv $$FILE $(ROOT_DIR)/$@
endef

all: raboniel rpgsolve rpgsolve-syn rpg-stela sweap sweap-noacc tslmt2rpg tslmt2rpg-syn
everything: all temos sweap-nobin

sweap:          check-ulimit $(SWEAP_LOGS)
sweap-noacc:    check-ulimit $(SWEAP_LAZY_LOGS)
sweap-nobin:    check-ulimit $(SWEAP_NOBIN_LOGS)
rpg-stela:      check-ulimit $(RPG_STELA_LOGS)
rpgsolve-syn:   check-ulimit $(RPG_SYN_LOGS)
rpgsolve:       check-ulimit $(RPG_LOGS)
raboniel:       check-ulimit $(RABONIEL_LOGS)
temos:          check-ulimit $(TEMOS_LOGS)
tslmt2rpg:      check-ulimit $(TSLMT2RPG_LOGS)
tslmt2rpg-syn:  check-ulimit $(TSLMT2RPG_SYN_LOGS)

################################################################################
# Here are the core commands that run a tool on a benchmark <bench>.<ext>
# and record all output into <bench>.<tool>.log
# The log also contains the exact command line, the return code,
# and the execution time (in ms)

$(SWEAP_LOGS): %.sweap.log: %.prog
	@echo "$(cmd) $< $(TIMEOUT)"
	@$(HEADER) ; timeout $(TIMEOUT) $(cmd) $< >> $$FILE 2>&1 ; $(FOOTER)

$(SWEAP_LAZY_LOGS): %.sweap-noacc.log: %.prog
	@echo "$(cmd) $< $(TIMEOUT)"
	@$(HEADER) ; timeout $(TIMEOUT) $(cmd) $< >> $$FILE 2>&1 ; $(FOOTER)

$(SWEAP_NOBIN_LOGS): %.sweap-nobin.log: %.prog
	@echo "$(cmd) $< $(TIMEOUT)"
	@$(HEADER) ; timeout $(TIMEOUT) $(cmd) $< >> $$FILE 2>&1 ; $(FOOTER)

$(RPG_STELA_LOGS): %.rpg-stela.log : %.rpg
	@echo "$(cmd) $< $(TIMEOUT)"
	@$(HEADER) ; timeout $(TIMEOUT) $(cmd) $< >> $$FILE 2>&1 ; $(FOOTER)

$(RPG_SYN_LOGS): %.rpgsolve-syn.log : %.rpg
	@echo "$(cmd) $< $(TIMEOUT)"
	@$(HEADER) ; timeout $(TIMEOUT) $(cmd) $< >> $$FILE 2>&1 ; $(FOOTER)

$(RPG_LOGS): %.rpgsolve.log : %.rpg
	@echo "$(cmd) $< $(TIMEOUT)"
	@$(HEADER) ; timeout $(TIMEOUT) $(cmd) $< >> $$FILE 2>&1 ; $(FOOTER)

$(RABONIEL_LOGS): %.raboniel.log : %.tslmt
	@echo "$(cmd) $< $(TIMEOUT)"
	@cd binaries ; $(HEADER) ;\
	timeout $(TIMEOUT) $(cmd) $(addprefix ../, $<) >> $$FILE 2>&1 ; $(FOOTER)

$(TEMOS_LOGS): %.temos.log : %.tslt
	@echo "$(cmd) $< $(TIMEOUT)"
	@$(HEADER) ; timeout $(TIMEOUT) $(cmd) $< >> $$FILE 2>&1 ; $(FOOTER)

$(TSLMT2RPG_LOGS): %.tslmt2rpg.log : %.tslmt
	@echo "$(cmd) $< $(TIMEOUT)"
	@$(HEADER) ; timeout $(TIMEOUT) $(cmd) $< >> $$FILE 2>&1 ; $(FOOTER)

$(TSLMT2RPG_SYN_LOGS): %.tslmt2rpg-syn.log : %.tslmt
	@echo "$(cmd) $< $(TIMEOUT)"
	@$(HEADER) ; timeout $(TIMEOUT) $(cmd) $< >> $$FILE 2>&1 ; $(FOOTER)

################################################################################

################################################################################
# Cleanup commands
clean: clean-aux
	@echo "Cleaning up all logs..."
	-@rm $(SWEAP_LOGS) 2>/dev/null || true
	-@rm $(SWEAP_LAZY_LOGS) 2>/dev/null || true
	-@rm $(RPG_LOGS) 2>/dev/null || true
	-@rm $(RPG_SYN_LOGS) 2>/dev/null || true
	-@rm $(RPG_STELA_LOGS) 2>/dev/null || true
	-@rm $(RABONIEL_LOGS) 2>/dev/null || true
	-@rm $(TEMOS_LOGS) 2>/dev/null || true
	-@rm $(TSLMT2RPG_LOGS) 2>/dev/null || true
	-@rm $(TSLMT2RPG_SYN_LOGS) 2>/dev/null || true

clean-aux: confirm
	@echo "Cleaning up auxiliary files..."
	-@rm -rf benchmarks/raboniel/*.t 2>/dev/null || true
	-@rm -rf benchmarks/raboniel/*.tsl 2>/dev/null || true
	-@rm -rf benchmarks/raboniel/*.py 2>/dev/null || true
	-@rm -rf benchmarks/raboniel/*.t_R*.tlsf 2>/dev/null || true
	-@rm -rf benchmarks/raboniel/*.t_R*.kiss 2>/dev/null || true

clean-timeouts: confirm
	@echo "Cleaning up logs for experiments that timed out..."
	-@tail -n2 $(RABONIEL_LOGS) 2>/dev/null | grep -B1 124 | grep "==>" | cut -d ' ' -f2 | xargs rm -v 2>/dev/null || true
	-@tail -n2 $(TEMOS_LOGS) 2>/dev/null | grep -B1 124 | grep "==>" | cut -d ' ' -f2 | xargs rm -v 2>/dev/null || true
	-@tail -n2 $(SWEAP_LOGS) 2>/dev/null | grep -B1 124 | grep "==>" | cut -d ' ' -f2 | xargs rm -v 2>/dev/null || true
	-@tail -n2 $(SWEAP_LAZY_LOGS) 2>/dev/null | grep -B1 124 | grep "==>" | cut -d ' ' -f2 | xargs rm -v 2>/dev/null || true
	-@tail -n2 $(RPG_LOGS) 2>/dev/null | grep -B1 124 | grep "==>" | cut -d ' ' -f2 | xargs rm -v 2>/dev/null || true
	-@tail -n2 $(RPG_SYN_LOGS) 2>/dev/null | grep -B1 124 | grep "==>" | cut -d ' ' -f2 | xargs rm -v 2>/dev/null || true
	-@tail -n2 $(RPG_STELA_LOGS) 2>/dev/null | grep -B1 124 | grep "==>" | cut -d ' ' -f2 | xargs rm -v 2>/dev/null || true
	-@tail -n2 $(TSLMT2RPG_LOGS) 2>/dev/null | grep -B1 124 | grep "==>" | cut -d ' ' -f2 | xargs rm -v 2>/dev/null || true
	-@tail -n2 $(TSLMT2RPG_SYN_LOGS) 2>/dev/null | grep -B1 124 | grep "==>" | cut -d ' ' -f2 | xargs rm -v 2>/dev/null || true

confirm:
	@echo -n "Are you sure? [y/N] " && read ans && [ $${ans:-N} = y ]
################################################################################

ULIM := $(shell ulimit -v)

# Checks whether a memory limit has been set
check-ulimit:
ifeq ("$(ULIM)", "unlimited")
	@echo -n "memory unlimited! Are you sure? [y/N] " && read ans && [ $${ans:-N} = y ]
endif

tables: #$(ALL_LOGS)
	@benchmarks/scripts/process_logs.py benchmarks

plots:
	cd benchmarks/scripts; \
	./cactus.py ../results/results.csv