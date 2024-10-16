# Shortnames we give to the tools
TOOLS := raboniel rpgsolve rpgsolve-syn rpg-stela sweap sweap-noacc temos
# Timeout for each benchmark, in seconds
TIMEOUT := 1200

# Directory that contains this Makefile
ROOT_DIR:=$(dir $(realpath $(firstword $(MAKEFILE_LIST))))

.PHONY: all others everything clean clean-aux clean-timeouts confirm $(TOOLS)

# Paths to benchmark files
SWEAP_BENCHS := 	$(basename $(wildcard benchmarks/sweap/*.prog))
SWEAP_BENCHS += 	$(basename $(wildcard benchmarks/sweap/drafts/*.prog))
RPG_BENCHS := 		$(basename $(wildcard benchmarks/rpgsolve/*.rpg))
RABONIEL_BENCHS := 	$(basename $(wildcard benchmarks/raboniel/*.tslmt))
TEMOS_BENCHS := 	$(basename $(wildcard benchmarks/temos/*.tslt))

SWEAP_LOGS := 		$(addsuffix .sweap.log, 			$(SWEAP_BENCHS))
SWEAP_LAZY_LOGS := 	$(addsuffix .sweap-noacc.log, 		$(SWEAP_BENCHS))
RPG_STELA_LOGS := 	$(addsuffix .rpg-stela.log,			$(RPG_BENCHS))
RPG_SYN_LOGS := 	$(addsuffix .rpgsolve-syn.log,		$(RPG_BENCHS))
RPG_LOGS := 		$(addsuffix .rpgsolve.log,			$(RPG_BENCHS))
RABONIEL_LOGS :=	$(addsuffix .raboniel.log,			$(RABONIEL_BENCHS))
TEMOS_LOGS :=		$(addsuffix .temos.log,				$(TEMOS_BENCHS))

SWEAP_CMD := python3 main.py --synthesise


# Tool command-line invocation
$(SWEAP_LOGS): cmd = 		python3 main.py --synthesise --accelerate --p
$(SWEAP_LAZY_LOGS): cmd = 	python3 main.py --synthesise --p
$(RPG_STELA_LOGS): cmd = 	rpg-stela solve --enable-no-pruning <
$(RPG_SYN_LOGS): cmd = 		rpgsolve --generate-program <
$(RPG_LOGS): cmd = 			rpgsolve <
$(RABONIEL_LOGS): cmd = 	./raboniel --spec
$(TEMOS_LOGS): cmd = 		temos.sh

# paths that the tool needs in $PATH
path = 						binaries
$(SWEAP_LOGS) : path = 		binaries:binaries/CPAchecker-2.3-unix/scripts
$(SWEAP_LAZY_LOGS): path = 	binaries:binaries/CPAchecker-2.3-unix/scripts
$(RPG_SYN_LOGS): path = 	binaries/z3-4-8:binaries
$(RABONIEL_LOGS): path = 	. 	# Because Raboniel will run from binaries/

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

all: raboniel rpgsolve rpgsolve-syn rpg-stela sweap sweap-noacc
everything: all temos

sweap: $(SWEAP_LOGS)
sweap-noacc: $(SWEAP_LAZY_LOGS)
rpg-stela: $(RPG_STELA_LOGS)
rpgsolve-syn: $(RPG_SYN_LOGS)
rpgsolve: $(RPG_LOGS)
raboniel: $(RABONIEL_LOGS)
temos: $(TEMOS_LOGS)

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

confirm:
	@echo -n "Are you sure? [y/N] " && read ans && [ $${ans:-N} = y ]
################################################################################
