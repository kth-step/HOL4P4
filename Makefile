default: docs/semantics/main.pdf

hol/p4Script.sml: ott/p4.ott ott/p4_sem.ott ott/p4_types.ott
	cd hol && ott -i ../ott/p4.ott -i ../ott/p4_sem.ott -i ../ott/p4_types.ott -o p4Script.sml && python3 ./polymorphise_p4Script.py
	
hol: hol/p4Script.sml hol/ottScript.sml hol/ottLib.sig hol/ottLib.sml
	Holmake -r -I hol
	
hol/arch: hol
	Holmake -r -I hol/arch
	
hol/exec: hol
	Holmake -r -I hol/exec
	
hol/test_tools: hol hol/arch hol/exec
	Holmake -r -I hol/test_tools
	
hol/concurrency: hol hol/test_tools
	Holmake -r -I hol/concurrency

hol/deter: hol hol/exec
	Holmake -r -I hol/deter
	
hol/examples: hol hol/arch hol/test_tools
	Holmake -r -I hol/examples

hol/import_tool: hol hol/arch
	Holmake -r -I hol/import_tool
	
hol/progress_preservation: hol hol/deter
	Holmake -r -I hol/progress_preservation
	
hol/symb_exec: hol hol/exec hol/test_tools
	Holmake -r -I hol/symb_exec

validate: hol/import_tool
	cd hol/import_tool && ./validate.sh
	
concurrency_tests: hol/import_tool hol/test_tools hol/concurrency
	Holmake -r -I hol/import_tool/concurrency_tests

docs/semantics/p4_defs.tex: ott/p4.ott
	ott -o $@ -tex_wrap false $< -i ott/p4_sem.ott -i ott/p4_types.ott

docs/semantics/main.pdf: docs/semantics/p4_defs.tex docs/semantics/main.tex docs/semantics/p4.bib
	cd docs/semantics && latexmk -pdf main.tex

clean:
	rm -f docs/semantics/p4_defs.tex hol/p4Script.sml
	cd hol && Holmake -r cleanAll && \
	cd arch && Holmake cleanAll && cd .. && \
	cd concurrency && Holmake cleanAll && cd .. && \
	cd deter && Holmake cleanAll && cd .. && \
	cd examples && Holmake cleanAll && cd .. && \
	cd exec && Holmake cleanAll && cd .. && \
	cd progress_preservation && Holmake cleanAll && cd .. && \
	cd symb_exec && Holmake cleanAll && cd .. && \
	cd test_tools && Holmake cleanAll && cd .. && \
	cd import_tool && Holmake cleanAll && \
	cd concurrency_tests && Holmake cleanAll && cd .. && \
	cd validation_tests && Holmake cleanAll \

.PHONY: default clean hol
