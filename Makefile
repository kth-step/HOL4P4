OTT = ott

default: docs/semantics/main.pdf

hol/p4Script.sml: ott/p4.ott ott/p4_sem.ott ott/p4_types.ott
	cd hol && $(OTT) -i ../ott/p4.ott -i ../ott/p4_sem.ott -i ../ott/p4_types.ott -o p4Script.sml && python3 ./polymorphise_p4Script.py

hol: hol/p4Script.sml hol/ottScript.sml hol/ottLib.sig hol/ottLib.sml
	Holmake -r -I hol

hol/p4_from_json: hol
	Holmake -r -I hol/p4_from_json

validate: hol/p4_from_json
	hol/p4_from_json/p4_from_json.sh validate

fetch_tests:
	hol/p4_from_json/p4_from_json.sh fetch-tests
	
metatheory: hol
	Holmake -r -I hol/metatheory

concurrency: hol/p4_from_json
	Holmake -r -I hol/p4_from_json/concurrency_tests

symb_exec_tests: hol
	Holmake -r -j1 -I hol/symb_exec/tests

docs/semantics/p4_defs.tex: ott/p4.ott
	ott -o $@ -tex_wrap false $< -i ott/p4_sem.ott -i ott/p4_types.ott

docs/semantics/main.pdf: docs/semantics/p4_defs.tex docs/semantics/main.tex docs/semantics/p4.bib
	cd docs/semantics && latexmk -pdf main.tex

clean:
	rm -f docs/semantics/p4_defs.tex hol/p4Script.sml
	cd hol && Holmake clean -r && cd p4_from_json && Holmake clean && cd validation_tests && Holmake clean && cd ../../symb_exec && Holmake clean && cd tests && Holmake clean

.PHONY: default clean hol symb_exec_tests validate fetch_tests
