OTT = ott

default: hol

hol/p4Script.sml: ott/p4.ott ott/p4_sem.ott ott/p4_types.ott
	cd hol && $(OTT) -i ../ott/p4.ott -i ../ott/p4_sem.ott -i ../ott/p4_types.ott -o p4Script.sml && python3 ./polymorphise_p4Script.py

hol: hol/p4Script.sml hol/ottScript.sml hol/ottLib.sig hol/ottLib.sml
	Holmake -r -I hol

hol_tests: hol
	Holmake -r -I hol/tests

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

docs: docs/semantics/main.pdf

docs/semantics/p4_defs.tex: ott/p4.ott
	ott -o $@ -tex_wrap false $< -i ott/p4_sem.ott -i ott/p4_types.ott

docs/semantics/main.pdf: docs/semantics/p4_defs.tex docs/semantics/main.tex docs/semantics/p4.bib
	cd docs/semantics && latexmk -pdf main.tex

# Every directory with a Holmakefile; hol is cleaned recursively to cover hol/eval
HOLDIRS = hol/tests hol/metatheory hol/p4_from_json hol/p4_from_json/validation_tests hol/p4_from_json/concurrency_tests \
          hol/symb_exec hol/symb_exec/tests hol/symb_exec/imp hol/symb_exec/example_ipsec

clean:
	rm -f docs/semantics/p4_defs.tex hol/p4Script.sml
	cd hol && Holmake clean -r
	for d in $(HOLDIRS); do (cd $$d && Holmake clean) || exit 1; done

.PHONY: default docs clean hol hol_tests hol/p4_from_json validate fetch_tests metatheory concurrency symb_exec_tests
