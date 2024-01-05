default: docs/semantics/main.pdf

hol/p4Script.sml: ott/p4.ott ott/p4_sem.ott ott/p4_types.ott
	cd hol && ott -i ../ott/p4.ott -i ../ott/p4_sem.ott -i ../ott/p4_types.ott -o p4Script.sml && python3 ./polymorphise_p4Script.py
	
hol: hol/p4Script.sml hol/ottScript.sml hol/ottLib.sig hol/ottLib.sml
	Holmake -r -I hol
	
hol/p4_from_json: hol
	Holmake -r -I hol/p4_from_json
	
validate: hol/p4_from_json
	cd hol/p4_from_json && ./validate.sh
	
concurrency: hol/p4_from_json
	Holmake -r -I hol/p4_from_json/concurrency_tests

docs/semantics/p4_defs.tex: ott/p4.ott
	ott -o $@ -tex_wrap false $< -i ott/p4_sem.ott -i ott/p4_types.ott

docs/semantics/main.pdf: docs/semantics/p4_defs.tex docs/semantics/main.tex docs/semantics/p4.bib
	cd docs/semantics && latexmk -pdf main.tex

clean:
	rm -f docs/semantics/p4_defs.tex hol/p4Script.sml
	cd hol && Holmake clean -r && cd p4_from_json && Holmake clean && cd validation_tests && Holmake clean

.PHONY: default clean hol
