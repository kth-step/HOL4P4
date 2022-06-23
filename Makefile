default: docs/semantics/main.pdf

hol/p4Script.sml: ott/p4.ott
	cd hol && ott -o p4Script.sml ../ott/p4.ott && python ./polymorphise_p4Script.py

hol: hol/p4Script.sml hol/ottScript.sml hol/ottLib.sig hol/ottLib.sml
	Holmake -r -I hol

docs/semantics/p4_defs.tex: ott/p4.ott
	ott -o $@ -tex_wrap false $<

docs/semantics/main.pdf: docs/semantics/p4_defs.tex docs/semantics/main.tex docs/semantics/p4.bib
	cd docs/semantics && latexmk -pdf main.tex

clean:
	rm -f docs/semantics/p4_defs.tex hol/p4Script.sml
	cd hol && Holmake clean

.PHONY: default clean hol
