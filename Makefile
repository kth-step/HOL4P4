default: docs/semantics/main.pdf

hol/p4Script.sml: ott/p4.ott
	cd hol && ott -o p4Script.sml ../ott/p4.ott

hol/p4parserScript.sml: ott/p4parser.ott
	cd hol && ott -o p4parserScript.sml ../ott/p4parser.ott

hol/p4newScript.sml: ott/p4_march.ott
	cd hol && ott -o p4newScript.sml ../ott/p4_march.ott

hol: hol/p4Script.sml hol/p4parserScript.sml hol/p4newScript.sml hol/ottScript.sml hol/ottLib.sig hol/ottLib.sml
	Holmake -I hol

docs/p4_defs.tex: ott/p4.ott
	ott -o $@ -tex_wrap false $<

docs/parser/main.tex: ott/p4parser.ott
	ott -o $@ $<

docs/semantics/main.pdf: docs/p4_defs.tex docs/semantics/main.tex docs/semantics/bib.bib
	cd docs/semantics && pdflatex main.tex && bibtex main && pdflatex main.tex && pdflatex main.tex

docs/parser/main.pdf: docs/parser/main.tex
	cd docs/parser && pdflatex main.tex && pdflatex main.tex && pdflatex main.tex

docs/pnp_sem/p4_parser_defs.tex: ott/p4parser.ott
	ott -o $@ -tex_wrap false $<

docs/pnp_sem_new/p4_new_defs.tex: ott/p4_march.ott
	ott -o $@ -tex_wrap false $<

clean:
	rm -f docs/p4_defs.tex hol/p4Script.sml hol/p4parserScript.sml
	cd hol && Holmake clean

.PHONY: default clean hol
