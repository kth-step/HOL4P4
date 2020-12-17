default: docs/semantics/main.pdf

hol/p4Script.sml: ott/p4.ott
	cd hol && ott -o p4Script.sml ../ott/p4.ott

hol/p4_parserScript.sml: ott/parser_sketch/p4_parser.ott
	cd hol && ott -o p4_parserScript.sml ../ott/parser_sketch/p4_parser.ott

hol: hol/p4Script.sml hol/p4_parserScript.sml hol/ottScript.sml hol/ottLib.sig hol/ottLib.sml
	Holmake -I hol

docs/p4_defs.tex: ott/p4.ott
	ott -o $@ -tex_wrap false $<

docs/parser/main.tex: ott/parser_sketch/p4_parser.ott
	ott -o $@ -tex_wrap false $<

docs/semantics/main.pdf: docs/p4_defs.tex docs/semantics/main.tex docs/semantics/bib.bib
	cd docs/semantics && pdflatex main.tex && bibtex main && pdflatex main.tex && pdflatex main.tex

docs/parser/main.pdf: docs/parser/main.tex
	cd docs/parser && pdflatex main.tex && pdflatex main.tex && pdflatex main.tex

clean:
	rm -f docs/p4_defs.tex hol/p4Script.sml
	cd hol && Holmake clean

.PHONY: default clean hol
