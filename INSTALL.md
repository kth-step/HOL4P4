# Installation for Ubuntu 22.04

This guide assumes a fresh install of Ubuntu 22.04.

## Dependencies

* HOL4
* Ott
* Python 3
* latexmk (for building documentation)
* ... and their dependencies

## Installation

First, navigate to the directory where you want to put the source code of Poly/ML and HOL4. Then, in the terminal:

1. Install a C compiler and Git

		sudo apt-get install build-essential git

2. Install Poly/ML 5.9

		git clone https://github.com/polyml/polyml.git
		cd polyml
		git checkout v5.9
		./configure --prefix=/usr
		make
		make install
		cd ..

3. Install HOL4 Kananaskis-14
	
		git clone https://github.com/HOL-Theorem-Prover/HOL.git
		cd HOL
		git checkout kananaskis-14
		poly < tools/smart-configure.sml
		bin/build
		cd ..
	
	If you are annoyed that bin/build gives errors when compiling SAT solvers, you may add the `gcc` flag `-std=c++14` to their respective `Makefile`s. However, these errors should not affect this project.

	Again, edit your `.bashrc`, now adding:

		export PATH=$PATH:[installation directory]/HOL/bin
	
	where `[installation directory]` is substituted with your installation directory, then

		source ~/.bashrc

4. Install OPAM

		sudo apt-get install opam
		opam init
	
	When prompted, make a choice whether to let OPAM set environment variables or not. Then run

		eval $(opam env --switch=default)
	
5. Install Ott 0.32

		opam pin add ott 0.32

6. Install Python 3

		sudo apt-get install python3

You may need to repeat `eval $(opam env)` depending on your choice in step 4 in order to use `ott` in the terminal.

Then, navigate to the directory where you want to install this repo, and do the following:

	git clone https://github.com/kth-step/p4ott.git
	cd p4ott
	make hol

This will build the HOL4 theories and associated libraries.

## Building documentation

You can also use `make docs/semantics/main.pdf` to build the documentation of the semantics. This requires some latex dependencies:

	sudo apt-get install texlive

## How to edit and interact with theories

The same tools used to edit HOL4 theories and run the HOL4 REPL can also be used for this project. Specifically, we recommend Emacs - a full guide for using HOL4 with Emacs can be found [here](https://hol-theorem-prover.org/HOL-interaction.pdf).
