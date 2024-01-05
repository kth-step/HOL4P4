# Using the Dockerfile

If you want to try out HOL4P4 in a more containerised fashion, you can do so using Docker. First, install Docker which in Ubuntu can be done with

	sudo apt-get install docker.io
	
Then, build and run the Docker image (in the root directory of this repo containing the Dockerfile):

	docker build -t hol4p4 .
	docker run -it hol4p4

# Manual Installation for Ubuntu 22.04

This guide assumes a fresh install of Ubuntu 22.04.

## Dependencies

* HOL4 
* Ott
* Petr4
* Git
* Python 3

## Installation

You may skip steps for components you already have installed.

First, navigate to the directory where you want to put the source code of Poly/ML and HOL4. Then, in the terminal:

1. Install a C compiler, Git and Python 3

		sudo apt-get install build-essential git python3

2. Install Poly/ML 5.9

		git clone https://github.com/polyml/polyml.git
		cd polyml
		git checkout v5.9
		./configure --prefix=/usr
		make
		sudo make install
		cd ..

3. Install HOL4 Kananaskis-14
	
		git clone https://github.com/HOL-Theorem-Prover/HOL.git
		cd HOL
		git checkout kananaskis-14
		poly < tools/smart-configure.sml
		bin/build
		cd ..
	
	If you are annoyed that bin/build gives errors when compiling SAT solvers, you may add the `gcc` flag `-std=c++14` to their respective `Makefile`s. However, these errors should not affect this project.

	If you want to be able to persistently compile HOL4 theories from anywhere, edit `~/.bashrc`, now adding:

		export PATH=$PATH:[installation directory]/HOL/bin
	
	where `[installation directory]` is substituted with the directory you cloned HOL4 in, then

		source ~/.bashrc
		
	Otherwise, if you don't want the HOL4 installation to be persistent on your system, simply run
	
		export PATH=$PATH:[installation directory]/HOL/bin
		
	in the terminal window you want to be able to compile HOL4 theories from.

4. Install OPAM

		sudo apt-get install opam
		opam init
	
	When prompted, make a choice whether to let OPAM set environment variables or not. Then run

		eval $(opam env --switch=default)
	
5. Install Ott 0.32

		opam pin add ott 0.32
		
6. Clone HOL4P4 and install Petr4 0.1.3

	Navigate to the directory where you want to install this repo, and do the following:

		git clone https://github.com/kth-step/HOL4P4.git
		cd HOL4P4
		
	then clone Petr4 in this location (do this even if you intend to use an existing Petr4 installation, this allows HOL4P4 to access example .p4 files for validation):

		git clone https://github.com/verified-network-toolchain/petr4.git
		cd petr4
		git checkout 0.1.3
	
	Then, follow the instructions for installing Petr4 from source [here](https://github.com/verified-network-toolchain/petr4/tree/0.1.3#installing-from-source), using version 0.1.12 of p4pp.
	
	Finally, do
	
		cd ..
		make hol
		
	This will build the HOL4 theories and associated libraries.

You may need to repeat `eval $(opam env)` depending on your choice in step 4 in order to use `ott` in the terminal.

## Building documentation

You can also use `make docs/semantics/main.pdf` to build the documentation of the semantics. This requires some latex dependencies:

	sudo apt-get install texlive

## How to edit and interact with theories

The same tools used to edit HOL4 theories and run the HOL4 REPL can also be used for this project. Specifically, we recommend Emacs - a full guide for using HOL4 with Emacs can be found [here](https://hol-theorem-prover.org/HOL-interaction.pdf).

# Automatic installation scripts for Ubuntu 22.04

The `scripts` directory contains installation scripts. These may be run when installing HOL4P4 e.g. on a fresh virtual machine by

	scripts/install.sh && scripts/install2.sh
