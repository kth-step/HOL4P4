# PolyGram


Docker ....


## To run PolyGram test cases (Ubuntu 22.04) [SKIP IF YOU ARE USING DOCKER]

This guide assumes a fresh install of Ubuntu 22.04.


You may skip steps for components you already have installed.

First, navigate to the directory where you want to put the source code of Poly/ML and HOL4. Then, in the terminal:

1. Install Poly/ML 5.9.2

		git clone https://github.com/polyml/polyml.git
		cd polyml
		git checkout v5.9.2
		./configure --prefix=/usr
		make
		sudo make install
		cd ..

2. Install HOL4 Trindemossen-2

		git clone https://github.com/HOL-Theorem-Prover/HOL.git
		cd HOL
		git checkout trindemossen-2
		poly < tools/smart-configure.sml
		bin/build
		cd ..
	

	If you want to be able to persistently compile HOL4 theories from anywhere, edit `~/.bashrc`, now adding:
		
		export PATH=$PATH:[installation directory]/HOL/bin
	
	where `[installation directory]` is substituted with the directory you cloned HOL4 in, then
		
		source ~/.bashrc
		
	Otherwise, if you don't want the HOL4 installation to be persistent on your system, simply run

		export PATH=$PATH:[installation directory]/HOL/bin

	in the terminal window you want to be able to compile HOL4 theories from.

		
3. Install CakeML (vHOL-Trindemossen-2) clone into the root of this repository (submit_hol4/):
        
		git clone https://github.com/CakeML/cakeml.git
        cd cakeml
        git checkout vHOL-Trindemossen-2
        cd misc && Holmake && cd ..
        cd basis && Holmake && cd ..
        cd translator && Holmake && cd ..
        cd unverified/sexpr-bootstrap && Holmake && cd ../..


4. Install the CakeML bootstrapped compiler
    Install the bootstrapped CakeML compiler matching the CakeML release for HOL Trindemossen-2 from:

    https://github.com/CakeML/cakeml/releases

    Extract the downloaded files and place them into the following empty folder:

        submit_hol4/hol/polygram/bdd_cake_test/

    Then build:

        cd hol/polygram/bdd_cake_test
        make


5. Make the preprocessing scripts executable
        
		chmod +x hol/polygram/policy_test_cases*/prepp.sh



## Usage

All commands listed here should be run from the root of the repository (submit_hol4/).

### Build

The build steps are incremental and must be run in order:

- `make hol`  compiles the excerpt of HOL4P4 theories that we use in `hol/`
- `make polygram`  compiles the Polygram theories in `hol/polygram/`
- `make cake`  compiles the CakeML translation in `hol/polygram/bdd_cake_trans/`, after this command, there should be 2 sexp files, that we compile when testing next step
- `make test`  runs the preprocessing and testing scripts for the policy test cases in `hol/polygram/policy_test_cases*/`


### For the test cases inspection

1. go to the file of interest (according to the Appendix's evaluation section):





Folder policy_test_cases contains Table II test cases.

    Each test case contains two pipelines

        First: convert_arith_policy_to_interval_tables
        Described in fwd_proofLib

        Second: convert_arith_policy_to_interval_tables_cake 
        defiend in fwd_proof_cakeLib

    Each file also contains the best order and worst order.

    by default, we run CakeML + Best order. To get the other ones (CakeML + worstorder ) (HOL best and worst), edit teh files and uncomment and comment the relenevt parts of the combination in mind.



Folder policy_test_cases_eq contains Table III test cases.
Folder policy_test_cases_gen_policy contains Table IV.  

2. go to the folder and run:
./prepp.sh

    notice that you might need to run 
    chmod +x prepp.sh


3. Once the running is over. 
to view the time logs they are in .hol/log they contain the time stamps (make sure you are in the folder where the test cases are)
   cd .hol/logs
   cat  internet_firewall_1Theory
to view the theorem (make sure you are in the folder where the test cases are), 
and you can only view theorems that succeded in the generation, the failing ones, will not have a xTheory file.
type the following:

    For example 
        cd policy_test_cases    
        hol ....... (you will enter a hol envirounment)
        load "internet_firewall_1Theory"; ........ load the testcase you like to view
        open internet_firewall_1Theory; .............. open theorem
        show_tags := true; ..... to show the hypothesis of the theorem in case used CakeML for MTBDD creation's serialization
        To select:
        internet_firewall_1Theory.policy_trans_fwd; .......... this will show the input to ILR policy translation.
        internet_firewall_1Theory.policy_trans_fwd_proof; ........ proof of input policy equivelnce with ILR
        internet_firewall_1Theory.policy_BDD; ............. policy mtbdd creation
        internet_firewall_1Theory.table_BDD; ............ table mtbdd creation
        internet_firewall_1Theory.table_trans_back; ...... table ILR to table out
        internet_firewall_1Theory.final_proof; ...... final proof theorem (equivelnce between input policy and output p4 table)

        The names of the theorems changes according to the folder as it uses a different pipeline.
        You can see these in the .hol/logs in "saved therem ____ thm_name " 
        thm_name would be the valid name

    
        NOTE: In Folder policy_test_cases_eq and policy_test_cases_gen_policy these are: 
            policy_trans_fwd_1
            policy_trans_fwd_2
            policy_trans_fwd_proof_1
            policy_trans_fwd_proof_2
            policy_BDD_1
            policy_BDD_2
            final_thm



        For checking MTBDD only (Table I) policy_test_cases_mtbdd have three theorems 
             policy_trans_fwd 
            policy_trans_fwd_proof
             policy_BDD 
        

    to exit holmode:
    ctrl + d


To clean up the .hol files in the test cases folders, you type:
Holmake clean
(Notice that this removes the .hol folder as well)

NOTE: for teh sake of teh evaluation, we reduce the time out to 300 seconds instead of 1200 seconds as in the paper.
to change it, go to the prepp file and edit 300s in this line to 1200s :
timeout 300s Holmake "internet_firewall_${i}Theory.uo"






### Pipeline Library Files

The pipeline is assembled according to the use case as described in the paper:


| File | Description | Used in |
|------|-------------|---------|
| **`fwd_proofLib.sml`** | (End to End verified) Policy-to-table pipeline that uses HOL4 `EVAL` for MTBDD construction. | `policy_test_cases` |
| **`fwd_proof_cakeLib.sml`** | Policy-to-table pipeline using CakeML (i.e., serialization is TBB) for MTBDD construction. | `policy_test_cases` |
| **`fwd_proof_policies_cakeLib.sml`** | Takes two policies as input and checks their equivalence. | `policy_test_cases_eq` |
| **`fwd_proof_gen_eq_cakeLib.sml`** | Generates a minimized policy from a given input policy. | `policy_test_cases_gen_policy` |


bdd_policy_cakeLib.sml not a pipeline but contains a acript to run mtbdd creation only for testing



## Theory Files Overview

### Core Theory Files

| File | Description |
|------|-------------|
| **`bdd_genScript.sml`** | **Generalized BDD Framework**. Contains the parametric BDD theory with generic data structures, semantics, construction algorithm (`mk_BDDPred`), optimization algorithm (`optimize_bdd_def`), and the four required properties (`prop1`-`prop4`) that any ILR must satisfy. |
| **`bdd_gen_wfScript.sml`** | **Well-Formedness Preservation**. Proves that the BDD construction algorithm maintains all well-formedness invariants (`BDD_WF`) including distinct keys, edge-label correspondence, leaf labeling conditions, and domain equality. |
| **`bdd_gen_orderScript.sml`** | **Variable Ordering Preservation**. Proves that the construction algorithm preserves the variable ordering invariant (`BDD_ordered`) when variables are eliminated in the given order. |
| **`bdd_gen_correctScript.sml`** | **Semantic Correctness**. Contains the main correctness theorems showing that if the ILR satisfies `prop1`-`prop4`, then the constructed BDD preserves the semantics of the original predicate. |
| **`bdd_gen_mergeScript.sml`** | **Merge Operation**. Proves that merging isomorphic subgraphs preserves well-formedness, ordering, and semantic correctness. |
| **`bdd_gen_eliminateScript.sml`** | **Elimination Operation**. Proves that removing redundant nodes (where both children are identical) preserves all BDD invariants and semantics. |
| **`bdd_gen_optimizationScript.sml`** | **Optimization Algorithm**. Proves correctness of the bottom up optimization algorithm (`optimize_bdd_def`), showing it preserves validity and semantics. |
| **`bdd_gen_isomorphScript.sml`** | **Graph Isomorphism**. Defines BDD isomorphism and proves that isomorphic BDDs have identical semantics under any assignment. |
| **`bdd_end_to_endScript.sml`** | **End-to-End Correctness**. Glues all previous results together, connecting the abstract BDD framework to the concrete ILR policy and table structures. Contains the main executable equivalence theorem. |





