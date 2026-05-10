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


### For the Test Cases Inspection

The time logs for all tables are saved under `logs_for_tables_in_paper/` in the corresponding subfolder (`Table I`, `Table II`, `Table III`, `Table IV`).

The test case folders and the scripts they run are as follows:

| Table | Folder | Script(s) |
|-------|--------|-----------|
| Table I - MTBDD creation | `bdd_creation_test_cases/` | `bdd_policy_cakeLib.sml` |
| Table II - Policy-to-table | `policy_test_cases/` | `fwd_proofLib.sml` or `fwd_proof_cakeLib.sml` (see commented lines in each file) |
| Table III - Policy equivalence | `policy_test_cases_eq/` | `fwd_proof_policies_cakeLib.sml` |
| Table IV - Policy minimization | `policy_test_cases_gen_policy/` | `fwd_proof_gen_eq_cakeLib.sml` |



---

#### Step 1 - Run the test cases

If you did not `make test` in the build, navigate to the folder of the test cases of interest e.g., `policy_test_cases/` and run:

	cd hol/polygram/policy_test_cases
	./prepp.sh

Repeat for any other folder you want to test (`bdd_creation_test_cases`, `policy_test_cases_eq`, `policy_test_cases_gen_policy`).

---

#### Step 2 - View the time logs

Once the run completes, the time logs are stored in `.hol/logs/` inside the test case folder. For example (you can also see the theorems names being stored there):

	cd .hol/logs
	cat internet_firewall_1Theory

---

#### Step 3 - View the theorems

Only test cases that completed successfully will have a generated theory file. To inspect a theorem, first launch HOL from the test case folder:

	cd hol/polygram/policy_test_cases
	hol

Then, inside the HOL environment, load and open the theory of interest:

	load "internet_firewall_1Theory";
	open internet_firewall_1Theory;
	show_tags := true;

The available theorems differ by folder. Check `.hol/logs/` for lines beginning with `saved theorem` to confirm valid theorem names. For reference:

**`policy_test_cases`** (Table II):

	internet_firewall_1Theory.policy_trans_fwd
	internet_firewall_1Theory.policy_trans_fwd_proof
	internet_firewall_1Theory.policy_BDD
	internet_firewall_1Theory.table_BDD
	internet_firewall_1Theory.table_trans_back
	internet_firewall_1Theory.final_proof

**`policy_test_cases_eq`** and **`policy_test_cases_gen_policy`** (Tables III & IV):

	internet_firewall_1Theory.policy_trans_fwd_1
	internet_firewall_1Theory.policy_trans_fwd_2
	internet_firewall_1Theory.policy_trans_fwd_proof_1
	internet_firewall_1Theory.policy_trans_fwd_proof_2
	internet_firewall_1Theory.policy_BDD_1
	internet_firewall_1Theory.policy_BDD_2
	internet_firewall_1Theory.final_thm

**`bdd_creation_test_cases`** (Table I):

	internet_firewall_1Theory.policy_trans_fwd
	internet_firewall_1Theory.policy_trans_fwd_proof
	internet_firewall_1Theory.policy_BDD

To exit the HOL environment:

	ctrl+d

---

#### Step 4 - Cleanup

To remove generated `.hol` files from a test case folder:

	Holmake clean


> **Note on Table II (`policy_test_cases`):** To replicate the full Table II results from the paper,  each test case file must be run four times - once per combination of pipeline and variable ordering. Each file contains clearly marked lines for all four combinations; simply comment/uncomment the relevant lines before each run:

| Combination | Pipeline | Ordering |
|-------------|----------|----------|
| ✅ Default (as shipped) | CakeML - `convert_arith_policy_to_interval_tables_cake` in(`fwd_proof_cakeLib.sml`) | Best order |
| | CakeML - `convert_arith_policy_to_interval_tables_cake` in (`fwd_proof_cakeLib.sml`) | Worst order |
| | HOL4 EVAL - `convert_arith_policy_to_interval_tables` in (`fwd_proofLib.sml`) | Best order |
| | HOL4 EVAL - `convert_arith_policy_to_interval_tables` in (`fwd_proofLib.sml`) | Worst order |

> **Note:** For evaluation purposes, the timeout is set to 300 seconds (vs. 1200 seconds in the paper). To change it, edit `prepp.sh` and update:
> ```
> timeout 300s Holmake "internet_firewall_${i}Theory.uo"
> ```


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





