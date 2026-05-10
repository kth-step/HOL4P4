# PolyGram



## Installations and pre-requists (Ubuntu 22.04) [SKIP IF YOU ARE USING DOCKER]

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

		
3. Install CakeML (vHOL-Trindemossen-2) clone into the root of this repository (HOL4P4/):
        
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

        HOL4P4/hol/polygram/bdd_cake_test/

    Then build:

        cd hol/polygram/bdd_cake_test
        make


5. Make the preprocessing scripts executable
        
		chmod +x hol/polygram/policy_test_cases*/prepp.sh



## Usage

All commands listed here should be run from the root of the repository (HOL4P4/).

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
| Table I - MTBDD creation | `policy_test_cases_mtbdd/` | `bdd_policy_cakeLib.sml` |
| Table II - Policy-to-table | `policy_test_cases/` | `fwd_proofLib.sml` or `fwd_proof_cakeLib.sml` (see commented lines in each file) |
| Table III - Policy equivalence | `policy_test_cases_eq/` | `fwd_proof_policies_cakeLib.sml` |
| Table IV - Policy minimization | `policy_test_cases_gen_policy/` | `fwd_proof_gen_eq_cakeLib.sml` |



---

#### Step 1 - Run the test cases

If you did not `make test` in the build, navigate to the folder of the test cases of interest e.g., `policy_test_cases/` and run:

	cd hol/polygram/policy_test_cases
	./prepp.sh

Repeat for any other folder you want to test (`policy_test_cases_mtbdd`, `policy_test_cases_eq`, `policy_test_cases_gen_policy`).

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

**`policy_test_cases_mtbdd`** (Table I):

	internet_firewall_1Theory.policy_trans_fwd
	internet_firewall_1Theory.policy_trans_fwd_proof
	internet_firewall_1Theory.policy_BDD

To exit the HOL environment:

	ctrl+d

---



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


> `bdd_policy_cakeLib.sml` is not a pipeline but contains a script to run MTBDD creation only for testing (Table I)



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



# Paper's Appendix B in MD format
## Formalization Correspondence

This section maps the definitions, theorems, and algorithms from the paper to their HOL4 mechanization. Each entry is given as `File.sml, lines x–y`.

> **Note:** The implementation may use different names for definitions and theorems than those used in the paper.

---

### Forwarding Languages (Section IV-A)

| Paper Item | File | Lines |
|------------|------|-------|
| Forwarding language structure | `bdd_genScript.sml` | 14–19 |
| Forwarding language properties | `bdd_genScript.sml` | 455–495 |

---

### Policy Language (Section IV-B)

| Paper Item | File | Lines |
|------------|------|-------|
| Policy syntax | `policy_arith_to_varScript.sml` | 20–51 |
| Policy semantics | `policy_arith_to_varScript.sml` | 54–172 |
| Policy ILR syntax | `policy_specScript.sml` | 19–20 |
| | `pred_specScript.sml` | 9–17 |
| Policy ILR semantics | `policy_specScript.sml` | 29–47 |
| ILR policy instantiation | `policy_specScript.sml` | 50–106 |
| ILR policy properties theorems | `policy_specScript.sml` | 115–771 |
| Definition of trans▶ | `policy_arith_to_varScript.sml` | 207–263 |
| Definition of trans◀ | `policy_var_to_arithScript.sml` | 22–60 |
| Theorem 1 (Sound policy translation and retranslation) | `policy_arith_to_varScript.sml` | 311–424 |
| | `policy_var_to_arithScript.sml` | 63–123 |

---

### Network Table Language (Section IV-D)

| Paper Item | File | Lines |
|------------|------|-------|
| Table syntax | `table_arith_to_intervalScript.sml` | 790–792 |
| Table semantics | `table_arith_to_intervalScript.sml` | 979–1017 |
| Table ILR syntax | `table_var_to_arithScript.sml` | 39–41 |
| | `policy_arith_to_varScript.sml` | 30–37 |
| Table ILR semantics | `tables_spec_oldScript.sml` | 133–167 |
| ILR table instantiation | `tables_specScript.sml` | 41–187 |
| ILR table properties theorems | `tables_specScript.sml` | 1920–2570 |
| Definition of trans◀ | `table_arith_to_intervalScript.sml` | 1885–1974 |
| Theorem 2 (Sound table retranslation) | `table_arith_to_intervalScript.sml` | 1979–2025 |

---

### MTBDD Verified Translation (Section V)

| Paper Item | File | Lines |
|------------|------|-------|
| MTBDD syntax | `bdd_genScript.sml` | 21–35 |
| MTBDD well-formedness definition | `bdd_genScript.sml` | 307–320 |
| MTBDD semantics | `bdd_genScript.sml` | 45–85 |
| MTBDD correctness definition | `bdd_genScript.sml` | 437–444 |
| `mk_layer` definition | `bdd_genScript.sml` | 208–235 |
| `mk_layer` correctness theorem | `bdd_gen_correctScript.sml` | 1514–1606 |
| `mk_layer` well-formedness theorem | `bdd_gen_wfScript.sml` | 920–948 |
| `merge` definition | `bdd_genScript.sml` | 640–646 |
| `merge` correctness theorem | `bdd_gen_mergeScript.sml` | 799–814 |
| `merge` well-formedness theorem | `bdd_gen_mergeScript.sml` | 2226–2265 |
| `eliminate` definition | `bdd_genScript.sml` | 650–655 |
| `eliminate` correctness theorem | `bdd_gen_eliminateScript.sml` | 553–570 |
| `eliminate` well-formedness theorem | `bdd_gen_eliminateScript.sml` | 1319–1431 |
| `optimize_mtbdd` definition | `bdd_genScript.sml` | 719–727 |
| `optimize_mtbdd` correctness theorem | `bdd_gen_optimizationScript.sml` | 242–280 |
| `optimize_mtbdd` well-formedness theorem | `bdd_gen_optimizationScript.sml` | 242–280 |
| `mk_mtbdd_opt` definition | `bdd_genScript.sml` | 747–754 |
| Theorem 3 (`mk_mtbdd_opt` correctness) | `bdd_gen_optimizationScript.sml` | 297–375 |
| `mk_mtbdd_opt` well-formedness theorem | `bdd_gen_optimizationScript.sml` | 297–375 |
| `is_isomorphic` definition | `bdd_isomorphScript.sml` | 124–129 |
| Theorem 4 (Isomorphism implies semantic equivalence) | `bdd_isomorphScript.sml` | 502–531 |
| End-to-end semantic equivalence theorem | `bdd_end_to_endScript.sml` | 858–939 |

---

### Implementation and Algorithms (Sections IV-E and VI)

| Paper Item | File | Notes |
|------------|------|-------|
| MTBDD-to-tables algorithm | `bdd_utilsLib.sml` | Lines 850–874. Untrusted SML. |
| Policy minimization algorithm | `bdd_utilsLib.sml` | Lines 1224–1594. Untrusted SML. |
| Translation to CakeML (trusted part) | `bdd_cake_trans/bdd_trans_progScript.sml` | Trusted |
| CakeML serialization & deserialization (TCB) | `bdd_cake_trans/common_parse_cakeml_ProgScript.sml` | Part of Unrusted Code Base. |
| | `bdd_cake_trans/policy_parse_cakeml_ProgScript.sml` | Part of Unrusted Code Base. |
| | `bdd_cake_trans/table_parse_cakeml_ProgScript.sml` | Part of Unrusted Code Base. |
| Output MTBDD creation binaries | `bdd_cake_test/test_bdd_policy` and `bdd_cake_test/test_bdd_table` | Appear after compiling the project. |

---

### Evaluation (Section VII)

| Paper Item | File | Description |
|------------|------|-------------|
| POLYGRAM end-to-end verified variant | `fwd_proofLib.sml` | Instantiated pipeline with policy input and table output. Fully HOL4-verified. |
| POLYGRAM CakeML variant | `fwd_proof_cakeLib.sml` | Policy input and table output using CakeML + serialization/deserialization (TCB). |
| Policy equivalence checking | `fwd_proof_policies_cakeLib.sml` | Instantiated pipeline with policy input and output for checking equality. |
| Policy minimization | `fwd_proof_gen_eq_cakeLib.sml` | Instantiated pipeline for policy minimization. |
| Table I - MTBDD creation times | `policy_test_cases_mtbdd/` | Time logs in `logs for tables in paper/Table I/`. Run `bdd_policy_cakeLib.sml`. |
| Table II - Policy-to-table benchmark | `policy_test_cases/` | Time logs in `logs for tables in paper/Table II/`. Run `fwd_proofLib.sml` or `fwd_proof_cakeLib.sml` depending on commented lines. |
| Table III - Policy equivalence | `policy_test_cases_eq/` | Time logs in `logs for tables in paper/Table III/`. Run `fwd_proof_policies_cakeLib.sml`. |
| Table IV - Policy minimization | `policy_test_cases_gen_policy/` | Time logs in `logs for tables in paper/Table IV/`. Run `fwd_proof_gen_eq_cakeLib.sml`. |


