# PolyGram


## To check PolyGram theorems:
        Holmake

## To run PolyGram test cases (Ubuntu 22.04)

This guide assumes a fresh install of Ubuntu 22.04.

1. Install CakeML (vHOL-Trindemossen-2) clone into the HOL4P4 folder:
        
		git clone https://github.com/CakeML/cakeml.git
        cd cakeml
        git checkout vHOL-Trindemossen-2
        cd misc && Holmake && cd ..
        cd basis && Holmake && cd ..
        cd translator && Holmake && cd ..
        cd unverified/sexpr-bootstrap && Holmake && cd ../..


2. Install the CakeML bootstrapped compiler
    Install the bootstrapped CakeML compiler matching the CakeML release for HOL Trindemossen-2 from:

    https://github.com/CakeML/cakeml/releases

    Extract the downloaded files and place them into the following empty folder:

        bdd_cake_test

    Then build:

        cd bdd_cake_test
        make


3. Make the preprocessing scripts executable
        
		chmod +x policy_test_cases*/prepp.sh




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



### Pipeline Library Files

The pipeline is assembled according to the use case as described in the paper:


| File | Description | Used in |
|------|-------------|---------|
| **`fwd_proof_cakeLib.sml`** | Policy-to-table pipeline using CakeML for MTBDD construction. | `policy_test_cases` |
| **`fwd_proofLib.sml`** | Policy-to-table pipeline using HOL4 `EVAL` for MTBDD construction. | `policy_test_cases` |
| **`fwd_proof_policies_cakeLib.sml`** | Takes two policies as input and checks their equivalence. | `policy_test_cases_eq` |
| **`fwd_proof_gen_eq_cakeLib.sml`** | Generates a minimized policy from a given input policy. | `policy_test_cases_gen_policy` |


## Test Case Output

For more detailed information on what is happening during each test case, inspect the `.hol/` directory inside each test case folder (for example `hol/polygram/policy_test_cases/.hol/`). Inside `.hol/log/`, each theorem has its own log file containing timing statistics for each stage of the pipeline.


