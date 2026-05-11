# PolyGram

This is the artifact for the paper **"PolyGram: A Certifying Compiler for Network Policies"** submitted to FMCAD 2026.

PolyGram is a certifying compiler for network forwarding policies. It takes a high-level policy as input and produces equivalent P4 match-action tables (or minimized policies), together with a machine-checked proof of semantic equivalence between the input policy and the generated forwarding. The proofs are mechanized in HOL4 and the MTBDD construction is additionally compiled to a verified CakeML binary.

This artifact contains:
- The HOL4 proof scripts for the PolyGram formalization
- The verified CakeML compiler pipeline
- Benchmark test cases reproducing the results from the paper (Tables I-IV)
- Interactive examples for exploring and extending the pipeline

## Artifact Overview

### Structure and Content

```
HOL4P4/
├── Dockerfile                        # Builds the self-contained artifact environment
├── LICENSE-APACHE                    # Apache 2.0 license
├── LICENSE-BSD                       # BSD 3-Clause license
├── COPYRIGHT                         # Copyright notice
├── Makefile                          # Top-level build file (make hol/polygram/cake/test)
├── cakeml/                           # CakeML installation (vHOL-Trindemossen-2)
├── hol/
│   ├── Holmakefile                   # HOL4 build file for HOL4P4 excerpt
│   ├── p4Script.sml                  # HOL4P4 dependency
│   ├── p4_auxScript.sml              # HOL4P4 dependency
│   └── polygram/
│       ├── Holmakefile               # HOL4 build file for PolyGram
│       ├── bdd_genScript.sml         # Generalized BDD framework
│       ├── ...					      # Other files
│       ├── bdd_gen_eliminateScript.sml # Elimination operation proofs
│       ├── fwd_proofLib.sml          # HOL4 EVAL pipeline
│       ├── fwd_proof_cakeLib.sml     # CakeML pipeline
│       ├── fwd_proof_policies_cakeLib.sml # Policy equivalence checker
│       ├── fwd_proof_gen_eq_cakeLib.sml   # Policy minimization
│       ├── bdd_cake_trans/           # CakeML translation scripts (trusted)
│       ├── bdd_cake_test/            # CakeML compiled binaries
│       ├── logs_for_tables_in_paper/ # Pre-run logs matching paper tables
│       ├── policy_test_cases*/       # Benchmark test case folders
│       └── reviewers_test_here/      # Interactive examples for reviewers
│           ├── paper_example_cakeml_bestScript.sml
│           ├── paper_example_cakeml_worstScript.sml
│           ├── paper_example_hol4_bestScript.sml
│           ├── paper_example_hol4_worstScript.sml
│           ├── policy_equiv_exampleScript.sml
│           ├── policy_min_exampleScript.sml
│           └── prepp.sh
```

---

## Resource Requirements

- **RAM:** 16 GB minimum
- **CPU cores:** 4+ cores recommended
- **Disk:** ~20 GB for the full Docker image (HOL4 + CakeML + artifact)
- **Time estimates (inside Docker):**

| Step | Command | Expected time |
|------|---------|---------------|
| HOL4P4 theories | `make hol` | ~30s |
| PolyGram theories | `make polygram` | ~1320s (`table_bs_propertiesTheory` alone takes ~10 min) |
| CakeML translation | `make cake` | ~800s |
| Benchmark test cases | `make test` | ~4000s |

---

## Setup: Using Docker (Recommended)

Docker provides a fully pre-installed environment ; you do **not** need to install HOL4, CakeML, or Poly/ML yourself.

### Step 1: Install Docker

If you do not have Docker installed, run:

```bash
sudo apt-get update
sudo apt-get install -y docker.io
```

Verify Docker is installed:

```bash
docker --version
```

Unzip the artifact:

```bash
gunzip polygram-artifact.tar.gz
```

### Step 2: Load the artifact image

```bash
docker load < polygram-artifact.tar
```

You should see: `Loaded image: polygram-artifact:fmcad2026`

### Step 3: Run the container

```bash
docker run -it polygram-artifact:fmcad2026
```

You will land inside the container at `/HOL4P4`, with HOL4, CakeML, and all dependencies ready. The theories are pre-built ; you can start inspecting immediately.

> **Note for Apple Silicon (M1/M2/M3) users:** Run with:
> ```bash
> docker run --platform linux/amd64 -it polygram-artifact:fmcad2026
> ```



## Installations and Prerequisites (Ubuntu 22.04)
> ⚠️ **WARNING:** ⚠️ **Skip this section if you are using Docker.**

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


<br>
<br>
<br>

---
## Usage

All commands listed here should be run from the root of the repository (HOL4P4/).

### 1. Build

> ⚠️ **WARNING: If you are using Docker, skip this section entirely and jump to [Inspecting the Paper's Test Cases](#2-inspecting-the-papers-test-cases).** ⚠️ The Docker image ships with everything pre-built: HOL4 theories, CakeML binaries, and all benchmark test cases are already compiled and ready to inspect.

The build steps below are provided for reproducibility only. They are time-consuming and cannot be interrupted mid-way. If you just want to explore the artifact, the Docker image is the right choice.

However, if you still want to rebuild from scratch, first clean the existing build:

```bash
make clean
```

Then run the steps in order:

- `make hol` compiles the excerpt of HOL4P4 theories that we use in `hol/`, expected time: ~30s.
- `make polygram` compiles the Polygram theories in `hol/polygram/`, expected time: ~1320s, (`table_bs_propertiesTheory` takes 10 minutes due to the long heavy proofs).
- `make cake` compiles the CakeML translation in `hol/polygram/bdd_cake_trans/`, after this command, there should be 2 sexp files in the repository `bdd_cake_test`, that we compile when testing next step, expected time: ~800s.
- `make test` runs all benchmark test cases in `hol/polygram/policy_test_cases*/`, expected time: ~4000s or more.


<br>
<br>

### 2. Inspecting the Paper's Test Cases

The time logs for all tables in the paper are saved under `logs_for_tables_in_paper/` in the corresponding subfolder (`Table_I`, `Table_II`, `Table_III`, `Table_IV`).

```bash
cd /HOL4P4/hol/polygram/logs_for_tables_in_paper/
ls
# you should see: Table_I  Table_II  Table_III  Table_IV

cd Table_II/
ls
# you should see: cakeml_best_order  cakeml_worst_order  hol4_best_order  hol4_worst_order

cd cakeml_best_order/
ls
# you should see the log files, one per test case

cat internet_firewall_1Theory
# shows the time log and saved theorem names for that test case
```


#### General description:
The test case folders and the scripts they run are as follows:

| Table | Folder | Script(s) |
|-------|--------|-----------|
| Table I - MTBDD creation | `policy_test_cases_mtbdd/` | `bdd_policy_cakeLib.sml` |
| Table II - Policy-to-table | `policy_test_cases_cakeml_best/` `policy_test_cases_cakeml_worst/` `policy_test_cases_hol4_best/` `policy_test_cases_hol4_worst/`| `fwd_proofLib.sml` for hol4 or `fwd_proof_cakeLib.sml` for cakeml |
| Table III - Policy equivalence | `policy_test_cases_eq/` | `fwd_proof_policies_cakeLib.sml` |
| Table IV - Policy minimization | `policy_test_cases_gen_policy/` | `fwd_proof_gen_eq_cakeLib.sml` |


The following steps show how to inspect the compiled theories inside the Docker image.
To inspect the contents of the files, we exemplify using `policy_test_cases_cakeml_best/internet_firewall_1.sml`, we add further instructions for other test case folders when needed:








#### Step 1 - Navigate to the folder of interest

Navigate to the folder of the test cases of interest e.g., `policy_test_cases_cakeml_best/`, run:

```bash
cd /HOL4P4/hol/polygram/policy_test_cases_cakeml_best

# You can skip the following re-run, 
# as this is pre-built version you are using :)
./prepp.sh
```

Repeat for any other folder you want to test/inspect later (`policy_test_cases_mtbdd`, `policy_test_cases_eq`, `policy_test_cases_gen_policy`...`policy_test_cases_*`).


> **Note:** For evaluation purposes, the timeout is set here to 20 seconds (vs. 1200 seconds in the paper). If you feel like you want to change it, edit `prepp.sh` and update (20s to 1200s) in this line:
> ```
> timeout 20s Holmake "internet_firewall_${i}Theory.uo"
> ```



#### Step 2 - View the time logs

Once the run completes (if you are using docker this is pre-done), the time logs being generated are stored in `.hol/logs/` inside the test case folder. For example (you can also see the *theorems names* being stored in HOL4 there):

```bash
cd /HOL4P4/hol/polygram/policy_test_cases_cakeml_best/.hol/logs
ls
cat internet_firewall_1Theory
```

For each successfully compiled `.sml` file (e.g., `internet_firewall_1Script.sml`), a corresponding theory file (`internet_firewall_1Theory`) is generated.



#### Step 3 - View the theorems

> **Note:** Only test cases `xScript.sml` that completed successfully will have a generated theory file `xTheory`. To inspect a theorem, first launch HOL from the test case folder:

```bash
cd /HOL4P4/hol/polygram/policy_test_cases_cakeml_best/

# Enter HOL4 mode via:
hol
```

Then, inside the HOL environment, load and open the theory of interest:

```sml
	load "internet_firewall_1Theory";
	open internet_firewall_1Theory;
	show_tags := true;
```

Display a theorem (type this):

```sml
	internet_firewall_1Theory.policy_trans_fwd_proof;
```

This will show the translation proof between input policy forwarding and its ILR representation.
> **Note:** It is easy to miss the semi-colon at the end, please do not forget to add it.

The available theorems differ by folder. The available theorems differ by folder. Check `.hol/logs/` for lines beginning with `saved theorem` to confirm valid theorem names see [Step 2](#step-2---view-the-time-logs) to confirm valid theorem names *or here we have a reference*:




In folders **`policy_test_cases_cakeml_best`**, **`policy_test_cases_cakeml_worst`**, **`policy_test_cases_hol4_best`** and **`policy_test_cases_hol4_worst`** for firewall (e.g., `internet_firewall_1Theory` to find them write `ls -la`) (Table II):
- `internet_firewall_1Theory.policy_trans_fwd;` -> trans-fwd result
- `internet_firewall_1Theory.policy_trans_fwd_proof;` -> soundness of trans-fwd (Theorem 1)
- `internet_firewall_1Theory.policy_BDD;` -> MTBDD1 result 
- `internet_firewall_1Theory.table_BDD;` -> MTBDD2 result 
- `internet_firewall_1Theory.table_trans_back;` -> trans-back soundness (Theorem 2)
- `internet_firewall_1Theory.final_proof;` -> end-to-end equivalence proof between policy and a table

In folder **`policy_test_cases_eq`** and **`policy_test_cases_gen_policy`** for firewall (e.g., `internet_firewall_xTheory` where `x` is a number, to check them type `ls -la`) (Tables III & IV):
- `internet_firewall_xTheory.policy_trans_fwd_1;` -> trans-fwd result for policy 1 
- `internet_firewall_xTheory.policy_trans_fwd_2;` -> trans-fwd result for policy 2 
- `internet_firewall_xTheory.policy_trans_fwd_proof_1;` -> soundness of trans-fwd for policy 1 (Theorem 1)
- `internet_firewall_xTheory.policy_trans_fwd_proof_2;` -> soundness of trans-fwd for policy 2 (Theorem 1)
- `internet_firewall_xTheory.policy_BDD_1;` -> MTBDD1 from policy 1 
- `internet_firewall_xTheory.policy_BDD_;` -> MTBDD2 from policy 2 
- `internet_firewall_xTheory.final_proof;` -> end-to-end equivalence between the two policies 

In folder **`policy_test_cases_mtbdd`** (Table I) for firewall (e.g., `internet_firewall_xTheory` where `x` is a number, to check them type `ls -la`):
- `internet_firewall_xTheory.policy_trans_fwd;` -> trans-fwd result
- `internet_firewall_xTheory.policy_trans_fwd_proof;` -> soundness of trans-fwd (Theorem 1)
- `internet_firewall_xTheory.policy_BDD;` -> MTBDD result



> **Note on Table II (folders **`policy_test_cases_cakeml_best`**, **`policy_test_cases_cakeml_worst`**, **`policy_test_cases_hol4_best`** and **`policy_test_cases_hol4_worst`**):**

| Combination | Pipeline used | Ordering |
|-------------|----------|----------|
| **`policy_test_cases_cakeml_best`** | CakeML (+ serialization trusted oracle) - `convert_arith_policy_to_interval_tables_cake` in(`fwd_proof_cakeLib.sml`) | Best order |
| **`policy_test_cases_cakeml_worst`**  | CakeML (+ serialization trusted oracle) - `convert_arith_policy_to_interval_tables_cake` in (`fwd_proof_cakeLib.sml`) | Worst order |
| **`policy_test_cases_hol4_best`** | HOL4 fully verified - `convert_arith_policy_to_interval_tables` in (`fwd_proofLib.sml`) | Best order |
| **`policy_test_cases_hol4_worst`** | HOL4 fully verified - `convert_arith_policy_to_interval_tables` in (`fwd_proofLib.sml`) | Worst order |




#### Step 4 - Exit HOL4

To exit the HOL environment:

	Ctrl+d



<br>
<br>
<br>

## Try PolyGram Yourself

### 1. Running the Paper Example

The running example from the paper (Figures 1, 4, and 5) is in `hol/polygram/reviewers_test_here/`. It contains four variants combining two pipeline types (CakeML binary or HOL4 EVAL) and two variable orders (best or worst):

- `paper_example_cakeml_bestScript.sml`
- `paper_example_cakeml_worstScript.sml`
- `paper_example_hol4_bestScript.sml`
- `paper_example_hol4_worstScript.sml`

To run all four variants:

```bash
cd /HOL4P4/hol/polygram/reviewers_test_here

#check the 4 examples variants:
ls

# You can skip the following re-run, 
# as this is pre-built version you are using :)
./prepp.sh
```

This compiles the CakeML binary and runs all four variants. Each variant produces a HOL4 theory file with the verified theorems.

#### Inspecting the Example Files

To open and inspect a variant:

```bash
micro paper_example_cakeml_bestScript.sml
```

Inside, you will find:

- **Packet type descriptor** : encodes the bit-vector width of each header field (line 45)
- **Atomic predicates** : e.g. `x1` for `ip.dst >= 10.0.0.0`, declared as HOL4 deep embeddings (lines 56-17)
- **Mapping m** (`atoms_map`) : maps variable names to atomic predicates (same as in Figure 4) (lines 89-97)
- **Policy rules** : the five rules from Figure 1, in order (lines 100-132)
- **Variable order and grouping** : controls MTBDD construction (Section V) (lines 160-168)
- **Pipeline invocation** : calls either `fwd_proof_cakeLib` (CakeML) or `fwd_proofLib` (HOL4 EVAL) (lines 185)

> **Note:** The policy is encoded as a HOL4 deep embedding. This keeps the pipeline free from untrusted compiler dependencies, at the cost of some verbosity.

> **Note:** The line number differs according to the test case, these are for `paper_example_cakeml_bestScript.sml`


To exit micro
Ctrl+q


#### Checking the Output

Inspect the generated theorems interactively:

```bash
	cd /HOL4P4/hol/polygram/reviewers_test_here
	hol
```

Then inside the HOL4 interactive session:

```sml
load "paper_example_cakeml_worstTheory";
open paper_example_cakeml_worstTheory;
show_tags := true;
```

You should see the following theorems:

- `paper_example_cakeml_worstTheory.policy_trans_fwd;` -> trans-fwd result
- `paper_example_cakeml_worstTheory.policy_trans_fwd_proof;` -> soundness of trans-fwd (Theorem 1)
- `paper_example_cakeml_worstTheory.policy_BDD;` -> MTBDD1 result 
- `paper_example_cakeml_worstTheory.table_BDD;` -> MTBDD2 result 
- `paper_example_cakeml_worstTheory.table_trans_back;` -> trans-back soundness (Theorem 2, you will see the tables here)
- `paper_example_cakeml_worstTheory.final_proof;` -> end-to-end equivalence proof between policy and a table


When you view the theorems, `paper_example_hol4_*` will show 

    ⊢ THM_CONTENT

whereas checking `paper_example_cakeml_*` will show

	[oracles: CakeML_policy_TCB, DISK_THM] [axioms: ] []
    ⊢ THM_CONTENT

The oracle tag `CakeML_policy_TCB` makes the trust assumption explicit: the CakeML binary implements verified `mk_mtbdd_opt` (Theorem 3), but the text file I/O between HOL4 and the binary is not verified and constitutes the TCB.

To exit HOL4:

Ctrl+d


---
<br>


### 2. Extending the Running Example

#### Adding a Rule

Open the variant you want to modify:

```bash
cd /HOL4P4/hol/polygram/reviewers_test_here
micro paper_example_cakeml_bestScript.sml
```

You need to update five things. For example, to add a rule that drops traffic with `ip.ttl <= 1`:

**1. Define the atomic predicate and lift it: (copy the following at line 72)**
```sml
val ttl_low = ``(arithm_le (lv_acc (lv_acc (lv_x "h") "ip") "ttl") ^(bdd_utilsLib.make_bv 1 8))``;
val a_ttl_low = ``arith_a ^ttl_low``;
```

**2. Add the predicate to the mapping m: (replace at line 91)**
```sml
val atoms_map = ``[
    ("x1", ^x1); 
	("x2", ^x2); 
	("x3", ^x3); 
	("x4", ^x4);
    ("y1", ^y1); 
	("y2", ^y2); 
	("z", ^z);
    ("ttl_low", ^ttl_low) (* <---- add here *)
]``;
```


**3. Define the rule: (copy the following at line 137)**
```sml
val arith_policy_rule_ttl = ``(^a_ttl_low, action ("drop", [])):single_rule``;
```

**4. Add it to the policy list before the default rule: (replace at line 140)**
```sml
val arith_policy_figure1 = “[
    ^arith_policy_rule1;
    ^arith_policy_rule2;
    ^arith_policy_rule3;
    ^arith_policy_rule4;
    ^arith_policy_rule_ttl;  (* <---- add here *)
    ^arith_policy_rule_default
]:single_rule list”;
```


**5. Add the variable to the order and grouping: (replace at line 165)**
```sml
val policy_order = “["y1";"x1";"x2";"x3";"x4";"y2";"z";"ttl_low"]”; (* <---- add here *)

val variables_grouping = “[
  ("tcp_dst1" ,["y1"]);
  ("ip_dst",["x1";"x2";"x3";"x4"]);
  ("tcp_dst2" ,["y2"]);
  ("ip_ttl" ,["z";"ttl_low"])  (* <---- add here *)
]”;
```



Save your changes:
Ctrl+s


Exit micro:
Ctrl+q


Then rerun:
```bash
./prepp.sh
```

You can see that the file has been compiler with an OK next to it. It means successfully generated a table and a proof of equivalence. *You can check the result again, the same way for the unmodified file.*


---
<br>

### 3. Policy Equivalence Example

The policy equivalence example is in `hol/polygram/reviewers_test_here/policy_equiv_exampleScript.sml`.

```bash
cd /HOL4P4/hol/polygram/reviewers_test_here
micro policy_equiv_exampleScript.sml
```

It demonstrates PolyGram's equivalence checking on two policies defined over three predicates:

- `y1` : `tcp.dstport <= 1023` (standard service ports)
- `y2` : `tcp.dstport >= 49152` (dynamic/ephemeral ports)
- `z`  : `ip.ttl >= 2` (packet has enough hops left)

Both policies produce the same forwarding behaviour, but are written differently (see the comment blocks in file `policy_equiv_exampleScript.sml`).
Each policy contains a rule that is **never reached** due to match-first semantics, yet PolyGram proves the two policies semantically equivalent.


Quit micro:
Ctrl+q


Then inspect the built result interactively:

```bash
hol
```

```sml
load "policy_equiv_exampleTheory";
open policy_equiv_exampleTheory;
show_tags := true;
```

The interesting theorem to inspect is:

- `policy_equiv_exampleTheory.final_proof;` -> end-to-end equivalence between the two policies

The theorem will show the equivalence.

Quit hol mode:
Ctrl+d

---
<br>

### 4. Policy Minimization Example

The policy minimization example is in `hol/polygram/reviewers_test_here/policy_min_exampleScript.sml`.

```bash
cd /HOL4P4/hol/polygram/reviewers_test_here
micro policy_min_exampleScript.sml
```

It demonstrates PolyGram's policy minimization on a bloated policy defined over three predicates.

The input policy has 9 rules with several issues that are hard to spot by hand:

- **Rule 2** : unsatisfiable . `y1 AND y2` is always false (disjoint port ranges)
- **Rule 4** : unsatisfiable . `y1 AND NOT y1` is always false
- **Rule 7** : unsatisfiable . `z AND NOT z` is always false
- **Rule 9** : unreachable . Rule 8 (`NOT z → fwd(2)`) always fires first due to match-first semantics
- **Rules 1, 3, 5, 6** : overlapping conditions that can be simplified

PolyGram automatically generates a *minimized policy of 1 rule* and produces a certified proof that the minimized policy is semantically equivalent to the original.


Quit micro: Ctrl+q

Inspecting the pre-built result:

```bash
hol
```

Then inside the HOL4 interactive session:

```sml
load "policy_min_exampleTheory";
open policy_min_exampleTheory;
show_tags := true;
```

The theorem to inspect is:

- `policy_min_exampleTheory.final_proof;` -> end-to-end equivalence between the original and minimized policy (there you can also see the minimized policy)

The theorem will show:

```
[oracles: CakeML_policy_TCB, DISK_THM] [axioms: ] []
⊢ THM_CONTENT
```

We can modify the pipeline to get a non-oracle theorem. It is like Lego!

Quit hol mode: Ctrl+d


#### Reproducing the Minimization

To modify the input policy and observe how PolyGram minimizes it, open the script:

```bash
micro policy_min_exampleScript.sml
```

You can add new rules, introduce unsatisfiable conditions, or reorder rules. For example, to add a redundant rule that is subsumed by Rule 1 (at line 77 copy the following):

```sml
val rule_new = ``(arith_and ^a_y1 (arith_and ^a_z (arith_not ^a_y2)),
                action ("fwd",[1])):single_rule``;
```

Add it to the policy list (line 118):

```sml
val arith_policy = "[
    ^rule1;
    ^rule_new;   (* <--- add here *)
    ^rule2;
    ...
]:single_rule list";
```

Quit micro: Ctrl+q
Then rerun:

```bash
./prepp.sh
```

PolyGram will produce the same minimized policy and a new equivalence proof, showing it correctly identified and removed the redundant rule.


<br>
<br>
<br>

---

## Pipeline Library Files

The pipeline is assembled according to the use case as described in the paper:


| File | Description | Used in |
|------|-------------|---------|
| **`fwd_proofLib.sml`** | (End to End verified) Policy-to-table pipeline that uses HOL4 `EVAL` for MTBDD construction. | `policy_test_cases` |
| **`fwd_proof_cakeLib.sml`** | Policy-to-table pipeline using CakeML (i.e., serialization is TCB) for MTBDD construction. | `policy_test_cases` |
| **`fwd_proof_policies_cakeLib.sml`** | Takes two policies as input and checks their equivalence. | `policy_test_cases_eq` |
| **`fwd_proof_gen_eq_cakeLib.sml`** | Generates a minimized policy from a given input policy. | `policy_test_cases_gen_policy` |


> **Note:** `bdd_policy_cakeLib.sml` is not a pipeline but contains a script to run MTBDD creation only for testing (Table I)


<br>
<br>
<br>

---
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


<br>
<br>
<br>

---
# Paper's Appendix B in MD format
## Formalization Correspondence

This section maps the definitions, theorems, and algorithms from the paper to their HOL4 mechanization. Each entry is given as `File.sml, lines x-y`.

> **Note:** The implementation may use different names for definitions and theorems than those used in the paper.

---

### Forwarding Languages (Section IV-A)

| Paper Item | File | Lines |
|------------|------|-------|
| Forwarding language structure | `bdd_genScript.sml` | 14-19 |
| Forwarding language properties | `bdd_genScript.sml` | 455-495 |

---

### Policy Language (Section IV-B)

| Paper Item | File | Lines |
|------------|------|-------|
| Policy syntax | `policy_arith_to_varScript.sml` | 20-51 |
| Policy semantics | `policy_arith_to_varScript.sml` | 54-172 |
| Policy ILR syntax | `policy_specScript.sml` | 19-20 |
| | `pred_specScript.sml` | 9-17 |
| Policy ILR semantics | `policy_specScript.sml` | 29-47 |
| ILR policy instantiation | `policy_specScript.sml` | 50-106 |
| ILR policy properties theorems | `policy_specScript.sml` | 115-771 |
| Definition of trans▶ | `policy_arith_to_varScript.sml` | 207-263 |
| Definition of trans◀ | `policy_var_to_arithScript.sml` | 22-60 |
| Theorem 1 (Sound policy translation and retranslation) | `policy_arith_to_varScript.sml` | 311-424 |
| | `policy_var_to_arithScript.sml` | 63-123 |

---

### Network Table Language (Section IV-D)

| Paper Item | File | Lines |
|------------|------|-------|
| Table syntax | `table_arith_to_intervalScript.sml` | 790-792 |
| Table semantics | `table_arith_to_intervalScript.sml` | 979-1017 |
| Table ILR syntax | `table_var_to_arithScript.sml` | 39-41 |
| | `policy_arith_to_varScript.sml` | 30-37 |
| Table ILR semantics | `tables_spec_oldScript.sml` | 133-167 |
| ILR table instantiation | `tables_specScript.sml` | 41-187 |
| ILR table properties theorems | `tables_specScript.sml` | 1920-2570 |
| Definition of trans◀ | `table_arith_to_intervalScript.sml` | 1885-1974 |
| Theorem 2 (Sound table retranslation) | `table_arith_to_intervalScript.sml` | 1979-2025 |

---

### MTBDD Verified Translation (Section V)

| Paper Item | File | Lines |
|------------|------|-------|
| MTBDD syntax | `bdd_genScript.sml` | 21-35 |
| MTBDD well-formedness definition | `bdd_genScript.sml` | 307-320 |
| MTBDD semantics | `bdd_genScript.sml` | 45-85 |
| MTBDD correctness definition | `bdd_genScript.sml` | 437-444 |
| `mk_layer` definition | `bdd_genScript.sml` | 208-235 |
| `mk_layer` correctness theorem | `bdd_gen_correctScript.sml` | 1514-1606 |
| `mk_layer` well-formedness theorem | `bdd_gen_wfScript.sml` | 920-948 |
| `merge` definition | `bdd_genScript.sml` | 640-646 |
| `merge` correctness theorem | `bdd_gen_mergeScript.sml` | 799-814 |
| `merge` well-formedness theorem | `bdd_gen_mergeScript.sml` | 2226-2265 |
| `eliminate` definition | `bdd_genScript.sml` | 650-655 |
| `eliminate` correctness theorem | `bdd_gen_eliminateScript.sml` | 553-570 |
| `eliminate` well-formedness theorem | `bdd_gen_eliminateScript.sml` | 1319-1431 |
| `optimize_mtbdd` definition | `bdd_genScript.sml` | 719-727 |
| `optimize_mtbdd` correctness theorem | `bdd_gen_optimizationScript.sml` | 242-280 |
| `optimize_mtbdd` well-formedness theorem | `bdd_gen_optimizationScript.sml` | 242-280 |
| `mk_mtbdd_opt` definition | `bdd_genScript.sml` | 747-754 |
| Theorem 3 (`mk_mtbdd_opt` correctness) | `bdd_gen_optimizationScript.sml` | 297-375 |
| `mk_mtbdd_opt` well-formedness theorem | `bdd_gen_optimizationScript.sml` | 297-375 |
| `is_isomorphic` definition | `bdd_isomorphScript.sml` | 124-129 |
| Theorem 4 (Isomorphism implies semantic equivalence) | `bdd_isomorphScript.sml` | 502-531 |
| End-to-end semantic equivalence theorem | `bdd_end_to_endScript.sml` | 858-939 |

---

### Implementation and Algorithms (Sections IV-E and VI)

| Paper Item | File | Notes |
|------------|------|-------|
| MTBDD-to-tables algorithm | `bdd_utilsLib.sml` | Lines 850-874. Untrusted SML. |
| Policy minimization algorithm | `bdd_utilsLib.sml` | Lines 1224-1594. Untrusted SML. |
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


