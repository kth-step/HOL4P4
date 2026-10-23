# Symbolic execution

The state of the single-thread symbolic execution is represented by a tuple of
`npaths` (current number of active symbolic paths), `path_tree` (a tree structure
holding n-chotomy theorems for every symbolic branch), a list of "symbolic states"
which are tuples of `path_id` (a unique number for every path), a number `fv_index` signifying
the current index used for introducing fresh free variables, the current path condition `path_cond`,
the current step theorem `step_thm`, a number representing fuel `fuel` which is decreased by every symbolic
step, and `nobranch_flag` which tells the symbolic executor to not perform a branch step
(typically set immediately after a branch).
Finally, there is a list accumulator of finished states, which, unlike the symbolic state
tuples, consist only of a path ID, a path condition and a step theorem.

To initialise the state, the symbolic executor takes an initial path condition and
an (integer) amount of fuel.

In addition, the symbolic executor has four language-specific static parameters:

`lang_regular_step: bool -> thm -> thm`: Takes one regular step in the language lang
   (takes a flag signifying whether the regular step is made just after a symbolic branch
    and a step theorem, and transforms the step theorem into a new one)

`lang_init_step_thm:thm`: Step theorem for zero steps

`lang_should_branch:(int * thm) -> (thm * int list) option`: Decides whether to branch
by looking at the current step theorem, and uses an index when creating fresh HOL4 variables
when overapproximating externs. Returns NONE if branching should not
happen, and an n-chotomy theorem stating that the disjunction of the branch conditions holds
as well as a list of updated free variable indices when branching.

`lang_is_finished:thm -> bool`: Decides whether symbolic execution should continue
on this path by looking at the current step theorem.

Note that branching consumes one step of (SML function) fuel.

## Concurrent version

The concurrent version retains the same parts of the state, now stored using SML references.
Additions are the number of threads stored as a reference `nthreads_ref` and
furthermore `all_done` (an SML condition variable) and `mutex_exec` (an SML mutex).

The idea is that the programmer providing the four language-specific static parameters
should not need to deal with the concurrency implementation. The concurrency is achieved
by parameterising the symbolic execution in terms of the following five functions:

`get_job: unit -> (int * int * thm * thm * int * bool) option`: This function returns
the head of the `work_queue` consisting of a path ID, free variable index, path condition,
step theorem, fuel and a flag indicating a preceding symbolic branch.

`append_jobs: (int * int * thm * thm * int * bool) list -> unit`: This function appends a
list of "symbolic states" to the `work_queue`.

`update_shared_state: bool -> term list * thm * term list * int list -> int * thm * int -> unit`:
This function takes a debug flag, and a tuple of a list of new path conditions, an n-chotomy theorem,
a list of new branch conditions and a list of new free variable indices (the result of branching),
and a tuple of a path ID, a step theorem and fuel. It's used after symbolic branching.

`finish_job: int * thm * thm -> bool`: This function appends one result to the list
of finished jobs, consisting of a tuple of a path ID, a path condition and a step theorem
(same as in the single-threaded case). If the `work_queue` is empty, the function
will decrement `nthreads_ref` and return `true`, otherwise `false`.

`register_new_worker_n: (unit -> unit) -> int -> unit`: This function takes a function
`work_fun:unit -> unit` and an integer `n`, forking `n` threads each computing `work_fun`,
up to the limit `nthreads_max`.

The concurrent version is still flaky since HOL4 is not perfectly thread safe.
Stick to the sequential `p4_symb_exec_prove_contract` unless you have a thread-safe HOL4 version.

## "Big-step" shortcuts

When the next statement is inside a local function, the P4 symbolic executor collapses
sequences of local small steps into one step using the big-step semantics in
`p4_bigstepScript.sml`, composed with the step theorem by `bigstep_arch_exec_comp'_NONE`
and `bigstep_arch_exec_comp'_SOME`. A new architecture needs a lemma like
`v1model_oracle_index_getter_setter_sane` in `p4_symb_execScript.sml`, which must also be
added to the list of these lemmas in `p4_symb_execLib.sml`.

## Symbolic packets

The input packet of a program can be a symbolic variable `p` of type `bool list` instead
of a list of bits by using `p4_append_input_list [(p, port)]` with the initial state.
Its length is branched on where it matters (see below). No fresh variables are
introduced. The theorems behind this are in `p4_symb_execScript.sml`, together with the
definitions for referring to the packet in postconditions:

* `packet_slice n w p` is the list of bits `n` to `n + w - 1` of `p` (as `EL` terms, with
  bit `0` as `HD p`), and
* `packet_word n p : 'a word` is the same as a word, with the width given by the type.

The evaluation stage of the postcondition prover unfolds both definitions, so they need not
be added to `postcond_rewr_thms`.
Whether enough bits remain for a method is decided from the path condition
(such as `336 <= LENGTH p` or `LENGTH p = 336` in the precondition). If neither
that nor its negation follows, the symbolic execution branches on it, and the path on which
the packet is too short (`PacketTooShort`) is explored as well. The final stage of the
postcondition prover decides the arithmetic on packet lengths with `numSimps.ARITH_ss`.

## Contracts

A contract is a theorem `p4_contract_at P ctx E Q` (`p4_symb_execScript.sml`): from every
state satisfying the precondition `P`, some number of steps of `arch_multi_exec ctx` reaches
a state that satisfies both the end point `E` and the postcondition `Q`. `P`, `E` and `Q` are
predicates on architectural states, and the definition does not constrain them further.

`p4_symb_exec_prove_contract` proves such a theorem by symbolic execution from the state term
`init_astate` under the path condition it is given. It runs every path until its state
satisfies `E`, proves `E` and `Q` for each final state, and combines the paths into the
contract. Since its step theorems speak only about `init_astate`, the tool forms the
precondition itself, as `\s. path_cond /\ s = init_astate`; the free variables of `init_astate`
and of the path condition stay universally quantified in the theorem. `E` is an argument of
`p4_symb_exec_prove_contract`, which fails with an error if a path has not reached `E` within
`n_max` steps (a branch also costs one step of fuel).

The end point decides what the contract says:

* `p4_finished` (block index 0 and no input left) is the end of the run. A finished state has
  no next step when block 0 is the input block and the input function fails on an empty input
  list, as in all three architectures (`p4_finished_arch_exec`). By `p4_contract_at_final`
  the contract then states that the run terminates and that every final state satisfies `Q`.
  Use this end point for properties of the output, including negative ones such as "never
  forwards to port 1".
* `\s. p4_block_next s k` stops when block `k` is about to start, for splitting a proof in two
  with `p4_combine_contracts` (see `tests/decomposeScript.sml`). Such a contract only says that
  `Q` holds at some point where block `k` is next.
* `\s. T` says that `Q` holds after some number of steps, possibly zero
  (`p4_contract'_contract_at`); with it the executor stops each path after its first step.

## Control plane

A contract covers one run from the initial state, and the control plane does not change
during the run:

* Table entries are the `ctrl` component of the initial state. Nothing in the semantics
  changes them, so every packet of the run sees the same entries. They can be symbolic,
  e.g. `t2_ctrl` in `tests/table_unknownScript.sml`, constrained by
  `v1model_tbl_is_well_formed` in the precondition; the contract then holds for every entry
  list that satisfies the precondition, but for one list per run.
* Default actions come from the program (the table map of each block in the context), not
  from `ctrl`. On a miss the semantics calls that action with the arguments written in the
  program (`NoAction` when the program declares no default). A controller may change a
  non-`const` default action at run time (P4_16 spec 14.2.1.3); contracts do not cover that.

`v1model_tbl_is_well_formed` constrains each entry: its action is one of the table's actions,
called with both leading flags (called from a table, hit) true and values of the action's
parameter types as arguments. The empty table satisfies it (`v1model_tbl_is_well_formed_NIL`),
and before running, the executor checks that every conjunct of the path condition about table
entries holds when the symbolic entry lists are empty, so that these conjuncts cannot make the
precondition unsatisfiable.

## Tests and examples

The tests are located in the `tests` subdirectory. After installation, run them by first executing
`Holmake` in this directory (`hol/symb_exec`), then in `tests`.

For more information, open a test in e.g. Emacs, then change the line

```sml
val debug_flag = false;
```

to

```sml
val debug_flag = true;
```

and send everything to the REPL to observe debug output of what's going on.

The import tool places the V1Model registers of a program in the initial state with contents `v1model_register_construct_inner size width oracle_index random_oracle`; keep that constant among the constants the executor never unfolds (the `stop_consts_never` argument of `p4_symb_exec_prove_contract`, see `tests/register_readScript.sml`) so that the contents stay folded.

A mid-size example can be found in the `example_ipsec` subdirectory. The Python
script `count_reds.py` can be used on the debug output to generate statistics about the symbolic execution.

The `imp` subdirectory contains an instantiation of the symbolic executor for a simple imperative language with loops.
