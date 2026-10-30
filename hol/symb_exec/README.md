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
and of the path condition stay universally quantified in the theorem. For a V1Model context
with a variable multicast ordering, the tool first conjoins `v1model_wf_ordering order_f` to
the path condition (see V1Model packet flow). `E` is an argument of
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

## Decomposition

A proof can be split at the start of a block `k`, except after the traffic manager of a V1Model
multicast packet (see V1Model packet flow). `get_v1model_wellformed_defs ctx init_astate k`
defines the predicate `p4_v1model_parser_wellformed`, which holds of a state when block `k` is
next, no packets are left, and the table entries and extern objects are those of `init_astate`,
except that the packet objects hold the rest of the packet and each register holds an arbitrary
array `reg_i` with `wellformed_register_array w reg_i`; the header, metadata and apply-result bits
and the oracle index are arbitrary. A variable of the context, such as the random oracle, that
still occurs in the extern objects or the table entries is a parameter of the predicate.

The steps, as in `tests/decompose_registerScript.sml`: a contract from `init_astate` to the end
point `\s. p4_block_next s k` with the predicate in its postcondition, which the simpset
`p4_wellformed_ss def` proves; a contract from `get_intermediate_state postcond def` under the
path condition `get_intermediate_path_cond postcond def`, the register conjuncts; and
`p4_combine_contracts c1 c2 def`. What the first part writes to a register is not carried to the
second.

## Control plane

A contract covers one run from the initial state, and the control plane does not change
during the run:

* Table entries are in the `ctrl` component of the initial state. For eBPF and VSS, `ctrl` is
  the table map. For V1Model, it is the pair of the table map and the multicast groups (e.g.
  `([], [(1, [(1, 0); (2, 0)])])` in `tests/multicastScript.sml`); the groups map a group id
  (the value of `mcast_grp`) to its list of (egress port, egress rid) copies, which the import
  tool puts in BMv2's replication order. Nothing in the semantics changes `ctrl`, so every
  packet of the run sees the same entries and groups. Table entries can be symbolic,
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

## V1Model packet flow

As in BMv2's simple_switch, a traffic manager (`v1model_traffic_manager`) runs between
ingress and egress. A packet with `mcast_grp` 0 and `egress_spec` 511 is dropped there and
egress does not run for it; a packet with `mcast_grp` 0 and another `egress_spec` runs egress
with `egress_port` set to `egress_spec`, `egress_spec` 0 and `instance_type` 0, and a packet
for which egress sets `egress_spec` to 511 is dropped at the output.

A packet with nonzero `mcast_grp` is replicated to the copies of that multicast group (see
Control plane), and the original is discarded whatever its `egress_spec`. An unknown or empty
group gives no output. The traffic manager takes an ordering `order_f` as a parameter:
`order_f oi c` is the order in which the copies `c` are processed, where `oi` is the oracle
index at the traffic manager. If it is not a permutation of `c`, the traffic manager has no
step. Each copy runs egress, compute checksum and the deparser, starting from the variables
and the packet at the end of ingress, with `egress_port` and `egress_rid` from the group,
`instance_type` 5 and `egress_spec` 0; an ingress `truncate` does not apply to the copies.
The `next_copy` block (`v1model_next_copy`) after the deparser emits every copy but the last
and starts egress on the next one, and the output block emits the last. A copy for which
egress sets `egress_spec` to 511 is dropped, the others are not. Registers and the other
extern objects keep their state from one copy to the next.

The import tool passes the identity ordering `\i l. l` in its concrete modes and a free
variable `order_f` in symbolic mode. The hand-written contexts in `tests` and `example_ipsec`
use the identity, except those in `tests/multicastScript.sml`. `v1model_ffblock_map_gen` in
`hol/p4_v1modelLib.sml` builds the fixed-function block map for a given ordering term.

* The executor branches on `v1model_is_drop_port` when `egress_spec` is symbolic: at the
  traffic manager (for `mcast_grp` 0), at `next_copy` while a multicast copy is pending, and at
  the output. It keeps that constant folded where needed itself, so it need not be in
  `stop_consts_rewr`.
* The executor needs a known `mcast_grp` at the traffic manager: it stops with an error when
  `mcast_grp` does not evaluate to a number there. A proof split before the traffic manager
  must therefore keep `mcast_grp` in the intermediate postcondition (see
  `tests/decomposeScript.sml`).
* When the ordering in the context is a variable `order_f`, the executor branches at the
  traffic manager of a multicast packet into one path for each distinct permutation `p` of the
  group's copies `c`, with `order_f oi c = p` in its path condition. The executor proves that
  these paths cover all cases from `v1model_wf_ordering order_f`, which
  `p4_symb_exec_prove_contract` conjoins to the path condition, so the contract's precondition
  has that conjunct. `v1model_wf_ordering f` (`p4_symb_execScript.sml`) is
  `!i l. PERM (f i l) l`; the contract holds for every `order_f` that satisfies it. The context
  definition then takes `order_f` as a parameter, as it takes `random_oracle` (see
  `tests/multicastScript.sml`). `p4_debug_symb_exec` conjoins `v1model_wf_ordering order_f` in
  the same way, but `p4_symb_exec` takes the path condition as given: called directly with such
  a context, it needs that conjunct in its path condition, or `symb_branch` cannot prove the
  branch at the traffic manager. With a closed ordering term the executor does not branch
  there. With any other ordering term (one with free variables that is not a variable), the
  executor stops with an error at the traffic manager of a packet whose group exists.
* Decomposition does not support a cut after the traffic manager (at the start of egress,
  compute checksum, the deparser, `next_copy` or the output block) of a packet whose multicast
  group has two or more copies. `p4_v1model_parser_wellformed` describes a state without the
  copies object that the traffic manager then creates, so it does not hold at such a cut and
  the first contract cannot be proved.
* `packet_has_port s p` (`p4_symb_execScript.sml`) holds only when the output is exactly one
  packet, on port `p`. For the copies of a multicast packet, `output_ports s` is the list of
  the ports of all output packets in output order; e.g. the postcondition
  `\s. is_perm (output_ports s) [1; 2]` says that the output is one packet on port 1 and one on
  port 2, in either order.
* The timestamps and queue fields of `standard_metadata`, and `egress_port` during ingress,
  are oracle bits; the queue fields are drawn anew for each multicast copy.

## assert, assume and random

In the semantics, `assert` and `assume` have no effect, as with p4c's `--ndebug`. With the trace
`p4_symb_exec_assertions` set (`set_trace "p4_symb_exec_assertions" 1`), the executor checks
them:

* `assert(c)`: `c` must follow from the path condition, by bit-blasting or by arithmetic on the
  numbers of the bit-strings. Otherwise the executor stops with "assert may fail".
* `assume(c)`: the path continues with `c` in its path condition, and the precondition of the
  contract gets the conjunct `!vs. pc ==> c`, where `pc` is the path condition at the call and
  `vs` are the executor's fresh variables in it. A path on which `c` contradicts the path
  condition ends at the call.

`random(r, lo, hi)` gives `r` fresh variables in `[lo, hi]`, unless the bounds alone decide the
value. See `tests/assert_assumeScript.sml`.

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
