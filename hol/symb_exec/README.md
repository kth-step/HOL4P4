# Symbolic execution

The state of the single-thread symbolic execution is represented by a tuple of
`npaths` (current number of active symbolic paths), `path_tree` (a tree structure
holding n-chotomy theorems for every symbolic branch), a list of "symbolic states"
which are tuples of `path_id` (a unique number for every path), a number `fv_index `signifying
the current index used for introducing fresh free variables, the current path condition `path_cond`,
the current step theorem `step_thm`, a number representing fuel `fuel` which is decreased by every symbolic
step, and `nobranch_flag` which tells the symbolic executor to not perform a branch step
(typically set immediately after a branch).
Finally, there is a list accumulator of finished states, which unlike the symbolic state
tuple consist only of a path ID, a path condition and a step theorem.

To initialise the state, the symbolic executor takes an initial path condition and
an (integer) amount of fuel.

In addition, the symbolic executor has four language-specific static parameters:

`lang_regular_step: bool -> thm -> thm`: Takes one regular step in the language lang
   (takes a flag signifying whether the regular step is made just after a symbolic branch,
    a step theorem and transforms it into a new step theorem)
 
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
should not need deal with the concurrency implementation. The concurrency is achieved
by parameterising the symbolic execution in terms of the following four functions:

`get_job: unit -> (int * int * thm * thm * int * bool) option`: This function returns
the head of the `work_queue` consisting of a path ID, free variable index, path condition,
step theorem, fuel and a flag indicating a preceding symbolic branch.

`append_jobs: (int * int * thm * thm * int * bool) list -> unit`: This function appends a
list of "symbolic states" to the `work_queue`.

`update_shared_state: bool -> term list * thm * term list * int list -> int * thm * int -> unit`:
This function takes a debug flag, and a tuple of a list of new path conditions, an n-chotomy theorem,
a list of new branch conditions and a list of new free variable indices (the result of branching),
and a tuple of a path ID, a step thm and fuel. It's used after symbolic branching.

`finish_job: int * thm * thm -> bool`: This function appends one result to the list
of finished jobs, consisting of a tuple of a path ID, a path condition and a step theorem,
(same as in the single-threaded case). If the `work_queue` is empty, the function
will decrement `nthreads_ref` and return `true`, otherwise `false`.

`register_new_worker_n: (unit -> unit) -> int -> unit`: This function takes a function
`work_fun:unit -> unit` and an integer `n`, forking `n` threads each computing `work_fun`,
up to the limit `nthreads_max`.

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

A mid-size example can be found in `example_ipsec` subdirectory. The Python
script `count_reds.py` can be used on the debug output to generate statistics about the symbolic execution.
