This directory contains a version of the HOL4P4 executable semantics that has been made modular with respect to certain optimizations: identifier type, optimization of table matching, and optimization of I/O. Please set appropriate identifier type (32-bit, 64-bit word) for your compilation target at the top of `p4_cake_auxLib.sml`, as well as optimization flags (`matching_optimization` and `io_optimization`). Note that setting `matching_optimization` will likely decrease performance; for this reason, it is disabled by default.

`p4_exec_sem_cakeScript.sml` contains an optimized reformulation of the regular executable semantics (found in `p4_exec_semScript.sml`).

`p4_cake_transformScript.sml` contains HOL4 functions to transform the actx and astate of the regular semantics to those of the optimized version. The SML functions are found in `p4_cake_transformLib.sml`.

`metatheory` contains a WIP sketch of a proof of correctness for the optimized semantics.

`programs` contains some P4 programs for evaluation purposes (for convenience, already imported to HOL4P4).

Note that the `Holmakefile` assumes that the cakeml directory is located in a certain place. You may need to change this depending on how your installation looks like.
