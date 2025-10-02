Please set identifier (32-bit, 64-bit word) for your compilation target in `p4_cake_auxLib.sml`, as well as optimization flags.

`p4_exec_sem_cakeScript.sml` contains an optimized reformulation of the regular executable semantics (found in `p4_exec_semScript.sml`).

`p4_cake_transformScript.sml` contains HOL4 functions to transform the actx and astate of the regular semantics to those of the optimized version. The SML functions are found in `p4_cake_transformLib.sml`.
