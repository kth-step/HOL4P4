NOTE: This directory uses HOL4 commit `718b3aa`, and is not guaranteed to function properly with the Trindemossen-1 release.

The CakeML release used in this directory is `v2882`.

Please set identifier (23-bit, 64-bit word) for your compilation target in `p4_cake_auxLib.sml`.

`p4_exec_sem_cakeScript.sml` contains a more CakeML-friendly reformulation of the regular executable semantics (found in `p4_exec_semScript.sml`).

`p4_cake_transformScript.sml` contains HOL4 functions to transform the actx and astate of the regular semantics to those of the CakeML-adjusted version. The SML functions are found in `p4_cake_transformLib.sml`.
