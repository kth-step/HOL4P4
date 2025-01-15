p4_exec_sem_cakeScript.sml contains a more CakeML-friendly reformulation of the regular executable semantics (found in p4_exec_semScript.sml).

p4_cake_transformScript.sml contains HOL4 functions to transform the actx and astate of the regular semantics to those of the CakeML-adjusted version. The SML functions are found in p4_cake_transformLib.sml.

p4_transformed_conditional_cakeScript.sml contains a transformed (using the above) CakeML export of the simple conditional example program.
