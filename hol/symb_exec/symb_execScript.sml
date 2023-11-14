open HolKernel boolLib liteLib simpLib Parse bossLib;

val _ = new_theory "symb_exec";

Theorem symb_exec_add_postcond:
!P f s s' Q.
(P ==> f s = SOME s') ==>
Q s' ==>
(P ==> f s = SOME s' /\ Q s')
Proof
metis_tac []
QED

val _ = export_theory ();
