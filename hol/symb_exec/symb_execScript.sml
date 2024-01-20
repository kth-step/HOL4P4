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

Definition disj_list_def:
(* (disj_list (h::[]) = h) /\ *)
 (disj_list (h::t) = (h \/ disj_list t)) /\
 (disj_list [] = F)
End

Theorem disj_list_COMM:
 !A B.
 (disj_list (A++B) <=> disj_list (B++A))
Proof
Induct_on ‘A’ >> Induct_on ‘B’ >> (
 fs[disj_list_def]
) >>
rpt strip_tac >>
Q.PAT_ASSUM ‘!B. disj_list (A ++ B) <=> disj_list (B ++ A)’ (fn thm => REWRITE_TAC [thm]) >>
fs[disj_list_def] >>
Q.PAT_X_ASSUM ‘!h. h \/ disj_list (A ++ B) <=> disj_list (B ++ h::A)’ (fn thm => REWRITE_TAC [GSYM thm]) >>
metis_tac[]
QED

Theorem disj_list_REWR:
 !a b B C.
 (((b \/ disj_list C)) <=> (disj_list (b::C))) /\
 ((a \/ b) <=> (a \/ disj_list [b]))
Proof
ONCE_REWRITE_TAC[disj_list_COMM] >>
fs[disj_list_def] >>
metis_tac[]
QED

Theorem disj_list_extra_REWR:
 !a A B.
 disj_list (a::[disj_list B]) = disj_list (a::B) /\
 disj_list ((disj_list B)::A) = disj_list (B++A)
Proof
Induct_on ‘A’ >> Induct_on ‘B’ >> (
 fs[disj_list_def]
) >>
metis_tac[]
QED

(*
Theorem disj_list_imp_REWR:
 !P a b B C.
 ((P ==> ((a \/ b) \/ disj_list C)) <=> (P ==> (b \/ disj_list (C++[a])))) /\
 ((P ==> (a \/ disj_list B)) <=> (P ==> (disj_list (B++[a])))) /\
 ((P ==> (a \/ b)) <=> (P ==> (b \/ disj_list [a])))
Proof
Cases_on ‘P’ >> (
  fs[]
) >>
fs[disj_list_REWR]
QED
*)

Theorem imp_REWR:
 !P.
 P <=> (T ==> P)
Proof
fs[]
QED

val _ = export_theory ();
