open HolKernel boolLib liteLib simpLib Parse bossLib;

val _ = new_theory "symb_exec";

Theorem symb_exec_add_postcond:
!P f s s' Q.
(P ==> f s = SOME s') ==>
(P ==> Q s') ==>
(P ==> f s = SOME s' /\ Q s')
Proof
metis_tac []
QED

Definition disj_list_def:
(* (disj_list (h::[]) = h) /\ *)
 (disj_list (h::t) = (h \/ disj_list t)) /\
 (disj_list [] = F)
End

Definition symb_true_def:
 symb_true = T
End

Definition symb_disj_def:
 symb_disj a b = (a \/ b)
End

Definition symb_conj_def:
 symb_conj a b = (a /\ b)
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

Theorem disj_list_EXCLUDED_MIDDLE:
 !a.
 disj_list [a; ~a]
Proof
fs[disj_list_def]
QED

Theorem disj_list_CONJ:
!a A.
(a /\ disj_list A) <=> (disj_list (MAP ( \b. symb_conj a b) A))
Proof
Induct_on ‘A’ >> (
 fs[disj_list_def, symb_conj_def]
) >>
metis_tac[]
QED

Theorem disj_list_symb_disj_REWR:
 !h h' t.
 (disj_list (h::(h'::[])) = symb_disj h h') /\
 (disj_list (h::t) = symb_disj h (disj_list t))
Proof
fs[disj_list_def, symb_disj_def]
QED

Theorem disj_list_symb_disj_REWR_extra:
 !h t.
 (disj_list (h::[(disj_list t)]) = disj_list (h::t))
Proof
fs[disj_list_def]
QED

Theorem symb_disj_F:
 !a b.
 (symb_disj F b = b) /\
 (symb_disj a F = a)
Proof
fs[symb_disj_def]
QED

(* This is used to keep track of which symbolic branches were made,
 * and later join them. The reason of the definition is to be able
 * to easily syntactically separate path condition and different
 * branch cases.
 * This is stored in the path_tree structure *)
Definition symb_branch_cases_def:
 symb_branch_cases path_cond case_list =
  (path_cond ==> disj_list case_list)
End

Theorem add_assum:
!A B.
(A ==> (symb_conj A B)) <=> (A ==> B)
Proof
fs[symb_conj_def]
QED

Theorem symb_conj_case:
!A B.
A ==> ((symb_conj A B) <=> B)
Proof
fs[symb_conj_def]
QED

Theorem AND_IMP_INTRO_SYM:
!A B C. A ==> B ==> C <=> B /\ A ==> C
Proof
metis_tac[]
QED

Theorem IMP_ADD_CONJ:
!A B C. (A ==> B) ==> ((A /\ C) ==> B)
Proof
fs[]
QED

val _ = export_theory ();
