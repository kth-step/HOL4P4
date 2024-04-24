open HolKernel boolLib liteLib simpLib Parse bossLib;

open p4Theory listTheory;

open symb_execTheory;

val _ = new_theory "p4_symb_exec";

Definition packet_has_port_def:
 packet_has_port (((i, in_out_list, in_out_list', scope), g_scope_list, arch_frame_list, status):'a astate) port_ok =
  case in_out_list' of
    [] => F
  | [(data, port)] => port = port_ok
  | _ => F
End

Definition p4_contract_def:
 p4_contract P ctx s Q =
  (P ==> ?n. arch_multi_exec ctx s n <> NONE /\ !s'. arch_multi_exec ctx s n = SOME s' ==> Q s')
End

(* TODO: This can be written using FOLDL *)
Definition p4_contract_list_def:
 (p4_contract_list P [] ctx s Q = T) /\
 (p4_contract_list P (h::[]) ctx s Q = p4_contract (P /\ h) ctx s Q) /\
 (p4_contract_list P (h::t) ctx s Q = (p4_contract (P /\ h) ctx s Q /\ p4_contract_list P t ctx s Q))
End

Theorem p4_contract_list_REWR:
 !R P P_list P_list' ctx s Q b.
 ((p4_contract_list R P_list ctx s Q /\ p4_contract (R /\ P) ctx s Q) <=>
   p4_contract_list R (P_list++[P]) ctx s Q)
 /\
 ((p4_contract (R /\ P) ctx s Q /\ b) <=> (p4_contract_list R [P] ctx s Q /\ b))
Proof
fs[p4_contract_list_def] >>
Induct_on ‘P_list’ >> (
 fs[p4_contract_list_def]
) >>
Cases_on ‘P_list’ >> (
 fs[p4_contract_list_def] >>
 metis_tac[]
)
QED

(* Sometimes the conjunction has been flipped. Then this is useful.
 * (CONJ_COMM is looping and so a hassle to use in proof procedures, among other reasons) *)
Theorem p4_contract_list_GSYM_REWR:
 !R P P_list ctx s Q b.
 ((p4_contract_list R P_list ctx s Q /\ (p4_contract (P /\ R) ctx s Q)) <=> (p4_contract_list R (P_list++[P]) ctx s Q)) /\
 ((p4_contract (P /\ R) ctx s Q /\ b) <=> (p4_contract_list R [P] ctx s Q /\ b))
Proof
fs[p4_contract_list_def] >>
Induct_on ‘P_list’ >> (
 fs[p4_contract_list_def, CONJ_COMM]
) >>
Cases_on ‘P_list’ >> (
 fs[p4_contract_list_def, CONJ_COMM] >>
 metis_tac[]
)
QED

Theorem p4_contract_imp_REWR:
 !P ctx s Q.
 ((p4_contract P ctx s Q) <=> (p4_contract (T /\ P) ctx s Q))
Proof
fs[p4_contract_def]
QED

Theorem p4_symb_exec_to_contract:
!P ctx s n s' Q.
(P ==> arch_multi_exec ctx s n = SOME s' /\ Q s') ==>
p4_contract P ctx s Q
Proof
fs[p4_contract_def] >>
rpt strip_tac >>
qexists_tac ‘n’ >>
rpt strip_tac >> (
 fs[]
)
QED

(* For branching and unification *)

Theorem p4_symb_exec_unify:
!P1 P2 ctx s Q.
p4_contract (P1 /\ P2) ctx s Q ==>
p4_contract (~P1 /\ P2) ctx s Q ==>
p4_contract P2 ctx s Q
Proof
fs[p4_contract_def] >>
metis_tac []
QED

(* Note that the point with this theorem is to avoid
 * brute-force rewriting or reasoning using disj_thm
 * when obtaining the conclusion *)
(*
Theorem p4_symb_exec_unify_n_gen:
!P_list R ctx s Q.
disj_list P_list ==>
p4_contract_list R P_list ctx s Q ==>
p4_contract R ctx s Q
Proof
Induct_on ‘P_list’ >> (
 fs [disj_list_def, p4_contract_list_def, p4_contract_def]
) >>
rpt strip_tac >> (
 Cases_on ‘P_list’ >> (
  fs [disj_list_def, p4_contract_list_def, p4_contract_def]
 )
)
QED
*)
Theorem p4_symb_exec_unify_n_gen:
!P_list R ctx s Q.
symb_branch_cases R P_list ==>
p4_contract_list R P_list ctx s Q ==>
p4_contract R ctx s Q
Proof
Induct_on ‘P_list’ >> (
 fs [symb_branch_cases_def, disj_list_def, p4_contract_list_def, p4_contract_def]
) >>
rpt strip_tac >> (
 Cases_on ‘P_list’ >> (
  fs [symb_branch_cases_def, disj_list_def, p4_contract_list_def, p4_contract_def] >>
  metis_tac[]
 )
)
QED

Definition ctrl_is_well_formed_def:
 ctrl_is_well_formed (ftymap, blftymap) (pblock_map:pblock_map, apply_table_f:'a apply_table_f) (ascope:'a) =
  !block_name pbl_type x_d_list b_func_map decl_list pars_map tbl_map.
   ALOOKUP pblock_map block_name = SOME (pbl_type, x_d_list, b_func_map, decl_list, pars_map, tbl_map) ==>
    !tbl mk_l actions default_f default_f_args.
     ALOOKUP tbl_map tbl = SOME (mk_l, actions, (default_f, default_f_args)) ==>
      !e_l. ?f f_args.
      apply_table_f (tbl, e_l, mk_l, actions, (default_f, default_f_args), ascope) = SOME (f, f_args) /\
       MEM f actions /\
       (EL 0 f_args = (e_v (v_bool T))) /\
       (f = default_f ==> ?b. EL 1 f_args = (e_v (v_bool b))) /\
       (f <> default_f ==> EL 1 f_args = (e_v (v_bool T))) /\
       ((?ftys ret_ty local_ftymap. ALOOKUP blftymap block_name = SOME local_ftymap /\
        ALOOKUP local_ftymap (funn_name f) = SOME (ftys, ret_ty:tau) /\
        v_to_tau_list (DROP 2 f_args) = SOME (ftys)) \/
       (ALOOKUP blftymap block_name = NONE \/
        (?local_ftymap.
         ALOOKUP blftymap block_name = SOME local_ftymap /\
         ALOOKUP local_ftymap (funn_name f) = NONE) /\
        (?ftys ret_ty. ALOOKUP ftymap (funn_name f) = SOME (ftys, ret_ty:tau) /\
         v_to_tau_list (DROP 2 f_args) = SOME (ftys))))
End

val _ = export_theory ();
