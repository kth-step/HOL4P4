open HolKernel boolLib liteLib simpLib Parse bossLib;

open p4Theory listTheory;

open symb_execTheory;

(* TODO: Split into file used by symbolic execution and file used by contract derivation *)
val _ = new_theory "p4_symb_exec";

Definition packet_has_port_def:
 packet_has_port (((i, in_out_list, in_out_list', scope), g_scope_list, arch_frame_list, status):'a astate) port_ok =
  case in_out_list' of
    [] => F
  | [(data, port)] => port = port_ok
  | _ => F
End

(* TODO: Just preliminary. Find out why packet is not found in output packet queue *)
(*
Definition get_packet'_def:
 get_packet' ((i, io_list, io_list', ((counter, ext_obj_map, v_map, ctrl):v1model_ascope)), g_scope_list, arch_frame_list, status) =
  case ALOOKUP ext_obj_map 0 of
  | SOME (INL (core_v_ext_packet bit_list)) => SOME bit_list
  | _ => NONE
End
*)

Definition get_packet_def:
 get_packet ((i, io_list, io_list', ((counter, ext_obj_map, v_map, ctrl):v1model_ascope)), g_scope_list, arch_frame_list, status) =
  case io_list' of
  | [(packet, port)] => SOME packet
  | _ => NONE
End

Definition packet_dropped_def:
 packet_dropped ((i, io_list, io_list', ((counter, ext_obj_map, v_map, ctrl):v1model_ascope)), g_scope_list, arch_frame_list, status) =
  case io_list' of
  | [] =>
   (case ALOOKUP v_map "standard_metadata" of
    | SOME (v_struct struct) =>
     (case ALOOKUP struct "egress_spec" of
      | SOME (v_bit (port_bl, n)) =>
       let port_out = v2n port_bl in
        if port_out = 511
        then T
        else F
      | _ => F)
    | _ => F)
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

Theorem p4_contract_list_REWR2:
 !R P_list P_list' ctx s Q.
 ((p4_contract_list R P_list ctx s Q /\ p4_contract_list R P_list' ctx s Q) <=> (p4_contract_list R (P_list++P_list') ctx s Q))
Proof
fs[p4_contract_list_def] >>
Induct_on ‘P_list’ >> (
 gs[p4_contract_list_def]
) >>
Cases_on ‘P_list’ >> (
 gs[p4_contract_list_def]
) >- (
 Cases_on ‘P_list'’ >> (
  gs[p4_contract_list_def]
 )
) >>
rpt strip_tac >>
eq_tac >> (
 rpt strip_tac >>
 res_tac >>
 gs[p4_contract_list_def]
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

Theorem p4_contract_pre_str:
!P P' ctx s Q.
(P' ==> P) ==>
(p4_contract P ctx s Q ==>
p4_contract P' ctx s Q)
Proof
fs[p4_contract_def]
QED

Definition p4_contract'_def:
 p4_contract' P ctx Q <=>
  !s.
   P s ==>
   ?n. arch_multi_exec ctx s n <> NONE /\
       !s'. arch_multi_exec ctx s n = SOME s' ==> Q s'
End

(* TODO: Annoying that entire ascope is used. You can make more efficient versions that only use ctrl, tailored for individual architectures. *)
Definition v1model_ctrl_is_well_formed_def:
 v1model_ctrl_is_well_formed (ftymap, blftymap, pblock_action_names_map) (pblock_map:pblock_map) ctrl =
  !block_name pbl_type x_d_list b_func_map decl_list pars_map tbl_map action_names_map.
   ALOOKUP pblock_map block_name = SOME (pbl_type, x_d_list, b_func_map, decl_list, pars_map, tbl_map) ==>
   ALOOKUP pblock_action_names_map block_name = SOME action_names_map ==>
    !tbl mk_l actions default_f default_f_args.
     ALOOKUP tbl_map tbl = SOME (mk_l, (default_f, default_f_args)) ==>
     ALOOKUP action_names_map tbl = SOME actions ==>
      !e_l.
      (* TODO: Keep the requirement that LENGTH e_l = LENGTH mk_l here? *)
      LENGTH e_l = LENGTH mk_l ==>
      !counter ext_obj_map v_map. ?f f_args.
      v1model_apply_table_f (tbl, e_l, mk_l, (default_f, default_f_args), (counter, ext_obj_map, v_map, ctrl):v1model_ascope) = SOME (f, f_args) /\
       (* f is in the list of actions for the table *)
       MEM f actions /\
       (* first argument is the Boolean T, signifying that the function call resulted from table application *)
       (oEL 0 f_args = SOME (e_v (v_bool T))) /\
       (* first argument is either:
        * a Boolean, if action name is that of the default action... *)
       (f = default_f ==> ?b. oEL 1 f_args = SOME (e_v (v_bool b))) /\
       (* or the Boolean T, if action name is not that of the default action. *)
       (f <> default_f ==> oEL 1 f_args = SOME (e_v (v_bool T))) /\
       (* Furthermore, the types of the arguments must agree with those associated with the action
        * in the relevant ftymap. *)
       (* Case 1: Block name is found in blftymap, and function name in the local ftymap.
         * Then, that local function type map applies. *)
       ((?ftys ret_ty local_ftymap.
         ALOOKUP blftymap block_name = SOME local_ftymap /\
         ALOOKUP local_ftymap (funn_name f) = SOME (ftys, ret_ty:tau) /\
         v_to_tau_list (DROP 2 f_args) = SOME (ftys)) \/
        (* Case 2: Either block name can't be found in blftymap, or function name can't be found in local ftymap.
         * Then, the global function type map applies. *)
        (ALOOKUP blftymap block_name = NONE \/
         (?local_ftymap.
          ALOOKUP blftymap block_name = SOME local_ftymap /\
          ALOOKUP local_ftymap (funn_name f) = NONE) /\
        (?ftys ret_ty. ALOOKUP ftymap (funn_name f) = SOME (ftys, ret_ty:tau) /\
         v_to_tau_list (DROP 2 f_args) = SOME (ftys))))
End

(* Old definition, using action list stored in in tbl_map:
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
*)

Definition v1model_tbl_is_well_formed_def:
 v1model_tbl_is_well_formed (ftymap, blftymap, pblock_action_names_map) (pblock_map:pblock_map) (tbl_name, tbl_entries) =
  !block_name pbl_type x_d_list b_func_map decl_list pars_map tbl_map action_names_map.
   ALOOKUP pblock_map block_name = SOME (pbl_type, x_d_list, b_func_map, decl_list, pars_map, tbl_map) ==>
   ALOOKUP pblock_action_names_map block_name = SOME action_names_map ==>
    !mk_l actions default_f default_f_args.
     ALOOKUP tbl_map tbl_name = SOME (mk_l, (default_f, default_f_args)) ==>
     ALOOKUP action_names_map tbl_name = SOME actions ==>
      !e_l.
      (* TODO: Keep the requirement that LENGTH e_l = LENGTH mk_l here? *)
      LENGTH e_l = LENGTH mk_l ==>
      !ctrl. ALOOKUP ctrl tbl_name = SOME tbl_entries ==>
      !counter ext_obj_map v_map. ?f f_args.
      v1model_apply_table_f (tbl_name, e_l, mk_l, (default_f, default_f_args), (counter, ext_obj_map, v_map, ctrl):v1model_ascope) = SOME (f, f_args) /\
       (* f is in the list of actions for the table *)
       MEM f actions /\
       (* first argument is the Boolean T, signifying that the function call resulted from table application *)
       (oEL 0 f_args = SOME (e_v (v_bool T))) /\
       (* first argument is either:
        * a Boolean, if action name is that of the default action... *)
       (f = default_f ==> ?b. oEL 1 f_args = SOME (e_v (v_bool b))) /\
       (* or the Boolean T, if action name is not that of the default action. *)
       (f <> default_f ==> oEL 1 f_args = SOME (e_v (v_bool T))) /\
       (* Furthermore, the types of the arguments must agree with those associated with the action
        * in the relevant ftymap. *)
       (* Case 1: Block name is found in blftymap, and function name in the local ftymap.
         * Then, that local function type map applies. *)
       ((?ftys ret_ty local_ftymap.
         ALOOKUP blftymap block_name = SOME local_ftymap /\
         ALOOKUP local_ftymap (funn_name f) = SOME (ftys, ret_ty:tau) /\
         v_to_tau_list (DROP 2 f_args) = SOME (ftys)) \/
        (* Case 2: Either block name can't be found in blftymap, or function name can't be found in local ftymap.
         * Then, the global function type map applies. *)
        (ALOOKUP blftymap block_name = NONE \/
         (?local_ftymap.
          ALOOKUP blftymap block_name = SOME local_ftymap /\
          ALOOKUP local_ftymap (funn_name f) = NONE) /\
        (?ftys ret_ty. ALOOKUP ftymap (funn_name f) = SOME (ftys, ret_ty:tau) /\
         v_to_tau_list (DROP 2 f_args) = SOME (ftys))))
End

val _ = export_theory ();
