open HolKernel boolLib liteLib simpLib Parse bossLib;

open p4Theory;

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

Theorem p4_symb_exec_unify:
!P1 P2 ctx s Q.
p4_contract (P1 /\ P2) ctx s Q ==>
p4_contract (~P1 /\ P2) ctx s Q ==>
p4_contract P2 ctx s Q
Proof
fs[p4_contract_def] >>
metis_tac []
QED

(* For branching and unification *)

(* OLD, with superfluous base case
Definition list_disj_def:
 (list_disj [] = T) /\
 (list_disj (h::t) = (h \/ list_disj t))
End
*)
(* TODO: What should the base case be? *)
Definition list_disj_def:
 (list_disj (h::t) =
  if t = []
  then h
  else (h \/ list_disj t))
End

Definition p4_contract_list_def:
 (p4_contract_list [] P ctx s Q = p4_contract P ctx s Q) /\
 (p4_contract_list (h::t) P ctx s Q =
  if t = []
  then p4_contract (h /\ P) ctx s Q
  else (p4_contract (h /\ P) ctx s Q /\ p4_contract_list t P ctx s Q))
End

val _ = export_theory ();
