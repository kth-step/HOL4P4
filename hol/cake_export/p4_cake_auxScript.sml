open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_cake_aux";

(* For concise display of bitstrings: *)
(* TODO: Move up to more fundamental theory *)
Definition word_def:
 word value width = (fixwidth width $ n2v value, width)
End

(* TODO: Write all the below parts in SML instead? *)

Datatype:
 tau_in =
   tau_in_bit_rand num
 | tau_in_bit_fix (num # num)
 | tau_in_xtl struct_ty ((string # tau_in) list)
End

Definition tau_of_type_def:
 tau_of_type t =
  case t of
     t_tau tau => SOME tau
   | t_string_names_a _ => NONE
End

(* Only used for utility, so arbs are not a problem *)
Definition tau_to_tau_in_def:
 tau_to_tau_in tau =
  case tau of
     tau_bit n => tau_in_bit_rand n
   | tau_bool => tau_in_bit_rand 1
   | tau_xtl struct_ty x_tau_l =>
    tau_in_xtl struct_ty
    (ZIP (MAP FST x_tau_l, MAP tau_to_tau_in (MAP SND x_tau_l)))
Termination
WF_REL_TAC ‘measure tau_size’ >>
rpt strip_tac >>
subgoal ‘?b. MEM (b,a) x_tau_l’ >- (
 imp_res_tac listTheory.MEM_EL >>
 qexists_tac ‘EL n (MAP FST x_tau_l)’ >>
 simp[listTheory.MEM_EL] >>
 qexists_tac ‘n’ >>
 gvs[p4_auxTheory.EL_pair_list]
) >>
imp_res_tac p4Theory.tau1_size_mem >>
fs[]
End

Definition tau_in_to_list_def:
 tau_in_to_list tau_in =
  case tau_in of
     tau_in_bit_rand n => [tau_in_bit_rand n]
   | tau_in_bit_fix (n',m) => [tau_in_bit_fix (n',m)]
   | tau_in_xtl struct_ty x_tau_in_l =>
    (case x_tau_in_l of
       [] => []
     | (h::t) => (tau_in_to_list (SND h)) ++ (tau_in_to_list (tau_in_xtl struct_ty t)))
End

Definition tau_in_sum_def:
 tau_in_sum tau_in =
  case tau_in of
     tau_in_bit_rand n => n
   | tau_in_bit_fix (n',m) => m
   | tau_in_xtl struct_ty x_tau_in_l =>
    (case x_tau_in_l of
       [] => 0
     | (h::t) => (tau_in_sum (SND h)) + (tau_in_sum (tau_in_xtl struct_ty t)))
End

Datatype:
 acc =
   acc_struct string acc
 | acc_fld string
End

Definition update_tau_in_def:
 (update_tau_in (acc_struct string acc) new_val tau_in =
  case tau_in of
      tau_in_bit_rand n => NONE
    | tau_in_bit_fix (n',m) => NONE
    | tau_in_xtl struct_ty x_tau_in_l =>
     (case ALOOKUP x_tau_in_l string of
      | SOME tau_in' =>
       (case update_tau_in acc new_val tau_in' of
        | SOME tau_in'' =>
         SOME $ tau_in_xtl struct_ty (p4$AUPDATE x_tau_in_l (string, tau_in''))
        | NONE => NONE)
      | NONE => NONE)) /\
 (update_tau_in (acc_fld field_name) new_val tau_in =
  case tau_in of
      tau_in_bit_rand n => NONE
    | tau_in_bit_fix (n',m) => NONE
    | tau_in_xtl struct_ty x_tau_in_l =>
     (case ALOOKUP x_tau_in_l field_name of
      | SOME $ tau_in_bit_rand n'' =>
       SOME $ tau_in_xtl struct_ty (p4$AUPDATE x_tau_in_l (field_name, tau_in_bit_fix (new_val, n'')))
      | SOME $ tau_in_bit_fix (n',m') =>
       SOME $ tau_in_xtl struct_ty (p4$AUPDATE x_tau_in_l (field_name, tau_in_bit_fix (new_val, m')))
      | _ => NONE))
End

Definition filter_tau_in_def:
 filter_tau_in (tau_in_xtl struct_ty x_tau_in_l) include_list =
  tau_in_xtl struct_ty (FILTER (\el. MEM (FST el) include_list) x_tau_in_l)
End
    
val _ = export_theory();
