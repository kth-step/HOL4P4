open HolKernel boolLib liteLib simpLib Parse bossLib;
open arithmeticTheory stringTheory containerTheory pred_setTheory
     listTheory finite_mapTheory;

open p4Lib;
open blastLib bitstringLib;
open p4Theory;
open p4_auxTheory;
open p4_coreTheory;

open bitstringTheory;
open wordsTheory;
open optionTheory;
open sumTheory;
open stringTheory;
open ottTheory;
open pairTheory;
open rich_listTheory;
open arithmeticTheory;
open alistTheory;
open numeralTheory;
open alistTheory;
open set_relationTheory;
open pred_setTheory;
open pred_setLib;

open bdd_genTheory;     
open pred_specTheory;     
open policy_specTheory;     
     
open tables_specTheory;

val _ = new_theory "tables_spec_new";

    


(* table simplifications *)


(*
examples of checks:
1. how many times we call?
When is it final?

mk_bdd 

*)



(*)
Definition simp_row_new_def:
  simp_row_new atoml =
  let simplified_row = MAP (\atom. simp_atom atom) atoml in
    let simplified_row' = FILTER (\x. is_not_true_var_atom x) simplified_row in
    case MEM False simplified_row' of
    | T => [False]
    | F => (

      FILTER (\x. is_not_true_var_atom x) simplified_row
    )
End
*)

(*
Definition simp_row_new_def:
  (simp_row_new [] = [True]) /\
  (simp_row_new (a::atoml) =
  let sa = simp_atom a in
  (case sa of
   | False => [False]
   | True => simp_row_new atoml
   | _ => sa ::( simp_row_new atoml)
  )
  )
End



Definition simp_tbl_new_def:
  simp_tbl_new ([]: 'a var_table) = [] /\
  simp_tbl_new ((atom,st,res)::tbl) = 
  let atom' = simp_row_new atom in
  case atom' of
  | [False] => simp_tbl_new tbl
  | [True] => [([True],st,res)]
  | _ => (atom',st,res)::(simp_tbl_new tbl) 
End



(*
Definition simp_tbl_new_def:
  simp_tbl_new (tbl: 'a var_table) =
  let st = MAP (\(atoml,st_num,res). simp_row_new atoml,st_num,res) tbl in
    FILTER (\(atoml,st,res). atoml <> [False]) st
End
*)

Definition simp_tbll_new_def:
  simp_tbll_new (tbll: 'a var_table_list) =
   MAP (\tbl. simp_tbl_new tbl) tbll
End


Definition simp_tables_new_def:
  simp_tables_new ((tbll: 'a var_table_list), st_in) =
   (simp_tbll_new tbll, st_in:num)
End
 
*)



Definition is_not_true_var_atom_def:
  (is_not_true_var_atom True = F) /\
  (is_not_true_var_atom _ = T)
End



Definition simp_row_new_def:
  simp_row_new atoml =
  let simp_row = MAP (\atom. simp_atom atom) atoml in
    let simp_row' = FILTER (\x. is_not_true_var_atom x) simp_row in
      case simp_row' of
      | [] => [True]
      | _ => 
          (case MEM False simp_row' of
           | T => [False]
           | F => simp_row')
End


        



Definition simp_table_new_def:
  (simp_table_new [] s = []) ∧
                  
  (simp_table_new ((atoms,st,res)::table)  NONE =
   let atoms' = simp_row_new atoms in
     case atoms' of
     | [False] => simp_table_new table NONE
     | _ =>  ((atoms', st, res)::simp_table_new table NONE)
  ) ∧
    
  (simp_table_new ((atoms,st,res)::table) (SOME s') =
   if (s' ≠ st) then
     simp_table_new table (SOME s')
   else
     (
     let atoms' = simp_row_new atoms in
       case atoms' of
       | [False] => simp_table_new table (SOME s')
       | [True] => [(atoms', st, res)]
       | _ =>  ((atoms', st, res) :: (simp_table_new table (SOME s')))
     )
  )
End



                        


Definition simp_tables_new_def:
  (simp_tables_new [] s = []) ∧
  (simp_tables_new (t::table) s = 
   (let t' = simp_table_new t s in
      ( case t' of
        | [([True], s , state s'')] => (t'::(simp_tables_new table (SOME s'')))
        | _ => (t'::(simp_tables_new table NONE))
      )
   )
  )
End




Definition simp_tables_wrapper_new_def:
  simp_tables_wrapper_new ((tbll: 'a var_table_list), st_in) =
   (simp_tables_new tbll (SOME st_in), st_in)
End






(*****************************)


Definition final_row_new_def:
  (final_row_new ([],_,_) s = NONE) ∧
  (final_row_new ([True], s', s'') s = (if s = s' then SOME s'' else NONE)) ∧
  (final_row_new _ s = NONE)
End
        



Definition final_tbl_new_def:
  (final_tbl_new [] s = NONE) ∧
  (final_tbl_new (row::rows) s =         
     case final_row_new row s of
       SOME a => SOME a
     | NONE => if (FST row = [False]) then final_tbl_new rows s else NONE
  )
End



Definition final_tbll_new_def:
  final_tbll_new ([]: 'a var_table_list) st_in = NONE ∧
  final_tbll_new [tbl] st_in =
  ( case final_tbl_new tbl st_in of
    | SOME (action a) => SOME (action a)
    | _ => NONE       
  )∧
  final_tbll_new (tbl::tbls) st_in =
  ( case final_tbl_new tbl st_in of
    | SOME (state n) => final_tbll tbls n
    | _ => NONE
  )
End


Definition final_tables_new_def:
  final_tables_new (tbll, st_in) =
  final_tbll_new tbll st_in
End









        


Definition table_structure_new_def:
  table_structure_new =
  <|
    sem := sem_tables;
    sub := mk_substitute_tables;
    simp := simp_tables_wrapper_new;
    final := final_tables_new;
    fv := fv_tables;
  |>
End            





                 
val _ = export_theory ();

    
