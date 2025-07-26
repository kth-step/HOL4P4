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

open policy_arith_to_varTheory;


val _ = new_theory "table_var_to_arith";




val _ = Hol_datatype ` 
  interval = Empty | Single of num => num | Union of interval => interval
`;


Type intvl_row = “:arith_lv option # (num # num) option # num # 'a action_expr”;
(* None = Empty, Some (a,b) = Single [a,b] *)
(* arith_lv from policy_arith_to_var*)

   
val _ = Hol_datatype `
   arith_atom_result = 
    SingleAtom of arithm_atom
  | UnionAtoms of arithm_atom => arithm_atom`;



val _ = Hol_datatype `
  pd_type = 
     type_length of num   
   | type_record of (string # pd_type) list  (* [f1:bs; ...; fn:bs_n] *)
`;

Type pd_type_struct = “: (string # pd_type) list”; 


                                                                


Definition get_lval_def:
  get_lval (a_True) = NONE ∧
  get_lval (a_False) = NONE ∧
  get_lval (arithm_gt lv _) = SOME lv ∧
  get_lval (arithm_lt lv _) = SOME lv ∧
  get_lval (arithm_eq lv _) = SOME lv
End



(* Convert atom_var to arithm_atom using m_e
   i.e. each cell in the line of var table will be converted
   directly to an aritmetic atom via this def.
 *)



               
Definition atom_to_arith_def:
  (atom_to_arith m_e True = SOME (SingleAtom a_True)) ∧
  (atom_to_arith m_e False = SOME (SingleAtom a_False)) ∧
  (atom_to_arith m_e (Var x) = 
    case ALOOKUP m_e x of
      | SOME a => SOME (SingleAtom a)
      | NONE => NONE) ∧
  (atom_to_arith m_e (Not a) = 
    case atom_to_arith m_e a of
      | SOME (SingleAtom a_True) => SOME (SingleAtom a_False)
      | SOME (SingleAtom a_False) => SOME (SingleAtom a_True)
      | SOME (SingleAtom (arithm_gt lv n)) => SOME (SingleAtom (arithm_lt lv (n+1)))
      | SOME (SingleAtom (arithm_lt lv n)) => SOME (SingleAtom (arithm_gt lv (n-1)))
      | SOME (SingleAtom (arithm_eq lv n)) => 
          if n = 0 then SOME (SingleAtom (arithm_gt lv 0))
          else SOME (UnionAtoms (arithm_lt lv n) (arithm_gt lv n))
      | SOME (UnionAtoms _ _) => NONE (* should not happen *)
      | NONE => NONE)
End





Definition arith_to_interval_def:
  (arith_to_interval a_True max = Single 0 max) ∧
  (arith_to_interval a_False max = Empty) ∧
  (arith_to_interval (arithm_gt _ n) max = 
     if n ≥ max then Empty else Single (n+1) max) ∧
  (arith_to_interval (arithm_lt _ n) max = 
     if n ≤ 0 then Empty else Single 0 (n-1)) ∧
  (arith_to_interval (arithm_eq _ n) max = 
     if n < 0 ∨ n > max then Empty else Single n n)
End
        
    

Definition intersect_single_def:
  intersect_single (SOME (a1,b1)) (Single a2 b2) =
  (let a = MAX a1 a2 in
     let b = MIN b1 b2 in
       if a ≤ b then
         SOME (a,b)
       else
         NONE
  ) ∧
  (intersect_single _ _ = NONE)
End





Definition is_True_or_False_def:
  is_True_or_False g =
  ((g = True) ∨ (g = False))
End







Definition process_guard_def:
  (process_guard _ _ _ [] = []) ∧
  (process_guard m_e max g (((lval_opt: arith_lv option), curr_int, (s:num), (res: 'a action_expr))::rows) =
    (case (atom_to_arith m_e g, curr_int) of
      | (NONE, _) => []
      | (SOME _, NONE) => [(lval_opt, NONE, s, res)] (* False interval *)
      | (SOME (SingleAtom a), SOME curr) =>
          (case intersect_single (SOME curr) (arith_to_interval a max) of
             | NONE => [(lval_opt, NONE, s, res)] (* Now returns False line *)
             | SOME new => [(lval_opt, SOME new, s, res)]
          )
      | (SOME (UnionAtoms a1 a2), SOME curr) =>
          (case (intersect_single (SOME curr) (arith_to_interval a1 max),
                 intersect_single (SOME curr) (arith_to_interval a2 max)) of
             | (NONE, NONE) => [(lval_opt, NONE, s, res)] (* False line *)
             | (SOME i1, NONE) => [(lval_opt, SOME i1, s, res)]
             | (NONE, SOME i2) => [(lval_opt, SOME i2, s, res)]
             | (SOME i1, SOME i2) => [(lval_opt, SOME i1, s, res);
                                      (lval_opt, SOME i2, s, res)]
          )
    ) ++ process_guard m_e max g rows)
End





(*
val test_lval = “lv_x "ttl"”;
val test_atom_eq = “arithm_eq ^test_lval 5”;
val test_atom_gt = “arithm_gt ^test_lval 3”;
val test_atom_lt = “arithm_lt ^test_lval 7”;

(* Test m_e mapping *)
val test_m_e = “[("x", ^test_atom_eq); ("y", ^test_atom_gt); ("z", ^test_atom_lt)]”;

(* Test row components *)
val test_s = “(1:num)”;
val test_res = “action "foo"”;
val test_lval_opt = “SOME ^test_lval”;
val test_curr_int = “SOME ((0:num), (10:num))”;  (* Initial interval [0,10] *)


val test_case1 = 
  EVAL “process_guard ^test_m_e 10 True [(^test_lval_opt, ^test_curr_int, ^test_s, ^test_res)]”;
(* expected: [(SOME (lv_x "ttl"), SOME (0,10), 1, action "foo")] *)

val test_case2 = 
  EVAL “process_guard ^test_m_e 10 (Var "x") [(^test_lval_opt, ^test_curr_int, ^test_s, ^test_res)]”;
(* expected: [(SOME (lv_x "ttl"), SOME (5,5), 1, action "foo")]  (exact match) *)
   
val test_case3 = 
  EVAL “process_guard ^test_m_e 10 (Var "y") [(^test_lval_opt, SOME ((0:num),(2:num)), ^test_s, ^test_res)]”;
(* expected: [(SOME (lv_x "ttl"),NONE,1,action "foo")]  (gt 3 doesn't intersect with [0,2]) *)

   
val test_case4 = 
  EVAL “process_guard ^test_m_e 10 (Not (Var "x")) [(^test_lval_opt, ^test_curr_int, ^test_s, ^test_res)]”;
(* expected: [
   (SOME (lv_x "ttl"), SOME (0,4), 1, action "foo"),
   (SOME (lv_x "ttl"), SOME (6,10), 1, action "foo")
] *)


val test_case5 = 
  EVAL “process_guard ^test_m_e 10 (Var "z") [
    (^test_lval_opt, SOME ((0:num),(5:num)), ^test_s, ^test_res);
    (^test_lval_opt, SOME ((8:num),(10:num)), ^test_s, ^test_res)
                                     ]”;

(* expected: [
   (SOME (lv_x "ttl"),SOME (0,5),1,action "foo");
      (SOME (lv_x "ttl"),NONE,1,action "foo")
] *)


val test_case6 = 
  EVAL “process_guard ^test_m_e 10 (Var "undefined") [(^test_lval_opt, ^test_curr_int, ^test_s, ^test_res)]”;

(* expected: []  (because lookup returns NONE) *)
*)
  


(* processing guards recursively *)
Definition process_guards_rec_def:
  (process_guards_rec _ _ [] acc = acc) ∧
  (process_guards_rec m_e max (g::gs) acc =
    let new_acc = FLAT (MAP (λrow. process_guard m_e max g [row]) acc) in
      process_guards_rec m_e max gs new_acc)
End




Definition convert_line_def:
  (convert_line m_e max ([], s, res) = [(NONE, SOME (0,max), s, res)]) ∧
  (convert_line m_e max (guards, s, res) =
    let lval_opt = if EVERY is_True_or_False guards then NONE
                   else (case guards of
                        | (Var x)::_ => (case ALOOKUP m_e x of
                                         | SOME a => get_lval a
                                         | NONE => NONE)
                        | (Not (Var x))::_ => (case ALOOKUP m_e x of
                                               | SOME a => get_lval a
                                               | NONE => NONE)
                        | _ => NONE
                        )
    in
      let initial_row = [(lval_opt, SOME (0,max), s, res)] in
        process_guards_rec m_e max guards initial_row
  )
End



(*
val test_lval = ``lv_x "ttl"``;
val test_atom = ``arithm_eq ^test_lval 5``;
val test_m_e = ``[("x", ^test_atom)]``;
val test_action = ``action "test"``;
val test_state = ``state 1``;
val test_curr_int = ``SOME (0,10)``;
val test_lval_opt = ``SOME ^test_lval``;



val test_case1 = 
  EVAL ``convert_line [] 100 ([], 0, ^test_action)``;
(* expect: [(NONE, SOME (0,100), 0, action "test")] *)

val test_case2a = 
  EVAL ``convert_line [] 100 ([True; False], 1, ^test_state)``;
(* expect: [(NONE,NONE,1,state 1)] *)


val test_case2b = 
  EVAL ``convert_line [] 100 ([True; True], 1, ^test_state)``;
(* expect: [(NONE, SOME (0,100), 1, state 1)] *)

      
(* Test 3: Single variable guard *)
val test_case3 = 
  EVAL ``convert_line ^test_m_e 10 ([Var "x"], 2, ^test_action)``;
(* Expect: [(SOME (lv_x "ttl"), SOME (5,5), 2, action "test")] *)

(* Test 4: Single negated variable *)
val test_case4 = 
  EVAL ``convert_line ^test_m_e 10 ([Not (Var "x")], 3, ^test_state)``;
(* Expect: [
     (SOME (lv_x "ttl"), SOME (0,4), 3, state 1),
     (SOME (lv_x "ttl"), SOME (6,10), 3, state 1)
   ] *)

(* Test 5: Undefined variable *)
val test_case5 = 
  EVAL ``convert_line ^test_m_e 10 ([Var "y"], 4, ^test_action)``;
(* Expect: [] *)

(* Test 6: Mixed guards *)
val test_case6 = 
  EVAL ``convert_line ^test_m_e 10 ([True; Var "x"; False], 5, ^test_state)``;
(* Expect: [(NONE,NONE,5,state 1)] *)

(* Test 7: Contradictory guards *)
val test_case7 = 
  EVAL ``convert_line ^test_m_e 10 ([Var "x"; Not (Var "x")], 6, ^test_action)``;
(* Expect: [(SOME (lv_x "ttl"),NONE,6,action "test")] *)

(* Test 8: Boundary case (0) *)
val test_zero_atom = ``arithm_eq ^test_lval 0``;
val test_m_e_zero = ``[("zero", ^test_zero_atom)]``;
val test_case8 = 
  EVAL ``convert_line ^test_m_e_zero 10 ([Not (Var "zero")], 7, ^test_state)``;
(* Expect: [(SOME (lv_x "ttl"), SOME (1,10), 7, state 1)] *)

(* Test 9: Multiple variables *)
val test_atom_gt = ``arithm_gt ^test_lval 3``;
val test_m_e_multi = ``[("x", ^test_atom); ("y", ^test_atom_gt)]``;
val test_case9 = 
  EVAL ``convert_line ^test_m_e_multi 10 ([Var "x"; Var "y"], 8, ^test_action)``;
(* [5,5] and [4,10]
   Expect: [(SOME (lv_x "ttl"), SOME (5,5), 8, action "test")] *)

*)



Definition resolve_lval_type_def:
  (resolve_lval_type (pd_type:pd_type_struct) (lv_x var) = ALOOKUP pd_type var ) ∧
  (resolve_lval_type pd_type (lv_acc lval var) = 
    case resolve_lval_type  pd_type lval of
    | SOME (type_record fields) => ALOOKUP fields var
    | _ => NONE)
End


Definition max_from_type_def:
  max_from_type type =
  (2:num) ** type - (1:num)
End


Definition resolve_pd_max_def:
  resolve_pd_max pd_type lval =
    case resolve_lval_type pd_type lval of
      | SOME (type_length n) => SOME (max_from_type n)
      | _ => NONE
End

(*        
val test_packet = “[
                      ("h", type_record [
                           ("ip", type_record [
                                ("ttl", type_length 64);
                                ("proto", type_length 6);
                                ("version", type_length 4)
                              ]);
                           ("src_zone", type_length 1);
                           ("threat_score", type_length 30);
                           ("auth_status", type_length 1)
                         ])
                    ]”;


                    
EVAL “resolve_pd_max ^test_packet (lv_acc (lv_acc (lv_x "h") "ip") "proto")”;
*)


        
                                                                

val _ = export_theory ();

    

