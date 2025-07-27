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


Type intvl_table = “:('a intvl_row) list”;
Type intvl_table_list = “:('a intvl_table ) list”;


   

   
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


  


(* processing guards recursively *)
Definition process_guards_rec_def:
  (process_guards_rec _ _ [] acc = acc) ∧
  (process_guards_rec m_e max (g::gs) acc =
    let new_acc = FLAT (MAP (λrow. process_guard m_e max g [row]) acc) in
      process_guards_rec m_e max gs new_acc)
End



Definition convert_line_def:
  (convert_line m_e pd_type ([], s, res) = [(NONE, SOME (0,255), s, res)]) ∧  (* Default max *)
  (convert_line m_e pd_type (guards, s, res) =
   let lval_opt = 
       if EVERY is_True_or_False guards then NONE
       else case guards of
            | (Var x)::_ => (case ALOOKUP m_e x of
                             | SOME a => get_lval a
                             | NONE => NONE)
            | (Not (Var x))::_ => (case ALOOKUP m_e x of
                                   | SOME a => get_lval a
                                   | NONE => NONE)
            | _ => NONE
    in
      case lval_opt of
      | NONE => 
          let initial_row = [(NONE, SOME (0,255), s, res)] in  (* Default max *)
          process_guards_rec m_e 255 guards initial_row
      | SOME lv =>
          case resolve_pd_max pd_type lv of
            | SOME max => 
                let initial_row = [(SOME lv, SOME (0,max), s, res)] in
                process_guards_rec m_e max guards initial_row
            | NONE => []  (* Invalid field reference *)
  )
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


Definition collect_guard_lvals_def:
  (collect_guard_lvals m_e (Var x) = 
    case ALOOKUP m_e x of 
      | SOME a => (case get_lval a of
                    | SOME lv => SOME lv
                    | NONE => NONE)
      | NONE => NONE) ∧  (* Undefined var treated as NONE *)
  (collect_guard_lvals m_e (Not (Var x)) = 
    case ALOOKUP m_e x of 
      | SOME a => (case get_lval a of
                    | SOME lv => SOME lv
                    | NONE => NONE)
      | NONE => NONE) ∧  (* Undefined var treated as NONE *)
  (collect_guard_lvals _ _ = NONE)
End

Definition all_vars_defined_def:
  (all_vars_defined m_e [] = T) ∧
  (all_vars_defined m_e (g::gs) =
    ((case g of
       | Var x => (case ALOOKUP m_e x of SOME _ => T | NONE => F)
       | Not (Var x) => (case ALOOKUP m_e x of SOME _ => T | NONE => F)
       | _ => T) ∧ 
    all_vars_defined m_e gs))
End

        

Definition table_wf_def:
  table_wf tbl m_e =
    case tbl of
      | [] => T
      | (guards,_,_)::_ =>
          all_vars_defined m_e guards ∧
          let all_lvals = MAP (collect_guard_lvals m_e) guards in
          case FILTER IS_SOME all_lvals of
            | [] => T
            | (SOME lv)::rest => EVERY (λopt. opt = SOME lv ∨ opt = NONE) rest
            | _ => F
End


                        


Definition convert_single_table_def:
  convert_single_table tbl m_e pd_type =
    if table_wf tbl m_e then
      SOME (FLAT (MAP (λline. convert_line m_e pd_type line) tbl))
    else NONE
End



Definition convert_tables_def:
  (convert_tables [] _ _ = SOME []) ∧
  (convert_tables (tbl::tbls) m_e pd_type =
    case convert_single_table tbl m_e pd_type of
      | NONE => NONE  (* Fail fast if any table fails *)
      | SOME res =>
          case convert_tables tbls m_e pd_type of
            | NONE => NONE
            | SOME res' => SOME (res :: res'))
End

(*

val policy1_var = “[[([Var "x"; Var "y"],(0:num),state (3:num));
                     ([Var "x"; Not (Var "y")],0,state 4);
                     ([Not (Var "x")],0,state 4)];
                     
                    [([Var "z"],4,state 7);
                     ([Not (Var "z")],4,state (8:num));
                     ([True],3,state 3)];
                     
                    [([True],3,action ("fwd",[1]));
                     ([True],7,action ("fwd",[2]));
                     ([True],8,action ("drop",[]))]]”;



val test_pd_nested = ``[
  ("h", type_record [
    ("len", type_length 5);  (* 15 *)
    ("flags", type_length 5); (* 3 *)
    ("ttl", type_length 5) (* 3 *)
  ])
  ]``;


val test_pd_nested = ``[
  ("h", type_record [
    ("len", type_length 4);  (* 15 *)
    ("flags", type_length 2); (* 3 *)
    ("ttl", type_length 5); (* 3 *)
  ])
  ]``;


  
val test_lval1 = ``lv_acc (lv_x "h") "ttl"``;
val test_lval2 = ``lv_acc (lv_x "h") "flags"``;

val test_atom1 = ``arithm_gt ^test_lval1 0``;
val test_atom2 = ``arithm_lt ^test_lval1 10``;
val test_atom3 = ``arithm_gt ^test_lval2 1``;

  
val test_m_e = ``[("x", ^test_atom1); ("y", ^test_atom2); ("z", ^test_atom3) ]``;




EVAL ``convert_tables ^policy1_var ^test_m_e ^test_pd_nested``;


*)
        

(*
val test_lval = ``lv_x "ttl"``;
val test_atom = ``arithm_eq ^test_lval 5``;
val test_m_e = ``[("x", ^test_atom)]``;
val test_action = ``action "drop"``;
val test_state = ``state 1``;

(* PD type setups *)
val test_pd_basic = ``[("ttl", type_length 4)]``;  (* 2^4-1 = 15 *)
val test_pd_nested = ``[
  ("hdr", type_record [
    ("len", type_length 4);  (* 15 *)
    ("flags", type_length 2) (* 3 *)
  ])
  ]``;


val test_case1 = 
  EVAL ``convert_single_table [([Var "x"], 1, ^test_action)] ^test_m_e ^test_pd_basic``;


val test_case2 =
  EVAL ``convert_single_table [([Not (Var "x")], 2, ^test_state)] ^test_m_e ^test_pd_basic``;

val test_m_e_nested = ``[("y", arithm_eq (lv_acc (lv_x "hdr") "len") 5)]``;
val test_case3 =
  EVAL ``convert_single_table [([Var "y"], 3, ^test_action)] ^test_m_e_nested ^test_pd_nested``;

val test_case4 =
  EVAL ``convert_single_table [([Var "missing"], 4, ^test_state)] ^test_m_e ^test_pd_basic``;

  
val test_case5 =
  EVAL ``convert_single_table [([Var "x"; Var "missing"], 5, ^test_action)] ^test_m_e ^test_pd_basic``;

val test_case6 =
  EVAL ``convert_single_table [([True; False], 6, ^test_state)] ^test_m_e ^test_pd_basic``;

val test_case7 =
  EVAL ``convert_single_table [([Var "x"; Not (Var "x")], 7, ^test_action)] ^test_m_e ^test_pd_basic``;

val test_m_e_with_undefined = ``[("x", ^test_atom); ("missing", arithm_eq (lv_x "undefined") 0)]``;
val test_case4a =
  EVAL ``convert_single_table [([Var "missing"], 4, ^test_state)] ^test_m_e_with_undefined ^test_pd_basic``;


(* Test data *)
val test_tbl1 = ``[([Var "x"], (1:num), action "a")]``;
val test_tbl2 = ``[([Not (Var "x")], (2:num), action "b")]``;
val test_m_e = ``[("x", arithm_eq (lv_x "ttl") 5)]``;
val test_pd = ``[("ttl", type_length 4)]``; (* MAX=15 *)

(* Flattened version *)
EVAL ``convert_tables [^test_tbl1; ^test_tbl2] ^test_m_e ^test_pd``;
(* SOME [
   [(SOME (lv_x "ttl"), SOME (5,5), 1, action "a")],
   [(SOME (lv_x "ttl"), SOME (0,4), 2, state 1);
    (SOME (lv_x "ttl"), SOME (6,15), 2, state 1)]
] *)
         
*)





                       

(* SEMANTICS *)







Definition sem_interval_def:
  (sem_interval (v:num) (SOME (lo, hi)) = (lo ≤ v ∧ v ≤ hi)) ∧
  (sem_interval _ NONE = F)  (* False interval *)
End


(* Check if an interval row matches *)
Definition is_intvl_match_row_def:
  is_intvl_match_row (st_in:num) (st_num:num) (interval: (num # num) option) v =
    (st_in = st_num ∧ sem_interval v interval)
End




(* Process all rows in an interval table *)
Definition check_all_intvl_rows_match_def:
  check_all_intvl_rows_match st_in intvl_tbl v =
  MAP (λ((lval_opt:arith_lv option ), intervall, st_num, res). 
                  (is_intvl_match_row st_in st_num intervall v, (res:'a action_expr))) intvl_tbl
End



(* Find first matching line in a converted table *)
Definition match_intvl_tbl_def:
  match_intvl_tbl (intvl_tbl: (('a intvl_row) list)) v st_in =
  let lines_res = check_all_intvl_rows_match st_in intvl_tbl v in
  case min_idx_till lines_res T of
    | SOME (idx, line) => SOME (SND line)
    | NONE => NONE
End




(* Process list of interval tables with state propagation *)
Definition match_intvl_tbll_def:
  (match_intvl_tbll ([]: 'a intvl_table_list) _ _ = NONE) ∧
  (match_intvl_tbll [intvl_tbl] v st_in =
    case match_intvl_tbl intvl_tbl v st_in of
      | SOME (action a) => SOME (action a)
      | _ => NONE) ∧
  (match_intvl_tbll (intvl_tbl::intvl_tbls) v st_in =
    case match_intvl_tbl intvl_tbl v st_in of
      | SOME (state n) => match_intvl_tbll intvl_tbls v n
      | _ => NONE)
End




(* Top-level interval table semantics *)
Definition sem_intvl_tables_def:
  sem_intvl_tables ((intvl_tbll: (('a intvl_table ) list)), st_in) v =
  match_intvl_tbll intvl_tbll v st_in
End



(*
val test_last_table = ``[
  (SOME (lv_x "ttl"), SOME ((5:num),(10:num)), (1:num), action "accept");
  (SOME (lv_x "ttl"), SOME (0,20), 1, action "reject")
]``;

EVAL ``sem_intvl_tables ([^test_last_table], 1) 7``; 
EVAL ``sem_intvl_tables ([^test_last_table], 1) 15``;





val test_tables = ``[
  (* Table 1: Accept small packets *)
  [(SOME (lv_x "size"), SOME ((0:num),(500:num)), (1:num), state 2);
   (SOME (lv_x "size"), SOME (501,1500), 1, state 2)];
   
  (* Table 2: Process medium packets *)  
  [(SOME (lv_x "size"), SOME (501,1000), 3, state 4);
   (SOME (lv_x "size"), SOME (900,1500), 2, state 5)];
   
  (* Table 3: Reject large packets *)
  [(SOME (lv_x "size"), SOME (501,1000), 4, action "accept");
   (SOME (lv_x "size"), SOME (501,1000), 5, action "reject")]
]``;


EVAL ``sem_intvl_tables (^test_tables, 1) 1000``;
*)





        
















     



        
                                                                

val _ = export_theory ();

    

