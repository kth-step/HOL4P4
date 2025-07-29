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

(*============================*)
(*    Types of arith tables   *)
(*============================*)

        
val _ = Hol_datatype ` 
  interval = Empty | Single of bitv => bitv
`;

val _ = Hol_datatype ` 
  airth_key = key_val of arith_lv | key_const of bitv
`;

        
Type intvl_row = “:(interval # num # 'a action_expr)”;
Type intvl_table = “:(airth_key # 'a intvl_row list)”;
Type intvl_table_list = “:('a intvl_table ) list”;


val _ = Hol_datatype `
  pd_type = 
     type_length of num   
   | type_record of (string # pd_type) list  (* [f1:bs; ...; fn:bs_n] *)
`;

Type pd_type_struct = “: (string # pd_type) list”; 





(*============================*)
(*    Auxiliary definitions   *)
(*============================*)

     
Definition get_lval_def:
  get_lval (a_True) = NONE ∧
  get_lval (a_False) = NONE ∧
  get_lval (arithm_gt lv _) = SOME lv ∧
  get_lval (arithm_lt lv _) = SOME lv
End

        
(* given a truct type and lval, this retrives the field type
 or bs width *)
Definition resolve_lval_type_def:
    resolve_lval_type pd_type lval = case lval of
    | lv_x var => ALOOKUP pd_type var
    | lv_acc lval var => 
        case resolve_lval_type pd_type lval of
          | SOME (type_record fields) => ALOOKUP fields var
          | _ => NONE
End

        
Definition max_from_type_def:
  max_from_type type =
  (2:num) ** type - (1:num)
End


Definition resolve_pd_min_max_def:
  resolve_pd_min_max pd_type lval =
    case resolve_lval_type pd_type lval of
      | SOME (type_length n) => SOME ((n2v 0, n), ( n2v (max_from_type n), n)  )
      | _ => NONE
End



Definition add_one_to_bv_def:
  add_one_to_bv bv=
  let (b,v) = bv in
    bitv_binop binop_add (b,v) (n2v 1, v)
End
    


Definition sub_one_of_bv_def:
  sub_one_of_bv bv=
  let (b,v) = bv in
    bitv_binop binop_sub (b,v) (n2v 1, v)
End
    


Definition bv_gt_than_def:
  bv_gt_than bv bv' =
  bitv_binpred binop_gt bv bv'
End


Definition bv_lt_than_def:
  bv_lt_than bv bv' =
  bitv_binpred binop_lt bv bv'
End


Definition bv_eq_to_def:
  bv_eq_to bv bv' =
  bitv_binpred binop_eq bv bv'
End
        




        
        
(*
EVAL “bitv_binpred binop_gt (n2v 2, (2:num)) (n2v 1, (2:num))”
*)
    


(*==================================*)
(*    Atoms coversion definitions   *)
(*==================================*)

    
(* Convert atom_var to arithm_atom using m_e
   i.e. each cell in the line of var table will be converted
   directly to an aritmetic atom via this def. *)


   
Definition atom_to_arith_def:
  atom_to_arith m_e g =
  (case g of
  | True => SOME a_True
  | False => SOME a_False
  | Var x => ALOOKUP m_e x
  | Not a => 
      (case atom_to_arith m_e a of
      | SOME a_True => SOME a_False
      | SOME a_False => SOME a_True
      | SOME (arithm_gt lv bv) =>
          ( case (add_one_to_bv bv) of
            | NONE => NONE
            | SOME bv' => SOME (arithm_gt lv bv')
          )
      | SOME (arithm_lt lv bv) =>
          ( case (sub_one_of_bv bv) of
            | NONE => NONE
            | SOME bv' => SOME (arithm_lt lv bv')
          )
      | NONE => NONE))
End
        
  


Definition arith_to_interval_def:
  arith_to_interval a min max =
    case a of
    | a_True => Single min max
    | a_False =>  Empty
    | arithm_gt _ n => 
        (case (bv_gt_than n max, bv_eq_to n max, add_one_to_bv n) of
        | (SOME T, _, _) => Empty
        | (SOME F, SOME T, _) => Empty
        | (SOME F, SOME F, SOME bv') => Single bv' max
        | _ => Empty)
    | arithm_lt _ n =>
        (case (bv_lt_than n min, bv_eq_to n min, sub_one_of_bv n) of
         | (SOME T, _, _) => Empty          (* n < min *)
         | (SOME F, SOME T, _) => Empty     (* n = min *)
         | (SOME F, SOME F, SOME bv') =>    (* n > min *)
             (case bv_gt_than n max of
              | SOME T => Single min max    (* n > max *)
              | SOME F => Single min bv'    (* min < n ≤ max *)
              | NONE => Empty
              | _ => Empty)
         | _ => Empty)
End



(*
val test_1_bs = “(n2v 1, (4:num))”;
val test_min  = “(n2v 0, (4:num))”;
val test_max  = “(n2v 4, (4:num))”;
        
EVAL “arith_to_interval (arithm_gt l ^test_1_bs) ^test_min ^test_max ”;  (*[2,4]*)
EVAL “arith_to_interval (arithm_gt l (n2v 4, (4:num))) ^test_min ^test_max”; (*empty interval*)
EVAL “arith_to_interval (arithm_gt l (n2v 5, (4:num))) ^test_min ^test_max”; (*empty interval*)
EVAL “arith_to_interval (arithm_gt l (n2v 0, (4:num))) ^test_min ^test_max”; (*[1,4]*)

val test_2_bs = ``(n2v 2, (4:num))``;
val test_max2  = ``(n2v 15, (4:num))``;

EVAL “arith_to_interval (arithm_lt l ^test_2_bs) ^test_min ^test_max2”;  (* [0,1] since x < 2 *)
EVAL “arith_to_interval (arithm_lt l ^test_min) ^test_min ^test_max2”;   (* Empty since x < 0 *)
EVAL “arith_to_interval (arithm_lt l ^test_max2) ^test_min ^test_max2”;  (* [0,14] since x < 15 *)
EVAL ``arith_to_interval (arithm_lt l (n2v 16, (4:num))) ^test_min ^test_max2``; (* Empty, invalid input *)
EVAL ``arith_to_interval (arithm_lt l (n2v 15, (4:num))) ^test_min ^test_max2``; (* [0,14] since x < 15 *)
EVAL ``arith_to_interval (arithm_lt l ^test_4_bs) ^test_min ^test_max2``;  (* [0,0] since x < 1 *)         
*)


        
Definition intersect_single_def:
  (intersect_single (Single (v1,w1) (v2,w2)) (Single (v3,w3) (v4,w4)) =
    if (w1 = w2) ∧ (w2 = w3) ∧ (w3 = w4) then
      case (bv_gt_than (v1,w1) (v3,w3), bv_gt_than (v2,w2) (v4,w4)) of
        | (SOME a1_gt_a2, SOME b1_gt_b2) =>
            let lower = if a1_gt_a2 then (v1,w1) else (v3,w3) in
            let upper = if b1_gt_b2 then (v4,w4) else (v2,w2) in
            case bv_gt_than lower upper of
              | SOME T => Empty
              | SOME F => Single lower upper
              | NONE => Empty
        | _ => Empty
    else Empty) ∧
  (intersect_single Empty _ = Empty) ∧
  (intersect_single _ Empty = Empty)
End

(*        
(* Test bitvectors - 4-bit width *)
val test_lo =  “(n2v 2, (4:num))”;  (* 2 in 4 bits *)
val test_mid = “(n2v 5, (4:num))”; (* 5 in 4 bits *)
val test_hi =  “(n2v 7, (4:num))”;  (* 7 in 4 bits *)
val test_min = “(n2v 0, (4:num))”; (* 0 in 4 bits *)
val test_max = “(n2v 15, (4:num))”; (* 15 in 4 bits *)

EVAL “intersect_single (Single ^test_lo ^test_hi) (Single ^test_mid ^test_max)”;(* Single (n2v 5,4) (n2v 7,4) *)
EVAL “intersect_single (Single ^test_min ^test_lo) (Single ^test_hi ^test_max)”;(* Empty, non-overlapping intervals *)
EVAL “intersect_single (Single ^test_mid ^test_hi) (Single ^test_mid ^test_hi)”;(* Single (n2v 5,4) (n2v 7,4) *)
EVAL “intersect_single (Single ^test_min ^test_max) (Single ^test_lo ^test_hi)”;(* Single (n2v 2,4) (n2v 7,4), one interval contained within another *)
EVAL “intersect_single (Single ^test_min ^test_max) (Single ^test_max ^test_max)”;(* Single (n2v 15,4) (n2v 15,4) *)
EVAL “intersect_single (Single ^test_min ^test_min) (Single ^test_min ^test_max)”;(* Single (n2v 0,4) (n2v 0,4) *)
EVAL “intersect_single Empty (Single ^test_lo ^test_hi)”;(* Empty *)
EVAL “intersect_single (Single ^test_mid ^test_hi) Empty”;(* Empty *)
EVAL “intersect_single (Single (n2v 2,4) (n2v 7,4)) (Single (n2v 5,8) (n2v 9,8))”;(* Empty (due to width mismatch) *)
EVAL “intersect_single (Single ^test_min ^test_mid) (Single ^test_mid ^test_hi)”;(* Single (n2v 5,4) (n2v 5,4) *)
EVAL “intersect_single (Single ^test_mid ^test_mid) (Single ^test_mid ^test_mid)”;(* Single (n2v 5,4) (n2v 5,4) *)
*)
        


Definition is_True_or_False_def:
  is_True_or_False g =
  ((g = True) ∨ (g = False))
End

    
Definition process_guard_to_arith_def:
  process_guard_to_arith m_e min max g curr_int =
   case atom_to_arith m_e g of
   | NONE => Empty                    (* Invalid guard becomes empty *)
   | SOME a_True => Single min max    (* True uses full range *)
   | SOME a_False => Empty            (* False is empty *)
   | SOME a => intersect_single curr_int (arith_to_interval a min max)
End





(*==================================*)
(*     line coversion definitions   *)
(*==================================*)

        
(*MAP (\x. process_guard_to_arith m_e min max g curr_int) guards_list*)        
(* think about splitting the procedure *)
Definition process_guards_rec_def:
  (process_guards_rec m_e min max [] init_int = init_int) ∧
  (process_guards_rec m_e min max (g::gs) init_int =
    process_guards_rec m_e min max gs (process_guard_to_arith m_e min max g init_int))
End


       
Definition convert_line_with_key_def:
  (convert_line_with_key m_e min max ([], s, res)  = NONE ) ∧
  (convert_line_with_key m_e min max (var_guards, s, res)  =
     SOME (process_guards_rec m_e min max var_guards (Single min max) , s, res))
End


Definition convert_lines_map_with_key_def:
  convert_lines_map_with_key m_e min max lines  =
   MAP (\line. convert_line_with_key m_e min max line) lines
End





(*==================================*)
(*  WFness conditions for var tbl   *)
(*==================================*)




Definition all_vars_defined_abstract_def:
  (all_vars_defined_abstract m_e [] = T) ∧
  (all_vars_defined_abstract m_e (True::rest) = all_vars_defined_abstract m_e rest) ∧
  (all_vars_defined_abstract m_e (False::rest) = all_vars_defined_abstract m_e rest) ∧
  (all_vars_defined_abstract m_e ((Var x)::rest) = 
   (case ALOOKUP m_e x of
     | SOME _ => all_vars_defined_abstract m_e rest
     | NONE => F)) ∧
  (all_vars_defined_abstract m_e ((Not g)::rest) = 
   (all_vars_defined_abstract m_e [g] ∧ all_vars_defined_abstract m_e rest))
End






Definition get_lval_of_guard_in_me_def:
  get_lval_of_guard_in_me m_e var_g = 
    case var_g of
      | Var x => (case ALOOKUP m_e x of
                  | SOME a => get_lval a
                  | NONE => NONE)
      | Not (Var x) => (case ALOOKUP m_e x of
                        | SOME a => get_lval a
                        | NONE => NONE)
      | _ => NONE
End


Definition get_guard_lvals_def:
  get_guard_lvals m_e guards = 
    FILTER (λ x . IS_SOME x ) (MAP (get_lval_of_guard_in_me m_e) guards)
End


Definition ALL_SAME_def:
  (ALL_SAME [] = T) ∧
  (ALL_SAME [x] = T) ∧
  (ALL_SAME (x::y::rest) = ((x = y) ∧ ALL_SAME (y::rest)))
End


Definition one_unique_lval_in_guards_def:
  one_unique_lval_in_guards m_e all_guards =
    let lvals = get_guard_lvals m_e all_guards in
    case lvals of
      | [] => NONE   (* No lvals found *)
      | h::t => if ALL_SAME (h::t) 
                then h  (* Returns SOME lv if all same *)
                else NONE
End      

       
Definition valid_line_def:
  valid_line (guards, s, res) = (guards ≠ [])
End


Definition valid_table_def:
  valid_table table = 
    ((table ≠ []) ∧ EVERY valid_line table)
End


Definition valid_tables_def:
  valid_tables tables = EVERY valid_table tables
End

  

(* Add this new function to analyze the entire table first *)
Definition analyze_table_type_def:
  (analyze_table_type m_e pd_type [] = NONE) ∧
  (analyze_table_type m_e pd_type table =
     let all_guards = FLAT (MAP FST table) in
       case all_vars_defined_abstract m_e all_guards  of
       | T => ( case EVERY (λx. x = (False:atom_var)) all_guards of
                | T => NONE
                | F =>  (case EVERY (λx. x = True ∨ x = False ) all_guards of
                         | T => SOME (T, key_const (n2v 1, 1), (n2v 0,1), (n2v 1,1))
                         | F => ( case one_unique_lval_in_guards m_e all_guards of
                                  (* All non-boolean guards use same lval *)
                                  | SOME lv => (
                                    case resolve_pd_min_max pd_type lv of
                                    | SOME (min,max) => SOME (T, key_val lv, min, max)
                                    | NONE => NONE
                                    )
                                  | NONE => NONE
                                )
                        )
              )
       | F => NONE 
  )
End


(*==================================*)
(*         Tables conversion        *)
(*==================================*)

Definition convert_single_table_def: 
  (convert_single_table [] m_e pd_type = NONE) ∧
  (convert_single_table lines m_e pd_type =                
   case analyze_table_type m_e pd_type lines of
   | SOME (T, key_type, min, max) =>       (* Convert all lines with the same key_type and max *)
       (case (EVERY IS_SOME (convert_lines_map_with_key m_e min max lines)) of
        | T => SOME (key_type, MAP THE (convert_lines_map_with_key  m_e min max lines))
        | F => NONE
       )
   | _ => NONE  (* Inconsistent table *)
  )
End

        
Definition convert_tables_def:
  (convert_tables [] _ _ = SOME []) ∧
  (convert_tables (tbl::tbls) m_e pd_type =
    if ¬(valid_tables (tbl::tbls)) then NONE
      else
        (case convert_single_table tbl m_e pd_type of
        | NONE => NONE  (* Fail immediately if any table fails *)
        | SOME converted_tbl =>
            (case convert_tables tbls m_e pd_type of
            | NONE => NONE
            | SOME converted_tbls => SOME (converted_tbl :: converted_tbls))
        )
      )
End



(*
val policy1_var = “[[([(Var "x" :atom_var); (Var "y" :atom_var)],(0 :num),
        (state (3 :num) :(string # num list) action_expr));
       ([(Var "x" :atom_var); Not (Var "y" :atom_var)],(0 :num),
        (state (4 :num) :(string # num list) action_expr));
       ([Not (Var "x" :atom_var)],(0 :num),
        (state (4 :num) :(string # num list) action_expr))];
      [([(Var "z" :atom_var)],(4 :num),
        (state (7 :num) :(string # num list) action_expr));
       ([Not (Var "z" :atom_var)],(4 :num),
        (state (8 :num) :(string # num list) action_expr));
       ([True],(3 :num),(state (3 :num) :(string # num list) action_expr))];
      [([True],(3 :num),action ("fwd",[(1 :num)]));
       ([True],(7 :num),action ("fwd",[(2 :num)]));
       ([True],(8 :num),action ("drop",([] :num list)))]]”;


val test_pd_nested = ``[
  ("h", type_record [
    ("len", type_length 5); 
    ("flags", type_length 5); 
    ("ttl", type_length 5)
  ])
]``;


val test_lval1 = ``lv_acc (lv_x "h") "ttl"``;
val test_lval2 = ``lv_acc (lv_x "h") "flags"``;
val test_lval3 = ``lv_x "z"``;


val test_atom1 = ``arithm_gt ^test_lval1 (n2v 0,5)``;  (* h.ttl > 0 *)
val test_atom2 = ``arithm_lt ^test_lval1 (n2v 10,5)``; (* h.ttl < 10 *)
val test_atom3 = ``arithm_lt ^test_lval2 (n2v 3,5)``;  (* h.flags < 3 *)

    
val test_m_e = ``[
  ("x", ^test_atom1); 
  ("y", ^test_atom2); 
  ("z", ^test_atom3)
]``;

EVAL ``convert_tables (^policy1_var) ^test_m_e ^test_pd_nested``;
        
*)



                  

(*==================================*)
(*    interval table semantics      *)
(*==================================*)




Definition is_intvl_match_row_def:
  is_intvl_match_row key (s_in:num) (packet_input:pd) (row:('a intvl_row)) =
  case (key, row) of
  | (key_val lval, (Single a b, s, res)) =>
      (let (a_v,a_w) = a in
        let (b_v,b_w) = b in
          (case resolve_lval packet_input lval of
           | SOME (val_bs (v,v_w)) => 
               (if (a_w = b_w) ∧ (b_w = v_w) then
                  (case (bv_lt_than (v,v_w) (a_v,a_w), bv_lt_than (b_v,b_w) (v,v_w)) of
                   | (SOME F, SOME F) => (s_in = s)  (* a ≤ v ≤ b *)
                   | (_, _) => F)
                else F
               )
           | SOME _ => F  (* non-numeric value *)
           | NONE => F))   (* lval not found *)
  | (key_val lval, (Empty, s, res)) => F                  
  | (key_const (c,c_w), (_, s, _)) => (s_in = s)
End

(*
(* Test bitvectors - all 4-bit width for consistency *)
val test_v0 = “(n2v 0, (4:num))”;    (* 0 *)
val test_v2 = “(n2v 2, (4:num))”;    (* 2 *)
val test_v4 = “(n2v 4, (4:num))”;    (* 4 *)
val test_v6 = “(n2v 6, (4:num))”;    (* 6 *)
val test_v15 = “(n2v 15, (4:num))”;  (* 15 *)

val test_packet = ``[("x", val_bs ^test_v4)]``;

val test_row_match = “(Single ^test_v2 ^test_v6, (1:num), action ("fwd", [(1:num)]))”;
val test_row_nomatch = “(Single ^test_v6 ^test_v15, (1:num), action ("fwd", [(1:num)]))”;
val test_row_empty = “(Empty, (1:num), action ("fwd", [(1:num)]))”;
val test_row_edge = “(Single ^test_v4 ^test_v4, (1:num), action ("fwd", [(1:num)]))”;

val test_key_val = “key_val (lv_x "x")”;
val test_key_const = “key_const ^test_v0”;

EVAL “is_intvl_match_row ^test_key_val 1 ^test_packet ^test_row_match”; (*T*)
EVAL “is_intvl_match_row ^test_key_val 1 ^test_packet ^test_row_nomatch”; (*F*)
EVAL “is_intvl_match_row ^test_key_val 1 ^test_packet ^test_row_empty”; (*F*)
EVAL “is_intvl_match_row ^test_key_val 1 ^test_packet ^test_row_edge”; (*T*)
EVAL “is_intvl_match_row ^test_key_const 1 ^test_packet ^test_row_match”; (*T*)

val test_v4_8bit = “(n2v 4, (8:num))”;
val test_row_width_mismatch = “(Single ^test_v2 ^test_v4_8bit, (1:num), action ("fwd", [(1:num)]))”;
EVAL “is_intvl_match_row ^test_key_val 1 ^test_packet ^test_row_width_mismatch”; (*F (width mismatch between 4 and 8) *)

val test_packet_missing = ``[("y", val_bs ^test_v4)]``;
EVAL “is_intvl_match_row ^test_key_val 1 ^test_packet_missing ^test_row_match”;
*)
        

(* Process all rows in an interval table *)
Definition check_all_intvl_rows_match_def:
  check_all_intvl_rows_match key st_in rows packet_input =
  MAP (λ(interval,s,res). is_intvl_match_row key (st_in:num) (packet_input:pd) (interval,s,res), res) rows
End



(* Find first matching line in a converted table *)
Definition match_intvl_tbl_def:
  match_intvl_tbl (intvl_tbl: 'a intvl_table) packet_input st_in =
  let (key, rows) = intvl_tbl in
    let lines_res = check_all_intvl_rows_match key st_in rows packet_input in
      case min_idx_till lines_res T of
      | SOME (idx, line) => SOME (SND line)
      | NONE => NONE
End


(* Process list of interval tables with state propagation *)
Definition match_intvl_tbll_def:
  (match_intvl_tbll ([]: 'a intvl_table_list) packet_input st_in = NONE) ∧
  (match_intvl_tbll [intvl_tbl] packet_input st_in =
    case match_intvl_tbl intvl_tbl packet_input st_in of
      | SOME (action a) => SOME (action a)
      | _ => NONE) ∧
  (match_intvl_tbll (intvl_tbl::intvl_tbls) packet_input st_in =
    case match_intvl_tbl intvl_tbl packet_input st_in of
      | SOME (state n) => match_intvl_tbll intvl_tbls packet_input n
      | _ => NONE)
End



(* Top-level interval table semantics *)
Definition sem_intvl_tables_def:
  sem_intvl_tables ((intvl_tbll: (('a intvl_table ) list)), st_in) (packet_input:pd) =
  match_intvl_tbll intvl_tbll packet_input st_in
End

(* IMPORTANT well formdness every var in m_e is indeed defined in pd*)




        

(*==================================*)
(*            P R O O F             *)
(*==================================*)





Theorem convert_tables_never_empty:
  ∀ h' t m_e packet_type.
    convert_tables (h'::t) m_e packet_type ≠ SOME []
Proof
  rw[convert_tables_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) 
QED
   

Theorem append_defined_implies_first_defined:
  ∀m_e l l'. all_vars_defined_abstract m_e (l ++ l') ⇒
              (all_vars_defined_abstract m_e l' ∧  all_vars_defined_abstract m_e l)
Proof
  Induct_on `l` >> simp[all_vars_defined_abstract_def] >>
  Cases >> simp[all_vars_defined_abstract_def] >>
  rpt strip_tac >> res_tac >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 
  res_tac
QED



        
Theorem  all_vars_defined_abstract_on_individual:       
  ∀ m_e  l.    
    (all_vars_defined_abstract m_e) (FLAT l) ⇒
    (EVERY (\x. all_vars_defined_abstract m_e x) l)
Proof
  Induct_on `l` >> simp[all_vars_defined_abstract_def] >>
  Cases >> simp[all_vars_defined_abstract_def] >>
  rpt strip_tac >> res_tac >>
  `h'::(t ++ FLAT l) = [h'] ++ t ++ FLAT l` by simp[] >> 
  `(h':: t) = [h'] ++ t ` by simp[] >> 
  metis_tac[append_defined_implies_first_defined]
QED


                   
Definition norm_match_tbl_def:
  (norm_match_tbl [] m_v st_in = NONE) ∧
  (norm_match_tbl (h::t) m_v st_in =
   let (guards,st,res) = h in
    if is_match_row st_in st guards m_v then
      SOME res
    else
      norm_match_tbl t m_v st_in)
End


Theorem norm_match_tbl_equiv:
  ∀tbl m_v st_in.
    norm_match_tbl tbl m_v st_in = match_tbl tbl m_v st_in
Proof
  Induct >> rw[] >-
  (
  fs[norm_match_tbl_def, match_tbl_def, check_all_rows_match_def, min_idx_till_def, INDEX_FIND_def]
  ) >>
  PairCases_on ‘h’ >>
  fs[norm_match_tbl_def, match_tbl_def, check_all_rows_match_def] >>
  Cases_on `is_match_row st_in h1 h0 m_v` >> fs[] >>
  gvs[min_idx_till_def, INDEX_FIND_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>  

  imp_res_tac INDEX_FIND_NONE_EXISTS >>
  imp_res_tac exists_index_some >>
  gvs[EXISTS_MAP] >>
  gvs[MAP_MAP_o] >>          
  imp_res_tac P_implies_next >>
  gvs[]     
QED




      




Theorem interval_single_table_converstion_correctness:
  ∀var_table m_e packet_input m_v interval_table packet_type st_in.
    ALL_DISTINCT (MAP FST m_e) ∧
    valid_table var_table  ∧
    (∀var atom.  ALOOKUP m_e var = SOME atom ⇒
                 ALOOKUP m_v var = eval_arithm_atom packet_input atom) ∧
    convert_single_table var_table m_e packet_type = SOME interval_table ⇒
    match_tbl var_table m_v st_in = match_intvl_tbl interval_table packet_input st_in
Proof
  cheat             
QED


        
Theorem interval_tables_conversion_correctness:
  ∀var_tables m_e packet_input m_v interval_tables packet_type st_in.
    ALL_DISTINCT (MAP FST m_e) ∧
    (∀var atom. 
       ALOOKUP m_e var = SOME atom ⇒ 
       ALOOKUP m_v var = eval_arithm_atom packet_input atom) ∧
    (convert_tables var_tables m_e packet_type = SOME interval_tables) ⇒
    sem_tables (var_tables, st_in) m_v = 
    sem_intvl_tables (interval_tables, st_in) packet_input
Proof
  Induct >> rpt strip_tac >-
   
   (fs[convert_tables_def, sem_tables_def, sem_intvl_tables_def] >>
    gvs[sem_tables_def, match_tbll_def, sem_intvl_tables_def, match_intvl_tbll_def]) >> 
  
  fs[convert_tables_def] >>     
  Cases_on ‘convert_single_table h m_e packet_type’ >> fs[] >>
  Cases_on ‘convert_tables var_tables m_e packet_type’ >> fs[] >>
  
  last_x_assum (drule_all_then strip_assume_tac) >>
  gvs[] >>
  

  ‘valid_table h’ by gvs[valid_tables_def] >>
        
  subgoal ‘match_tbl h m_v st_in = match_intvl_tbl x packet_input st_in’ >-
   ( cheat) >>
   
    (*metis_tac[interval_single_table_converstion_correctness] ) >>
     *)
  
  simp[sem_tables_def, sem_intvl_tables_def] >>
  
  Cases_on ‘var_tables’ >>
  Cases_on ‘x'’ >>
  gvs[] >|[
    (* both are last tables*)
    fs[match_tbll_def, match_intvl_tbll_def] 
    ,
    fs[convert_tables_def]
    ,
    gvs[convert_tables_never_empty]
    ,
    fs[match_tbll_def, match_intvl_tbll_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
    fs[sem_tables_def, sem_intvl_tables_def] 
  ]   
QED









        
   


                                                                

val _ = export_theory ();










