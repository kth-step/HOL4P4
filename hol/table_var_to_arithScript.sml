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

        
Type intvl_row        = “:(interval option # num # 'a action_expr)”;
Type intvl_table      = “:(airth_key # 'a intvl_row list)”;
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

Definition check_widths_def:
  check_widths (v1,w1) (v2,w2) (v3,w3) (v4,w4) = 
    (w1 = w2 ∧ w2 = w3 ∧ w3 = w4)
End

        
Definition get_lval_def:
  get_lval (a_True) = NONE ∧
  get_lval (a_False) = NONE ∧
  get_lval (arithm_gt lv _) = SOME lv ∧
  get_lval (arithm_lt lv _) = SOME lv
End

        
(* given a struct type and lval, this retrives the field type
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
      | SOME (type_length n) => SOME ((fixwidth n (n2v 0), n), ( fixwidth n (n2v (max_from_type n)), n)  )
      | _ => NONE
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
EVAL “bv_eq_to ([F;F], (2:num)) (n2v 0, (1:num))”; (* none *)
EVAL “bv_eq_to ([F;F], (3:num)) ([F;F;T], (3:num))”; (* F *)
EVAL “bv_eq_to ([F], (3:num)) ([F;F], (3:num))”; (* T *)
*)

        
Definition add_one_to_bv_def:
  add_one_to_bv bv=
  let (b,v) = bv in
    if b = n2v (max_from_type v) then
      NONE
    else
      bitv_binop binop_add (b,v) (n2v 1, v)
End
    
(*
EVAL “add_one_to_bv ([T;T;T;T], (4:num))”;
EVAL “add_one_to_bv ([T;T;T;T], (3:num))”;
EVAL “add_one_to_bv ([T;F;T;T], (3:num))”;
*)  

Definition sub_one_of_bv_def:
  sub_one_of_bv bv=
  let (b,v) = bv in
    if (bv_eq_to bv (n2v 0 , v) = SOME F) then
      bitv_binop binop_sub (b,v) (n2v 1, v) 
    else
      NONE
End
    
(*
EVAL “sub_one_of_bv ([T;T;T;T], (4:num))”;
EVAL “bitv_binop binop_sub ([T;T;T;T], (4:num)) (n2v 1, 4)”;

EVAL “sub_one_of_bv ([T;F], (4:num))”;
EVAL “sub_one_of_bv ([F;F;F], (4:num))”;
*) 




        
(*==================================*)
(*    Atoms coversion definitions   *)
(*==================================*)

    
(* Convert atom_var to arithm_atom using me
   i.e. each cell in the line of var table will be converted
   directly to an aritmetic atom via this def. *)
   
Definition atom_to_arith_def:
  atom_to_arith me g =
  (case g of
  | True => SOME a_True
  | False => SOME a_False
  | Var x => ALOOKUP me x
  | Not a => 
      (case atom_to_arith me a of
      | SOME a_True => SOME a_False
      | SOME a_False => SOME a_True
      | SOME (arithm_gt lv bv) =>
          ( case (add_one_to_bv bv) of
            | NONE => NONE
            | SOME bv' => SOME (arithm_lt lv bv')
          )
      | SOME (arithm_lt lv bv) =>
          ( case (sub_one_of_bv bv) of
            | NONE => NONE
            | SOME bv' => SOME (arithm_gt lv bv')
          )
      | NONE => NONE))
End
        


Definition arith_to_interval_def:
  arith_to_interval a min max =
    case a of
    | a_True => SOME (Single min max)
    | a_False => NONE
    | arithm_gt _ n => 
        (case (bv_gt_than n max, bv_eq_to n max, add_one_to_bv n) of
        | (SOME F, SOME F, SOME bv') => SOME (Single bv' max)
        | _ => NONE)
    | arithm_lt _ n =>
        (case (bv_lt_than n min, bv_eq_to n min, sub_one_of_bv n) of
         | (SOME F, SOME F, SOME bv') =>    (* n > min *)
             (case bv_gt_than n max of
              | SOME T => SOME (Single min max)    (* n > max *)
              | SOME F => SOME (Single min bv')    (* min < n ≤ max *)
              | _ => NONE)
         | _ => NONE)
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
EVAL ``arith_to_interval (arithm_lt l (n2v 1, (4:num))) ^test_min ^test_max2``;  (* [0,0] since x < 1 *)         
*)




Definition intersect_single_def:
  (intersect_single (SOME (Single (v1,w1) (v2,w2))) (SOME (Single (v3,w3) (v4,w4))) =
   (if (w1 = w2) ∧ (w2 = w3) ∧ (w3 = w4) then
     (case (bv_gt_than (v1,w1) (v3,w3), bv_gt_than (v2,w2) (v4,w4)) of
      | (SOME a1_gt_a2, SOME b1_gt_b2) =>
          (let lower = if a1_gt_a2 then (v1,w1) else (v3,w3) in
            let upper = if b1_gt_b2 then (v4,w4) else (v2,w2) in
              (case bv_gt_than lower upper of
               | SOME F => SOME (Single lower upper)
               | _ => NONE       (* Shouldn't happen per bv_gt_than spec *)
              ))
      | _ => NONE)  (* Invalid comparison *)
   else NONE)) ∧  (* Width mismatch *)

        
  (intersect_single NONE _ = NONE) ∧
  (intersect_single _ NONE = NONE) ∧
  (intersect_single (SOME Empty) _ = NONE) ∧
  (intersect_single _ (SOME Empty) = NONE)
End

        
(*        
(* Test bitvectors - 4-bit width *)
val test_lo =  “(n2v 2, (4:num))”;  (* 2 in 4 bits *)
val test_mid = “(n2v 5, (4:num))”; (* 5 in 4 bits *)
val test_hi =  “(n2v 7, (4:num))”;  (* 7 in 4 bits *)
val test_min = “(n2v 0, (4:num))”; (* 0 in 4 bits *)
val test_max = “(n2v 15, (4:num))”; (* 15 in 4 bits *)

EVAL “intersect_single ( SOME (Single  ^test_lo ^test_hi)) ( SOME (Single  ^test_mid ^test_max))”;(* Single (n2v 5,4) (n2v 7,4) *)
EVAL “intersect_single ( SOME (Single  ^test_min ^test_lo)) ( SOME (Single  ^test_hi ^test_max))”;(* NONE, non-overlapping intervals *)
EVAL “intersect_single ( SOME (Single  ^test_mid ^test_hi)) ( SOME (Single  ^test_mid ^test_hi))”;(* Single (n2v 5,4) (n2v 7,4) *)
EVAL “intersect_single ( SOME (Single  ^test_min ^test_max)) ( SOME (Single  ^test_lo ^test_hi))”;(* Single (n2v 2,4) (n2v 7,4), one interval contained within another *)
EVAL “intersect_single ( SOME (Single  ^test_min ^test_max)) ( SOME (Single  ^test_max ^test_max))”;(* Single (n2v 15,4) (n2v 15,4) *)
EVAL “intersect_single ( SOME (Single  ^test_min ^test_min)) ( SOME (Single  ^test_min ^test_max))”;(* Single (n2v 0,4) (n2v 0,4) *)
EVAL “intersect_single NONE ( SOME (Single  ^test_lo ^test_hi))”;(* NONE *)
EVAL “intersect_single ( SOME (Single  ^test_mid ^test_hi)) NONE”;(* NONE *)
EVAL “intersect_single ( SOME (Single  (n2v 2,4) (n2v 7,4))) ( SOME (Single  (n2v 5,8) (n2v 9,8)))”;(* NONE (due to width mismatch) *)
EVAL “intersect_single ( SOME (Single  ^test_min ^test_mid)) ( SOME (Single  ^test_mid ^test_hi))”;(* Single (n2v 5,4) (n2v 5,4) *)
EVAL “intersect_single ( SOME (Single  ^test_mid ^test_mid)) ( SOME (Single  ^test_mid ^test_mid))”;(* Single (n2v 5,4) (n2v 5,4) *)
*)
        


Definition is_True_or_False_def:
  is_True_or_False g =
  ((g = True) ∨ (g = False))
End

        
Definition process_guard_to_arith_def:
  process_guard_to_arith me min max g curr_int =
   case atom_to_arith me g of
   | NONE => NONE                            (* Invalid guard becomes NONE *)
   | SOME a_True => SOME (Single min max)            (* True uses full range, TODO, might be current interval *)
   | SOME a_False => NONE                    (* False becomes NONE *)
   | SOME a => 
       case curr_int of
       | NONE => NONE                        (* Propagate NONE if curr_int is NONE *)
       | SOME intvl => intersect_single (SOME intvl) (arith_to_interval a min max)
End



(*==================================*)
(*     line coversion definitions   *)
(*==================================*)


        
Definition process_guards_rec_def:
  (process_guards_rec me min max [] init_int = init_int) ∧
  (process_guards_rec me min max (g::gs) init_int =
    case init_int of
    | NONE => NONE
    | SOME intvl =>
        case process_guard_to_arith me min max g (SOME intvl) of
        | NONE => NONE
        | SOME new_intvl => process_guards_rec me min max gs (SOME new_intvl))
End

        
Definition convert_line_with_key_def:
  (convert_line_with_key me min max ([], s, res) = NONE) ∧
  (convert_line_with_key me min max (var_guards, s, res) =
    case process_guards_rec me min max var_guards (SOME (Single min max)) of
    | NONE => SOME (NONE, s, res)  
    | SOME interval => SOME (SOME interval, s, res))
End

        
Definition convert_lines_map_with_key_def:
  convert_lines_map_with_key me min max lines =
   MAP (\line.case convert_line_with_key me min max line of
     | NONE => NONE  (* This is for completely invalid lines *)
     | SOME x => SOME x   (* Preserve the (interval option, state, action) structure *)) lines
End





(*==================================*)
(*  WFness conditions for var tbl   *)
(*==================================*)




Definition all_vars_defined_abstract_def:
  (all_vars_defined_abstract me [] = T) ∧
  (all_vars_defined_abstract me (True::rest) = all_vars_defined_abstract me rest) ∧
  (all_vars_defined_abstract me (False::rest) = all_vars_defined_abstract me rest) ∧
  (all_vars_defined_abstract me ((Var x)::rest) = 
   (case ALOOKUP me x of
     | SOME _ => all_vars_defined_abstract me rest
     | NONE => F)) ∧
  (all_vars_defined_abstract me ((Not g)::rest) = 
   (all_vars_defined_abstract me [g] ∧ all_vars_defined_abstract me rest))
End






Definition get_lval_of_guard_in_me_def:
  get_lval_of_guard_in_me me var_g = 
    case var_g of
      | Var x => (case ALOOKUP me x of
                  | SOME a => get_lval a
                  | NONE => NONE)
      | Not (Var x) => (case ALOOKUP me x of
                        | SOME a => get_lval a
                        | NONE => NONE)
      | _ => NONE
End


Definition get_guard_lvals_def:
  get_guard_lvals me guards = 
    FILTER (λ x . IS_SOME x ) (MAP (get_lval_of_guard_in_me me) guards)
End


Definition ALL_SAME_def:
  (ALL_SAME [] = T) ∧
  (ALL_SAME [x] = T) ∧
  (ALL_SAME (x::y::rest) = ((x = y) ∧ ALL_SAME (y::rest)))
End


Definition one_unique_lval_in_guards_def:
  one_unique_lval_in_guards me all_guards =
    let lvals = get_guard_lvals me all_guards in
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
  analyze_table_type me pd_type table =
   if table = [] then NONE else 
     let all_guards = FLAT (MAP FST table) in
       case all_vars_defined_abstract me all_guards  of
       | T => ( case EVERY (λx. x = (False:atom_var)) all_guards of
                | T => NONE
                | F =>  (case EVERY (λx. x = True) all_guards of
                         | T => SOME (T, key_const (n2v 1, 1), (n2v 0,1), (n2v 1,1))
                         | F => ( case one_unique_lval_in_guards me all_guards of
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
End


(*==================================*)
(*         Tables conversion        *)
(*==================================*)

Definition convert_single_table_def: 
  (convert_single_table [] me pd_type = NONE) ∧
  (convert_single_table lines me pd_type =                
   case analyze_table_type me pd_type lines of
   | SOME (T, key_type, min, max) =>       
       let converted_lines = convert_lines_map_with_key me min max lines in
         if EVERY IS_SOME converted_lines then
           SOME (key_type, MAP THE converted_lines)  (* All lines valid *)
         else
           NONE  (* At least one line was completely invalid (NONE) *)
   | _ => NONE  (* Inconsistent table *)
  )
End

        
Definition convert_tables_def:
  (convert_tables [] _ _ = SOME []) ∧
  (convert_tables (tbl::tbls) me pd_type =
    if ¬(valid_tables (tbl::tbls)) then NONE
      else
        (case convert_single_table tbl me pd_type of
        | NONE => NONE  (* Fail immediately if any table fails *)
        | SOME converted_tbl =>
            (case convert_tables tbls me pd_type of
            | NONE => NONE
            | SOME converted_tbls => SOME (converted_tbl :: converted_tbls))
        )
      )
End



(*
val policy1_var = “[[([(Var "x" :atom_var); (Var "y" :atom_var)],(0 :num), (state (3 :num) :(string # num list) action_expr));
       ([(Var "x" :atom_var); Not (Var "y" :atom_var)],(0 :num), (state (4 :num) :(string # num list) action_expr));
       ([Not (Var "x" :atom_var)],(0 :num),                      (state (4 :num) :(string # num list) action_expr))];
       
      [([(Var "z" :atom_var)],(4 :num),                          (state (7 :num) :(string # num list) action_expr));
       ([Not (Var "z" :atom_var)],(4 :num),                      (state (8 :num) :(string # num list) action_expr));
       ([True],(3 :num),                                         (state (3 :num) :(string # num list) action_expr))];
       
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

    
val test_me = ``[
  ("x", ^test_atom1); 
  ("y", ^test_atom2); 
  ("z", ^test_atom3)
]``;

EVAL ``convert_tables (^policy1_var) ^test_me ^test_pd_nested``;
        
*)



                  

(*==================================*)
(*    interval table semantics      *)
(*==================================*)




Definition is_intvl_match_row_def:
  is_intvl_match_row key (s_in:num) (packet_input:pd) (row:('a intvl_row)) =
  case (key, row) of
  | (key_val lval, (SOME (Single a b), s, res)) =>
      (let (a_v,a_w) = a in
        let (b_v,b_w) = b in
          (case resolve_lval packet_input lval of
           | SOME (val_bs (v,v_w)) => 
               (if (a_w = b_w) ∧ (b_w = v_w) then
                  (case (bv_lt_than (v,v_w) (a_v,a_w), bv_lt_than (b_v,b_w) (v,v_w)) of
                   | (SOME F, SOME F) => (s_in = s)  (* a ≤ v ≤ b *)
                   | _ => F)
                else F
               )
           | SOME _ => F  (* non-numeric value *)
           | NONE => F))   (* lval not found *)
  | (key_val lval, (NONE, s, res)) => F  (* Empty interval never matches *)             
  | (key_const (c,c_w), (_, s, _)) => (s_in = s)  (* Constant key matches state only *)
End

      

(*
(* Test bitvectors - all 4-bit width for consistency *)
val test_v0 = “(n2v 0, (4:num))”;    (* 0 *)
val test_v2 = “(n2v 2, (4:num))”;    (* 2 *)
val test_v4 = “(n2v 4, (4:num))”;    (* 4 *)
val test_v6 = “(n2v 6, (4:num))”;    (* 6 *)
val test_v15 = “(n2v 15, (4:num))”;  (* 15 *)

val test_packet = ``[("x", val_bs ^test_v4)]``;

val test_row_match = “(SOME (Single ^test_v2 ^test_v6), (1:num), action ("fwd", [(1:num)]))”;
val test_row_nomatch = “(SOME (Single ^test_v6 ^test_v15), (1:num), action ("fwd", [(1:num)]))”;
val test_row_empty = “((NONE: interval option), (1:num), action ("fwd", [(1:num)]))”;
val test_row_edge = “(SOME (Single ^test_v4 ^test_v4), (1:num), action ("fwd", [(1:num)]))”;

val test_key_val = “key_val (lv_x "x")”;
val test_key_const = “key_const ^test_v0”;

EVAL “is_intvl_match_row ^test_key_val 1 ^test_packet ^test_row_match”; (*T*)
EVAL “is_intvl_match_row ^test_key_val 1 ^test_packet ^test_row_nomatch”; (*F*)
EVAL “is_intvl_match_row ^test_key_val 1 ^test_packet ^test_row_empty”; (*F*)
EVAL “is_intvl_match_row ^test_key_val 1 ^test_packet ^test_row_edge”; (*T*)
EVAL “is_intvl_match_row ^test_key_const 1 ^test_packet ^test_row_match”; (*T*)

val test_v4_8bit = “(n2v 4, (8:num))”;
val test_row_width_mismatch = “(SOME (Single ^test_v2 ^test_v4_8bit), (1:num), action ("fwd", [(1:num)]))”;
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

(* IMPORTANT well formdness every var in me is indeed defined in pd*)




        

(*==================================*)
(*            P R O O F             *)
(*==================================*)





Theorem convert_tables_never_empty:
  ∀ h' t me packet_type.
    convert_tables (h'::t) me packet_type ≠ SOME []
Proof
  rw[convert_tables_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) 
QED
   

Theorem append_defined_implies_first_defined:
  ∀me l l'. all_vars_defined_abstract me (l ++ l') ⇒
              (all_vars_defined_abstract me l' ∧  all_vars_defined_abstract me l)
Proof
  Induct_on `l` >> simp[all_vars_defined_abstract_def] >>
  Cases >> simp[all_vars_defined_abstract_def] >>
  rpt strip_tac >> res_tac >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 
  res_tac
QED



Theorem check_all_rows_match_length:
  ∀ tbl mv st_in.
    LENGTH (check_all_rows_match st_in tbl mv) = LENGTH (tbl)
Proof
  Induct >>
  gvs[check_all_rows_match_def]
QED


Theorem convert_lines_map_with_key_length:
  ∀ tbl me min max.
    LENGTH (convert_lines_map_with_key me min max tbl) = LENGTH tbl
Proof
  Induct >>
  gvs[convert_lines_map_with_key_def]
QED


Theorem check_all_intvl_rows_match_comb_length:
  ∀ tbl me min max key st_in packet_input.
    LENGTH (check_all_intvl_rows_match key st_in (MAP THE (convert_lines_map_with_key me min max tbl)) packet_input) =
    LENGTH tbl
Proof
  Induct >>
  gvs[check_all_intvl_rows_match_def, convert_lines_map_with_key_def]
QED




Theorem guards_in_tbl_not_empty:
  ∀ tbl x guards st_row res_row.
  valid_table tbl ∧
  x < LENGTH tbl ∧
  EL x tbl = (guards,st_row,res_row) ⇒
  guards ≠ []      
Proof
  rw[valid_table_def, EVERY_EL, valid_line_def] >>
  res_tac >>
  metis_tac[valid_line_def]           
QED
        



Theorem all_rows_true_then_lval_none_thm:
  ∀ rows snlist me.
    EVERY (λx. x = True) rows ∧
    FILTER (λx. IS_SOME x) (MAP (get_lval_of_guard_in_me me) rows) = snlist ⇒
    EVERY IS_NONE  snlist
Proof
  Induct >>
  rpt strip_tac >>
  gvs[] >>
  rpt (BasicProvers.FULL_CASE_TAC >> rgs[]) >>
  gvs[get_lval_of_guard_in_me_def]
QED
    
        
        
Theorem every_true_then_in_mv_true_l_thm:
  ∀ row st res mv x tbl.
    x < LENGTH tbl ∧
    EL x tbl = (row,st,res) ∧
    EVERY (λx. x = True) (FLAT (MAP FST tbl)) ⇒
    is_atoml_true row mv
Proof
  rw[is_atoml_true_def] >>
  imp_res_tac EL_MEM >>           
  gvs[EVERY_MEM] >>
  rpt strip_tac >>
  imp_res_tac mem_fst_snd >>
  gvs[MEM_FLAT] >>
  res_tac >>
  gvs[sem_atom_def]
QED

        
Theorem all_rows_true_then_no_unique:
  ∀ rows me.
    EVERY (λx. x = True) rows ⇒             
    one_unique_lval_in_guards me rows = NONE
Proof
  
  gvs[one_unique_lval_in_guards_def] >>                            
  gvs[get_guard_lvals_def, get_lval_of_guard_in_me_def] >>
  rpt strip_tac >>
  rpt (BasicProvers.FULL_CASE_TAC >> rgs[]) >>
  imp_res_tac all_rows_true_then_lval_none_thm >>
  gvs[]
QED
  


        
        
Theorem  all_vars_defined_abstract_on_individual:       
  ∀ me  l.    
    (all_vars_defined_abstract me) (FLAT l) ⇒
    (EVERY (\x. all_vars_defined_abstract me x) l)
Proof
  Induct_on `l` >> simp[all_vars_defined_abstract_def] >>
  Cases >> simp[all_vars_defined_abstract_def] >>
  rpt strip_tac >> res_tac >>
  `h'::(t ++ FLAT l) = [h'] ++ t ++ FLAT l` by simp[] >> 
  `(h':: t) = [h'] ++ t ` by simp[] >> 
  metis_tac[append_defined_implies_first_defined]
QED






        
Definition norm_match_tbl_def:
  (norm_match_tbl [] mv st_in = NONE) ∧
  (norm_match_tbl (h::t) mv st_in =
   let (guards,st,res) = h in
    if is_match_row st_in st guards mv then
      SOME res
    else
      norm_match_tbl t mv st_in)
End


Theorem norm_match_tbl_equiv:
  ∀tbl mv st_in.
    norm_match_tbl tbl mv st_in = match_tbl tbl mv st_in
Proof
  Induct >> rw[] >-
  (
  fs[norm_match_tbl_def, match_tbl_def, check_all_rows_match_def, min_idx_till_def, INDEX_FIND_def]
  ) >>
  PairCases_on ‘h’ >>
  fs[norm_match_tbl_def, match_tbl_def, check_all_rows_match_def] >>
  Cases_on `is_match_row st_in h1 h0 mv` >> fs[] >>
  gvs[min_idx_till_def, INDEX_FIND_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>  

  imp_res_tac INDEX_FIND_NONE_EXISTS >>
  imp_res_tac exists_index_some >>
  gvs[EXISTS_MAP] >>
  gvs[MAP_MAP_o] >>          
  imp_res_tac P_implies_next >>
  gvs[]     
QED





Theorem check_intvl_rows_elementwise_correct:
  ∀l key st_in packet_input x x'.
    x < LENGTH l ∧
    EL x l = SOME x' ⇒
    (EL x (check_all_intvl_rows_match key st_in (MAP THE l) packet_input) =
     HD (check_all_intvl_rows_match key st_in [x'] packet_input))
Proof
  rpt gen_tac >> strip_tac >>
  (* Expand both sides *)
  simp[check_all_intvl_rows_match_def] >>
  gvs[EL_MAP]                              
QED


Triviality unique_lval_gt_same_triv1:
  ∀ var guards lval lval' me p.
    one_unique_lval_in_guards me (Var var::guards) = SOME lval ∧
    ALOOKUP me var = SOME (arithm_gt lval' p) ⇒
    lval = lval'
Proof
  rw[one_unique_lval_in_guards_def] >>
  gvs[get_guard_lvals_def] >>
  gvs[get_lval_of_guard_in_me_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[get_lval_def]
QED




Triviality unique_lval_lt_same_triv1:
  ∀ var guards lval lval' me p.
    one_unique_lval_in_guards me (Var var::guards) = SOME lval ∧
    ALOOKUP me var = SOME (arithm_lt lval' p) ⇒
    lval = lval'
Proof
  rw[one_unique_lval_in_guards_def] >>
  gvs[get_guard_lvals_def] >>
  gvs[get_lval_of_guard_in_me_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[get_lval_def]
QED


        
Theorem bs_op_means_same_length:
  ∀ op lval_bs v_bs x.        
    SOME x = bitv_binpred op lval_bs v_bs ⇒
    (SND lval_bs = SND v_bs)
Proof
  rpt strip_tac >>
  PairCases_on ‘lval_bs’ >>
  PairCases_on ‘v_bs’ >>
  gvs[bitv_binpred_def]
QED


        
Triviality types_wfness_trivial:
  ∀ lval lval_bs min max packet_type packet_input.
  resolve_pd_min_max packet_type lval = SOME (min,max) ∧
resolve_lval packet_input lval = SOME (val_bs lval_bs) ⇒
  ((SND min = SND lval_bs) ∧ (SND max = SND lval_bs)  ∧
   (SND min ≠ 0) ∧ (SND max ≤ 128) (* <---- this part i need to infer from here or wfness cond*)
  )
Proof
cheat (* add wfness condition that guarantees this in the beggining *)
QED

     


Theorem last_edge_of_binpred_bs:
  ∀ binpred v v' n.
    n ≠ 0 ∧
    bitv_binpred_inner binpred v v' n = NONE ⇒
    n > 128
Proof

RW.ONCE_RW_TAC [bitv_binpred_inner_def] >>
rpt strip_tac >>
ntac 128 (BasicProvers.FULL_CASE_TAC >-
fs[]) >>
intLib.COOPER_TAC
QED




Theorem last_edge_of_binop_bs:
  ∀ binpred v v' n.
    n ≠ 0 ∧
    bitv_binop_inner binpred v v' n = NONE ⇒
    n > 128
Proof

RW.ONCE_RW_TAC [bitv_binop_inner_def] >>
rpt strip_tac >>
ntac 128 (BasicProvers.FULL_CASE_TAC >-
fs[]) >>
intLib.COOPER_TAC
QED



      
Theorem no_bs_is_larger_than_the_largest:
  ∀ n n'.
    n' ≠ 0 ∧ n' ≤ 128 ⇒
    bitv_binpred_inner binop_gt n (n2v (max_from_type n')) (n':num) = SOME F
Proof
  rw[max_from_type_def] >>
  RW.ONCE_RW_TAC [bitv_binpred_inner_def] >>
  rpt strip_tac >>
  
  rpt(
    BasicProvers.FULL_CASE_TAC >-
     (EVAL_TAC >>
      intLib.COOPER_TAC)) >>
  intLib.COOPER_TAC
QED



Theorem no_bs_is_less_that_the_least:
  ∀ n n'.
    n' ≠ 0 ∧ n' ≤ 128 ⇒
    bitv_binpred_inner binop_lt n (n2v 0) n' = SOME F
Proof
  
  rw[max_from_type_def] >>
  RW.ONCE_RW_TAC [bitv_binpred_inner_def] >>
  rpt strip_tac >>
  
  rpt(
    BasicProvers.FULL_CASE_TAC >- 
     (EVAL_TAC >>
      intLib.COOPER_TAC)) >>
  intLib.COOPER_TAC
QED













        

       
(*   
open bitTheory;
   
∀ bl a.
  0 < a ∧ a ≤ 128 ∧
  w2n (v2w bl) = (2 ** a - 1) ⇒
  bl  = n2v (2 ** a - 1) 

rpt strip_tac >>
‘v2n (n2v (2 ** a - 1)) = (2 ** a - 1)’ by gvs[v2n_n2v]
‘v2w (w2v w) = w’ by gvs[v2w_w2v]

                        rw[GSYM n2w_v2n]


‘v2w bl = n2w (v2n bl) ’ by fs[n2w_v2n] >>                                
‘w2n (n2w  (v2n bl)) = 2 ** a − 1’ by metis_tac[n2w_v2n]
                                

v2n_n2v


     gvs[v2w_n2v, v2w_w2v, w2n_v2w, w2v_v2w, w2w_v2w]          
gvs[w2n_v2w, MOD_2EXP_DIMINDEX]



‘n2v(w2n (v2w bl)) = n2v(2 ** a − 1)’ by gvs[]



                                                                                

  RW.ONCE_RW_TAC [bitv_binpred_inner_def] >>
rpt strip_tac >>
BasicProvers.FULL_CASE_TAC >-

gvs[get_word_binpred_def] >>
gvs[WORD_LO, WORD_HI] >>

fs [NOT_LESS, NOT_GREATER, LESS_OR_EQ] >>
fs[max_from_type_def]
             
(*
   `340282366920938463463374607431768211455 = 2 ** 128 - 1` by EVAL_TAC >>
`340282366920938463463374607431768211456 = 2 ** 128` by EVAL_TAC >>
*)



        
gvs[w2n_v2w, bitTheory.MOD_2EXP_def] >>

gvs[n2v_def, boolify_def]

Cases_on ‘p0 =
        [T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T;
         T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T;
         T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T;
         T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T;
         T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T;
         T; T; T; T; T; T; T; T; T; T; T; T; T]’ >> gvs[]





             

     


        
     
w ≠ 0 ∧
w ≤ 128 ∧
bitv_binpred_inner binop_eq p1 p2 w = SOME T ⇒
p1 = p2


                                                           
RW.ONCE_RW_TAC [bitv_binpred_inner_def] >>
rpt strip_tac >>
BasicProvers.FULL_CASE_TAC >-

 gvs[get_word_binpred_def] >>
gvs[word_eq_def] >>
   
gvs[WORD_LO, WORD_HI] >>



EVAL “word_eq (v2w [F;F])  (v2w [F;F;F])”




EVAL “word_hi ”


EVAL “w2v (0xACw: word8)”;

EVAL “(0xFFw: word8) = (0xFFw: word8) ”
EVAL “(0xFFw: word128) = (0xFFw: word128) ”

EVAL “v2w [T; F; F; T] = v2w [F; T; F; F; T]”

 EVAL “w2v ((1w: word4) + 3w)”;     

(* [T;F;T;T;F;F;T;F] *)                                                        

EVAL “w2v (0xACw)”;
EVAL “(0xACw)”;

             
   
decide_tac
        
             
metis_tac[]
        
EVAL_TAC >>
intLib.COOPER_TAC >>
blastLib.FULL_BBLAST_TAC >>
blastLib.BBLAST_TAC


fs[LESS_MOD]


                
v2w_w2v    



(* Define two 8-bit words *)
val w1 = ``0x7Fw: word8``;  (* 01111111 = 127 *)
val w2 = ``0x03w: word8``;  (* 00000011 = 3 *)

(* Add them (result wraps on overflow) *)
val sum = EVAL ``^w1 + ^w2``;




(* Define two 8-bit words *)
val w1 = ``0xFEw: word8``;  (* 01111111 = 127 *)
val w2 = ``0x03w: word8``;  (* 00000011 = 3 *)

(* Add them (result wraps on overflow) *)
val sum = EVAL ``w2v (^w1 + ^w2)``;

EVAL “w2v (^sum)”





EVAL “fixwidth 7 [F;F]”
EVAL “n2v 7”
EVAL “fixwidth 5 (n2v 7)”
*)

   


(*
   
        

Theorem empty_intersection_guard:
  ∀me mv packet_input packet_type h min max guards lval.
    all_vars_defined_abstract me (h::guards) ∧
    one_unique_lval_in_guards me (h::guards) = SOME lval ∧
    resolve_pd_min_max packet_type lval = SOME (min,max) ∧
                       
    (∀var atom. ALOOKUP me var = SOME atom ⇒
               ALOOKUP mv var = eval_arithm_atom packet_input atom) ∧

    process_guard_to_arith me min max h (SOME (Single min max)) = NONE
    ⇒
    sem_atom h mv ≠ SOME T
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on ‘h’ >> fs[sem_atom_def, process_guard_to_arith_def] >|[
    
    (* True case, can't make empty interval *)
    fs[atom_to_arith_def, arith_to_interval_def]
      
    ,
    (* Var case, main contradiction *) 
    rename1 ‘Var var’ >>
    
    subgoal ‘?atom. ALOOKUP me var = SOME atom’ >-
     (fs[all_vars_defined_abstract_def] >>
      rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) ) >>
      
    
    gvs[] >>
    ‘ALOOKUP mv var = eval_arithm_atom packet_input atom’ by metis_tac[] >>
    
    Cases_on ‘ALOOKUP mv var’ >> gvs[] >>
    gvs[atom_to_arith_def] >>
    
    (* show that a and a' are the same *)
    imp_res_tac unique_lval_gt_same_triv1 >>
    imp_res_tac unique_lval_lt_same_triv1 >>
    gvs[] >>

        
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[eval_arithm_atom_def]) >|[

        (*case greater*)
                                    
        (* min and max analysis to show they are actually min and max*)
        
        rename1 ‘resolve_lval packet_input lval = SOME (val_bs lval_bs)’ >>
        (* now p is the constant that we are comparing with... *)
        
        Cases_on ‘x’ >> gvs[] >>
        
        (* we know since the (gt or lt) peration is not none, lval_bs and p has the same length*)
        imp_res_tac bs_op_means_same_length >>
        imp_res_tac types_wfness_trivial >>

        (* we also know the exact min and max values*)
        gvs[resolve_pd_min_max_def] >>
        rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
        
        Cases_on ‘(arith_to_interval (arithm_gt lval p)
             (fixwidth (SND lval_bs) (n2v 0),SND lval_bs)
             (fixwidth (SND lval_bs) (n2v (max_from_type (SND lval_bs))),
              SND lval_bs)) = NONE’ >>
        gvs[intersect_single_def] >|[
          
          (* intersection in empty *)
          PairCases_on ‘p’ >> gvs[] >>
          PairCases_on ‘lval_bs’ >> gvs[] >>
          
          gvs[arith_to_interval_def] >>
          rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 
          gvs[intersect_single_def] >>
          gvs[add_one_to_bv_def, bv_eq_to_def, bv_gt_than_def] >>
          rgs[bitv_binop_def, bitv_binpred_def] >>
          
          (*solve most the cases cases *)
          gvs[] >>
          imp_res_tac last_edge_of_binpred_bs >>
          imp_res_tac last_edge_of_binop_bs >>
          gvs[] >>
          
          
          Cases_on ‘bitv_binop_inner binop_add p0 (n2v 1) lval_bs1’ >> gvs[] >>
          
          imp_res_tac no_bs_is_larger_than_the_largest >> gvs[] >>
          rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 


                      
          cheat  
          
          ,
          
          (* intersection is not empty *)
          PairCases_on ‘p’ >> gvs[] >>
          PairCases_on ‘lval_bs’ >> gvs[] >>
          
          gvs[arith_to_interval_def] >>
          rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 
          gvs[intersect_single_def] >>
          gvs[add_one_to_bv_def, bv_eq_to_def, bv_gt_than_def] >>
          rgs[bitv_binop_def, bitv_binpred_def] >>

                              

          PairCases_on ‘x’ >> gvs[] >>
          ‘lval_bs1=x1’ by cheat >> (* there is a theorem in teh old project *)
          fs[Once intersect_single_def] >>
          
          rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 
          
          gvs[intersect_single_def] >>
          gvs[add_one_to_bv_def, bv_eq_to_def, bv_gt_than_def] >>
          rgs[bitv_binop_def, bitv_binpred_def] >>
          
          (*solve most the cases cases *)
          gvs[] >>
          imp_res_tac last_edge_of_binpred_bs >>
          imp_res_tac last_edge_of_binop_bs >>
          gvs[] >>
          
          
          Cases_on ‘bitv_binop_inner binop_add p0 (n2v 1) lval_bs1’ >> gvs[] >>
          
          imp_res_tac no_bs_is_larger_than_the_largest >> gvs[]
        ]
        ,

        
        (* lt case *)

        

           
                

       ] 
(* not case *)
        cheat                                                            
]
QED



EVAL “bitv_binop_inner binop_add (n2v 3) (n2v 1) (2:num)”


  rename1 ‘resolve_lval packet_input lval = SOME (val_bs lval_bs)’ >>
        (* now p is teh constant that we are comparing with... *)
        
        Cases_on ‘x’ >> gvs[] >>
        
        (* we know since the operation is not none, lval_bs and p has the same length*)
        imp_res_tac bs_op_means_same_length >>
        imp_res_tac types_wfness_trivial >>
        
        gvs[resolve_pd_min_max_def] >>
        rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 
        
        Cases_on ‘(arith_to_interval (arithm_lt lval p) (n2v 0,SND lval_bs)
             (n2v (max_from_type (SND lval_bs)),SND lval_bs)) = Empty’ >>
        gvs[intersect_single_def] >|[
          
          (* intersection in empty *)
          PairCases_on ‘p’ >> gvs[] >>
          PairCases_on ‘lval_bs’ >> gvs[] >>
          
          gvs[arith_to_interval_def] >>
          rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 
          gvs[intersect_single_def] >>
          gvs[add_one_to_bv_def, bv_eq_to_def, bv_gt_than_def, bv_lt_than_def, bv_lt_than_def, sub_one_of_bv_def] >>
          rgs[bitv_binop_def, bitv_binpred_def] >>
          
          (*solve most the cases cases *)
          gvs[] >>
          imp_res_tac last_edge_of_binpred_bs >>
          imp_res_tac last_edge_of_binop_bs >>
          gvs[] >>
          imp_res_tac no_bs_is_larger_than_the_largest >> gvs[] >>
          imp_res_tac no_bs_is_less_that_the_least >> gvs[] >>
          rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 




                      
          cheat >>
          EVAL “bitv_binop_inner binop_sub (n2v 0) (n2v 1) (3:num)”
               EVAL “bitv_binpred_inner binop_eq p0 (n2v 0) lval_bs1” = SOME T

          EVAL “w2v ([F;T], (2:num))”
              gvs[w2v_def]

                                                                                
------------------------------------------------
          
          ,
          
          (* intersection is not empty *)
          PairCases_on ‘p’ >> gvs[] >>
          PairCases_on ‘lval_bs’ >> gvs[] >>
          
          gvs[arith_to_interval_def] >>
          rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 
          gvs[intersect_single_def] >>
          gvs[add_one_to_bv_def, bv_eq_to_def, bv_gt_than_def] >>
          rgs[bitv_binop_def, bitv_binpred_def] >>

                              

          PairCases_on ‘x’ >> gvs[] >>
          ‘lval_bs1=x1’ by cheat >> (* there is a theorem in teh old project *)
          fs[Once intersect_single_def] >>
          
          rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 
          
        gvs[arith_to_interval_def] >>
          rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 
          gvs[intersect_single_def] >>
          gvs[add_one_to_bv_def, bv_eq_to_def, bv_gt_than_def, bv_lt_than_def, bv_lt_than_def, sub_one_of_bv_def] >>
          rgs[bitv_binop_def, bitv_binpred_def] >>
          
          (*solve most the cases cases *)
          gvs[] >>
          imp_res_tac last_edge_of_binpred_bs >>
          imp_res_tac last_edge_of_binop_bs >>
          gvs[] >>
          imp_res_tac no_bs_is_larger_than_the_largest >> gvs[] >>
          imp_res_tac no_bs_is_less_that_the_least >> gvs[] >>
          
          
          cheat
        ]



cheat

*)
        


(******************************************************************)


        




        
   
(*
                                                        


Theorem none_interval_implies_false_guard:
  ∀guards me min max mv lval packet_input packet_type.
    (∀var atom. ALOOKUP me var = SOME atom ⇒
                ALOOKUP mv var = eval_arithm_atom packet_input atom) ∧
    all_vars_defined_abstract me guards ∧
    one_unique_lval_in_guards me guards = SOME lval ∧
    resolve_pd_min_max packet_type lval = SOME (min,max) ∧
    process_guards_rec me min max guards (SOME(Single min max)) = NONE
    ⇒
    ¬is_atoml_true guards mv
Proof
  Induct_on ‘guards’ >> rw[]>-
   fs[process_guards_rec_def] >>
  

  fs[process_guards_rec_def] >>
  Cases_on `process_guard_to_arith me min max h (SOME (Single min max))` >> fs[] >|[
    (* prove for head *)

       
    simp[is_atoml_true_def, EVERY_MEM] >>
    rpt strip_tac >>

        
    (* needs  empty_intersection_guard to be proven *) cheat
    ,
    
    first_x_assum drule >> rw[] >>
    Cases_on ‘one_unique_lval_in_guards me guards’ >> gvs[] >|[
        (* if nothing is unique it means it had been all True or false*)
        (* if all true then process_guards_rec ca never return empty *)
        (* if false exsists, then the goal ¬is_atoml_true holds by contradition*)
        cheat
        ,
      (*here analysis on head and tail
        where head cannot be true from 5, and the tail from IH, needs so much work*) 
        
      ]
    )
QED



        

        



(*************************************)        

Theorem row_matching_in_table_context:
  ∀me mv tbl packet_input packet_type st_in guards st_row res_row key min max interval st res x.
      
    ALL_DISTINCT (MAP FST me) ∧
    valid_table tbl ∧
    (∀var atom. ALOOKUP me var = SOME atom ⇒
               ALOOKUP mv var = eval_arithm_atom packet_input atom) ∧
    analyze_table_type me packet_type tbl = SOME (T,key,min,max) ∧ 
    guards ≠ [] ∧

    x < LENGTH tbl ∧
    EL x tbl = (guards,st_row,res_row) ∧

           
    convert_line_with_key me min max (guards,st_row,res_row) = SOME (interval,st,res)
    ⇒
    ((is_match_row st_in st_row guards mv ⇔
         is_intvl_match_row key st_in packet_input (interval,st,res)) ∧
        res_row = res)
Proof
        
  rpt gen_tac >> strip_tac >>
     
  Cases_on ‘key’ >|[
    (* Case 1: key_val *)
    rgs[analyze_table_type_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> rgs[]) >>  
    gvs[] >>
    
    (* we check if the row contains at least one lval or not *)
    Cases_on ‘one_unique_lval_in_guards me guards’ >> gvs[] >|[
      (* if not, trivial,  all values are true and false or not defined (by contrdiction)*)
      cheat
      ,
      
      (* else this lval will be the same for the whole table *)
      ‘a=x'’ by cheat >>
      Cases_on ‘guards’ >> gvs[] >>

      gvs[convert_line_with_key_def] >>
      Cases_on ‘process_guards_rec me min max (h::t) (SOME (Single min max))’ >> gvs[] >|[
               
          simp[is_match_row_def, is_intvl_match_row_def] >>
          strip_tac >>
          ‘all_vars_defined_abstract me (h::t)’ by cheat >>  (* trivial from condition *)
          irule none_interval_implies_false_guard >>
          qexistsl_tac [‘a’,‘me’, ‘max’, ‘min’, ‘packet_input’, ‘packet_type’] >>
          gvs[]
          ,
          (*process retunrs some*)


        ]


               
    ]
    ,
    (* Case 2: key_const *)
    
     rgs[analyze_table_type_def] >>
     rpt (BasicProvers.FULL_CASE_TAC >> rgs[]) >>
     imp_res_tac all_rows_true_then_no_unique >>
     gvs[] >>
      
     Cases_on ‘guards’ >> gvs[convert_line_with_key_def] >>
     rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>  

     gvs[is_match_row_def, is_intvl_match_row_def] >>
     ‘is_atoml_true (h::t) mv’ by metis_tac[every_true_then_in_mv_true_l_thm] >> gvs[]
  ]
QED






Theorem all_vars_defined_abstract_normalize:
  ∀ h guards me.
    all_vars_defined_abstract me (h::guards) ⇒
    all_vars_defined_abstract me [h] ∧
    all_vars_defined_abstract me guards
Proof
  Cases_on ‘h’ >>                          
  rw[all_vars_defined_abstract_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[])
QED


                             

 (*       
∀ guards x' me.
MEM x' guards ∧
all_vars_defined_abstract me guards ∧
one_unique_lval_in_guards me guards = NONE ⇒
x' = True ∨ x' = False

Induct >>
gvs[] >>
rpt strip_tac >>
imp_res_tac all_vars_defined_abstract_normalize >>
rgs[Once one_unique_lval_in_guards_def] >>
rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>




gvs[all_vars_defined_abstract_def, one_unique_lval_in_guards_def] >>
rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
gvs[get_guard_lvals_def]


    
        
      
               
∀ tbl guards me x st_row res_row.
  x < LENGTH tbl ∧
  EL x tbl = (guards,st_row,res_row) ∧
  all_vars_defined_abstract me (FLAT (MAP FST tbl)) ∧
  one_unique_lval_in_guards me guards = NONE ⇒
  EVERY  (λx. x = True ∨ x = False) guards 


         rpt strip_tac >> 
gvs[EVERY_MEM] >>
imp_res_tac EL_MEM >>   
 rpt strip_tac >>
  imp_res_tac mem_fst_snd >>
  gvs[MEM_FLAT] >>
imp_res_tac all_vars_defined_abstract_on_individual >>
gvs[EVERY_MEM] >>
res_tac >>
*)



  
        
        
(*******************************************************)


        
Theorem el_rows_match_check_thm:
  ∀me mv packet_input packet_type  st_in tbl x interval st res key min max.
    ALL_DISTINCT (MAP FST me) ∧
    valid_table tbl ∧
    (∀var atom.
       ALOOKUP me var = SOME atom ⇒
       ALOOKUP mv var = eval_arithm_atom packet_input atom) ∧
    analyze_table_type me packet_type tbl = SOME (T,key,min,max) ∧ 
    LENGTH (convert_lines_map_with_key me min max tbl) =
    LENGTH (check_all_rows_match st_in tbl mv) ∧
    EL x (convert_lines_map_with_key me min max tbl) =
    SOME (interval,st,res) ∧
    x < LENGTH (check_all_rows_match st_in tbl mv)
    ⇒
    EL x (check_all_rows_match st_in tbl mv) =
    (is_intvl_match_row key st_in packet_input (interval,st,res),res)
Proof

  rpt gen_tac >> strip_tac >>
  fs[convert_lines_map_with_key_def, check_all_rows_match_def] >>
  gvs[] >>
  
  Cases_on ‘EL x tbl’ >>   Cases_on ‘r’ >>
  rename1 ‘EL x tbl = (guards, st_row, res_row)’ >>
  
  gvs[EL_MAP] >>
  
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>

  ‘guards ≠ []’ by metis_tac[guards_in_tbl_not_empty] >>
          
  imp_res_tac row_matching_in_table_context >>
  gvs[] 
QED




Theorem interval_all_rows_converstion_correctness:
  ∀ tbl me packet_input mv packet_type st_in key min max.
    ALL_DISTINCT (MAP FST me) ∧
    valid_table tbl ∧
    (∀var atom.
       ALOOKUP me var = SOME atom ⇒
       ALOOKUP mv var = eval_arithm_atom packet_input atom) ∧
    EVERY IS_SOME (convert_lines_map_with_key me min max (tbl)) ∧
    analyze_table_type me packet_type tbl = SOME (T,key,min,max) ⇒
    ((check_all_rows_match st_in tbl mv) =
     (check_all_intvl_rows_match key st_in (MAP THE (convert_lines_map_with_key me min max tbl)) packet_input))
Proof
  rw[LIST_EQ_REWRITE] >|[
    
    ‘LENGTH (check_all_rows_match st_in tbl mv) = LENGTH (tbl)’ by gvs[check_all_rows_match_length] >>
    ‘LENGTH (convert_lines_map_with_key me min max tbl) = LENGTH tbl’ by gvs[convert_lines_map_with_key_length] >>
    gvs[check_all_intvl_rows_match_comb_length]
    ,


    ‘LENGTH (convert_lines_map_with_key me min max tbl) =
     LENGTH (check_all_rows_match st_in tbl mv)’ by gvs[check_all_rows_match_length, convert_lines_map_with_key_length] >>
    gvs[EVERY_EL] >>
    
    first_x_assum (strip_assume_tac o (Q.SPECL [‘x’])) >>
    res_tac >>

    Cases_on ‘EL x (convert_lines_map_with_key me min max tbl)’ >> rw[IS_SOME_DEF] >> gvs[] >>

    imp_res_tac check_intvl_rows_elementwise_correct >>
    ‘x < LENGTH (convert_lines_map_with_key me min max tbl)’ by gvs[] >>
    res_tac >>
                                                                                          
    first_x_assum (strip_assume_tac o (Q.SPECL [‘st_in’, ‘packet_input’, ‘key’])) >>
    res_tac >>
                                        
    gvs[] >>

    gvs[check_all_intvl_rows_match_def] >>
    PairCases_on ‘x'’ >>
    gvs[] >>

    rename1 ‘EL x (convert_lines_map_with_key me min max tbl) = SOME (interval,st,res)’ >>
    imp_res_tac  el_rows_match_check_thm (* theorem here*)
  ]
QED


      
Theorem interval_single_table_converstion_correctness:
  ∀var_table me packet_input mv interval_table packet_type st_in.
    ALL_DISTINCT (MAP FST me) ∧
    valid_table var_table  ∧
    (∀var atom.  ALOOKUP me var = SOME atom ⇒
                 ALOOKUP mv var = eval_arithm_atom packet_input atom) ∧
    convert_single_table var_table me packet_type = SOME interval_table ⇒
    match_tbl var_table mv st_in = match_intvl_tbl interval_table packet_input st_in
Proof
  
  Cases_on ‘var_table’ >>
  rpt strip_tac >-
   gvs[valid_table_def] >>
  
  gvs[convert_single_table_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>  
  
  rename1 ‘analyze_table_type me packet_type (row::tbl) = SOME (T,key,min,max)’ >>
  gvs[match_tbl_def, match_intvl_tbl_def] >>
  
  ‘(check_all_rows_match st_in (row::tbl) mv) = (check_all_intvl_rows_match key st_in
               (MAP THE (convert_lines_map_with_key me min max (row::tbl)))
               packet_input)’ by metis_tac[interval_all_rows_converstion_correctness] >>    (* thm here *)
  
  gvs[]
QED

        

        
Theorem interval_tables_conversion_correctness:
  ∀var_tables me packet_input mv interval_tables packet_type st_in.
    ALL_DISTINCT (MAP FST me) ∧
    (∀var atom. 
       ALOOKUP me var = SOME atom ⇒ 
       ALOOKUP mv var = eval_arithm_atom packet_input atom) ∧
    (convert_tables var_tables me packet_type = SOME interval_tables) ⇒
    sem_tables (var_tables, st_in) mv = 
    sem_intvl_tables (interval_tables, st_in) packet_input
Proof
  Induct >> rpt strip_tac >-
   
   (fs[convert_tables_def, sem_tables_def, sem_intvl_tables_def] >>
    gvs[sem_tables_def, match_tbll_def, sem_intvl_tables_def, match_intvl_tbll_def]) >> 
  
  fs[convert_tables_def] >>     
  Cases_on ‘convert_single_table h me packet_type’ >> fs[] >>
  Cases_on ‘convert_tables var_tables me packet_type’ >> fs[] >>
  
  last_x_assum (drule_all_then strip_assume_tac) >>
  gvs[] >>
  

  ‘valid_table h’ by gvs[valid_tables_def] >>
        
  subgoal ‘match_tbl h mv st_in = match_intvl_tbl x packet_input st_in’ >-
   ( metis_tac[interval_single_table_converstion_correctness] ) >>                 (*thm here*)
  
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






*)


        
   


                                                                

val _ = export_theory ();











