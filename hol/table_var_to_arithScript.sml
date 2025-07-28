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
  interval = Empty | Single of num => num
`;

val _ = Hol_datatype ` 
  airth_key = key_val of arith_lv | key_const of num
`;

        
Type intvl_row = “:airth_key # interval # num # 'a action_expr”;
(* None = Empty, Some (a,b) = Single [a,b] *)
(* arith_lv from policy_arith_to_var*)

Type intvl_table = “:('a intvl_row) list”;
Type intvl_table_list = “:('a intvl_table ) list”;

(*   
val _ = Hol_datatype `
   arith_atom_result =  SingleAtom of arithm_atom | UnionAtoms of arithm_atom => arithm_atom`;
*)

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
  get_lval (arithm_lt lv _) = SOME lv
End

        
(* given a truct type and lval, this retrives the field type
 or bs width *)
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
   directly to an aritmetic atom via this def. *)       
Definition atom_to_arith_def:
  (atom_to_arith m_e True = SOME a_True) ∧   
  (atom_to_arith m_e False = SOME a_False) ∧
                 
  (atom_to_arith m_e (Var x) =                                    
    case ALOOKUP m_e x of
      | SOME a => SOME a
      | NONE => NONE) ∧
      
  (atom_to_arith m_e (Not a) = 
    case atom_to_arith m_e a  of
      | SOME (a_True) => SOME a_False
      | SOME (a_False) => SOME a_True
                                                      
      | SOME (arithm_gt lv n) => SOME (arithm_lt lv (n+1))
      | SOME (arithm_lt lv n) => SOME (arithm_gt lv (n-1))                                                                              
      | NONE => NONE)
End
        

Definition arith_to_interval_def:
  (arith_to_interval a_True max = Single 0 max) ∧
  (arith_to_interval a_False max = Empty) ∧
  (arith_to_interval (arithm_gt _ n) max = 
     if n ≥ max then Empty else Single (n+1) max) ∧
  (arith_to_interval (arithm_lt _ n) max = 
     if n ≤ 0 then Empty 
     else if n > max then Single 0 max
     else Single 0 (n-1)) 
End
        

Definition intersect_single_def:
  intersect_single (Single (a1:num) b1) (Single a2 b2) =
  (let a = MAX a1 a2 in
     let b = MIN b1 b2 in
       if a ≤ b then
         Single a b
       else
         Empty
  ) ∧
  (intersect_single _ _ = Empty)
End


Definition is_True_or_False_def:
  is_True_or_False g =
  ((g = True) ∨ (g = False))
End




Definition process_guard_def:
  (process_guard m_e max g [] = []) ∧
  (process_guard m_e max g (((key: airth_key), curr_int, (s:num), (res: 'a action_expr))::rows) =
   (case (atom_to_arith m_e g, curr_int) of
      | (NONE, _) => []
      | (SOME _, Empty) => [(key, Empty, s, res)] (* False interval *)
      | (SOME a , curr_int ) =>
          (let inter_op = intersect_single curr_int (arith_to_interval a max) in
            [(key, inter_op, s, res)]
          )
    ) ++ process_guard m_e max g rows)
End


(* processing guards recursively *)
Definition process_guards_rec_def:
  (process_guards_rec m_e max  [] acc = acc) ∧
  (process_guards_rec m_e max (g::gs) acc =
    let new_acc = FLAT (MAP (λrow. process_guard m_e max g [row]) acc) in
      process_guards_rec m_e max gs new_acc)
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


Definition is_bool_or_unique_var_def:
  is_bool_or_unique_var m_e var_guards = 
    let lvals = FILTER IS_SOME (MAP (get_lval_of_guard_in_me m_e) var_guards) in
    case lvals of
      | [] => SOME (T, NONE)  (* All guards are boolean *)
      | (SOME lv)::rest => 
          if EVERY (λx. x = SOME lv) rest 
          then SOME (T, SOME lv)  (* All non-boolean guards use same LVal *)
          else NONE              (* Different LVals detected *)
End





Definition analyze_table_type_def:
  (analyze_table_type m_e pd_type [] = SOME (T, key_const 1, 1)) ∧
  (analyze_table_type m_e pd_type ((var_guards, s, res)::lines) =
   let all_guards = FLAT (MAP FST (((var_guards, s, res)::lines))) in
   let lvals = FILTER IS_SOME (MAP (get_lval_of_guard_in_me m_e) all_guards) in
   case lvals of
     | [] => SOME (T, key_const 1, 1)  (* All guards are boolean across entire table *)
     | (SOME lv)::rest => 
         if EVERY (λx. x = SOME lv) rest 
         then (case resolve_pd_max pd_type lv of
               | SOME max => SOME (T, key_val lv, max)  (* All non-boolean guards use same LVal *)
               | NONE => NONE)
         else NONE)              (* Different LVals detected *)
End

 

Definition convert_line_with_key_def:
  (convert_line_with_key m_e key_type max ([], s, res) = 
   [(key_type, Single 1 1, s, res)]) ∧ (* Default case for empty guards *)
  (convert_line_with_key m_e key_type max (var_guards, s, res) =
   let initial_arith_row = [(key_type, Single 0 max, s, res)] in
     process_guards_rec m_e max var_guards initial_arith_row)
End




Definition convert_single_table_fixed_def:
  (convert_single_table_fixed [] m_e pd_type = SOME []) ∧
  (convert_single_table_fixed table m_e pd_type =
    case analyze_table_type m_e pd_type table of
      | NONE => NONE  (* Inconsistent table *)
      | SOME (T, key_type, max) =>
          let process_line = λline. convert_line_with_key m_e key_type max line in
          SOME (FLAT (MAP process_line table)))
End




Definition convert_tables_def:
  (convert_tables_fixed [] _ _ = SOME []) ∧
  (convert_tables_fixed (tbl::tbls) m_e pd_type =
    case convert_single_table_fixed tbl m_e pd_type of
      | NONE => NONE  (* Fail immediately if any table fails *)
      | SOME converted_tbl =>
          case convert_tables_fixed tbls m_e pd_type of
            | NONE => NONE
            | SOME converted_tbls => SOME (converted_tbl :: converted_tbls))
End



(*
val policy1_var = “([[([(Var "x" :atom_var); (Var "y" :atom_var)],(0 :num),
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
       ([True],(8 :num),action ("drop",([] :num list)))]])”;

val policy1_var = “([[([(Var "x" :atom_var); (Var "y" :atom_var)],(0 :num),
        (state (3 :num) :(string # num list) action_expr));
       ([(Var "x" :atom_var); Not (Var "y" :atom_var)],(0 :num),
        (state (4 :num) :(string # num list) action_expr));
        ([True],(0 :num),(state (3 :num) :(string # num list) action_expr));
       ([Not (Var "x" :atom_var)],(0 :num),
        (state (4 :num) :(string # num list) action_expr))];
      [([(Var "z" :atom_var)],(4 :num),
        (state (7 :num) :(string # num list) action_expr));
       ([Not (Var "z" :atom_var)],(4 :num),
        (state (8 :num) :(string # num list) action_expr));
       ([True],(3 :num),(state (3 :num) :(string # num list) action_expr))];
      [([True],(3 :num),action ("fwd",[(1 :num)]));
       ([True],(7 :num),action ("fwd",[(2 :num)]));
       ([True],(8 :num),action ("drop",([] :num list)))]])”;

val test_pd_nested = ``[
  ("h", type_record [
    ("len", type_length 5); 
    ("flags", type_length 5); 
    ("ttl", type_length 5) 
  ])
  ]``;


  
val test_lval1 = ``lv_acc (lv_x "h") "ttl"``;
val test_lval2 = ``lv_acc (lv_x "h") "flags"``;

val test_atom1 = ``arithm_gt ^test_lval1 0``;
val test_atom2 = ``arithm_lt ^test_lval1 10``;
val test_atom3 = ``arithm_lt ^test_lval2 3``;

  
val test_m_e = ``[("x", ^test_atom1); ("y", ^test_atom2); ("z", ^test_atom3) ]``;

EVAL ``convert_tables_fixed ^policy1_var ^test_m_e ^test_pd_nested``;


*)
    
                  
(*
(* SEMANTICS *)
Definition is_intvl_match_row_def:
  is_intvl_match_row  (s_in:num) (packet_input:pd) (row:('a intvl_row)) =
    case row of
      (SOME lval, SOME (a,b), s, res) =>
        (case resolve_lval packet_input lval of
           SOME (val_num v) =>  (a ≤ v ∧ v ≤ b ∧ (s_in = s))
         | SOME _ => F  (* Non-numeric value *)
         | NONE => F )   (* Lval not found *)
    | (NONE, SOME (a,b), s, res) =>  (s_in = s)
    | (NONE, NONE, s, res) =>  F
    | (SOME lval, NONE, s, res) =>  F
End

        

(* Process all rows in an interval table *)
Definition check_all_intvl_rows_match_def:
  check_all_intvl_rows_match st_in intvl_tbl packet_input =
  MAP (λ(lval_opt, intervall, st_num, res). 
         (is_intvl_match_row st_in (packet_input:pd) (lval_opt , intervall, st_num, res)),
          (res:'a action_expr)) intvl_tbl
End



(* Find first matching line in a converted table *)
Definition match_intvl_tbl_def:
  match_intvl_tbl (intvl_tbl: (('a intvl_row) list)) packet_input st_in =
  let lines_res = check_all_intvl_rows_match st_in intvl_tbl packet_input in
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





        
(*
val test_packet = “[("src_ip", val_num 192); ("dst_port", val_num 80)]”;
val test_packet2 = “[("src_ip", val_num 10); ("dst_port", val_num 22)]”;
val initial_state = “(0:num)”;

(* Test tables *)
val test_table1 = ``[
  (SOME (lv_x "dst_port"), SOME (75, 85), 0, state 1);
  (NONE, SOME (0, 100), 0, state 2)
] : (arith_lv option # (num # num) option # num # string action_expr) list``;

  
val test_table2 = ``[
  (SOME (lv_x "src_ip"), SOME (190, 200), 1, action "allow_internal");
  (NONE, NONE, 2, action "default_deny")
] : (arith_lv option # (num # num) option # num # string action_expr) list``;

(* Test table list with state transitions *)
val test_tables = “[^test_table1; ^test_table2]: (arith_lv option # (num # num) option # num # string action_expr) list list”;

(* Test cases *)
val test1 = EVAL ``sem_intvl_tables (^test_tables, ^initial_state) ^test_packet``;
  *)               





(**********)
(* proof *)
(**********)





Theorem convert_tables_never_empty:
  ∀ h' t m_e packet_type.
    convert_tables (h'::t) m_e packet_type ≠ SOME []
Proof
  rw[convert_tables_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) 
QED




        

Definition norm_match_tbl_def:
  (norm_match_tbl [] m_v st_in = NONE) ∧
  (norm_match_tbl ((guards,st,res)::t) m_v st_in =
    if is_match_row st_in st guards m_v then
      SOME res
    else
      norm_match_tbl t m_v st_in)
End


Definition norm_match_intvl_tbl_def:
  (norm_match_intvl_tbl [] packet_input st_in = NONE) ∧
  (norm_match_intvl_tbl ((lval_opt,interval,st,res)::t) packet_input st_in =
    if is_intvl_match_row st_in packet_input (lval_opt,interval,st,res) then
      SOME res
    else
      norm_match_intvl_tbl t packet_input st_in)
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




Theorem norm_match_intvl_tbl_equiv:
  ∀tbl packet_input st_in.
    norm_match_intvl_tbl tbl packet_input st_in = 
    match_intvl_tbl tbl packet_input st_in
Proof
   Induct >> rw[] >-
  (
  fs[norm_match_intvl_tbl_def, match_intvl_tbl_def, check_all_intvl_rows_match_def, min_idx_till_def, INDEX_FIND_def]
  ) >>
  PairCases_on ‘h’ >>
  fs[norm_match_intvl_tbl_def, match_intvl_tbl_def, check_all_intvl_rows_match_def] >>
  Cases_on ‘is_intvl_match_row st_in packet_input (h0,h1,h2,h3)’ >> fs[] >>
  gvs[min_idx_till_def, INDEX_FIND_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>  

  imp_res_tac INDEX_FIND_NONE_EXISTS >>
  imp_res_tac exists_index_some >>
  gvs[EXISTS_MAP] >>
  gvs[MAP_MAP_o] >>                 
  imp_res_tac P_implies_next >>
  gvs[]     
QED



Theorem norm_match_intvl_tbl_append:
  ∀t1 t2 packet_input st_in.
    norm_match_intvl_tbl (t1 ++ t2) packet_input st_in =
    case norm_match_intvl_tbl t1 packet_input st_in of
      | NONE => norm_match_intvl_tbl t2 packet_input st_in
      | SOME res => SOME res
Proof
  Induct_on ‘t1’ >> rw[norm_match_intvl_tbl_def] >>
  PairCases_on ‘h’ >>  gvs[norm_match_intvl_tbl_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[])          
QED


        



Theorem semantic_single_table_equivalence_normalized:
  ∀var_table m_e packet_input m_v interval_table packet_type st_in.
    ALL_DISTINCT (MAP FST m_e) ∧
    (∀var atom. ALOOKUP m_e var = SOME atom ⇒
               ALOOKUP m_v var = eval_arithm_atom packet_input atom) ∧
    convert_single_table var_table m_e packet_type = SOME interval_table ⇒
    norm_match_tbl var_table m_v st_in =
    norm_match_intvl_tbl interval_table packet_input st_in
Proof
  Induct_on ‘var_table’ >>
  rpt gen_tac >> strip_tac  >|[
    fs[convert_single_table_def, norm_match_tbl_def, norm_match_intvl_tbl_def]
    ,                            
    PairCases_on ‘h’ >>
    fs[convert_single_table_def] >>
    Cases_on ‘convert_line m_e packet_type (h0,h1,h2)’ >> fs[] >>
    rename1 ‘convert_line _ _ _ = SOME lines’ >>
    Cases_on ‘convert_single_table var_table m_e packet_type’ >> fs[] >>
    rename1 ‘convert_single_table _ _ _ = SOME interval_tail’ >>
    simp[norm_match_tbl_def] >>
    
    (* Key step: prove head equivalence *)
    ‘(∃line. MEM line lines ∧ 
             is_intvl_match_row st_in packet_input line) ⇔ 
              is_match_row st_in h1 h0 m_v ’ by (
      cheat
      ) >>

    Cases_on ‘is_match_row st_in h1 h0 m_v’ >> fs[] >|[
        (* head*)
        gvs[] >>
        fs[norm_match_intvl_tbl_append] >>
        rpt (BasicProvers.FULL_CASE_TAC >> fs[])  >>
        cheat      
        ,
        (* rest by IH*)
        res_tac >>
        first_x_assum (strip_assume_tac o (Q.SPECL [‘st_in’])) >>
        fs[norm_match_intvl_tbl_def] >>
        fs[norm_match_intvl_tbl_append] >>
        rpt (BasicProvers.FULL_CASE_TAC >> fs[])  >>         
        (*needs a lemma*)
        cheat

      ]
  ]
        
QED

        



Theorem interval_single_table_converstion_correctness:
  ∀var_table m_e packet_input m_v interval_table packet_type st_in.
    ALL_DISTINCT (MAP FST m_e) ∧
    (∀var atom.  ALOOKUP m_e var = SOME atom ⇒
                 ALOOKUP m_v var = eval_arithm_atom packet_input atom) ∧
    convert_single_table var_table m_e packet_type = SOME interval_table ⇒
    match_tbl var_table m_v st_in = match_intvl_tbl interval_table packet_input st_in
Proof

  rpt strip_tac >>
gvs[GSYM norm_match_intvl_tbl_equiv] >>
gvs[GSYM norm_match_tbl_equiv] >>
metis_tac[semantic_single_table_equivalence_normalized]
QED
   
     
        
               
Theorem interval_tables_conversion_correctness:
  ∀var_tables m_e packet_input m_v interval_tables packet_type st_in.
    ALL_DISTINCT (MAP FST m_e) ∧
    
    (∀var atom. 
       ALOOKUP m_e var = SOME atom ⇒ 
       ALOOKUP m_v var = eval_arithm_atom packet_input atom) ∧
    
    (convert_tables var_tables m_e packet_type = SOME interval_tables) ⇒
    
    (* Semantic equivalence *)
    sem_tables (var_tables, st_in) m_v = 
    sem_intvl_tables (interval_tables, st_in) packet_input
Proof
  Induct >> rpt strip_tac >|[
    (* empty table input*)
    fs[convert_tables_def, sem_tables_def, sem_intvl_tables_def] >>
    gvs[sem_tables_def, match_tbll_def, sem_intvl_tables_def, match_intvl_tbll_def] 
    ,
    fs[convert_tables_def] >>     
    Cases_on ‘convert_single_table h m_e packet_type’ >> fs[] >>
    Cases_on ‘convert_tables var_tables m_e packet_type’ >> fs[] >>

    last_x_assum (drule_all_then strip_assume_tac) >>
    gvs[] >>

    
   ‘match_tbl h m_v st_in = match_intvl_tbl x packet_input st_in’ by (
   cheat
      ) >>

    Cases_on ‘var_tables’ >>
    Cases_on ‘x'’ >>
    gvs[] >|[

        (* both are last tables*)
        fs[match_tbll_def, match_intvl_tbll_def] >> cheat
        ,
        fs[convert_tables_def] >> cheat
        ,
        gvs[convert_tables_never_empty] >> cheat
        ,
        fs[match_tbll_def, match_intvl_tbll_def] >> cheat
      ]   
  ]         
QED



   














     *)



        
                                                                

val _ = export_theory ();

    

