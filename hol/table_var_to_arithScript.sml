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

Type intvl_table = “:('a intvl_row) list”;
Type intvl_table_list = “:('a intvl_table ) list”;



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
  (process_guard m_e max g (key, curr_int, s, res) =
    case atom_to_arith m_e g of
      | NONE => (key, Empty, s, res) (* Invalid guard becomes empty *)
      | SOME a_True => (key, Single 0 max, s, res) (* True uses full range *)
      | SOME a_False => (key, Empty, s, res) (* False is empty *)
      | SOME a => 
          (key, intersect_single curr_int (arith_to_interval a max), s, res))
End



        
Definition process_guards_rec_def:
  (process_guards_rec m_e max [] row = row) ∧
  (process_guards_rec m_e max (g::gs) row =
    process_guards_rec m_e max gs (process_guard m_e max g row))
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

        
(* Add this new function to analyze the entire table first *)
Definition analyze_table_type_def:
  (analyze_table_type m_e pd_type [] = SOME (T, key_const 1, 1)) ∧
                      
  (analyze_table_type m_e pd_type ((var_guards, s, res)::lines) =
   
   let all_guards = FLAT (MAP FST (((var_guards, s, res)::lines))) in
     
     (* First check if all variables are defined in m_e *)
     if ¬(all_vars_defined_abstract m_e all_guards)
     then
       NONE
     else
       let lvals = FILTER IS_SOME (MAP (get_lval_of_guard_in_me m_e) all_guards) in
         case lvals of
         | [] => SOME (T, key_const 1, 1)  (* All guards are boolean across entire table *)
         | (NONE)::rest => NONE 
         | (SOME lv)::rest => 
             if EVERY (λx. x = SOME lv) rest 
             then (case resolve_pd_max pd_type lv of
                   | SOME max => SOME (T, key_val lv, max)  (* All non-boolean guards use same LVal *)
                   | NONE => NONE)
             else NONE)              (* Different LVals detected *)
  
End

 


        
Definition convert_line_with_key_def:
  (convert_line_with_key m_e key_type max ([], s, res) =
    (* Empty guards - use full range of the key's type *)
    (key_type, Single 0 max, s, res)) ∧
  (convert_line_with_key m_e key_type max (var_guards, s, res) =
    process_guards_rec m_e max var_guards (key_type, Single 0 max, s, res))
End



Definition convert_single_table_def:
  (convert_single_table [] m_e pd_type = SOME []) ∧
  (convert_single_table lines m_e pd_type =
    case analyze_table_type m_e pd_type lines of
      | SOME (T, key_type, max) =>
          (* Convert all lines with the same key_type and max *)
          SOME (MAP (λline. convert_line_with_key m_e key_type max line) lines)
      | _ => NONE  (* Inconsistent table *)
  )
End

        



Definition convert_tables_def:
  (convert_tables [] _ _ = SOME []) ∧
  (convert_tables (tbl::tbls) m_e pd_type =
    case convert_single_table tbl m_e pd_type of
    | NONE => NONE  (* Fail immediately if any table fails *)
    | SOME converted_tbl =>
        case convert_tables tbls m_e pd_type of
        | NONE => NONE
        | SOME converted_tbls => SOME (converted_tbl :: converted_tbls))
End



(*
val policy1_var = “([[([(Var "x" :atom_var); (Var "y" :atom_var)],(0 :num),
        (state (3 :num) :(string # num list) action_expr));
       ([(Var "x" :atom_var); Not (Var "y" :atom_var)],(0 :num),
        (state (4 :num) :(string # num list) action_expr));
       ([False],(3 :num),action ("fwd",[(1 :num)]));
       ([True; False],(3 :num),action ("fwd",[(1 :num)]));
                  ([True],(3 :num),action ("fwd",[(1 :num)]));
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

EVAL ``convert_tables ^policy1_var ^test_m_e ^test_pd_nested``;
*)


    
                  

(* SEMANTICS *)
Definition is_intvl_match_row_def:
  is_intvl_match_row  (s_in:num) (packet_input:pd) (row:('a intvl_row)) =
    case row of
      ( key_val lval, Single a b, s, res) =>
        (case resolve_lval packet_input lval of
         | SOME (val_num v) =>  (a ≤ v ∧ v ≤ b ∧ (s_in = s))
         | SOME _ => F  (* non-numeric value *)
         | NONE => F )   (* lval not found *)
    | (key_val lval, Empty, s, res) =>  F                  
    | (key_const a, _ , s, _) =>  (s_in = s)
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
  (key_val (lv_x "dst_port"), Single 75 85, 0, state 1);
  (key_const 1, Single 0 100, 0, state 2)
] : (airth_key # interval # num # string action_expr) list``;

  
val test_table2 = ``[
  (key_val (lv_x "src_ip"), Single 190 200, (1:num), action "allow_internal");
  (key_const 1, Empty, 2, action "default_deny")
] : (airth_key # interval # num # string action_expr) list``;

(* Test table list with state transitions *)
val test_tables = “[^test_table1; ^test_table2]: ((airth_key # interval # num # string action_expr)) list list”;

(* Test cases *)
val test1 = EVAL ``sem_intvl_tables (^test_tables, ^initial_state) ^test_packet``;
               
*)










        

(**********)
(* proof  *)
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
  (norm_match_tbl (h::t) m_v st_in =
   let (guards,st,res) = h in
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





Theorem intersect_single_comm:
  ∀i1 i2. intersect_single i1 i2 = intersect_single i2 i1
Proof
  Cases_on `i1` >> Cases_on `i2` >> 
  rw[intersect_single_def] >>
  rw[MAX_COMM, MIN_COMM]
QED

Theorem intersect_single_assoc:
  ∀i1 i2 i3. intersect_single i1 (intersect_single i2 i3) = 
             intersect_single (intersect_single i1 i2) i3
Proof
  Cases_on `i1` >> Cases_on `i2` >> Cases_on `i3` >>
  rw[intersect_single_def] >>
  rw[MAX_ASSOC, MIN_ASSOC] >>
  decide_tac
QED







        
(*
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
  rpt gen_tac >> strip_tac  >-
   fs[convert_single_table_def, norm_match_tbl_def, norm_match_intvl_tbl_def] >>
  
  PairCases_on ‘h’ >>
  gvs[convert_single_table_def] >>

  rpt (BasicProvers.FULL_CASE_TAC >> fs[])  >>
  rename1 `_ = SOME (_, key_type, max)` >>
  gvs[] >>

  qabbrev_tac `ch = (convert_line_with_key m_e key_type max (h0,h1,h2))` >>
  PairCases_on `ch` >> simp[] >>

  (* Unfold the normalized matching functions *)
  fs[norm_match_tbl_def, norm_match_intvl_tbl_def] >>

  Cases_on ‘is_match_row st_in h1 h0 m_v’ >> rgs[] >|[
    ‘is_intvl_match_row st_in packet_input (convert_line_with_key m_e key_type max (h0,h1,h2))’ by cheat >>
    gvs[] >>
    cheat >>
    ,
    
    ‘~is_intvl_match_row st_in packet_input (convert_line_with_key m_e key_type max (h0,h1,h2))’ by cheat >>
    gvs[] >>
    first_x_assum match_mp_tac >>
    qexists_tac `m_e` >>
    qexists_tac `packet_type` >>

    Cases_on ‘var_table’ >> gvs[] >>
    gvs[convert_single_table_def] >>

    cheat
   
    (* incorrect, i can't use teh same key to analyse everything, as we might have var on top, then get true and so on in the bottom*)
                                  

  ]
 
QED
*)


(*



ALL_DISTINCT (MAP FST m_e) ∧
(∀var atom.
          ALOOKUP m_e var = SOME atom ⇒
          ALOOKUP m_v var = eval_arithm_atom packet_input atom) ⇒
convert_line_with_key m_e key max (guards,s,res) = (arith_key,interval,st,res') ⇒
((is_match_row st_in s guards m_v ⇔
   is_intvl_match_row st_in packet_input (arith_key,interval,st,res')) ∧ s = st'  ∧ res = res')


rpt gen_tac >> strip_tac >>
Cases_on ‘guards’ >> gvs[convert_line_with_key_def] >|[
    rpt strip_tac >>
    gvs[is_match_row_def, is_intvl_match_row_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> fs[])  >>
    




  ]

    













   
        

Theorem mapped_lists_equivalent:
  ∀var_table interval_table m_v packet_input st_in m_e packet_type.
    ALL_DISTINCT (MAP FST m_e) ∧
    (∀var atom. ALOOKUP m_e var = SOME atom ⇒
                ALOOKUP m_v var = eval_arithm_atom packet_input atom) ∧
    convert_single_table var_table m_e packet_type = SOME interval_table ⇒
    MAP (λ(gs,s,r). (is_match_row st_in s gs m_v, r)) var_table =
    MAP (λ(lv,i,s,r). (is_intvl_match_row st_in packet_input (lv,i,s,r), r)) interval_table
Proof
Induct_on `var_table` >>
  rpt gen_tac >> strip_tac >-
  (* Base case *) (
    fs[convert_single_table_def] >>
    fs[MAP]
  ) >>

  PairCases_on `h` >> rename1 `(guards, s, res)` >>
Cases_on ‘interval_table’ >-
 (gvs[convert_single_table_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[])
 ) >>

‘∃ q r' . analyze_table_type m_e packet_type ((guards,s,res)::var_table) =
 SOME (T,q,r')’ by
  (gvs[convert_single_table_def] >>
   rpt (BasicProvers.FULL_CASE_TAC >> gvs[])
  )


‘(is_match_row st_in s guards m_v,res) =
 (λ(lv,i,s,r). (is_intvl_match_row st_in packet_input (lv,i,s,r),r)) h’ by (

    PairCases_on ‘h’ >>
    gvs[] >>
    gvs[convert_single_table_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[])

    ) >>
 
gvs[analyze_table_type_def] >>
rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >|[
    gvs[convert_single_table_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
    gvs[analyze_table_type_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[])
        gvs[convert_line_with_key_def] >>
    ‘FILTER IS_SOME
          (
           MAP (get_lval_of_guard_in_me m_e) (FLAT (MAP FST var_table))) =
     []’ by cheat >>

    cheat >>




          
    ,

     
   gvs[is_match_row_def, is_intvl_match_row_def]



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
  rpt gen_tac >> strip_tac >>
  imp_res_tac mapped_lists_equivalent >> simp[] >>
  
  gvs[convert_single_table_def, match_tbl_def, match_intvl_tbl_def,
      check_all_rows_match_def, check_all_intvl_rows_match_def] >>
      
  gvs[ELIM_UNCURRY]               
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
  
    
  subgoal ‘match_tbl h m_v st_in = match_intvl_tbl x packet_input st_in’ >-
            ( cheat) >>
    metis_tac[interval_single_table_converstion_correctness] ) >>
  
  
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
] 
QED


   

*)
                                                                

val _ = export_theory ();










