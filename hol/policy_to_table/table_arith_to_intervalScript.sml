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
open tables_spec_oldTheory;

open table_bs_propertiesTheory;
     
open policy_arith_to_varTheory;
open table_var_to_arithTheory;

val _ = new_theory "table_arith_to_interval";


(*==========================================*)
(*         Types of interval tables         *)
(*==========================================*)       
val _ = Hol_datatype ` 
  interval = Empty | Single of bitv => bitv
`;

val _ = Hol_datatype ` 
  interval_key = key_val of arith_lv | key_const of bitv
`;

        
Type intvl_row        = “:(interval list # num # 'a action_expr)”;
Type intvl_table      = “:(interval_key # 'a intvl_row list)”;
Type intvl_table_list = “:('a intvl_table ) list”;



Definition wf_bit_def:
  wf_bit (bl,len) =
         (LENGTH bl = len)
End


Definition mk_max_bv_def:
  mk_max_bv bit_len =
  (fixwidth bit_len (n2v (max_from_type bit_len)),bit_len)
End
           
Definition mk_min_bv_def:
  mk_min_bv bit_len =
  (fixwidth bit_len (n2v 0),bit_len)
End        




Definition wf_packet_def:
  wf_packet packet_type packet_input =
  ∀ lval n.  resolve_lval_type packet_type lval = SOME (type_length n) ⇒
             n > 0 ∧ n < 129 ∧ ∃ bs. (resolve_lval packet_input lval = SOME (val_bs bs) ∧
                    wf_bit bs ∧ SND bs = n)
End

           

(*===============================================*)
(*       convert arith table to interval table   *)
(*===============================================*)

           
Definition arith_to_interval_def:
  arith_to_interval a bit_len =
    case a of
    | a_True => SOME (Single (mk_min_bv bit_len) (mk_max_bv bit_len))
    | a_False => SOME Empty
    | arithm_ge _ n =>
        (let (bl,len) = n in
          if (bit_len = len) ∧ wf_bit n  then
             SOME (Single n (mk_max_bv bit_len))
           else
             NONE)
          
    | arithm_le _ n =>
        (let (bl,len) = n in
           if (bit_len = len) ∧ wf_bit n then
              SOME (Single (mk_min_bv bit_len) n)
            else
              NONE)
End


Definition convert_arith_list_to_interval_def:
  convert_arith_list_to_interval arith_guards bit_len =
      MAP (λg. arith_to_interval g bit_len) arith_guards 
End

        
Definition convert_arith_rows_to_arith_def:
  convert_arith_rows_to_arith arith_table bit_len =
      MAP (λ(arith_guards,st,res). convert_arith_list_to_interval arith_guards bit_len, st, res) arith_table
End


Definition valid_line_def:
  valid_line (guards, s, res) = (guards ≠ [])
End


Definition valid_table_def:
  valid_table table = 
    ((table ≠ []) ∧ EVERY valid_line table)
End

(*
Definition valid_tables_def:
  valid_tables tables = EVERY valid_table tables
End
*)

        

val _ = Hol_datatype ` 
  ret_arth_indic = isTrue | isFalse | is_lval of arith_lv
`;
      


Definition arth_indic_in_lval_def:
  arth_indic_in_lval isTrue = F ∧
  arth_indic_in_lval isFalse = F ∧
  arth_indic_in_lval (is_lval _) = T           
End


      
Definition get_lval_from_arith_def:
  get_lval_from_arith a_True = isTrue ∧
  get_lval_from_arith a_False = isFalse ∧
  get_lval_from_arith (arithm_ge lv _) = is_lval lv ∧
  get_lval_from_arith (arithm_le lv _) = is_lval lv
End
           


Definition get_lval_of_ret_arith_list_def:
  get_lval_of_ret_arith_list ret_arith_guards =
  let filtered = FILTER (λx. arth_indic_in_lval x) ret_arith_guards in
    (case nub filtered of
    | [is_lval lv] => SOME (is_lval lv)
    | _ => NONE)                           (* if no lval at all after filtering,
                                              or more than one, then NONE*)
End
           

(* this should be for the whole table*)        
Definition get_lval_of_arith_list_def:
  get_lval_of_arith_list arith_guards =
  let lvals = MAP (λarith_g. get_lval_from_arith arith_g) arith_guards in
        ( case EVERY (λx. ¬ arth_indic_in_lval x) lvals of                (* case all True *)
          | T => SOME isTrue
          | F =>
              ( case get_lval_of_ret_arith_list lvals of     
                | SOME lv => SOME lv                           (* case blend, return single lval*)
                | NONE => NONE                                 (* faluty case, shouldn't be reached*)
              )
        )
        
End


(* checks if arithmetic table is convertable to interval table,
 we do not need to do this as a first step for vars anymore *) 
Definition analyze_arith_table_type_def:
  analyze_arith_table_type pd_type arith_table =
  if valid_table arith_table then
    let all_guards = FLAT (MAP FST arith_table) in
      (case get_lval_of_arith_list all_guards of
       | SOME isFalse => NONE
       | SOME isTrue => SOME (key_const (n2v 1, 1), 1)
       | SOME (is_lval lval) =>
           (case resolve_lval_type pd_type lval of
            | SOME (type_length n) => SOME (key_val lval, n)
            | _ => NONE
           )
       | NONE => NONE
      )
  else
    NONE
End

        
        
Definition convert_arith_to_interval_table_def:
  convert_arith_to_interval_table arith_table pd_type =
  case analyze_arith_table_type pd_type arith_table of
  | NONE => NONE 
  | SOME (key, bit_len) =>    
    (let converted = convert_arith_rows_to_arith arith_table bit_len in
    if every_is_some_in_l converted ∧ arith_table ≠ [] then
      SOME ((key, rm_optl converted): 'a intvl_table)
    else
      NONE
    )
End



(*


val test_pd_type = ``[("h" , type_record [("ttl", type_length 8);
                                          ("src", type_length 8)])]``;
                               

                                  
EVAL “convert_arith_to_interval_table
      [([   a_True;
         arithm_ge (lv_acc (lv_x "h") "ttl") (fixwidth 8 (n2v 1),8);
         arithm_le (lv_acc (lv_x "h") "ttl") (fixwidth 8 (n2v 3),8)],1, action "fwd1");
        
       ([arithm_ge (lv_acc (lv_x "h") "ttl") (fixwidth 8 (n2v 4),8)],1,action "fwd2");

       ([a_False],1,action "drop");

        ([a_True],1,action "drop")]

       ^test_pd_type”



      
EVAL “convert_arith_to_interval_table
      [([a_False],1, action "fwd1");
        
       ([a_True],1,action "fwd2");

       ([a_False],1,action "drop");

        ([a_False],1,action "drop")]

       ^test_pd_type”

       

        
*)



        


(*===============================================*)
(*       sem arith_table = sem interval_table    *)
(*===============================================*)



(* bv here could be from the lval in pd or from const*)
Definition eval_interval_atom_def:
  (eval_interval_atom bv pd Empty = SOME F) ∧
  (eval_interval_atom bv pd (Single a b) =
   case (bv_ge_than bv a, bv_le_than bv b) of
   | (SOME T, SOME T) => SOME T
   | (SOME F, SOME _) => SOME F
   | (SOME _, SOME F) => SOME F
   | (_,_) => NONE
  )
End        

   
Definition is_interval_guards_true_def:
  is_interval_guards_true interval_guards bv pd =
  EVERY (λ interval_atom. eval_interval_atom bv pd interval_atom = SOME T ) interval_guards
End      

         
Definition extract_bv_from_key_def:
  (extract_bv_from_key (key_val lval) pd =
   case resolve_lval pd lval of
   | SOME (val_bs bv) => SOME bv
   | _ => NONE
  )∧
  (extract_bv_from_key (key_const bv) pd = SOME bv)
End
         
         
Definition is_interval_match_row_def:
  is_interval_match_row st_in st_num artih_atoml bv pd = 
   ((st_in = st_num) ∧ is_interval_guards_true artih_atoml bv pd ∧ artih_atoml ≠ [])
End

        
Definition check_interval_table_sem_def:
  check_interval_table_sem st_in (interval_table: 'a intvl_table) pd =
  (let (key, intvl_lines) = interval_table in
     case (extract_bv_from_key key pd) of
     | SOME bv =>
       SOME (MAP (\(interval_guards, st, res).
         (is_interval_match_row st_in st interval_guards bv pd, res))  intvl_lines)
     | NONE => NONE
  )
End



Definition match_interval_table_def:
  match_interval_table (interval_table:'a intvl_table) pd st_in=
  case check_interval_table_sem st_in interval_table pd of
    | SOME res =>
      (case min_idx_till res T of
        SOME (idx, line) => SOME (SND line)
       | NONE => NONE
      )
    | NONE => NONE
End


(*



val example_pd =  
 “([ ("h", val_record [
            ("ttl", val_bs (fixwidth 8 (n2v 1), (8:num)))
     ])]): pd”;


val example_interval_table=
 “(key_val (lv_acc (lv_x "h") "ttl"),
        [([Single ([F; F; F; F; F; F; F; F],8) ([T; T; T; T; T; T; T; T],8);
           Single ([F; F; F; F; F; F; F; T],8) ([T; T; T; T; T; T; T; T],8);
           Single ([F; F; F; F; F; F; F; F],8) ([F; F; F; F; F; F; T; T],8)],
          1,action "fwd1");
         ([Single ([F; F; F; F; F; T; F; F],8) ([T; T; T; T; T; T; T; T],8)],
          1,action "fwd2"); ([Empty],1,action "drop");
         ([Single ([F; F; F; F; F; F; F; F],8) ([T; T; T; T; T; T; T; T],8)],
          1,action "drop")]): string intvl_table”;
        
EVAL “match_interval_table 
      ^example_interval_table
      ^example_pd (1:num) ”;

*)








Theorem extract_bv_from_key_not_none:
  ∀ arith_table packet_type packet_input key rows.        
    wf_packet packet_type packet_input ∧
    convert_arith_to_interval_table arith_table packet_type = SOME (key,rows) ⇒
    extract_bv_from_key key packet_input ≠ NONE
Proof
  rw[convert_arith_to_interval_table_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[analyze_arith_table_type_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[extract_bv_from_key_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  
  gvs[wf_packet_def] >>
  res_tac >> fs[] >>
  Cases_on ‘resolve_lval packet_input a’ >> gvs[]
QED





Theorem get_lval_ret_isTrue_then_bool_guards:
  ∀ l.
    get_lval_of_arith_list l = SOME isTrue ⇒
    EVERY (λx. x = a_True ∨ x = a_False) l
Proof
  Induct >>
  rw[get_lval_of_arith_list_def] >>
  rpt strip_tac >-  
   (Cases_on ‘h’ >>
    gvs[get_lval_from_arith_def, arth_indic_in_lval_def]) >>
  
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[get_lval_of_ret_arith_list_def])
QED



Theorem table_isbool_then_row_is_bool:
  ∀ row st res mv x tbl.
    x < LENGTH tbl ∧
    EL x tbl = (row,st,res) ∧
    EVERY (λx. x = a_True ∨ x = a_False) (FLAT (MAP FST tbl)) ⇒
    EVERY (λx. x = a_True ∨ x = a_False) row 
Proof
  rpt strip_tac >>
  imp_res_tac EL_MEM >>           
  gvs[EVERY_MEM] >>
  rpt strip_tac >>
  imp_res_tac mem_fst_snd >>
  gvs[MEM_FLAT] >>
  res_tac >>
  gvs[]
QED



Theorem arith_interval_equiv_for_bool_atoms:
  ∀ a packet_input.       
    (a = a_True ∨ a = a_False) ⇒
    (eval_interval_atom (n2v 1,1) packet_input (THE (arith_to_interval a 1)) =
     eval_arithm_atom packet_input a )
Proof           
  rw[arith_to_interval_def, eval_interval_atom_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[eval_arithm_atom_def, eval_interval_atom_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  EVAL_TAC >>
  
  gvs[bv_ge_than_def, bv_le_than_def, mk_max_bv_def, mk_min_bv_def, max_from_type_def] >>
  gvs[bitv_binpred_def, bitv_binpred_inner_def]
QED




Theorem arith_interval_equiv_for_bool_atoms_l:
  ∀ arith_guards packet_input.
    EVERY (λx. x = a_True ∨ x = a_False) arith_guards  ⇒
    (is_interval_guards_true
     (MAP (λg. THE (arith_to_interval g 1)) arith_guards) (n2v 1,1) packet_input  ⇔
       is_arith_guards_true arith_guards packet_input)
Proof
  rw[is_interval_guards_true_def, is_arith_guards_true_def] >>
  gvs[] >>
  EQ_TAC >> strip_tac  >>
  
  gvs[EVERY_EL] >>
  rpt strip_tac >>
  gvs[EL_MAP] >>
  res_tac >>

  imp_res_tac arith_interval_equiv_for_bool_atoms >>
  metis_tac[]
QED         

          
Definition relevant_atom_key_def:
  relevant_atom_key a_True a = T ∧
  relevant_atom_key a_False a  = T ∧
  relevant_atom_key (arithm_ge a' bv) a = (a'=a) ∧
  relevant_atom_key (arithm_le a' bv) a = (a'=a) 
End


           
Triviality nub_every:
  ∀ l a.
    nub l = [a] ⇒
    EVERY (λx. x=a)  l
Proof
  Induct >> 
  rpt strip_tac >>
  gvs[nub_def] >>         
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[EVERY_MEM]
QED


           
Theorem every_key_is_relevant_thm:
  ∀ l a.
    get_lval_of_arith_list l = SOME (is_lval a) ⇒
    EVERY (λx. relevant_atom_key x a ) l
Proof        
  rw[get_lval_of_arith_list_def] >>
  gvs[get_lval_of_ret_arith_list_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  
  imp_res_tac nub_every >>  
  
  gvs[EVERY_MEM] >>
  rpt strip_tac >>
  
  gvs[MEM_FILTER] >>
  gvs[MEM_MAP] >>
  
  Cases_on ‘x’ >> gvs[relevant_atom_key_def] >>
  
  
  first_x_assum (strip_assume_tac o (Q.SPECL [‘is_lval a'’])) >>
  gvs[arth_indic_in_lval_def] >|[
    ‘is_lval a' = get_lval_from_arith (arithm_ge a' p)’ by gvs[get_lval_from_arith_def] >>                            
    res_tac >>
    gvs[]
    ,
    ‘is_lval a' = get_lval_from_arith (arithm_le a' p)’ by gvs[get_lval_from_arith_def] >>                            
    res_tac >>
    gvs[]
  ]
QED
      



Theorem every_flat_then_every_mem:
  ∀ p row st res mv x tbl.
    x < LENGTH tbl ∧
    EL x tbl = (row,st,res) ∧
    EVERY p (FLAT (MAP FST tbl)) ⇒
    EVERY p row 
Proof
  rpt strip_tac >>
  imp_res_tac EL_MEM >>           
  gvs[EVERY_MEM] >>
  rpt strip_tac >>
  imp_res_tac mem_fst_snd >>
  gvs[MEM_FLAT] >>
  res_tac >>
  gvs[]
QED



Theorem bs_is_between_its_max_min:
  ∀ bs packet_input.
    SND bs > 0 ∧ SND bs < 129 ⇒
    eval_interval_atom bs packet_input (Single (mk_min_bv (SND bs)) (mk_max_bv (SND bs))) = SOME T
Proof
  rw[eval_interval_atom_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  
  PairCases_on ‘bs’ >>  
  gvs[bv_ge_than_def, bv_le_than_def] >>
  gvs[mk_max_bv_def, mk_min_bv_def] >>
  
  gvs[all_bs_larger_than_zero] >>             
  gvs[every_bs_is_less_than_max_fixwidth]
QED

                                                                                                


                                                                                                
Theorem sem_arith_var_atom_imp:
  ∀ interval_atom arith_atom packet_type packet_input lval k_val n bool.
    wf_packet packet_type packet_input ∧
    extract_bv_from_key (key_val lval) packet_input = SOME k_val ∧
    resolve_lval_type packet_type lval = SOME (type_length n) ∧
    relevant_atom_key arith_atom lval ∧
    arith_to_interval arith_atom n = SOME interval_atom ⇒
    ((eval_interval_atom k_val packet_input interval_atom = SOME bool ⇒
      eval_arithm_atom packet_input arith_atom = SOME bool) ∧
     (eval_arithm_atom packet_input arith_atom = SOME bool ⇒
    eval_interval_atom k_val packet_input interval_atom = SOME bool))
Proof

  rw[] >>
  (
  gvs[wf_packet_def] >>
  res_tac >>
  gvs[extract_bv_from_key_def] >>
       
  Cases_on ‘arith_atom’ >> rpt strip_tac >> gvs[] >|[
    gvs[eval_arithm_atom_def, arith_to_interval_def] >>
    gvs[bs_is_between_its_max_min]
    ,
    gvs[eval_arithm_atom_def, arith_to_interval_def, eval_interval_atom_def]
    ,
    gvs[relevant_atom_key_def] >>
    gvs[eval_arithm_atom_def, arith_to_interval_def] >>
                              
    PairCases_on ‘p’ >> gvs[] >>

    gvs[eval_interval_atom_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
    gvs[bv_ge_than_def, bv_le_than_def] >>
                 
    gvs[mk_max_bv_def] >>
    PairCases_on ‘bs’ >>
    gvs[every_bs_is_less_than_max_fixwidth]
    ,
    gvs[relevant_atom_key_def] >>
    gvs[eval_arithm_atom_def, arith_to_interval_def] >>
                              
    PairCases_on ‘p’ >> gvs[] >>

    gvs[eval_interval_atom_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
    gvs[bv_ge_than_def, bv_le_than_def] >>
                 
    gvs[mk_min_bv_def] >>
    PairCases_on ‘bs’ >>       
    gvs[all_bs_larger_than_zero]
  ]) 
QED






Theorem atoml_arith_interval_correct:
∀ arith_guards packet_type packet_input lval k_val n.

  wf_packet packet_type packet_input ∧
  extract_bv_from_key (key_val lval) packet_input = SOME k_val ∧
  
   ( ∀n'.
       n' < LENGTH arith_guards ⇒
       IS_SOME (arith_to_interval (EL n' arith_guards) n)) ∧
   
   resolve_lval_type packet_type lval = SOME (type_length n) ∧
   EVERY (λx. relevant_atom_key x lval) arith_guards  ⇒
  
  
  (is_interval_guards_true (MAP (λg. THE (arith_to_interval g n)) arith_guards) k_val packet_input  ⇔
     is_arith_guards_true arith_guards packet_input) 
Proof
  
  rw[is_interval_guards_true_def, is_arith_guards_true_def] >>
  gvs[] >>

  EQ_TAC >> strip_tac  >>
  
  gvs[EVERY_EL] >>
  rpt strip_tac >>
  gvs[EL_MAP] >>
  res_tac >>
  
  Cases_on ‘arith_to_interval (EL n' arith_guards) n’ >> rgs[] >>
  ‘relevant_atom_key (EL n' arith_guards) lval’ by gvs[] >>
  metis_tac[sem_arith_var_atom_imp]
QED
   

Theorem convert_arith_to_interval_table_length:
  ∀ arith_table interval_table packet_type key. 
    convert_arith_to_interval_table arith_table packet_type = SOME (key,interval_table) ⇒
    LENGTH interval_table = LENGTH arith_table
Proof
  rw[convert_arith_to_interval_table_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[convert_arith_rows_to_arith_def, rm_optl_def]
QED

  
                            


Theorem table_arith_interval_correct:
  ∀ arith_table interval_table packet_type packet_input st_in.
    wf_packet packet_type packet_input ∧
    convert_arith_to_interval_table arith_table packet_type =
    SOME interval_table ⇒
    check_interval_table_sem st_in interval_table packet_input = 
    SOME (check_arith_table_sem st_in arith_table packet_input)
Proof
                                    
  rw[check_interval_table_sem_def, check_arith_table_sem_def] >>
  
  Cases_on ‘interval_table’ >> 
  gvs[] >>
  
  Cases_on ‘extract_bv_from_key q packet_input’ >> gvs[] >| [
    ‘extract_bv_from_key q packet_input ≠ NONE’ by metis_tac[extract_bv_from_key_not_none]
    ,
    
    simp[LIST_EQ_REWRITE] >>
    ‘LENGTH r = LENGTH arith_table’ by metis_tac[convert_arith_to_interval_table_length] >>
    gvs[] >>

    rpt strip_tac >>
    gvs[EL_MAP] >>

    Cases_on ‘EL x' r’ >> Cases_on ‘r'’ >>
    Cases_on ‘EL x' arith_table’ >> Cases_on ‘r'’ >>


    rename1 ‘EL x' r = (interval_guards,interval_st,interval_res)’ >>
    rename1 ‘EL x' arith_table = (arith_guards,arith_st,arith_res)’ >>
    gvs[] >>


        
    gvs[convert_arith_to_interval_table_def] >>
    Cases_on ‘analyze_arith_table_type packet_type arith_table’ >> gvs[] >>
    Cases_on ‘x''’ >> gvs[] >>

    rename1 ‘i < LENGTH arith_table’ >>
    rename1 ‘extract_bv_from_key key packet_input = SOME k_val’ >>

    gvs[rm_optl_def] >>
    gvs[EL_MAP] >>
    
    gvs[every_is_some_in_l_def] >>
    gvs[EVERY_EL] >>
    res_tac >>
            
    Cases_on ‘EL i (convert_arith_rows_to_arith arith_table r')’ >> Cases_on ‘r’ >>
    rename1 ‘EL i (convert_arith_rows_to_arith arith_table r') = (interval_list,st_num,res)’ >>
    gvs[] >>   
    
    gvs[convert_arith_rows_to_arith_def] >>
    gvs[EL_MAP] >>
       
    gvs[convert_arith_list_to_interval_def] >>
    gvs[MAP_MAP_o] >>
    gvs[combinTheory.o_DEF] >>

    gvs[is_interval_match_row_def, is_arith_match_row_def] >>
    gvs[EL_MAP] >>

    gvs[analyze_arith_table_type_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >|[
        (* case key is constant*)
        gvs[extract_bv_from_key_def] >>
        imp_res_tac get_lval_ret_isTrue_then_bool_guards >>
        imp_res_tac every_flat_then_every_mem >>
        imp_res_tac arith_interval_equiv_for_bool_atoms_l >>
        metis_tac[]
        ,
        (* case key is lval*)
        imp_res_tac every_key_is_relevant_thm >>
        imp_res_tac every_flat_then_every_mem >>
        metis_tac[atoml_arith_interval_correct]
      ]
  ]
QED
       


Theorem full_table_arith_interval_correct:
  ∀ arith_table interval_table packet_input packet_type st_in.
    wf_packet packet_type packet_input ∧
    (convert_arith_to_interval_table arith_table packet_type = SOME interval_table) ⇒
    (match_interval_table interval_table packet_input st_in =
    match_arith_table arith_table packet_input st_in)
Proof
  rw[match_interval_table_def, match_arith_table_def] >>

  ‘check_interval_table_sem st_in interval_table packet_input  =
   SOME (check_arith_table_sem st_in arith_table packet_input) ’ by metis_tac[table_arith_interval_correct] >>
  gvs[] 
QED

        



(*==========================================*)
(*    Types of single interval tables       *)
(*==========================================*)       

        
Type sintvl_row        = “:(interval option # num # 'a action_expr)”;
Type sintvl_table      = “:(interval_key # 'a sintvl_row list)”;
Type sintvl_table_list = “:('a sintvl_table ) list”;



(*===============================================*)
(*    Convert interval tables to sinterval       *)
(*===============================================*) 

     
Definition bv_gt_than_def:
  bv_gt_than bv bv' =
  bitv_binpred binop_gt bv bv'
End


Definition bv_lt_than_def:
  bv_lt_than bv bv' =
  bitv_binpred binop_lt bv bv'
End

        

Definition check_widths_interval_def:
  check_widths_interval (v1,w1) (v2,w2) (v3,w3) (v4,w4) = 
  (w1 = w2 ∧ w2 = w3 ∧ w3 = w4 ∧
   wf_bit (v1,w1) ∧
   wf_bit (v2,w2) ∧
   wf_bit (v3,w3) ∧
   wf_bit (v4,w4) 
  )
End


        
Definition intersect_interval_def:
  intersect_interval (SOME (Single bv1 bv2)) (SOME (Single bv3 bv4)) =
  (case (bv_ge_than bv1 bv3, bv_ge_than bv2 bv4) of
   | (SOME a1_gt_a2, SOME b1_gt_b2) =>
       (let lower = if a1_gt_a2 then bv1 else bv3 in
          let upper = if b1_gt_b2 then bv4 else bv2 in
            (case bv_gt_than lower upper of
             | SOME F => SOME (Single lower upper)
             | SOME T => SOME Empty
             | _ => NONE
            )
       )
   | _ => NONE)
 ∧

  intersect_interval (SOME Empty) _ = SOME Empty ∧                     
  intersect_interval _ (SOME Empty) = SOME Empty ∧
  intersect_interval _ _ = NONE          
End



Definition mk_full_interval_def:
  mk_full_interval bit_len =
  Single (mk_min_bv bit_len) (mk_max_bv bit_len)
End



Definition operate_intersect_def:
 operate_intersect interval_g acc =
 case acc of
 | NONE => NONE
 | SOME acc_intvl =>
     case intersect_interval (SOME interval_g) (SOME acc_intvl) of
     | NONE => NONE
     | SOME Empty => NONE
     | SOME intvl => SOME intvl
End

        
Definition intersect_list_def:
 intersect_list bit_len list_gl  =
 let initial = SOME (mk_full_interval bit_len) in
   FOLDL (λacc interval_g. operate_intersect interval_g acc) initial list_gl
End
                                            

Definition convert_interval_to_sinterval_rows_def:
  convert_interval_to_sinterval_rows bit_len interval_rows =
  MAP (\(interval_guards, st, res). (
          if interval_guards = [] then
            NONE
          else
            intersect_list bit_len interval_guards , st, res)) interval_rows
End
          
     

Definition wf_interval_def:
  (wf_interval (Single a b) = (wf_bit a ∧ wf_bit b)) ∧ 
  (wf_interval Empty = T) 
End
     

Definition wf_interval_table_def:
  wf_interval_table interval_table =
  EVERY (λ interval. wf_interval interval) (FLAT (MAP FST interval_table))
End

     
     
Definition convert_interval_to_sinterval_table_def:
  convert_interval_to_sinterval_table interval_table pd_type =
  let (key, interval_rows) = interval_table in
    if interval_rows = [] then NONE else
      if ¬ (wf_interval_table interval_rows) then NONE else
        case key of
        | key_val lval =>
            ( case resolve_lval_type pd_type lval of
              | SOME (type_length bit_len) => SOME (key, convert_interval_to_sinterval_rows bit_len interval_rows)
              | _ => NONE 
            )
        | key_const (bl,n) =>
            if (n > 0 ∧ n < 129 ∧ LENGTH bl = n) then
              SOME (key, convert_interval_to_sinterval_rows n interval_rows)
            else
              NONE
End





    



        
(*



            
val example_pd =  
 “([("h", type_length 4)])”;


val example_interval_table1 =
 “(key_val (lv_x "h"),
        [([Single (fixwidth 4 (n2v 0), 4) (fixwidth 4 (n2v 10), 4);
           Single (fixwidth 4 (n2v 1), 4) (fixwidth 4 (n2v 10), 4);
           Single (fixwidth 4 (n2v 0), 4) (fixwidth 4 (n2v 3), 4)], 1, action "result1");
         ([Single (fixwidth 4 (n2v 4), 4) (fixwidth 4 (n2v 10), 4)], 1, action "result2"); 
         ([Empty], 1, action "result3");
         ([Single (fixwidth 4 (n2v 0), 4) (fixwidth 4 (n2v 10), 4)], 1, action "result4")]): string intvl_table”;

EVAL “convert_interval_to_sinterval_table ^example_interval_table1 ^example_pd”




fun make_bv n len = let
val n_term = numSyntax.term_of_int n
val len_term = numSyntax.term_of_int len
in
“(fixwidth ^(len_term) (n2v ^(n_term)), ^(len_term))”
end



fun make_interval a b len = let
val a_term = make_bv a len
val b_term = make_bv b len
in
“Single ^a_term ^b_term”
end



            
val example_pd2 =  
 “([("h", type_length 5)])”;


        
val example_interval_table2 =
 “(key_val (lv_x "h"),
        [([^(make_interval 1 10 5);
           ^(make_interval 2 8 5);
           ^(make_interval 3 15 5)]   , 1, action "result1");
         ([^(make_interval 5 6 5)]       , 1, action "result2"); 
         ([Empty], 1, action "result3");
         ([^(make_interval 8 11 5)]       , 1, action "result4")]): string intvl_table”;

EVAL “convert_interval_to_sinterval_table ^example_interval_table2 ^example_pd2”




val =   (make_interval 1 1 1)”


val example_interval_table1 =
 “(key_const ((fixwidth 1 (n2v 1), (1:num))),
        [([^(make_interval 1 1 1);
           ^(make_interval 1 1 1);
           ^(make_interval 1 1 1)], 1, action "result1");
         ([^(make_interval 0 1 1)], 1, action "result2"); 
         ([Empty], 1, action "result3");
         ([^(make_interval 0 1 1)], 1, action "result4")]): string intvl_table”;

EVAL “convert_interval_to_sinterval_table ^example_interval_table1 ^example_pd”



     



     
*)



(*===============================================*)
(*           Semantics of sinterval              *)
(*===============================================*) 
        
Definition is_sinterval_match_row_def:
  is_sinterval_match_row st_in st_num sinterval bv pd = 
   ((st_in = st_num) ∧ eval_interval_atom bv pd sinterval = SOME T)
End



Definition check_sinterval_rows_sem_def:
  check_sinterval_rows_sem st_in st_num sinterval bv pd=
  (case sinterval of
  | SOME (Single a b) => is_sinterval_match_row st_in st_num (Single a b) bv pd
  | _ => F
  )
End

        
Definition check_sinterval_table_sem_def:
  check_sinterval_table_sem st_in (sinterval_table: 'a sintvl_table) pd =
  (let (key, sintvl_lines) = sinterval_table in
     case (extract_bv_from_key key pd) of
     | SOME bv =>
       SOME (MAP (\(sinterval_guard, st, res).
         (check_sinterval_rows_sem st_in st sinterval_guard bv pd , res))  sintvl_lines)
     | NONE => NONE
  )
End



Definition match_sinterval_table_def:
  match_sinterval_table (sinterval_table:'a sintvl_table) pd st_in=
  case check_sinterval_table_sem st_in sinterval_table pd of
    | SOME res =>
      (case min_idx_till res T of
        SOME (idx, line) => SOME (SND line)
       | NONE => NONE
      )
    | NONE => NONE
End





(*==================================================*)
(*    Proof correctness interval to sinterval       *)
(*==================================================*)


Theorem wfness_type_of_lval_thm:
  ∀ lval len bs packet_type packet_input.         
    wf_packet packet_type packet_input ∧
    resolve_lval_type packet_type lval = SOME (type_length len) ∧
    resolve_lval packet_input lval = SOME (val_bs bs) ⇒
    SND bs > 0 ∧ SND bs < 129 ∧ wf_bit bs ∧ len = SND bs
Proof
  rw[wf_packet_def] >>
  res_tac >>
  gvs[]
QED


    

Theorem intersect_none_not_atom_true:
  ∀ bs packet_input p1 p2.
  SND bs > 0 ∧ SND bs < 129 ∧
  operate_intersect (Single p1 p2) (SOME (mk_full_interval (SND bs))) = NONE ⇒
  eval_interval_atom bs packet_input (Single p1 p2) ≠ SOME T
Proof
  rpt strip_tac >>
  gvs[operate_intersect_def, eval_interval_atom_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  
  gvs[mk_full_interval_def] >>
  gvs[intersect_interval_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  
  gvs[bv_le_than_def, bv_ge_than_def, bv_gt_than_def, mk_max_bv_def, mk_min_bv_def] >>
  
  PairCases_on ‘bs’ >>
  PairCases_on ‘p1’ >>
  PairCases_on ‘p2’ >>
  gvs[] >>
  
  imp_res_tac bitv_binpred_same_length >> gvs[] >>
  imp_res_tac last_edge_of_binpred_neg >> gvs[] >>                 
  imp_res_tac every_bs_is_not_larger_than_max_fixwidth >> gvs[] >>
  imp_res_tac transitive_binpred1 >> gvs[] >>
  imp_res_tac all_bs_larger_than_zero >> gvs[]
              
QED


        

Theorem intersect_none_not_atom_true_full:                      
  ∀ packet_type packet_input interval lval len bs. 
    SND bs > 0 ∧ SND bs < 129 ∧ len = SND bs ∧
    operate_intersect interval (SOME (mk_full_interval len)) = NONE  ⇒
    eval_interval_atom bs packet_input interval ≠ SOME T     
Proof                    
  Cases_on ‘interval’ >>
  rpt strip_tac >-
   gvs[eval_interval_atom_def] >>

  gvs[] >>
  metis_tac[intersect_none_not_atom_true]
QED



Theorem intersect_empty_not_atom_true_full:                      
  ∀ packet_type packet_input interval1 interval2 lval len bs. 
    operate_intersect interval1 interval2 = SOME Empty  ⇒
    eval_interval_atom bs packet_input interval1 ≠ SOME T 
Proof                    
  Cases_on ‘interval1’ >>
  Cases_on ‘interval2’ >>


   gvs[eval_interval_atom_def] >>
  
  gvs[operate_intersect_def, eval_interval_atom_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[])
QED


   

Triviality operate_intersect_with_empty_results_none:
∀ h. operate_intersect Empty h = NONE
Proof
  Cases_on ‘h’ >>
  gvs[operate_intersect_def] >>
  gvs[intersect_interval_def]
QED


   
Theorem if_bs_ge_not_gt_max_then_eq:        
  ∀ a len.
    len < 129 ∧ len > 0 ∧
    wf_bit (a,len) ∧
    bitv_binpred binop_gt (a,len) (fixwidth len (n2v (max_from_type len)),len) = SOME F ∧
    bitv_binpred binop_ge (a,len) (fixwidth len (n2v (max_from_type len)),len) = SOME T ⇒
    a = fixwidth len (n2v (max_from_type len))
Proof
  Rewrite.ONCE_REWRITE_TAC [bitv_binpred_def] >>
  Rewrite.ONCE_REWRITE_TAC [bitv_binpred_inner_def] >>
  rpt strip_tac >>
  
  rpt(
    BasicProvers.FULL_CASE_TAC >-(                         
        fs[] >>
        gvs[get_word_binpred_def] >>
        
        gvs[WORD_HIGHER_OR_EQ, v2w_11] >>
        fs[wf_bit_def] >>
        gvs[] )
    ) >> metis_tac[]
QED




Theorem if_bs_le_ge_max_then_eq:
  ∀ len a .
    len < 129 ∧
    len > 0 ∧
    wf_bit (a,len) ∧
    bitv_binpred binop_ge (a,len) (fixwidth len (n2v (max_from_type len)),len) = SOME T ∧
    bitv_binpred binop_le (a,len) (n2v (max_from_type len),len) = SOME T ⇒
    a = fixwidth len (n2v (max_from_type len))
Proof
  Rewrite.ONCE_REWRITE_TAC [bitv_binpred_def] >>
  Rewrite.ONCE_REWRITE_TAC [bitv_binpred_inner_def] >>
  rpt strip_tac >>
  
  rpt(
    BasicProvers.FULL_CASE_TAC >-(                         
        fs[] >>
        gvs[get_word_binpred_def] >>
        
        gvs[WORD_HIGHER_OR_EQ, v2w_11] >>
        fs[wf_bit_def] >>
        gvs[] >>
        
        gvs[fixwidth_max_all] >>
        blastLib.FULL_BBLAST_TAC 
      )
    ) >> metis_tac[]
QED


Theorem if_bs_ge_max_then_eq:        
  ∀ a len.
    len < 129 ∧ len > 0 ∧
    wf_bit (a,len) ∧
    bitv_binpred binop_ge (a,len) (fixwidth len (n2v (max_from_type len)),len) = SOME T ⇒
    a = fixwidth len (n2v (max_from_type len))
Proof
  rpt strip_tac >>
  imp_res_tac every_bs_is_less_than_max >>
  first_x_assum (strip_assume_tac o (Q.SPECL [‘a’])) >>
  metis_tac[if_bs_le_ge_max_then_eq]
QED

        

        
Theorem operate_intersect_w_max_results_len:
  ∀ interval a b len.
    len > 0 ∧ len < 129 ∧ wf_interval interval ∧ 
    operate_intersect interval (SOME (mk_full_interval len)) = SOME (Single a b) ⇒
    (interval = Single a b  ∧ SND a = len ∧ SND b = len)
Proof
  Cases_on ‘interval’ >>                                                         
  gvs[operate_intersect_def] >>
  rpt strip_tac >>
  
  PairCases_on ‘a’ >> gvs[] >>
  PairCases_on ‘b’ >> gvs[] >>

  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[intersect_interval_def, mk_full_interval_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  
  gvs[bv_ge_than_def, bv_gt_than_def, mk_min_bv_def, mk_max_bv_def] >>
  
  imp_res_tac bitv_binpred_same_length >> gvs[] >>
  imp_res_tac all_bs_larger_than_zero >> gvs[] >|[
    PairCases_on ‘p’ >> gvs[]
    ,
    PairCases_on ‘p’ >> gvs[]
    ,
    PairCases_on ‘p0’ >> gvs[wf_interval_def] >>
    imp_res_tac if_bs_ge_max_then_eq
    ,
    PairCases_on ‘p’ >> gvs[]
  ] 
QED



Theorem operate_intersect_two_intervals_len:
  ∀ len len1 len2 a b c d interval.
    len > 0 ∧ len < 129 ∧
    operate_intersect interval (SOME (Single (a,len) (b,len))) = SOME (Single (c,len1) (d,len2)) ⇒
    len = len1 ∧ len = len2
Proof
  rw[operate_intersect_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>

  Cases_on ‘interval’ >>
  rpt strip_tac >>
  gvs[operate_intersect_def, eval_interval_atom_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  
  gvs[intersect_interval_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
      
  gvs[wf_interval_def, wf_bit_def] >>
  gvs[bv_le_than_def, bv_ge_than_def, bv_gt_than_def, mk_max_bv_def, mk_min_bv_def] >>
  
  imp_res_tac bitv_binpred_same_length >> gvs[]
QED




Theorem op_intersect_none_or_empty_then_not_true:
  ∀ packet_input len interval bs a b .
    len > 0 ∧ len < 129 ∧
    eval_interval_atom (bs,len) packet_input (Single (a,len) (b,len)) = SOME T ∧
    (operate_intersect interval (SOME (Single (a,len) (b,len))) = NONE ∨
     operate_intersect interval (SOME (Single (a,len) (b,len))) = SOME Empty
    ) ⇒
    eval_interval_atom (bs,len) packet_input interval ≠ SOME T
Proof

  rw[operate_intersect_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  
  
  Cases_on ‘interval’ >>
  rpt strip_tac >>
  gvs[operate_intersect_def, eval_interval_atom_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>

  gvs[intersect_interval_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  
  PairCases_on ‘p0’ >>
  PairCases_on ‘p’ >>
  gvs[] >>
  
  
  gvs[wf_interval_def, wf_bit_def] >>
  gvs[bv_le_than_def, bv_ge_than_def, bv_gt_than_def, mk_max_bv_def, mk_min_bv_def] >>
  
  imp_res_tac bitv_binpred_same_length >> gvs[] >>
  imp_res_tac last_edge_of_binpred_neg >> gvs[] >>                 
  imp_res_tac every_bs_is_not_larger_than_max_fixwidth >> gvs[] >>
  imp_res_tac transitive_binpred1 >> gvs[] >>
  imp_res_tac all_bs_larger_than_zero >> gvs[]
QED



Theorem two_intervals_eval_is_true_then_intersection_in_true:
  ∀ len interval a b c d bs packet_input.
    len > 0 ∧ len < 129 ∧
    eval_interval_atom (bs,len) packet_input (Single (a,len) (b,len)) = SOME T ∧
    eval_interval_atom (bs,len) packet_input interval = SOME T ∧
    operate_intersect interval (SOME (Single (a,len) (b,len))) = SOME (Single (c,len) (d,len)) ⇒ 
    eval_interval_atom (bs,len) packet_input (Single (c,len) (d,len)) = SOME T
Proof
 rw[operate_intersect_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  
  
  Cases_on ‘interval’ >>
  rpt strip_tac >>
  gvs[operate_intersect_def, eval_interval_atom_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  
  gvs[intersect_interval_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>


  gvs[wf_interval_def, wf_bit_def] >>
  gvs[bv_le_than_def, bv_ge_than_def, bv_gt_than_def, mk_max_bv_def, mk_min_bv_def] >>
  
  imp_res_tac bitv_binpred_same_length >> gvs[] 
QED



Theorem foldl_single_none_empty_then_not_match:
  ∀ interval_list a b len  st_in s_in_intvl bs (packet_input:(string # pd_val) list ).
    len > 0 ∧ len < 129 ∧
    eval_interval_atom (bs,len) packet_input (Single (a,len) (b,len)) = SOME T ∧
    (FOLDL (λacc interval_g. operate_intersect interval_g acc)
          (SOME (Single (a,len) (b,len)))
          interval_list = NONE ∨
     FOLDL (λacc interval_g. operate_intersect interval_g acc)
           (SOME (Single (a,len) (b,len)))
           interval_list = SOME Empty
    )
     ⇒
    ~is_interval_match_row st_in s_in_intvl interval_list (bs,len) packet_input
Proof  
  Induct >> 
  gvs[] >>
  rpt strip_tac >>

  (
  Cases_on ‘operate_intersect h (SOME (Single (a,len) (b,len)))’ >|[

      gvs[is_interval_match_row_def] >>
      gvs[is_interval_guards_true_def] >>
      rw[] >>
      imp_res_tac op_intersect_none_or_empty_then_not_true        
      , 
      
      Cases_on ‘x’ >> gvs[] >|[

          gvs[is_interval_match_row_def] >>
          gvs[is_interval_guards_true_def] >>
          rw[] >>
          imp_res_tac op_intersect_none_or_empty_then_not_true      
          ,

          PairCases_on ‘p’ >>
          PairCases_on ‘p0’  >>
          imp_res_tac operate_intersect_two_intervals_len >>
          gvs[] >>

          rename1 ‘operate_intersect interval (SOME (Single (a,len) (b,len))) =
                   SOME (Single (c,len) (d,len))’ >>

          first_x_assum (strip_assume_tac o (Q.SPECL [‘c’, ‘d’, ‘len’,‘st_in’, ‘s_in_intvl’,
                                                      ‘bs’, ‘packet_input’])) >>
          
          subgoal ‘eval_interval_atom (bs,len) packet_input (Single (c,len) (d,len)) =
                   SOME T’ >-
           (
           gvs[is_interval_match_row_def, is_interval_guards_true_def] >>
           metis_tac [two_intervals_eval_is_true_then_intersection_in_true]
           ) >>
                                    
          gvs[] >>
          fs[is_interval_match_row_def, is_interval_guards_true_def] >> gvs[] >>
          metis_tac[NOT_EVERY]       
        ]
    ]
  )
QED





Theorem intersection_of_intervals_lists_none_empty_not_match:
  ∀interval_list bs len (packet_input:(string # pd_val) list ) (st_in:num) s_in_intvl.
    SND bs > 0 ∧ SND bs < 129 ∧ len = SND bs ∧
     
    EVERY (λinterval. wf_interval interval) interval_list ∧
    interval_list ≠ [] ∧
    
    (intersect_list len interval_list = NONE ∨
     intersect_list len interval_list = SOME Empty )   ⇒
    ¬is_interval_match_row st_in s_in_intvl interval_list bs packet_input
Proof
                               
  gvs[intersect_list_def] >>
  Induct >> gvs[] >>
  rw[FOLDL] >>
  rpt strip_tac >>
  (* case NONE and empty, same proof *)
  (
  Cases_on ‘operate_intersect h (SOME (mk_full_interval (SND bs)))’ >> gvs[] >|[
      gvs[is_interval_match_row_def] >>
      gvs[is_interval_guards_true_def] >>
      rw[] >>
      metis_tac[intersect_none_not_atom_true_full] 
      ,
      Cases_on ‘x’ >> gvs[] >|[
          (* case empty*)
          gvs[is_interval_match_row_def] >>
          gvs[is_interval_guards_true_def] >>
          rw[] >>
          imp_res_tac intersect_empty_not_atom_true_full
          ,
          
          ‘SND p = SND bs ∧
           SND p0 = SND bs ∧
           h = (Single p p0)’ by metis_tac[operate_intersect_w_max_results_len] >>
                
          Cases_on ‘interval_list = []’ >> gvs[] >>

          (* from last goal in assumptions  *)
          PairCases_on ‘p’ >> gvs[] >>
          PairCases_on ‘p0’ >> gvs[] >>
          PairCases_on ‘bs’ >> gvs[] >>
          
          rename1 ‘operate_intersect (Single (a,len) (b,len)) (SOME (mk_full_interval len)) =
                   SOME (Single (a,bs1) (b,len))’ >>
                   
          gvs[is_interval_match_row_def, is_interval_guards_true_def] >>
          assume_tac foldl_single_none_empty_then_not_match >>
          first_x_assum (strip_assume_tac o (Q.SPECL [‘interval_list’, ‘a’, ‘b’, ‘len’, ‘st_in’, ‘st_in’,
                                                      ‘bs0’, ‘packet_input’])) >>      
          gvs[is_interval_match_row_def, is_interval_guards_true_def]
         
      ]
  ]
)
QED     
                             




Theorem starting_from_none_intersection_results_none:
  ∀ interval_list.
    FOLDL (λacc interval_g. operate_intersect interval_g acc) NONE interval_list = NONE 
Proof
  Induct >> rw[] >>
  Cases_on ‘operate_intersect h NONE’ >> gvs[operate_intersect_def]
QED

                                                                                    
Theorem starting_from_empty_intersection_results_none_or_empty:
  ∀ interval_list a b.
    FOLDL (λacc interval_g. operate_intersect interval_g acc) (SOME Empty) interval_list = a ⇒
    (a = NONE ∨ a = SOME Empty)
Proof
 Induct >> rw[] >>
  Cases_on ‘operate_intersect h (SOME Empty)’ >> gvs[] >>

 rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
 gvs[starting_from_none_intersection_results_none] >>

 (
 Cases_on ‘h’ >> rgs[Once intersect_interval_def] >>
 rgs[Once operate_intersect_def, intersect_interval_def]      
 )

QED
         



Theorem two_wf_interval_intersection_results_wf_interval:
  ∀ interval1 interval2 interval3.
    wf_interval interval1 ∧
    wf_interval interval2 ∧
    operate_intersect interval1 (SOME interval2) = SOME interval3 ⇒
    wf_interval interval3
Proof
  Cases_on ‘interval1’ >>
  Cases_on ‘interval2’ >>
  rw[wf_interval_def, operate_intersect_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[intersect_interval_def]) >>
  
  gvs[wf_interval_def, wf_bit_def]
QED




Theorem transitive_binpred2:
  ∀ len a b c.
    len > 0 ∧
    len < 129 ∧
    
    bitv_binpred binop_ge (a,len) (b,len) = SOME T ∧
    bitv_binpred binop_le (c,len) (b,len) = SOME T  ⇒
    bitv_binpred binop_le (c,len) (a,len) = SOME T
Proof
  rw[bitv_binpred_def] >>
  Rewrite.ONCE_REWRITE_TAC [bitv_binpred_inner_def, get_word_binpred_def] >>
  rpt strip_tac >>
  
  rpt(
    BasicProvers.FULL_CASE_TAC >-
     (fs[get_word_binpred_def] >>
      gvs[bitv_binpred_inner_def, get_word_binpred_def] >>
      blastLib.FULL_BBLAST_TAC 
     )
    ) >> intLib.COOPER_TAC  
QED




Theorem transitive_binpred3:
  ∀ len a b c.
    len > 0 ∧
    len < 129 ∧                                                        
    bitv_binpred binop_ge (a,len) (b,len) = SOME T ∧
    bitv_binpred binop_ge (c,len) (a,len) = SOME T ⇒
    bitv_binpred binop_ge (c,len) (b,len) = SOME T
Proof
  rw[bitv_binpred_def] >>
  Rewrite.ONCE_REWRITE_TAC [bitv_binpred_inner_def, get_word_binpred_def] >>
  rpt strip_tac >>
  
  rpt(
    BasicProvers.FULL_CASE_TAC >-
     (fs[get_word_binpred_def] >>
      gvs[bitv_binpred_inner_def, get_word_binpred_def] >>
      blastLib.FULL_BBLAST_TAC 
     )
    ) >> intLib.COOPER_TAC 
QED


Theorem transitive_binpred4:
  ∀ len a b c.
    len > 0 ∧
    len < 129 ∧
    bitv_binpred binop_ge (a,len) (b,len) = SOME F ∧
    bitv_binpred binop_ge (c,len) (a,len) = SOME F ⇒
    bitv_binpred binop_ge (c,len) (b,len) = SOME F
Proof
  rw[bitv_binpred_def] >>
  Rewrite.ONCE_REWRITE_TAC [bitv_binpred_inner_def, get_word_binpred_def] >>
  rpt strip_tac >>
  
  rpt(
    BasicProvers.FULL_CASE_TAC >-
     (fs[get_word_binpred_def] >>
      gvs[bitv_binpred_inner_def, get_word_binpred_def] >>
      blastLib.FULL_BBLAST_TAC 
     )
    ) >> intLib.COOPER_TAC 
QED


Theorem transitive_binpred5:
  ∀ len a b c.
    len > 0 ∧
    len < 129 ∧
    bitv_binpred binop_ge (a,len) (b,len) = SOME F ∧
    bitv_binpred binop_le (c,len) (a,len) = SOME T ⇒
    bitv_binpred binop_le (c,len) (b,len) = SOME T
Proof

  rw[bitv_binpred_def] >>
  Rewrite.ONCE_REWRITE_TAC [bitv_binpred_inner_def, get_word_binpred_def] >>
  rpt strip_tac >>
  
  rpt(
    BasicProvers.FULL_CASE_TAC >-
     (fs[get_word_binpred_def] >>
      gvs[bitv_binpred_inner_def, get_word_binpred_def] >>
      blastLib.FULL_BBLAST_TAC 
     )
    ) >> intLib.COOPER_TAC 

QED

        




Theorem intersection_preserves_evaluation_thm:
  ∀ interval1 interval2 interval3 bs len packet_input.
    len >0 ∧ len <129 ∧
    operate_intersect interval1 (SOME interval2) = SOME interval3 ⇒
    (
    eval_interval_atom (bs,len) packet_input interval1 = SOME T ∧
    eval_interval_atom (bs,len) packet_input interval2 = SOME T
    ⇔
      eval_interval_atom (bs,len) packet_input interval3 = SOME T )
Proof


  Cases_on ‘interval1’ >>
  Cases_on ‘interval2’ >>
  rw[operate_intersect_def] >>
 rpt (BasicProvers.FULL_CASE_TAC >> gvs[intersect_interval_def]) >>
  (* all cases *)
  (
  PairCases_on ‘p’ >>
  PairCases_on ‘p'’ >>
  PairCases_on ‘p0’ >>
  PairCases_on ‘p0'’ >>
  
  
  gvs[eval_interval_atom_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[intersect_interval_def]) >>

  
  
  gvs[bv_le_than_def, bv_ge_than_def, bv_gt_than_def] >>
  
  
  
  imp_res_tac bitv_binpred_same_length >> gvs[] >>
  imp_res_tac last_edge_of_binpred_neg >> gvs[] >>                 
  imp_res_tac transitive_binpred1 >> gvs[] >>
  imp_res_tac transitive_binpred2 >> gvs[] >>
  imp_res_tac transitive_binpred3 >> gvs[] >>
  imp_res_tac transitive_binpred4 >> gvs[] >>
  imp_res_tac transitive_binpred5 >> gvs[]
  )
QED





Theorem intersection_eval_row_interval_sinterval_correct:
  ∀ interval_list len a b c d bs bs0 packet_input.
    len > 0 ∧
    len < 129 ∧
    wf_interval (Single (c,len) (d,len)) ∧
    EVERY (λinterval. wf_interval interval) interval_list ∧
    FOLDL (λacc interval_g. operate_intersect interval_g acc)
          (SOME (Single (c,len) (d,len))) interval_list = SOME (Single a b) ⇒
    (eval_interval_atom (bs0,len) packet_input (Single a b) = SOME T ⇔
       is_interval_guards_true (Single (c,len) (d,len)::interval_list) (bs0,len) packet_input)
Proof
  gvs[intersect_list_def] >>
  Induct >> gvs[] >>
  rw[FOLDL] >>
  rpt strip_tac >|[
    
    gvs[is_interval_guards_true_def]  
    ,
        
    Cases_on ‘operate_intersect h (SOME (Single (c,len) (d,len)))’ >|[
        assume_tac starting_from_none_intersection_results_none >>
        gvs[]
        ,
        Cases_on ‘x’ >> gvs[] >|[
            assume_tac starting_from_empty_intersection_results_none_or_empty >>
            gvs[] >>
            first_x_assum (strip_assume_tac o (Q.SPECL [‘interval_list’])) >>
            gvs[]
            ,
                     
            PairCases_on ‘p’ >>
            PairCases_on ‘p0’ >>
            imp_res_tac operate_intersect_two_intervals_len >> gvs[] >>

            first_x_assum (strip_assume_tac o (Q.SPECL [‘len’, ‘a’, ‘b’, ‘p0'’, ‘p00’, ‘bs0’, ‘packet_input’])) >>
            gvs[] >>

                        
            ‘wf_interval (Single (p0',len) (p00,len))’ by metis_tac[two_wf_interval_intersection_results_wf_interval] >>
            gvs[] >>

            simp[is_interval_guards_true_def] >>
            metis_tac[intersection_preserves_evaluation_thm]
          ]
      ]
  ]
QED





                                     

Theorem intersection_eval_row_interval_sinterval_correct_full:
  ∀ interval_list bs len (packet_input:(string # pd_val) list ) a b.
    SND bs > 0 ∧ SND bs < 129 ∧ len = SND bs ∧
        
    EVERY (λinterval. wf_interval interval) interval_list ∧
    interval_list ≠ [] ∧
    
    intersect_list len interval_list = SOME (Single a b)    ⇒
    (eval_interval_atom bs packet_input (Single a b) = SOME T ⇔
       is_interval_guards_true interval_list bs packet_input)
Proof

  gvs[intersect_list_def] >>
  Induct >> gvs[] >>
  rw[FOLDL] >>
  rpt strip_tac >>
  
  Cases_on ‘operate_intersect h (SOME (mk_full_interval (SND bs)))’ >> gvs[] >|[
    (* starting from none, results none *)
    assume_tac starting_from_none_intersection_results_none >>
    gvs[]
    ,
    
    Cases_on ‘x’ >> gvs[] >|[
        assume_tac starting_from_empty_intersection_results_none_or_empty >>
        gvs[] >>
        first_x_assum (strip_assume_tac o (Q.SPECL [‘interval_list’])) >>
        gvs[]
        ,
        
        ‘SND p = SND bs ∧
         SND p0 = SND bs ∧
         h = (Single p p0)’ by metis_tac[operate_intersect_w_max_results_len] >>
        gvs[] >>


        PairCases_on ‘p’ >> gvs[] >>
        PairCases_on ‘p0’ >> gvs[] >>
        PairCases_on ‘bs’ >> gvs[] >>
        
        rename1 ‘operate_intersect (Single (c,len) (d,len)) (SOME (mk_full_interval len)) =
                 SOME (Single (c,bs1) (d,len))’ >>
        metis_tac [intersection_eval_row_interval_sinterval_correct]
      ]
  ]
QED




                                                                                             

Theorem  check_sinterval_table_sem_table_correct:
  ∀ packet_input packet_type interval_table sinterval_table st_in.
    wf_packet packet_type packet_input ∧
    convert_interval_to_sinterval_table interval_table packet_type =
    SOME sinterval_table ⇒
    check_sinterval_table_sem st_in sinterval_table packet_input =
    check_interval_table_sem st_in interval_table packet_input
Proof

  rpt strip_tac >>
  PairCases_on ‘sinterval_table’ >>
  PairCases_on ‘interval_table’ >>                                
  rename1 ‘convert_interval_to_sinterval_table (key_intvl,tbl_intvl) packet_type = SOME (skey_intvl,stbl_intvl)’ >>
  
  gvs[convert_interval_to_sinterval_table_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >|[
    
    (*key val*)
    
    gvs[check_sinterval_table_sem_def, check_interval_table_sem_def] >>
    Cases_on ‘extract_bv_from_key (key_val a) packet_input’ >> gvs[] >>
    
    simp[LIST_EQ_REWRITE] >>
    ‘LENGTH (convert_interval_to_sinterval_rows n tbl_intvl) =
     LENGTH tbl_intvl’ by rw[convert_interval_to_sinterval_rows_def] >>
    gvs[] >>
    
    
    rpt strip_tac >>
    gvs[EL_MAP] >>
    
    Cases_on ‘EL x' (convert_interval_to_sinterval_rows n tbl_intvl)’ >> Cases_on ‘r’ >>
    Cases_on ‘EL x' tbl_intvl’ >> Cases_on ‘r’ >>
    
    rename1 ‘EL x' (convert_interval_to_sinterval_rows n tbl_intvl) = (sinterval,s_in_sintvl,res_sintvl)’ >>
    rename1 ‘EL x' tbl_intvl = (interval_list,s_in_intvl,res_intvl)’ >>
    gvs[] >>
    
    gvs[convert_interval_to_sinterval_rows_def] >>
    Cases_on ‘tbl_intvl = []’ >> gvs[] >>
    gvs[EL_MAP] >>
    
    Cases_on ‘interval_list = []’ >> gvs[] >-
     gvs[check_sinterval_rows_sem_def, is_interval_match_row_def] >>
    
    gvs[check_sinterval_rows_sem_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
    
    gvs[wf_interval_table_def] >>
    imp_res_tac every_flat_then_every_mem >>
    
    gvs[extract_bv_from_key_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >|[
      (* intersect list is NONE, then not a match row*)
      
      imp_res_tac wfness_type_of_lval_thm >> gvs[] >>
      metis_tac[intersection_of_intervals_lists_none_empty_not_match]
      ,
      (*intersect list is Empty, then contrd or false, then not all atoms were true*)
      
      imp_res_tac wfness_type_of_lval_thm >> gvs[] >>
      metis_tac[intersection_of_intervals_lists_none_empty_not_match]
      ,
      (*intersect list is something, then semantics must match*)
      
      gvs [is_sinterval_match_row_def, is_interval_match_row_def] >>
      
      imp_res_tac wfness_type_of_lval_thm >> gvs[] >>
      metis_tac[intersection_eval_row_interval_sinterval_correct_full] 
    ]                                  
    ,

        
    (* key const *)
    gvs[check_sinterval_table_sem_def, check_interval_table_sem_def] >>
    Cases_on ‘extract_bv_from_key (key_const (q,LENGTH q)) packet_input’ >> gvs[] >>

    gvs[extract_bv_from_key_def] >>
    simp[LIST_EQ_REWRITE] >>
    
    ‘LENGTH (convert_interval_to_sinterval_rows (LENGTH q) tbl_intvl) =
     LENGTH tbl_intvl’ by rw[convert_interval_to_sinterval_rows_def] >>
    gvs[] >>
    
    rpt strip_tac >>
    gvs[EL_MAP] >>
    
    Cases_on ‘EL x (convert_interval_to_sinterval_rows (LENGTH q) tbl_intvl)’ >> Cases_on ‘r’ >>
    Cases_on ‘EL x tbl_intvl’ >> Cases_on ‘r’ >>
    
    rename1 ‘EL x (convert_interval_to_sinterval_rows (LENGTH q) tbl_intvl) = (sinterval,s_in_sintvl,res_sintvl)’ >>
    rename1 ‘EL x tbl_intvl = (interval_list,s_in_intvl,res_intvl)’ >>
    gvs[] >>
    
    
    gvs[convert_interval_to_sinterval_rows_def] >>
    Cases_on ‘tbl_intvl = []’ >> gvs[] >>
    gvs[EL_MAP] >>
    
    Cases_on ‘interval_list = []’ >> gvs[] >-
     gvs[check_sinterval_rows_sem_def, is_interval_match_row_def] >>
    
    gvs[check_sinterval_rows_sem_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>

    gvs[wf_interval_table_def] >>
    imp_res_tac every_flat_then_every_mem >>
    
    gvs[extract_bv_from_key_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
    
    gvs [is_sinterval_match_row_def, is_interval_match_row_def] >|[
        
        strip_tac >>
        assume_tac intersection_of_intervals_lists_none_empty_not_match >>
        first_x_assum (strip_assume_tac o (Q.SPECL [‘interval_list’, ‘((q:bool list), LENGTH q)’, ‘LENGTH (q:bool list)’,
                                                    ‘packet_input’, ‘(st_in:num)’, ‘(s_in_intvl:num)’])) >>
        gvs[is_interval_match_row_def]
           
        ,
        strip_tac >>
        assume_tac intersection_of_intervals_lists_none_empty_not_match >>
        first_x_assum (strip_assume_tac o (Q.SPECL [‘interval_list’, ‘((q:bool list), LENGTH q)’, ‘LENGTH (q:bool list)’,
                                                    ‘packet_input’, ‘(st_in:num)’, ‘(s_in_intvl:num)’])) >>
        gvs[is_interval_match_row_def]
        ,
        
        gvs [is_sinterval_match_row_def, is_interval_match_row_def] >>
        assume_tac intersection_eval_row_interval_sinterval_correct_full >>
        
        first_x_assum (strip_assume_tac o (Q.SPECL [‘interval_list’, ‘((q:bool list), LENGTH q)’, ‘LENGTH (q:bool list)’,
                                                    ‘packet_input’, ‘p’, ‘p0’])) >>
        
        gvs[]
      ]      
  ]
QED






Theorem match_sinterval_table_correct:
  ∀ interval_table sinterval_table packet_input packet_type st_in.
    wf_packet packet_type packet_input ∧
    (convert_interval_to_sinterval_table interval_table packet_type  = SOME sinterval_table) ⇒
    ( match_sinterval_table sinterval_table packet_input st_in=
      match_interval_table interval_table packet_input st_in)
Proof
  rw[match_sinterval_table_def, match_interval_table_def] >>
  ‘check_sinterval_table_sem st_in sinterval_table packet_input =
   check_interval_table_sem st_in interval_table packet_input’ by metis_tac[check_sinterval_table_sem_table_correct] >>
  gvs[]
QED





(*======================================================*)
(*    now we merge the last three steps in one stage    *)
(*    from variables to arith table                     *)
(*    then from arith to many intervals table           *)
(*    then from intervals to single sinterval table     *)
(*======================================================*)



Definition convert_var_to_sinterval_table_def:
  convert_var_to_sinterval_table var_table me pd_type=
  (case convert_var_to_arith_table var_table me of
   | SOME arith_table =>
       ( case convert_arith_to_interval_table arith_table pd_type of
         | SOME interval_table =>  convert_interval_to_sinterval_table interval_table pd_type 
         | NONE => NONE
       )
   | NONE => NONE)
End





(*


val test_pd = ``[("ttl", type_length 5);
                 ("src", type_length 5)]``;
                 
val test_me = ``[("x1", arithm_ge (lv_x "ttl") (fixwidth 5 (n2v 0), 5));
                ("x2",  arithm_le (lv_x "ttl") (fixwidth 5 (n2v 10), 5))]``;


val test_var_table = ``[
  ([True; Var "x1"; Var "x2"], 1n, action "fwd1");
  ([Var "x1"; Not "x2"], 1n, action "fwd2");
  ([Var "x2"; Not "x2"], 1n, action "fwd3");
  ([True], 1n, action "drop")
]``;

                        
val test_final_table = 
  EVAL ``convert_var_to_sinterval_table ^test_var_table ^test_me ^test_pd``;



val test_var_table2 = ``[
  ([True; True], 1n, action "fwd1");
  ([False], 1n, action "fwd2");
  ([Var "x2"; Not "x2"], 1n, action "fwd3");
  ([True], 1n, action "drop")
]``;

                   
val test_final_table2 = 
  EVAL ``convert_var_to_sinterval_table ^test_var_table2 ^test_me ^test_pd``;





  
val test_var_table3 = ``[
  ([True; True], 1n, action "fwd1");
  ([False], 1n, action "fwd2");
  ([True], 1n, action "fwd3");
  ([True], 1n, action "drop")
]``;

                   
val test_final_table3 = 
  EVAL ``convert_var_to_sinterval_table ^test_var_table2 ^test_me ^test_pd``;

*)
     


        
Definition convert_var_to_sinterval_tables_def:
  convert_var_to_sinterval_tables [] me pd_type= NONE ∧
  convert_var_to_sinterval_tables var_tables me pd_type=
  let converted_list = MAP (λvar_table. convert_var_to_sinterval_table var_table me pd_type) var_tables in
    if EVERY IS_SOME converted_list then
      SOME (MAP THE converted_list)
    else
      NONE
End



(* semantics of last stage's full tables chain of the three steps var-arith-intervals-sinterval*)


(* Process table list with state propagation *) 
Definition match_sinterval_tbll_def:
  match_sinterval_tbll [] packet_input st_in = NONE ∧
  match_sinterval_tbll [sinterval_table] packet_input st_in =
  ( case match_sinterval_table sinterval_table packet_input st_in of
    | SOME (action a) => SOME (action a)
    | _ => NONE       
  )∧
  match_sinterval_tbll (sinterval_table::tbls) packet_input st_in =
  ( case match_sinterval_table sinterval_table packet_input st_in of
    | SOME (state n) => match_sinterval_tbll tbls packet_input n
    | _ => NONE
  )
End

 
(* Top-level table semantics, return the starting state as well*)       
Definition sem_sinterval_tables_def:
  sem_sinterval_tables (sinterval_tbll,st_in) packet_input =
   match_sinterval_tbll sinterval_tbll packet_input st_in
End




(* final tables translation *)

Theorem correct_tables_from_var_to_sinterval_thm:
  ∀var_tables sinterval_tables st_in me packet_type.
    ∀ packet_input mv.
      
      (∀var. lookup_is_some mv var ⇔ lookup_is_some me var) ∧
      (∀var atom. 
         ALOOKUP me var = SOME atom ⇒ 
         ALOOKUP mv var = eval_arithm_atom packet_input atom) ∧
      wf_packet packet_type packet_input ∧
      convert_var_to_sinterval_tables var_tables me packet_type = SOME sinterval_tables ⇒
                                      
      ( sem_tables ((var_tables: 'a var_table_list),st_in) mv =
        sem_sinterval_tables ((sinterval_tables: 'a sintvl_table_list),st_in) packet_input )
Proof
  Induct_on ‘var_tables’ >>      
  rw[sem_tables_def, sem_sinterval_tables_def] >-
   gvs[convert_var_to_sinterval_tables_def] >>
  
  rgs[convert_var_to_sinterval_tables_def] >>
  Cases_on ‘convert_var_to_sinterval_table h me packet_type’ >> gvs[] >>
  rgs[Once convert_var_to_sinterval_table_def] >>
  rpt (BasicProvers.full_case_tac >> gvs[]) >>
  
  simp[match_tbll_def, match_sinterval_tbll_def] >>
  
  imp_res_tac table_var_arith_correct >>
  first_x_assum (strip_assume_tac o (Q.SPECL [‘st_in’])) >>
  
  imp_res_tac full_table_arith_interval_correct >>
  first_x_assum (strip_assume_tac o (Q.SPECL [‘st_in’])) >>
  
  imp_res_tac match_sinterval_table_correct >>
  first_x_assum (strip_assume_tac o (Q.SPECL [‘st_in’])) >>
  
  Cases_on ‘var_tables’   >| [ 
    simp[match_tbll_def, match_sinterval_tbll_def]
    ,
    
    simp[match_tbll_def, match_sinterval_tbll_def] >>
    rpt (BasicProvers.full_case_tac >> gvs[]) >>
    
    gvs[Once convert_var_to_sinterval_tables_def] >>
    res_tac >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘n’])) >>
    metis_tac[sem_tables_def, sem_sinterval_tables_def] 
  ]
QED




        





        
val _ = export_theory ();







