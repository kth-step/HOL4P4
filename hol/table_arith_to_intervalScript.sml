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
  match_interval_table st_in (interval_table:'a intvl_table) pd =
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
        
EVAL “match_interval_table (1:num)
      ^example_interval_table
      ^example_pd ”;

*)


        
(* questions:
   1. is this correct or is it way too strong∃
   2. should it be = instead of implication
   3. should this to be for all fields of packet or the fields that appear in the policy only?
 *)

Definition wf_packet_def:
  wf_packet packet_type packet_input =
  ∀ lval n.  resolve_lval_type packet_type lval = SOME (type_length n) ⇒
             ∃ bs. (resolve_lval packet_input lval = SOME (val_bs bs) ∧
                    wf_bit bs ∧ SND bs = n ∧ n > 0 ∧ n < 129)
End




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





fun w_is_less_than_max_fixwidth_thm len =
let
  val size_term = numSyntax.term_of_int len
  val word_ty = wordsSyntax.mk_int_word_type len
                            
    val a = mk_var("a", word_ty)
  
  val goal = 
    ``∀ a . ^a ≤₊ v2w (fixwidth ^size_term (n2v (max_from_type ^size_term ))) ``;
  
  val thm = prove(goal,
                 gvs[max_from_type_def] >>
                 EVAL_TAC >>
                 blastLib.FULL_BBLAST_TAC )
in
  thm
end;

val w_is_less_than_max_fixwidth_thms = List.tabulate(128, fn i => w_is_less_than_max_fixwidth_thm (i+1));
val w_is_less_than_max_fixwidth_all1 = LIST_CONJ w_is_less_than_max_fixwidth_thms;
val w_is_less_than_max_fixwidth_all1_thm = save_thm("w_is_less_than_max_fixwidth_all1_sizes", w_is_less_than_max_fixwidth_all1);





        
Theorem every_bs_is_less_than_max_fixwidth:
  ∀ bl len.
    len > 0 ∧ len < 129 ⇒
    bitv_binpred binop_le (bl,len) (fixwidth len (n2v (max_from_type len)),len) = SOME T
Proof
  rw[] >>
  RW.ONCE_RW_TAC [bitv_binpred_def] >>
  gvs[] >>
  rpt strip_tac >>
  RW.ONCE_RW_TAC [bitv_binpred_inner_def] >>
  
  rewrite_tac[get_word_binpred_def] >>
                                    
  rpt(
    BasicProvers.FULL_CASE_TAC >-
     (
     fs[] >>
     gvs[w_is_less_than_max_fixwidth_all1_thm]
     ) 
    ) >>
  
  intLib.COOPER_TAC
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

                                                                                                



Theorem sem_arith_var_atom_imp1:
  ∀ interval_atom arith_atom packet_type packet_input lval k_val n bool.
    wf_packet packet_type packet_input ∧
    extract_bv_from_key (key_val lval) packet_input = SOME k_val ∧
    resolve_lval_type packet_type lval = SOME (type_length n) ∧
    relevant_atom_key arith_atom lval ∧
    eval_interval_atom k_val packet_input interval_atom = SOME bool ∧
    arith_to_interval arith_atom n = SOME interval_atom ⇒
    eval_arithm_atom packet_input arith_atom = SOME bool 
Proof

  rw[] >>
  
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
  ] 
QED


        
Theorem sem_arith_var_atom_imp2:
  ∀ interval_atom arith_atom packet_type packet_input lval k_val n bool.
    wf_packet packet_type packet_input ∧
    extract_bv_from_key (key_val lval) packet_input = SOME k_val ∧
    resolve_lval_type packet_type lval = SOME (type_length n) ∧
    relevant_atom_key arith_atom lval ∧
    eval_arithm_atom packet_input arith_atom = SOME bool ∧
    arith_to_interval arith_atom n = SOME interval_atom ⇒
    eval_interval_atom k_val packet_input interval_atom = SOME bool
Proof

  rw[] >>
  
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
  ] 
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
  ‘relevant_atom_key (EL n' arith_guards) lval’ by gvs[] >- 
   metis_tac[sem_arith_var_atom_imp1] >>
  metis_tac[sem_arith_var_atom_imp2] 
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
    (match_interval_table st_in interval_table packet_input =
    match_arith_table st_in arith_table packet_input)
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


Definition bv_gt_than_def:
  bv_gt_than bv bv' =
  bitv_binpred binop_gt bv bv'
End


Definition bv_lt_than_def:
  bv_lt_than bv bv' =
  bitv_binpred binop_lt bv bv'
End

        

Definition intersect_interval_def:
  intersect_interval (SOME (Single bv1 bv2)) (SOME (Single bv3 bv4)) =                     
  (case (bv_ge_than bv1 bv3, bv_ge_than bv2 bv4) of
   | (SOME a1_gt_a2, SOME b1_gt_b2) =>
       (let lower = if a1_gt_a2 then bv1 else bv3 in
          let upper = if b1_gt_b2 then bv4 else bv2 in
            (case bv_gt_than lower upper of
             | SOME F => SOME (Single lower upper)
             | _ => NONE           
            )
       )
   | _ => NONE) ∧

  intersect_interval (SOME Empty) _ = NONE ∧                     
  intersect_interval _ (SOME Empty) = NONE ∧
  intersect_interval _ _ = NONE          
End

(*
EVAL 
  “intersect_interval (SOME (Single (n2v 0, 5) (n2v 0, 5))) 
   (SOME (Single (n2v 0, 5) (n2v 0, 5)))”; (*[0,0]*)

EVAL “intersect_interval (SOME (Single (n2v 0, 5) (n2v 2, 5))) 
                        (SOME (Single (n2v 1, 5) (n2v 3, 5)))”; (*[1,2]*)

EVAL “intersect_interval (SOME (Single (n2v 0, 5) (n2v 1, 5))) 
                        (SOME (Single (n2v 2, 5) (n2v 3, 5)))”; (*NONE*)                                               
        
EVAL “intersect_interval (SOME (Single (n2v 0, 5) (n2v 4, 5))) 
                        (SOME (Single (n2v 1, 5) (n2v 3, 5)))”; (*[1,3]*)

EVAL “intersect_interval (SOME Empty) (SOME (Single (n2v 0, 5) (n2v 1, 5)))”;
        
EVAL “intersect_interval (SOME (Single (n2v 0, 5) (n2v 2, 5))) 
                        (SOME (Single (n2v 2, 5) (n2v 4, 5)))”; (*[2,2]*)
*)

Definition intersect_list_def:
  (intersect_list [] interval_acc = interval_acc) ∧
  (intersect_list (interval_g::interval_gl) interval_acc =
   case intersect_interval (SOME interval_g) interval_acc of
   | NONE => NONE
   | SOME intvl => intersect_list interval_gl (SOME intvl) 
  )
End
        
(*
EVAL “intersect_list [] (SOME (Single (n2v 0, 5) (n2v 1, 5)))”; (*[0,1]*)

EVAL “intersect_list [Single (n2v 0, 5) (n2v 1, 5)] (SOME (Single (n2v 0, 5) (n2v 0, 5)))”;(*0,0*)

EVAL “intersect_list [Single (n2v 1, 5) (n2v 3, 5); Single (n2v 2, 5) (n2v 4, 5)] 
                    (SOME (Single (n2v 0, 5) (n2v 5, 5)))”; (*[2,3]*)


EVAL “intersect_list [Single (n2v 1, 5) (n2v 4, 5); Single (n2v 2, 5) (n2v 3, 5)] 
                    NONE”;

EVAL “intersect_list [Single (n2v 0, 5) (n2v 1, 5); Single (n2v 3, 5) (n2v 4, 5)] 
                    (SOME (Single (n2v 2, 5) (n2v 2, 5)))”; (*NONE*)

EVAL “intersect_list [Single (n2v 2, 5) (n2v 8, 5); Single (n2v 4, 5) (n2v 6, 5)] 
                    (SOME (Single (n2v 0, 5) (n2v 10, 5)))”; (*[4,6]*)


EVAL “intersect_interval (SOME (Single (n2v 3, 5) (n2v 1, 5))) 
                        (SOME (Single (n2v 0, 5) (n2v 2, 5)))”; (*NONE*)
*)




Definition convert_interval_to_sinterval_rows_def:
  convert_interval_to_sinterval_rows bit_len interval_rows =
  MAP (\(interval_guards, st, res).
          (intersect_list interval_guards (SOME (Single (mk_min_bv bit_len) (mk_max_bv bit_len))), st, res )
      ) interval_rows
End
          
     

Definition convert_interval_to_sinterval_table_def:
  convert_interval_to_sinterval_table interval_table pd_type =
  let (key, interval_rows) = interval_table in
    case key of
    | key_val lval =>
        ( case resolve_lval_type pd_type lval of
          | SOME (type_length bit_len) => SOME (key, convert_interval_to_sinterval_rows bit_len interval_rows)
          | _ => NONE 
        )
    | key_const (bl,n) => SOME (key, convert_interval_to_sinterval_rows n interval_rows)
End



(*
val example_pd =  
 “([("h", type_length 8)])”;


val example_interval_table1 =
 “(key_val (lv_x "h"),
        [([Single (n2v 0, 8) (n2v 255, 8);
           Single (n2v 1, 8) (n2v 255, 8);
           Single (n2v 0, 8) (n2v 3, 8)], 1, action "result1");
         ([Single (n2v 4, 8) (n2v 255, 8)], 1, action "result2"); 
         ([Empty], 1, action "result3");
         ([Single (n2v 0, 8) (n2v 255, 8)], 1, action "result4")]): string intvl_table”;

EVAL “convert_interval_to_sinterval_table ^example_interval_table1 ^example_pd”;

*)





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
         ( check_sinterval_rows_sem st_in st sinterval_guard bv pd , res))  sintvl_lines)
     | NONE => NONE
  )
End



Definition match_sinterval_table_def:
  match_sinterval_table st_in (sinterval_table:'a sintvl_table) pd =
  case check_sinterval_table_sem st_in sinterval_table pd of
    | SOME res =>
      (case min_idx_till res T of
        SOME (idx, line) => SOME (SND line)
       | NONE => NONE
      )
    | NONE => NONE
End





(*

wf_packet packet_type packet_input ∧
convert_interval_to_sinterval_table interval_table packet_type =
        SOME sinterval_table ⇒
check_sinterval_table_sem st_in sinterval_table packet_input =
        check_interval_table_sem st_in interval_table packet_input


rpt strip_tac >>
PairCases_on ‘sinterval_table’ >>
PairCases_on ‘interval_table’ >>                                
rename1 ‘convert_interval_to_sinterval_table (key_intvl,tbl_intvl) packet_type = SOME (skey_intvl,stbl_intvl)’ >>

gvs[convert_interval_to_sinterval_table_def] >>
rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >|[

(*key val*)
                                
gvs[check_sinterval_table_sem_def, check_interval_table_sem_def] >>
,
(* key const *)


  ]








                                       



        

 ∀ interval_table sinterval_table packet_input packet_type st_in.
    wf_packet packet_type packet_input ∧
    (convert_interval_to_sinterval_table interval_table packet_type  = SOME sinterval_table) ⇒
    ( match_sinterval_table st_in sinterval_table packet_input =
    match_interval_table st_in interval_table packet_input)
        

rw[match_sinterval_table_def, match_interval_table_def] >>
‘check_sinterval_table_sem st_in sinterval_table packet_input =
check_interval_table_sem st_in interval_table packet_input’ by cheat
gvs[]


*)
        







        



                                                                

val _ = export_theory ();







