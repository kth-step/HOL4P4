open HolKernel boolLib simpLib Parse bossLib;

open pairTheory;
open listTheory;
open rich_listTheory;
open alistTheory;
open arithmeticTheory;

open p4_auxTheory;

open bdd_genTheory;     
open tables_spec_oldTheory;
open policy_specTheory;     


val _ = new_theory "tables_spec";


(* A description of the tables ILR and its functions instansiations *)    

Definition is_not_true_var_atom_def:
  (is_not_true_var_atom True = F) ∧
  (is_not_true_var_atom _ = T)
End



Definition simp_row_def:
  simp_row atoml =
  if atoml = [] then [] else
  let simp_row = MAP (\atom. simp_atom atom) atoml in
    let simp_row' = FILTER (\x. is_not_true_var_atom x) simp_row in
      case simp_row' of
      | [] => [True]
      | _ => 
          (case MEM False simp_row' of
           | T => [False]
           | F => simp_row')
End





(*
here we work with none, and some.
these represent the state of the previous table.

If the previous table is final, it menas it has only one line and one state as a result.
this state as a reult represent the answer of the previous table, that we will use to match on the current table.

If is it SOME (st_num), then we have the ability to reduce the current table so much, otherwise,
if NONE, then we do not know the previous table what it could return yet,
thus we reduce but not as much when evaluating it EVAL. 
   
*)


        
Definition simp_table_def:
  (simp_table [] s = []) ∧
                  
  (simp_table ((atoms,st,res)::table)  NONE =
   let atoms' = simp_row atoms in
     case atoms' of
     | [False] => simp_table table NONE
     | _ =>  ((atoms', st, res)::simp_table table NONE)
  ) ∧
    
  (simp_table ((atoms,st,res)::table) (SOME s') =
   if (s' ≠ st) then
     simp_table table (SOME s')
   else
     (
     let atoms' = simp_row atoms in
       case atoms' of
       | [False] => simp_table table (SOME s')
       | [True] => [(atoms', st, res)]
       | _ =>  ((atoms', st, res) :: (simp_table table (SOME s')))
     )
  )
End



(* simplify table by table in the tables list. if the table is final i.e.
   one row only and containng true, then we know what is the state to match on
   the next table in the list, else we just casually reduce *)

Definition simp_tables_def:
  (simp_tables [] s = []) ∧
  (simp_tables (t::tbll) s = 
   (let t' = simp_table t s in
      ( case t' of
        | [([True], st , state s'')] => (t'::(simp_tables tbll (SOME s'')))
        | _ => (t'::(simp_tables tbll NONE))
      )
   )
  )
End



Definition simp_tables_wrapper_def:
  simp_tables_wrapper ((tbll: 'a var_table_list), st_in) =
   (simp_tables tbll (SOME st_in), st_in)
End



Definition final_row_def:
  (final_row ([],_,_) s = NONE) ∧
  (final_row ([True], s', s'') s = (if s = s' then SOME s'' else NONE)) ∧
  (final_row _ s = NONE)
End
        



Definition final_tbl_def:
  (final_tbl [] s = NONE) ∧
  (final_tbl (row::rows) s =         
     case final_row row s of
       SOME a => SOME a
     | NONE => if (FST row = [False]) then final_tbl rows s else NONE
  )
End



Definition final_tbll_def:
  final_tbll ([]: 'a var_table_list) st_in = NONE ∧
  final_tbll [tbl] st_in =
  ( case final_tbl tbl st_in of
    | SOME (action a) => SOME (action a)
    | _ => NONE       
  )∧
  final_tbll (tbl::tbls) st_in =
  ( case final_tbl tbl st_in of
    | SOME (state n) => final_tbll tbls n
    | _ => NONE
  )
End



Definition final_tables_def:
  final_tables (tbll, st_in) =
  final_tbll tbll st_in
End



Definition table_structure_def:
  table_structure =
  <|
    sem := sem_tables;
    sub := mk_substitute_tables;
    simp := simp_tables_wrapper;
    final := final_tables;
    fv := fv_tables;
  |>
End            



Triviality simp_row_not_empty:
  ∀ atoms.
    simp_row atoms = [] ⇔ atoms = []
Proof
  rw[simp_row_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) 
QED



Theorem simp_row_sub_false_head:
  ∀ atoms_list x b.
    (simp_row (mk_substitute_row (True::atoms_list) x b) = [False] ⇒
     simp_row (mk_substitute_row (atoms_list) x b) = [False]) ∧
    (simp_row (mk_substitute_row (NotFalse::atoms_list) x b) = [False] ⇒
     simp_row (mk_substitute_row (atoms_list) x b) = [False])
    
Proof
  Induct >>
  rw[mk_substitute_row_def, simp_row_def] >>
  gvs[mk_substitute_atom_def, simp_atom_def, is_not_true_var_atom_def]
QED



Theorem simp_row_sub_false_var_head:
  ∀ atoms_list mv x s b.
    (ALOOKUP mv s = SOME T ∧
    ALOOKUP mv x = SOME b ∧
    simp_row (mk_substitute_row (Var s::atoms_list) x b) = [False] ⇒
     simp_row (mk_substitute_row atoms_list x b) = [False]) ∧

    (ALOOKUP mv s = SOME F ∧
     ALOOKUP mv x = SOME b ∧
     simp_row (mk_substitute_row (Not s::atoms_list) x b) = [False] ⇒
     simp_row (mk_substitute_row atoms_list x b) = [False]) 
Proof
  Induct >>
  rw[mk_substitute_row_def, simp_row_def] >>
  gvs[mk_substitute_atom_def, simp_atom_def, is_not_true_var_atom_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[mk_substitute_atom_def, simp_atom_def, is_not_true_var_atom_def]
QED





Theorem simp_sub_row_false_then_atoms_sem_false:
  ∀ atoms_list x b mv.
    ALOOKUP mv x = SOME b ∧
    simp_row (mk_substitute_row atoms_list x b) = [False] ⇒
    ~ is_atoml_true atoms_list mv
Proof
  
  Induct >-
   rw[mk_substitute_row_def, simp_row_def, is_atoml_true_def] >>
  
  rw[] >>
  Cases_on ‘h’ >>
  
  (imp_res_tac simp_row_sub_false_head >>
   res_tac >>
   gvs[is_atoml_true_def] >>
   gvs[sem_var_atom_def]) >>
  
  strip_tac >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  imp_res_tac simp_row_sub_false_var_head  >>
  gvs[]
QED
    

        

Theorem simp_sub_empty_then_min_index_none:
  ∀ t x b s_in mv.
    ALOOKUP mv x = SOME b ∧
    simp_table (mk_substitute_tbl t x b) (SOME s_in) = [] ⇒
    min_idx_till (check_all_rows_match s_in t mv) T = NONE
Proof

  Induct >> rw[] >|[
    rw[mk_substitute_tbl_def, simp_table_def] >>
    gvs[check_all_rows_match_def, min_idx_till_def, INDEX_FIND_def]
    ,
    
    PairCases_on ‘h’ >>
    rename1 ‘((atoms_list,st,res)::t)’ >>
    gvs[Once mk_substitute_tbl_normalize2] >>
    gvs[check_all_rows_match_def, is_match_row_def] >>
    rgs[simp_table_def] >>
    
    
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
        
    (res_tac >>
     rgs[min_idx_till_def] >>
     gvs[INDEX_FIND_NONE_EXISTS]) >>
    
    imp_res_tac simp_sub_row_false_then_atoms_sem_false >>
    fs[]          
  ]
QED



        

Triviality mk_substitute_row_empty:
  ∀ atoms_list x b.
    mk_substitute_row atoms_list x b = [] ⇒
    atoms_list = []
Proof
  Induct >> gvs[mk_substitute_row_def]
QED




Triviality simp_table_mk_substitute_tbl_empty1:
  ∀ t h x b s_in.
    simp_table (mk_substitute_tbl (h::t) x b) (SOME s_in) = [] ⇒
    simp_table (mk_substitute_tbl t x b) (SOME s_in) = []
Proof
  rw[mk_substitute_tbl_def, simp_table_def] >>
  PairCases_on ‘h’ >>
  gvs[simp_table_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) 
QED



        
Theorem simp_table_sub_every_prop1:
  ∀ t x b  s_in mv.
    ALOOKUP mv x = SOME b ∧
    simp_table (mk_substitute_tbl t x b) (SOME s_in) = [] ⇒
    EVERY ($¬ ∘ (λ(p,a). p)) (MAP
                              (λ(atoml,st_num,res'). (s_in = st_num ∧ is_atoml_true atoml mv ∧ atoml ≠ [],res')) t)
Proof
  
  Induct >>
  rw[] >|[
    PairCases_on ‘h’ >> gvs[] >>
    rpt strip_tac >>
    Cases_on ‘h0’ >> gvs[mk_substitute_tbl_def, simp_table_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
    imp_res_tac simp_sub_row_false_then_atoms_sem_false
    ,
    imp_res_tac simp_table_mk_substitute_tbl_empty1 >>
    res_tac >>
    gvs[]
  ]
QED 
        
               
               
        
Theorem simp_sub_empty_then_min_index_tbl_none:
∀ t x b s_in mv s_num res.
  ALOOKUP mv x = SOME b ∧
  simp_table (mk_substitute_tbl t x b) (SOME s_in) = [([],s_num,res)] ⇒
  min_idx_till (check_all_rows_match s_in t mv) T = NONE
Proof

  Induct >> rw[] >|[
    gvs[check_all_rows_match_def, min_idx_till_def, INDEX_FIND_def]
    ,
    
    PairCases_on ‘h’ >>
    rename1 ‘((atoms_list,st,result)::t)’ >>
    gvs[Once mk_substitute_tbl_normalize2] >>
    gvs[check_all_rows_match_def, is_match_row_def] >>
    rgs[simp_table_def] >>
    
    
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
        
    (res_tac >>
     rgs[min_idx_till_def] >>
     gvs[INDEX_FIND_NONE_EXISTS]) >>
    
    imp_res_tac simp_sub_row_false_then_atoms_sem_false >>
    fs[] >>


    imp_res_tac simp_row_not_empty >> gvs[] >>
    imp_res_tac mk_substitute_row_empty >> gvs[] >>        
    imp_res_tac simp_table_sub_every_prop1
  ]
QED


                             
Theorem match_tbll_head_empty:
  ∀ tbll mv s_in.
    match_tbll ([]::tbll) mv s_in = NONE
Proof
  rw[] >> Cases_on ‘tbll’ >> 
  gvs[match_tbll_def, match_tbl_def, check_all_rows_match_def, min_idx_till_def, INDEX_FIND_def]
QED




Theorem match_tbll_row_empty:
  ∀ tbll st res mv s_in.
    match_tbll ([([],st,res)]::tbll) mv s_in = NONE
Proof
 rw[] >> Cases_on ‘tbll’ >> 
 gvs[match_tbll_def, match_tbl_def, check_all_rows_match_def, min_idx_till_def, INDEX_FIND_def, is_match_row_def]
QED




Theorem match_tbll_final_before_ending_none:
  ∀ tbll st mv s_in a.
    tbll ≠ [] ⇒
    match_tbll ([([True],st,action a)]::tbll) mv s_in = NONE
Proof
  rw[] >> Cases_on ‘tbll’ >> 
  gvs[match_tbll_def, match_tbl_def, check_all_rows_match_def, min_idx_till_def,
      INDEX_FIND_def, is_match_row_def, is_atoml_true_def, sem_var_atom_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[])
QED


        
Triviality simp_tables_sub_not_empty_table:
 ∀ t x b l.
  simp_tables (mk_substitute_tbl t x b::l) NONE ≠ []
Proof
  rw[simp_tables_def, mk_substitute_tbl_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[])
QED



Triviality simp_table_impossible_case1:
  ∀ atoml h s_in t t' st_num res st_num' res'.
    simp_table [(atoml, st_num, res)] (SOME s_in) ≠ [(True::t::t',st_num',res')]
Proof
  Induct_on ‘atoml’ >> 
  gvs[simp_table_def] >> rpt strip_tac >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[simp_row_def]) >>
  rw[] >>
  gvs[is_not_true_var_atom_def]
QED   



Theorem filtering_not_true_then_not_mem:
  ∀ atoml filtered_list.
    FILTER (λx. is_not_true_var_atom x) (MAP (λatom. simp_atom atom) atoml) = filtered_list ⇒
    ¬ MEM True filtered_list ∧ ¬ MEM NotTrue filtered_list ∧ ¬ MEM NotFalse filtered_list
Proof
  Induct >>
  rw[is_not_true_var_atom_def] >>
  Cases_on ‘h’ >>
  gvs[simp_atom_def, is_not_true_var_atom_def]
QED

                   

Theorem filtering_not_true_then_notTrue_notFalse_mem:
  ∀ atoml filtered_list x b.
    FILTER (λx. is_not_true_var_atom x) (MAP (λatom. simp_atom atom) (mk_substitute_row atoml x b)) =
    filtered_list ⇒
    (¬ MEM NotTrue filtered_list ∧ ¬ MEM NotFalse filtered_list) 
Proof
  Induct_on ‘atoml’ >>
  rw[mk_substitute_row_def, simp_atom_def, is_not_true_var_atom_def] >>
  (
    Cases_on ‘h’ >> gvs[mk_substitute_atom_def, simp_atom_def, is_not_true_var_atom_def] >>
    gvs[mk_substitute_row_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[simp_atom_def])
  )
QED



Theorem simp_table_impossible_case2:
  ∀ l t t' s_in st_num res.        
    (simp_table l (SOME s_in) ≠ [(True::t::t',st_num,res)]) ∧
    (simp_table l (SOME s_in) ≠ [(False::t',st_num,res)])
Proof                 
  Induct_on ‘l’ >>
  rw[] >>
  gvs[simp_table_def] >>
  Cases_on ‘l’ >>
  PairCases_on ‘h’ >>
  gvs[simp_table_impossible_case1] >>
  gvs[simp_table_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[simp_row_def]) >>
  rw[] >>
  gvs[is_not_true_var_atom_def] >>
  imp_res_tac filtering_not_true_then_not_mem >>
  gvs[]
QED



Theorem simp_table_impossible_case3:
∀ l t t' s_in st_num res mv x b.
  (simp_table (mk_substitute_tbl t x b) (SOME s_in) ≠ [(NotTrue::t',st_num,res)]) ∧
  (simp_table (mk_substitute_tbl t x b) (SOME s_in) ≠ [(NotFalse::t',st_num,res)])                 
Proof
  Induct_on ‘t’ >>
  rw[] >>
  gvs[simp_table_def, mk_substitute_tbl_def] >>
  PairCases_on ‘h’ >>
  gvs[simp_table_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[simp_row_def]) >>
  rw[] >>
  imp_res_tac filtering_not_true_then_not_mem >>
  gvs[] >>
  res_tac >>
  gvs[] >>
  imp_res_tac filtering_not_true_then_notTrue_notFalse_mem >> gvs[]
QED


    
Theorem simp_table_return_true_then_rows_none:
  ∀ tbl rows h1 h2.
    simp_table tbl NONE = [(True::rows,h1,h2)] ⇒
    rows = []
Proof
  
  Induct >>
  rw[simp_table_def] >>
  
  Cases_on ‘tbl’ >> PairCases_on ‘h’ >> gvs[simp_table_def]  >>       
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[simp_row_def]) >>
  imp_res_tac filtering_not_true_then_not_mem >>
  gvs[]
QED          




Triviality length_of_simp_single_table:
 ∀rows anyop.
   LENGTH (simp_tables [rows] anyop) ≤ 1
Proof
Induct >> rw[simp_tables_def] >>
rpt (BasicProvers.FULL_CASE_TAC >> gvs[simp_row_def]) 
QED



Triviality simp_tables_single_not_empty:
∀ rows anyop.
simp_tables [rows] anyop ≠ []
Proof
  rw[simp_tables_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[simp_row_def]) 
QED
                                                


Triviality simp_table_none_append:
  ∀ rows h.
    simp_table (h::rows) NONE = (simp_table [h] NONE)++(simp_table rows NONE)
Proof
  rw[] >> PairCases_on ‘h’ >>
  rw[simp_table_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[simp_row_def]) 
QED




Theorem min_idx_till_none_eq_res:
  ∀ l1 l2 res.
    min_idx_till l1 T = min_idx_till l2 T ⇒
    (min_idx_till ((F,res)::l1) T = NONE) = (min_idx_till l2 T = NONE)
Proof

  rw[min_idx_till_def] >>
  gvs[INDEX_FIND_def] >>
  Cases_on ‘INDEX_FIND 0 (λ(p,a). p) l1’ >> 
  gvs[P_NONE_hold] >>
                   
  Cases_on ‘INDEX_FIND 0 (λ(p,a). p) l2’ >> gvs[] >>
  Cases_on ‘INDEX_FIND 1 (λ(p,a). p) l1’ >> gvs[] >>
  imp_res_tac P_NONE_hold2 >>
  gvs[]
QED



Theorem min_idx_till_some_eq_res:     
  ∀ l1 l2 res.
    min_idx_till l1 T = min_idx_till l2 T ⇒
    ∃ n m res' . (min_idx_till ((F,res)::l1) T = SOME (n,res')) =
                 (min_idx_till            l2 T = SOME (m,res'))
Proof

  rw[min_idx_till_def] >>
  gvs[INDEX_FIND_def] >>
  Cases_on ‘INDEX_FIND 0 (λ(p,a). p) l1’ >> gvs[] >>
  
  gvs[P_NONE_hold] >>
  
  Cases_on ‘INDEX_FIND 0 (λ(p,a). p) l2’ >> gvs[] >>
  Cases_on ‘INDEX_FIND 1 (λ(p,a). p) l1’ >> gvs[] >>
  imp_res_tac P_NONE_hold2 >>
  gvs[] >>
  
  Cases_on ‘x’ >> Cases_on ‘x'’ >>
  imp_res_tac P_implies_next >>
  gvs[] >>
  qexistsl_tac [‘SUC q’, ‘q’, ‘r’] >>
  gvs[] 
QED



Theorem INDEX_FIND_some_eq_next: 
  ∀ l1 res n.
  INDEX_FIND 0 (λ(p,a). p) l1 = SOME (n,res) ⇔ INDEX_FIND 1 (λ(p,a). p) l1 = SOME (n + 1,res)
Proof
  rw[] >>
  Cases_on ‘INDEX_FIND 0 (λ(p,a). p) l1’ >>
  gvs[P_NONE_hold] >>
  
  Cases_on ‘x’ >> gvs[] >>
  imp_res_tac P_implies_next >>
  gvs[ADD1]
QED


        
Theorem min_idx_till_some_eq_next: 
  ∀ l1 res res' n.
  (min_idx_till l1 T = SOME (n,res)) ⇔  (min_idx_till ((F,res')::l1) T = SOME (n+1,res))
Proof
  rw[min_idx_till_def, INDEX_FIND_def] >>
  gvs[INDEX_FIND_some_eq_next]
QED




Theorem INDEX_FIND_some_eq_next2: 
  ∀ l1 res n.
  (INDEX_FIND 0 (λ(p,a). p) l1 = SOME (n -1,res) ∧ n>0) ⇔ INDEX_FIND 1 (λ(p,a). p) l1 = SOME (n,res)
Proof
  rw[] >>
  Cases_on ‘INDEX_FIND 0 (λ(p,a). p) l1’ >>
  gvs[P_NONE_hold] >>
  
  Cases_on ‘x’ >> gvs[] >>
  imp_res_tac P_implies_next >>
  gvs[ADD1] >>
  
  Cases_on ‘n’ >> gvs[ADD1]   
QED

    

        
Theorem min_idx_till_some_eq_next2: 
  ∀ l1 res res' n.
  (min_idx_till l1 T = SOME (n-1,res) ∧ n>0) ⇔ (min_idx_till ((F,res')::l1) T = SOME (n,res))
Proof
  rw[min_idx_till_def, INDEX_FIND_def] >>
  gvs[INDEX_FIND_some_eq_next] >>
  Cases_on ‘INDEX_FIND 1 (λ(p,a). p) l1’ >> gvs[] >>
  Cases_on ‘x’ >> gvs[] >>
  imp_res_tac INDEX_FIND_some_eq_next2 >>
   Cases_on ‘n’ >> gvs[ADD1] 
QED

    

Triviality simp_row_false_emptyl:
  ∀ atoml t.        
    simp_row atoml = False::t ⇒
    simp_row atoml = [False]
Proof
  rw[simp_row_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) 
QED


      
Theorem min_idx_check_rows_simp_tbl_none:
  ∀ rows st_in simp_rows simp_rows' mv.
    simp_table rows NONE = simp_rows ∧
    simp_table rows (SOME st_in) = simp_rows' ⇒
    (min_idx_till (check_all_rows_match st_in simp_rows mv) T = NONE) =
    (min_idx_till (check_all_rows_match st_in simp_rows' mv) T = NONE)
Proof

  Induct_on ‘rows’ >>
  rpt strip_tac >-
   rgs[simp_table_def] >>
  
  PairCases_on ‘h’ >>
  rename1 ‘simp_table ((atoms,st,res)::rows) (SOME st_in)’ >>
  rgs[simp_table_def] >>
  Cases_on ‘simp_row atoms’ >> gvs[] >|[
    Cases_on ‘st_in ≠ st’ >>
    gvs[] >|[
      gvs[check_all_rows_match_def] >>
      simp[Once is_match_row_def] >>
      metis_tac[min_idx_till_none_eq_res]
      ,
      gvs[check_all_rows_match_def] >>
      gvs[is_match_row_def, min_idx_till_def] >>
      gvs[INDEX_FIND_def, index_none_not_every]
    ]
    ,

    Cases_on ‘st_in ≠ st’ >>
    gvs[] >|[
        Cases_on ‘h’ >> gvs[] >>
        (
        imp_res_tac simp_row_false_emptyl >>
        gvs[] >>
        gvs[check_all_rows_match_def] >>
        simp[Once is_match_row_def] >>
        metis_tac[min_idx_till_none_eq_res]
        )
        
        ,
        (* when st is the same as st_in*)
        Cases_on ‘t’ >> gvs[] >|[
            rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
            (gvs[check_all_rows_match_def, is_match_row_def, is_atoml_true_def, sem_var_atom_def] >>
             gvs[min_idx_till_def, INDEX_FIND_def, index_none_not_every])
            ,
            Cases_on ‘h’ >> gvs[] >>
            (gvs[check_all_rows_match_def, is_match_row_def, is_atoml_true_def, sem_var_atom_def] >>
             gvs[min_idx_till_def, INDEX_FIND_def, index_none_not_every]) 
          ]                         
      ]
  ]
QED






(* TODO: refactor this proof *)         
Theorem min_idx_check_rows_simp_tbl_some:
  ∀ rows st_in simp_rows simp_rows' mv.
    simp_table rows NONE = simp_rows ∧
    simp_table rows (SOME st_in) = simp_rows' ⇒
    ∃ m n res. (min_idx_till (check_all_rows_match st_in simp_rows mv) T = SOME (n, res)) =
               (min_idx_till (check_all_rows_match st_in simp_rows' mv) T = SOME (m, res))
Proof

  Induct_on ‘rows’ >>
  rpt strip_tac >-
   rgs[simp_table_def, check_all_rows_match_def, min_idx_till_def, INDEX_FIND_def] >>
  
  PairCases_on ‘h’ >>
  rename1 ‘simp_table ((atoms,st,res)::rows) (SOME st_in)’ >>
  rgs[simp_table_def] >>
  Cases_on ‘simp_row atoms’ >> gvs[] >|[
           
    Cases_on ‘st_in ≠ st’ >>
    gvs[] >|[
      gvs[check_all_rows_match_def] >>
      simp[Once is_match_row_def] >>
                
      first_x_assum (strip_assume_tac o (Q.SPECL [‘st_in’, ‘mv’])) >>
      qexistsl_tac [‘m’, ‘n+1’, ‘res'’] >>      
      gvs[GSYM min_idx_till_some_eq_next]

      ,
      gvs[check_all_rows_match_def] >>
      gvs[is_match_row_def] >>
                            
      first_x_assum (strip_assume_tac o (Q.SPECL [‘st’, ‘mv’])) >>
      qexistsl_tac [‘m+1’, ‘n+1’, ‘res'’] >>      
      gvs[GSYM min_idx_till_some_eq_next] 
      
    ]
    ,

    Cases_on ‘st_in ≠ st’ >>
    gvs[] >|[
        Cases_on ‘h’ >> gvs[] >>
        (
        imp_res_tac simp_row_false_emptyl >>
        gvs[] >>
        
        
        gvs[check_all_rows_match_def] >>
        simp[Once is_match_row_def] >>
        
        first_x_assum (strip_assume_tac o (Q.SPECL [‘st_in’, ‘mv’])) >>
        qexistsl_tac [‘m’, ‘n+1’, ‘res'’] >> 
        gvs[GSYM min_idx_till_some_eq_next]
        )
        
        ,
        (* when st is the same as st_in*)
        Cases_on ‘t’ >> gvs[] >|[
            rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
            (gvs[check_all_rows_match_def, is_match_row_def, is_atoml_true_def, sem_var_atom_def] >>
             gvs[min_idx_till_def, INDEX_FIND_def, index_none_not_every]) >|[

              qexistsl_tac [‘0’, ‘0’, ‘(T,res)’] >> 
              gvs[]
              ,

              first_x_assum (strip_assume_tac o (Q.SPECL [‘st’, ‘mv’])) >>
              qexistsl_tac [‘m+1’, ‘n+1’, ‘res’] >>      
              gvs[GSYM INDEX_FIND_some_eq_next] 
              ,
              qexistsl_tac [‘0’, ‘0’, ‘(T,res)’] >> 
              gvs[]
              ,
              BasicProvers.FULL_CASE_TAC >> gvs[] >|[
                  qexistsl_tac [‘0’, ‘0’, ‘(T,res)’] >> 
                  gvs[]
                  ,
                  
                  first_x_assum (strip_assume_tac o (Q.SPECL [‘st’, ‘mv’])) >>
                  qexistsl_tac [‘m+1’, ‘n+1’, ‘res’] >>      
                  gvs[GSYM INDEX_FIND_some_eq_next] 

                ]
              ,
              rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >|[
                  first_x_assum (strip_assume_tac o (Q.SPECL [‘st’, ‘mv’])) >>
                  qexistsl_tac [‘m+1’, ‘n+1’, ‘res’] >>      
                  gvs[GSYM INDEX_FIND_some_eq_next] 
                  ,
                  qexistsl_tac [‘0’, ‘0’, ‘(T,res)’] >> 
                  gvs[]
                  ,
                  first_x_assum (strip_assume_tac o (Q.SPECL [‘st’, ‘mv’])) >>
                  qexistsl_tac [‘m+1’, ‘n+1’, ‘res’] >>      
                  gvs[GSYM INDEX_FIND_some_eq_next] 
                ]
            ]
            ,
            Cases_on ‘h’ >> gvs[] >>
            (gvs[check_all_rows_match_def, is_match_row_def, is_atoml_true_def, sem_var_atom_def] >>
             gvs[min_idx_till_def, INDEX_FIND_def, index_none_not_every]) >|[

                rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >|[
                  qexistsl_tac [‘0’, ‘0’, ‘(T,res)’] >> 
                  gvs[]
                  ,
                  first_x_assum (strip_assume_tac o (Q.SPECL [‘st’, ‘mv’])) >>
                  qexistsl_tac [‘m+1’, ‘n+1’, ‘res’] >>      
                  gvs[GSYM INDEX_FIND_some_eq_next] 
                ]
                ,
                
                first_x_assum (strip_assume_tac o (Q.SPECL [‘st’, ‘mv’])) >>
                qexistsl_tac [‘m+1’, ‘n+1’, ‘res’] >>      
                gvs[GSYM INDEX_FIND_some_eq_next] 
                ,
                
                first_x_assum (strip_assume_tac o (Q.SPECL [‘st’, ‘mv’])) >>
                qexistsl_tac [‘m+1’, ‘n+1’, ‘res’] >>      
                gvs[GSYM INDEX_FIND_some_eq_next] 
                ,
                
                rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >|[
                  qexistsl_tac [‘0’, ‘0’, ‘(T,res)’] >> 
                  gvs[]
                  ,
                  first_x_assum (strip_assume_tac o (Q.SPECL [‘st’, ‘mv’])) >>
                  qexistsl_tac [‘m+1’, ‘n+1’, ‘res’] >>      
                  gvs[GSYM INDEX_FIND_some_eq_next] 
                  ]
                ,
                 rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >|[
                  qexistsl_tac [‘0’, ‘0’, ‘(T,res)’] >> 
                  gvs[]
                  ,
                  first_x_assum (strip_assume_tac o (Q.SPECL [‘st’, ‘mv’])) >>
                  qexistsl_tac [‘m+1’, ‘n+1’, ‘res’] >>      
                  gvs[GSYM INDEX_FIND_some_eq_next] 
                  ]
                ,
                rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >|[
                    
                    first_x_assum (strip_assume_tac o (Q.SPECL [‘st’, ‘mv’])) >>
                    qexistsl_tac [‘m+1’, ‘n+1’, ‘res’] >>      
                    gvs[GSYM INDEX_FIND_some_eq_next]
                    ,
                    qexistsl_tac [‘0’, ‘0’, ‘(T,res)’] >> 
                    gvs[]
                    ,
                    first_x_assum (strip_assume_tac o (Q.SPECL [‘st’, ‘mv’])) >>
                    qexistsl_tac [‘m+1’, ‘n+1’, ‘res’] >>      
                    gvs[GSYM INDEX_FIND_some_eq_next]
                  ]

              ]
          ]                         
      ]
  ]
QED






Theorem  min_idx_till_none_not_none:      
  ∀ l .        
    (min_idx_till l T = NONE) ⇔
      ¬ (min_idx_till l T ≠ NONE)
Proof
  gvs[min_idx_till_def]
QED

Triviality a_not_a:
∀ l . min_idx_till l T = NONE ∧ min_idx_till l T ≠ NONE ⇒ F
Proof
  gvs[min_idx_till_def]
QED



Triviality simp_table_none_empty_some_empty:
  ∀ rows n.
    simp_table rows NONE = [] ⇒
    simp_table rows (SOME n) = []
Proof
  Induct >>
  rw[simp_table_def] >>
  PairCases_on ‘h’ >>
  gvs[simp_table_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[simp_row_def]) 
QED


        
Triviality simp_table_none_true_cases:
  ∀ rows n st res.
    (simp_table rows NONE = [([True],st,res)] ⇒
    (simp_table rows (SOME n) = [([True],st,res)] ∨
     simp_table rows (SOME n) = []
    )) ∧

    ( ∀ s . simp_table rows NONE = [([Var s],st,res)] ⇒
     (simp_table rows (SOME n) = [([Var s],st,res)] ∨
      simp_table rows (SOME n) = []                              
     )) ∧

    ( ∀ s l. simp_table rows NONE = [(Var s::l,st,res)] ⇒
     (simp_table rows (SOME n) = [(Var s::l,st,res)] ∨
      simp_table rows (SOME n) = []                              
     )) ∧

    ( ∀ s . simp_table rows NONE = [([Not s],st,res)] ⇒
     (simp_table rows (SOME n) = [([Not s],st,res)] ∨
      simp_table rows (SOME n) = []                              
     )) ∧

    ( ∀ s l. simp_table rows NONE = [(Not s::l,st,res)] ⇒
     (simp_table rows (SOME n) = [(Not s::l,st,res)] ∨
      simp_table rows (SOME n) = []                              
     )) ∧

    ( ∀ a l. simp_table rows NONE = [(a::l,st,res)] ⇒
     (simp_table rows (SOME n) = [(a::l,st,res)] ∨
      simp_table rows (SOME n) = []                              
     )) ∧

    ( ∀ a l. simp_table rows NONE = [([],st,res)] ⇒
     (simp_table rows (SOME n) = [([],st,res)] ∨
      simp_table rows (SOME n) = []                              
     )) 
Proof
  Induct >>
  rw[simp_table_def] >>
  PairCases_on ‘h’ >>
  gvs[simp_table_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[simp_row_def]) >>
  
  imp_res_tac simp_table_none_empty_some_empty >>
  imp_res_tac filtering_not_true_then_not_mem >>
  gvs[]
QED



        
Triviality simp_table_true_cases1:
∀ rows n atoml st1 st2 res1 res2.
simp_table rows NONE = [(True::atoml,st1,res1)] ∧
simp_table rows (SOME n) = [([True],st2,res2)] ⇒
(st1=st2 ∧ st2=n ∧ res1=res2)
Proof

  Induct >>
  rw[simp_table_def] >>
  PairCases_on ‘h’ >>
  gvs[simp_table_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  
  imp_res_tac simp_table_none_empty_some_empty >>
  imp_res_tac filtering_not_true_then_not_mem >>
  gvs[] >>
  res_tac
QED




Triviality simp_row_cannot_result1:
  ∀ atoml a l.
    simp_row atoml ≠ [NotFalse] ∧
    simp_row atoml ≠ [NotTrue] ∧
    simp_row atoml ≠ False::a::l ∧
    simp_row atoml ≠ True::a::l ∧
    simp_row atoml ≠ NotFalse::a::l ∧
    simp_row atoml ≠ NotTrue::a::l

Proof
  Induct >>
  rw[simp_row_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  Cases_on ‘h’ >> gvs[simp_atom_def, is_not_true_var_atom_def] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac filtering_not_true_then_not_mem >> gvs[]
QED


        

Theorem simp_table_cannot_result1:
  ∀ rows st res.
    (simp_table rows NONE ≠ [([NotFalse],st,res)]) ∧
    (simp_table rows NONE ≠ [([NotTrue],st,res)]) ∧
    (simp_table rows NONE ≠ [([False],st,res)]) ∧
                    
    (∀ a l.(simp_table rows NONE ≠ [(False::a::l,st,res)])) ∧
    (∀ a l.(simp_table rows NONE ≠ [(True::a::l,st,res)])) ∧
    (∀ a l.(simp_table rows NONE ≠ [(NotTrue::a::l,st,res)])) ∧
    (∀ a l.(simp_table rows NONE ≠ [(NotFalse::a::l,st,res)]))
Proof
  
  Induct >>
  rw[simp_table_def] >>
  PairCases_on ‘h’ >>
  gvs[simp_table_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  rpt strip_tac >>
  gvs[simp_row_cannot_result1] 
QED   
               





Theorem min_idx_check_rows_simp_tbl_some2:
  ∀ rows st_in mv simp_rows simp_rows' m n r r'.
    simp_table rows NONE = simp_rows ∧
    simp_table rows (SOME st_in) = simp_rows' ⇒
    (min_idx_till (check_all_rows_match st_in simp_rows mv) T = SOME (n, r)) ∧
    (min_idx_till (check_all_rows_match st_in simp_rows' mv) T = SOME (m, r')) ⇒
    r=r'
Proof

  Induct_on ‘rows’ >>
  rpt strip_tac >-
   rgs[simp_table_def, check_all_rows_match_def, min_idx_till_def, INDEX_FIND_def] >>
  
  
  PairCases_on ‘h’ >>
  rename1 ‘simp_table ((atoms,st,res)::rows) (SOME st_in)’ >>
  rgs[simp_table_def] >>
  Cases_on ‘simp_row atoms’ >> gvs[] >-
   (
   imp_res_tac simp_row_not_empty >>
   gvs[] >>
   Cases_on ‘st_in ≠ st’ >>
   gvs[check_all_rows_match_def] >>
   gvs[GSYM INDEX_FIND_some_eq_next2] >>
   res_tac >>
   gvs[is_match_row_def] >>

   gvs[GSYM min_idx_till_some_eq_next2] >>
   res_tac 
   ) >>
        
  Cases_on ‘st_in ≠ st’ >>
  gvs[] >|[
        Cases_on ‘h’ >> gvs[] >>
        gvs[check_all_rows_match_def] >>
        gvs[is_match_row_def] >>

        gvs[GSYM min_idx_till_some_eq_next2] >>
        res_tac >>

        Cases_on ‘t’ >> gvs[simp_row_cannot_result1]
        ,

        Cases_on ‘h’ >> Cases_on ‘t’ >>  gvs[simp_row_cannot_result1] >>

        (gvs[check_all_rows_match_def, is_match_row_def, is_atoml_true_def, sem_var_atom_def] >>
         gvs[min_idx_till_def, INDEX_FIND_def, index_none_not_every]) >>
         
        rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
        gvs[GSYM min_idx_till_some_eq_next2] >>
        res_tac >>


                
        gvs[INDEX_FIND_some_eq_next] >>
        Cases_on ‘n’ >> Cases_on ‘m’ >> gvs[index_find_not_prev, ADD1] >>
        res_tac 
]
                               
QED


               
          
        
        
Theorem simp_tables_single_match_eq:
  ∀ rows n tbl tbl' mv.
    simp_tables [rows] NONE = [tbl] ∧
    simp_tables [rows] (SOME n) = [tbl'] ⇒
    match_tbl tbl mv n = match_tbl tbl' mv n
Proof

  rw[simp_tables_def, match_tbl_def] >>
  Cases_on ‘simp_table rows NONE’ >> 
  Cases_on ‘simp_table rows (SOME n)’ >> 
  gvs[] >>
  
  imp_res_tac min_idx_check_rows_simp_tbl_none >>
  imp_res_tac min_idx_check_rows_simp_tbl_some >>
  gvs[] >>
  
  (first_x_assum (strip_assume_tac o (Q.SPECL [‘mv’])) >>
   first_x_assum (strip_assume_tac o (Q.SPECL [‘mv’]))) >| [
    
    imp_res_tac simp_table_none_empty_some_empty >> gvs[]
    ,
    
    Cases_on ‘t’ >> PairCases_on ‘h’ >> gvs[] >>
    Cases_on ‘h0’ >> gvs[] >>
    
    (rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>     
     gvs[check_all_rows_match_def, min_idx_till_def, is_match_row_def] >>
     gvs[INDEX_FIND_def])
    
    ,
    
    Cases_on ‘t’ >> PairCases_on ‘h’ >> gvs[] >>
    Cases_on ‘h0’ >> gvs[] >|[
        
        Cases_on ‘t'’ >> PairCases_on ‘h'’ >> gvs[] >>
        (rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>     
         gvs[check_all_rows_match_def, min_idx_till_def, is_match_row_def] >>
         gvs[INDEX_FIND_def])
        ,
        
        Cases_on ‘h’ >> Cases_on ‘t’ >> gvs[] >>
        gvs[simp_table_cannot_result1]  >>
        (
        TRY(Cases_on ‘h2’) >> gvs[] >>
        imp_res_tac simp_table_none_true_cases >> gvs[] >>
        first_x_assum (strip_assume_tac o (Q.SPECL [‘n’])) >>
        gvs[])
        
        ,                
        Cases_on ‘t'’ >> PairCases_on ‘h'’ >> gvs[] >|[
            Cases_on ‘h'0’ >> gvs[] >|[
              
              (rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>     
               gvs[check_all_rows_match_def, min_idx_till_def, is_match_row_def] >>
               gvs[INDEX_FIND_def])
              ,
              
              rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
              gvs[is_atoml_true_def, sem_var_atom_def] >>                     
              
              imp_res_tac min_idx_check_rows_simp_tbl_some2 >>
              res_tac >> gvs[] >>
              res_tac >> gvs[] 
                            
            ]
            ,
            rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
            gvs[is_atoml_true_def, sem_var_atom_def] >>                     
            
            imp_res_tac min_idx_check_rows_simp_tbl_some2 >>
            res_tac >> gvs[] 
          ]
        ,
        Cases_on ‘t'’ >> PairCases_on ‘h'’ >> gvs[] >|[
            Cases_on ‘h'0’ >> gvs[] >|[
              
              (rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>     
               gvs[check_all_rows_match_def, min_idx_till_def, is_match_row_def] >>
               gvs[INDEX_FIND_def])
              ,
              
              rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
              gvs[is_atoml_true_def, sem_var_atom_def] >>                     
              
              imp_res_tac min_idx_check_rows_simp_tbl_some2 >>
              res_tac >> gvs[] >>
              res_tac >> gvs[] 
                            
            ]
            ,
            rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
            gvs[is_atoml_true_def, sem_var_atom_def] >>                     
            
            imp_res_tac min_idx_check_rows_simp_tbl_some2 >>
            res_tac >> gvs[] 
          ]
      ]
  ]
QED
              


                                                
Theorem match_tbll_single_some_none_eq:
  ∀rows mv n.
    match_tbll (simp_tables [rows] NONE) mv n =
    match_tbll (simp_tables [rows] (SOME n)) mv n
Proof
  
  rw[] >>
  assume_tac length_of_simp_single_table >>
  first_assum (strip_assume_tac o (Q.SPECL [‘rows’, ‘NONE’])) >>
  first_x_assum (strip_assume_tac o (Q.SPECL [‘rows’, ‘SOME n’])) >>
 
  Cases_on ‘simp_tables [rows] NONE’ >> gvs[] >>
  Cases_on ‘simp_tables [rows] (SOME n)’ >> gvs[] >>
  
  gvs[simp_tables_single_not_empty] >>
  Cases_on ‘t’ >> gvs[] >>
  Cases_on ‘t'’ >> gvs[] >>
  
  gvs[match_tbll_def] >>
  imp_res_tac simp_tables_single_match_eq >>
  metis_tac[]
QED




Triviality simp_tables_res_empty_length:
  ∀ tbll sop.
    simp_tables tbll sop = [] ⇒
    tbll = []
Proof
  Cases_on ‘sop’ >>
  Induct >> rw[simp_tables_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) 
QED

        
Triviality simp_tables_res_single_length:
  ∀ tbll tbl n sop.
    simp_tables tbll sop = [tbl] ⇒
    LENGTH tbll = 1
Proof
  Induct >> rw[simp_tables_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  imp_res_tac simp_tables_res_empty_length
QED



(*
new definition for simp_tables 
so that the proofs are easier to deal with
*)


Definition next_state_def:
  next_state t' = case t' of
                  | [([True], s, state s'')] => SOME s''
                  | _ => NONE
End


Definition simp_tables2_def:
  (simp_tables2 [] s = []) ∧
  (simp_tables2 (t::tbll) s = 
   let t' = simp_table t s in
   t' :: simp_tables2 tbll (next_state t')
  )
End


Theorem simp_tables_eq:
  ∀ l s.
    simp_tables l s = simp_tables2 l s
Proof 
  Induct >>
  rw[simp_tables2_def, simp_tables_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>     
  
  Cases_on ‘s’ >> gvs[next_state_def]
QED


Theorem next_state_rel_to_final_match_res:
  ∀ tbl n n' n'' mv.
    match_tbl tbl mv n = SOME (state n') ∧
    next_state tbl = SOME n'' ⇒
    n' = n''
Proof
  rw[next_state_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> rgs[]) >>
  gvs[match_tbl_def, check_all_rows_match_def, is_match_row_def,
      is_atoml_true_def, min_idx_till_def, sem_var_atom_def, INDEX_FIND_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> rgs[]) 
QED



Theorem simp_table_eq_none_some:
  ∀ tbl t_s t_n mv n.
    simp_table tbl (SOME n) = t_s ∧
    simp_table tbl NONE = t_n ⇒
    match_tbl t_n mv n = match_tbl t_s mv n
Proof

  rw[match_tbl_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> rgs[])  >>
  
  ‘∃ l . simp_table tbl NONE = l’ by gvs[] >>
  ‘∃ l' . simp_table tbl (SOME n) = l'’ by gvs[] >|[
    
    imp_res_tac min_idx_check_rows_simp_tbl_none >>
    gvs[]
    ,
    imp_res_tac min_idx_check_rows_simp_tbl_none >>
    gvs[] >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘mv’])) >>
    gvs[]
    ,
    imp_res_tac min_idx_check_rows_simp_tbl_some2 >>
    gvs[] >>
    
    first_x_assum (strip_assume_tac o (Q.SPECL [‘r'’, ‘mv’, ‘q'’])) >>
    gvs[]
  ]
QED


        
        
Theorem match_tbll_simp_tables_eq_thm:
  ∀tbll mv n.
    match_tbll (simp_tables tbll NONE) mv n =
    match_tbll (simp_tables tbll (SOME n)) mv n
Proof
  
Induct_on ‘tbll’ >> rw[] >|[
    gvs[simp_tables_def]
    ,
    Cases_on ‘tbll’ >> gvs[] >|[
        gvs[match_tbll_single_some_none_eq]
        ,
        Cases_on ‘simp_tables (h::h'::t) (SOME n)’ >>
        Cases_on ‘simp_tables (h::h'::t) NONE’ >>  
        imp_res_tac simp_tables_res_empty_length >> gvs[] >>
                    
        Cases_on ‘t'’ >>
        Cases_on ‘t''’ >>  
        imp_res_tac simp_tables_res_single_length >> gvs[] >> 

        rename1 ‘match_tbll (t1_n::t2_n::t3_n) mv n = match_tbll (t1_s::t2_s::t3_s) mv n’ >>
                    

        gvs[simp_tables_eq] >>
        
        (Q.PAT_X_ASSUM ‘simp_tables2 (h::h'::t) (SOME n) = t1_s::t2_s::t3_s’
          (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once simp_tables2_def] thm))) >>
        
        
        
        (Q.PAT_X_ASSUM ‘simp_tables2 (h::h'::t) NONE = t1_n::t2_n::t3_n’
          (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once simp_tables2_def] thm))) >>
        
        rgs[] >>
        
        simp[match_tbll_def] >>
        ‘match_tbl t1_n mv n = match_tbl t1_s mv n’ by (imp_res_tac simp_table_eq_none_some >>
                                                        first_x_assum (strip_assume_tac o (Q.SPECL [‘mv’]))
                                                       ) >>
        
        
        Cases_on ‘match_tbl t1_s mv n’ >> rgs[] >>
        Cases_on ‘x’ >> rgs[] >>
                
        Cases_on ‘next_state t1_s’ >>
        Cases_on ‘next_state t1_n’ >>
        rgs[] >>
        
        imp_res_tac next_state_rel_to_final_match_res >> gvs[]
      ]
  ]
QED
   


(* to do : same as simp_table_cannot_result1 merge them *)
Theorem simp_table_cannot_result2:
  ∀ rows st res n.
    (simp_table rows (SOME n) ≠ [([NotFalse],st,res)]) ∧
    (simp_table rows (SOME n) ≠ [([NotTrue],st,res)]) ∧
    (simp_table rows (SOME n) ≠ [([False],st,res)]) ∧
                    
    (∀ a l.(simp_table rows (SOME n) ≠ [(False::a::l,st,res)])) ∧
    (∀ a l.(simp_table rows (SOME n) ≠ [(True::a::l,st,res)])) ∧
    (∀ a l.(simp_table rows (SOME n) ≠ [(NotTrue::a::l,st,res)])) ∧
    (∀ a l.(simp_table rows (SOME n) ≠ [(NotFalse::a::l,st,res)])) 
Proof
  
  Induct >>
  rw[simp_table_def] >>
  PairCases_on ‘h’ >>
  gvs[simp_table_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  rpt strip_tac >>
  gvs[simp_row_cannot_result1] 
QED





        
Theorem sem_var_atom_sub_same:
  ∀ atom mv x b b'.
    ALOOKUP mv x = SOME b  ⇒
    (sem_var_atom atom mv = SOME b' ⇔
    sem_var_atom (mk_substitute_atom atom x b) mv = SOME b')
Proof
  Cases >>
  rw[sem_var_atom_def, mk_substitute_atom_def] >>
  Cases_on ‘b'’ >> gvs[]
QED


Theorem sem_var_atoml_sub_same_imp1:
  ∀ atoml mv x b.        
    ALOOKUP mv x = SOME b ∧
    EVERY (λminipred. sem_var_atom minipred mv = SOME T) atoml ⇒
    EVERY (λminipred. sem_var_atom minipred mv = SOME T)
          (MAP (λatom. mk_substitute_atom atom x b) atoml)
Proof
  Induct >>
  rw[] >>
  imp_res_tac sem_var_atom_sub_same
QED


Theorem sem_var_atoml_sub_same_imp2:
  ∀ atoml mv x b.        
    ALOOKUP mv x = SOME b ∧
    EVERY (λminipred. sem_var_atom minipred mv = SOME T)
          (MAP (λatom. mk_substitute_atom atom x b) atoml) ⇒
    EVERY (λminipred. sem_var_atom minipred mv = SOME T) atoml
Proof
  Induct >>
  rw[] >>
  imp_res_tac sem_var_atom_sub_same >>
  res_tac
QED


        
        
Theorem is_match_row_mk_sub_eq:
  ∀ atoml st s_in mv x b.
    ALOOKUP mv x = SOME b ⇒
    (is_match_row s_in st atoml mv ⇔ is_match_row s_in st (mk_substitute_row atoml x b) mv)
Proof
  Induct >>
  rw[is_match_row_def] >>
  gvs[mk_substitute_row_def, is_atoml_true_def] >>
  
  EQ_TAC >> rw[] >>
  
  imp_res_tac sem_var_atom_sub_same >> gvs[] >>
  imp_res_tac sem_var_atoml_sub_same_imp1 >> gvs[] >>
  imp_res_tac sem_var_atoml_sub_same_imp2 >> gvs[]
QED


    
Theorem check_all_rows_match_sub_eq:
  ∀ tbl x b mv s_in.
    ALOOKUP mv x = SOME b ⇒
    (check_all_rows_match s_in tbl mv = check_all_rows_match s_in (mk_substitute_tbl tbl x b) mv)
Proof
  Induct >>
  rw[check_all_rows_match_def] >-
   gvs[mk_substitute_tbl_def] >>
  
  PairCases_on ‘h’ >>
  gvs[check_all_rows_match_def] >>
  
  res_tac >>
  first_x_assum (strip_assume_tac o (Q.SPECL [‘s_in’])) >>
  gvs[] >>
  
  gvs[mk_substitute_tbl_def] >>
  assume_tac (INST_TYPE [“:'a ”|-> “:num”  ] is_match_row_mk_sub_eq)  >>
  metis_tac[]
QED                           



Triviality simp_row_single_true_rel:
  ∀ atoms h.
    simp_row (h::atoms) = [True] ⇒
    (simp_row atoms = [True] ∨ atoms = [])
Proof
  rw[simp_row_def] >>
  gvs[] 
QED
      


Triviality simp_row_single_false_rel:
  ∀ t h mv.
    sem_var_atom h mv = SOME T ∧
    simp_row (h::t) = [False] ⇒
    simp_row (t) = [False]
Proof
  rw[simp_row_def] >>
  gvs[is_not_true_var_atom_def]  >>
  
  Cases_on ‘h’ >> gvs[simp_row_def, sem_var_atom_def, simp_atom_def, is_not_true_var_atom_def] >>  
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[])
QED        


           
Theorem simp_row_true_imp_atoml_true:
  ∀ atoms mv.
    atoms ≠ [] ∧
    simp_row atoms = [True] ⇒
    (is_atoml_true atoms mv)
Proof
  Induct >>
  rw[is_atoml_true_def] >|[
    
    (* for head *)
    rgs[Once simp_row_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>

    gvs[is_not_true_var_atom_def] >>
    Cases_on ‘h’ >> gvs[simp_atom_def, is_not_true_var_atom_def, is_atoml_true_def, sem_var_atom_def]
    ,
        
    (* for list *)
    imp_res_tac simp_row_single_true_rel >>
    res_tac >> gvs[] >>
    
    Cases_on ‘atoms’ >>
    imp_res_tac simp_row_not_empty >> gvs[] >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘mv’])) >>
    gvs[is_atoml_true_def]
  ]
QED





                                          
        
Theorem simp_row_false_imp_atoml_false:
  ∀ atoms mv.
    simp_row atoms = [False] ⇒
    ~ (is_atoml_true atoms mv)
Proof
  Induct >>
  rw[is_atoml_true_def] >-
   rgs[simp_row_def] >>
  
  
  Cases_on ‘atoms’ >>
  imp_res_tac simp_row_not_empty >> gvs[] >>
  first_x_assum (strip_assume_tac o (Q.SPECL [‘mv’])) >>
  gvs[is_atoml_true_def] >|[
    Cases_on ‘h’ >> gvs[simp_row_def, sem_var_atom_def, simp_atom_def, is_not_true_var_atom_def]    
    ,
    imp_res_tac simp_row_single_false_rel >>
    res_tac
  ]
QED


Triviality filter_simp_empty_then_all_true:
  ∀ atoms mv.
    atoms ≠ [] ∧
    FILTER (λx. is_not_true_var_atom x) (MAP (λatom. simp_atom atom) atoms) = [] ⇒
    EVERY (λminipred. sem_var_atom minipred mv = SOME T) atoms
Proof
  Induct >>
  rw[] >>
  Cases_on ‘h’ >> gvs[sem_var_atom_def, simp_atom_def, is_not_true_var_atom_def] >>    
  Cases_on ‘atoms’ >> gvs[]
QED
                                          
        
        
Theorem simp_row_var_imp_atoml_true:
  ∀ atoms mv s.
    simp_row atoms = [Var s] ⇒
    (is_atoml_true atoms mv ⇔ is_atoml_true [Var s] mv)
Proof
  Induct >>
  rw[is_atoml_true_def] >-
   gvs[simp_row_def] >>
  
  Cases_on ‘h’ >> gvs[simp_row_def, sem_var_atom_def, simp_atom_def, is_not_true_var_atom_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[is_atoml_true_def, sem_var_atom_def] >>
  imp_res_tac filter_simp_empty_then_all_true >>
  gvs[]
QED




Theorem simp_row_not_imp_atoml_true:
  ∀ atoms mv s.
    simp_row atoms = [Not s] ⇒
    (is_atoml_true atoms mv ⇔ is_atoml_true [Not s] mv)
Proof
  Induct >>
  rw[is_atoml_true_def] >-
   gvs[simp_row_def] >>
  
  Cases_on ‘h’ >> gvs[simp_row_def, sem_var_atom_def, simp_atom_def, is_not_true_var_atom_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[is_atoml_true_def, sem_var_atom_def] >>

  imp_res_tac filter_simp_empty_then_all_true >>
  gvs[] >>
                         
  first_x_assum (strip_assume_tac o (Q.SPECL [‘mv’])) >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[])
QED




Theorem simp_row_list_imp_atoml_true:
  ∀ atoms l mv.
    simp_row atoms = l ⇒
    is_atoml_true atoms mv = is_atoml_true l mv
Proof
  Induct >>
  rw[is_atoml_true_def] >-
   gvs[simp_row_def] >>
  
  Cases_on ‘h’ >> gvs[simp_row_def, sem_var_atom_def, simp_atom_def, is_not_true_var_atom_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[is_atoml_true_def, sem_var_atom_def]
QED


                                          
Theorem min_idx_till_simp_eq_none:
  ∀ l s_in mv.
    min_idx_till (check_all_rows_match s_in l mv) T = NONE ⇔
      min_idx_till (check_all_rows_match s_in (simp_table l (SOME s_in)) mv) T = NONE
Proof
  
  Induct >>
  rw[]  >-
   gvs[simp_table_def] >>
  
  PairCases_on ‘h’ >>         
  rename1 ‘((atoms,st,res)::rows)’ >>
  
  gvs[simp_table_def] >>
  Cases_on ‘s_in ≠ st’ >> gvs[] >|[
    gvs[check_all_rows_match_def, is_match_row_def] >>
    metis_tac[min_idx_till_none_eq_res]
    ,
    Cases_on ‘simp_row atoms’ >-
     (
     imp_res_tac simp_row_not_empty >> gvs[] >>
     gvs[check_all_rows_match_def, is_match_row_def] >>
     metis_tac[min_idx_till_none_eq_res]
     ) >>
    
    
    Cases_on ‘t’ >> gvs[] >| [
        Cases_on ‘h’ >> gvs[simp_row_cannot_result1] >| [
          
          (* true case *)
          gvs[check_all_rows_match_def] >>
          gvs[is_match_row_def] >>
          Cases_on ‘atoms = []’ >-
           gvs[simp_row_def] >>
          imp_res_tac simp_row_true_imp_atoml_true >>
          first_x_assum (strip_assume_tac o (Q.SPECL [‘mv’])) >>
          gvs[min_idx_till_def, is_atoml_true_def, INDEX_FIND_def, sem_var_atom_def]
          ,
          (* false *)
          imp_res_tac simp_row_false_imp_atoml_false >>
          first_x_assum (strip_assume_tac o (Q.SPECL [‘mv’])) >>
          gvs[check_all_rows_match_def] >>
          gvs[is_match_row_def] >>
          metis_tac[min_idx_till_none_eq_res]
          ,
          (* var case *)
          gvs[check_all_rows_match_def, is_match_row_def] >>
          Cases_on ‘atoms = []’ >-
           gvs[simp_row_def] >>
          gvs[] >>
          imp_res_tac simp_row_var_imp_atoml_true >>
          gvs[] >>
          Cases_on ‘is_atoml_true [Var s] mv’ >> gvs[] >|[
              gvs[min_idx_till_def, is_atoml_true_def, INDEX_FIND_def, sem_var_atom_def]
              ,
              metis_tac[min_idx_till_none_eq_res]
            ]
          ,
          (* case not *)
          gvs[check_all_rows_match_def, is_match_row_def] >>
          Cases_on ‘atoms = []’ >-
           gvs[simp_row_def] >>
          gvs[] >>
          imp_res_tac simp_row_not_imp_atoml_true >>
          gvs[] >> 
          Cases_on ‘is_atoml_true [Not s] mv’ >> gvs[] >|[
              gvs[min_idx_till_def, is_atoml_true_def, INDEX_FIND_def, sem_var_atom_def]
              ,
              metis_tac[min_idx_till_none_eq_res]
            ]               
        ]
        ,
        gvs[check_all_rows_match_def, is_match_row_def] >>
        imp_res_tac simp_row_list_imp_atoml_true >>
        gvs[] >>

        Cases_on ‘atoms = []’ >-
         gvs[simp_row_def] >>
        gvs[] >>
              
        Cases_on ‘is_atoml_true (h::h'::t') mv’ >> gvs[] >|[
            gvs[min_idx_till_def, is_atoml_true_def, INDEX_FIND_def, sem_var_atom_def]
            ,
            metis_tac[min_idx_till_none_eq_res]
          ]                                                    
      ]      
  ]                    
QED

        


    
Theorem min_idx_till_simp_sub_eq_none:
  ∀ t t' mv x b s_in.
    ALOOKUP mv x = SOME b ∧
    simp_table (mk_substitute_tbl t x b) (SOME s_in) = t' ⇒
    (min_idx_till (check_all_rows_match s_in t mv) T = NONE ⇔
       min_idx_till (check_all_rows_match s_in t' mv) T = NONE )
Proof
  rw[] >>
  ‘check_all_rows_match s_in t mv = check_all_rows_match s_in (mk_substitute_tbl t x b) mv’
    by gvs[check_all_rows_match_sub_eq] >>
  gvs[] >>
  metis_tac[min_idx_till_simp_eq_none]
QED




(* to do : same proof as none, merge them *)
Theorem min_idx_till_simp_eq_some:
  ∀l s_in mv r r' idx idx'.
    min_idx_till (check_all_rows_match s_in l mv) T = SOME (idx,r) ∧
    min_idx_till (check_all_rows_match s_in (simp_table l (SOME s_in)) mv) T = SOME (idx',r')       ⇒
    r = r'
Proof
  Induct >>
  rw[]  >-
   gvs[simp_table_def] >>
  
  PairCases_on ‘h’ >>         
  rename1 ‘((atoms,st,res)::rows)’ >>
  
  gvs[simp_table_def] >>
  Cases_on ‘s_in ≠ st’ >> gvs[] >|[
    gvs[check_all_rows_match_def, is_match_row_def] >>
    gvs[GSYM min_idx_till_some_eq_next2] >>
    res_tac
    ,
    Cases_on ‘simp_row atoms’ >-
     (
     imp_res_tac simp_row_not_empty >> gvs[] >>
     gvs[check_all_rows_match_def, is_match_row_def] >>
     gvs[GSYM min_idx_till_some_eq_next2] >>
     res_tac
     ) >>
   
    Cases_on ‘t’ >> gvs[] >| [
        Cases_on ‘h’ >> gvs[simp_row_cannot_result1] >| [
          
          (* true case *)
          gvs[check_all_rows_match_def] >>
          gvs[is_match_row_def] >>
          Cases_on ‘atoms = []’ >-
           gvs[simp_row_def] >>
          imp_res_tac simp_row_true_imp_atoml_true >>
          first_x_assum (strip_assume_tac o (Q.SPECL [‘mv’])) >>
          gvs[min_idx_till_def, is_atoml_true_def, INDEX_FIND_def, sem_var_atom_def]
          ,
          (* false *)
          imp_res_tac simp_row_false_imp_atoml_false >>
          first_x_assum (strip_assume_tac o (Q.SPECL [‘mv’])) >>
          gvs[check_all_rows_match_def] >>
          gvs[is_match_row_def] >>
          gvs[GSYM min_idx_till_some_eq_next2] >>
          res_tac
          ,
          (* var case *)
          gvs[check_all_rows_match_def, is_match_row_def] >>
          Cases_on ‘atoms = []’ >-
           gvs[simp_row_def] >>
          gvs[] >>
          imp_res_tac simp_row_var_imp_atoml_true >>
          gvs[] >>
          Cases_on ‘is_atoml_true [Var s] mv’ >> gvs[] >|[
              gvs[min_idx_till_def, is_atoml_true_def, INDEX_FIND_def, sem_var_atom_def]
              ,
              gvs[GSYM min_idx_till_some_eq_next2] >>
              res_tac
            ]
          ,
          (* case not *)
          gvs[check_all_rows_match_def, is_match_row_def] >>
          Cases_on ‘atoms = []’ >-
           gvs[simp_row_def] >>
          gvs[] >>
          imp_res_tac simp_row_not_imp_atoml_true >>
          gvs[] >> 
          Cases_on ‘is_atoml_true [Not s] mv’ >> gvs[] >|[
              gvs[min_idx_till_def, is_atoml_true_def, INDEX_FIND_def, sem_var_atom_def]
              ,
               gvs[GSYM min_idx_till_some_eq_next2] >>
              res_tac
            ]               
        ]
        ,
        gvs[check_all_rows_match_def, is_match_row_def] >>
        imp_res_tac simp_row_list_imp_atoml_true >>
        gvs[] >>

        Cases_on ‘atoms = []’ >-
         gvs[simp_row_def] >>
        gvs[] >>
              
        Cases_on ‘is_atoml_true (h::h'::t') mv’ >> gvs[] >|[
            gvs[min_idx_till_def, is_atoml_true_def, INDEX_FIND_def, sem_var_atom_def]
            ,
             gvs[GSYM min_idx_till_some_eq_next2] >>
              res_tac
          ]                                                    
      ]   
  ]
QED


        
Theorem min_idx_till_simp_sub_eq_some:
  ∀ t t' mv x b s_in idx idx' res res'.
    ALOOKUP mv x = SOME b ∧
    simp_table (mk_substitute_tbl t x b) (SOME s_in) = t' ∧
    min_idx_till (check_all_rows_match s_in t mv) T = SOME (idx, res) ∧
    min_idx_till (check_all_rows_match s_in t' mv) T = SOME (idx', res') ⇒
    res = res'
Proof
  rw[] >>
  ‘check_all_rows_match s_in t mv = check_all_rows_match s_in (mk_substitute_tbl t x b) mv’
    by gvs[check_all_rows_match_sub_eq] >>
  gvs[] >>
  metis_tac[min_idx_till_simp_eq_some]
QED

      
      

    
Theorem prop1_mini_subcases:
  ∀ t l s_in  x b mv.
    ALOOKUP mv x = SOME b ∧
    simp_table (mk_substitute_tbl t x b) (SOME s_in) = l ⇒
    match_tbl t mv s_in = match_tbl l mv s_in
Proof
  rw[match_tbl_def] >>
  
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  ‘∃l. (simp_table (mk_substitute_tbl t x b) (SOME s_in)) = l’ by gvs[] >>
  rgs[] >|[
    
    imp_res_tac min_idx_till_simp_sub_eq_none >> gvs[]
    ,
    imp_res_tac min_idx_till_simp_sub_eq_none >> gvs[] 
    ,
    PairCases_on ‘r’ >> PairCases_on ‘r'’ >> gvs[] >>
    imp_res_tac min_idx_till_simp_sub_eq_some >> gvs[]
  ]
QED



        
Triviality simp_table_final_case:
  ∀ rows n st res.
    simp_table rows (SOME n) = [([True],st,res)] ⇒
    (n=st)
Proof

  Induct >>
  rw[simp_table_def] >>
  PairCases_on ‘h’ >>
  gvs[simp_table_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[])
QED


Triviality match_tbl_simple_final_case:
  ∀ h1 st s_in n n' mv.
    match_tbl [([True],st,state n)] mv s_in = SOME (state n') ⇒
    (s_in = st ∧ n = n')
Proof
  rw[match_tbl_def, check_all_rows_match_def, is_match_row_def,
       is_atoml_true_def, sem_var_atom_def, min_idx_till_def, INDEX_FIND_def] >>
   rpt (BasicProvers.FULL_CASE_TAC >> gvs[])
QED
        



Theorem prop1_tables_verbose:
  ∀ tbll mv h b s_in.
    ALOOKUP mv h = SOME b
    ⇒
    sem_tables (simp_tables (MAP (λt. mk_substitute_tbl t h b) tbll) (SOME s_in),s_in) mv =
    sem_tables (tbll,s_in) mv
Proof
 Induct >> rw[] >-
   (
   gvs[simp_tables_def, match_tbll_def]
   ) >>
  

  
   (* we need to be able to cut the tables list into something manageble for the proof*)
   rename1 ‘mk_substitute_tbl t x b’ >>

   simp[simp_tables_def] >>
   Cases_on ‘simp_table (mk_substitute_tbl t x b) (SOME s_in)’ >> gvs[] >|[

    (*case when the whole first table is empty *)
    gvs[sem_tables_def, match_tbll_head_empty] >>
    Cases_on ‘tbll’ >> gvs[] >>
    
    simp[match_tbll_def, match_tbl_def] >>
    imp_res_tac simp_sub_empty_then_min_index_none >>
    gvs[min_idx_till_def, check_all_rows_match_def, INDEX_FIND_def]

    ,

    Cases_on ‘t'’ >> gvs[] >|[
             
        PairCases_on ‘h’ >> gvs[] >>
        Cases_on ‘h0’ >> gvs[] >|[

          (* case when the first table's row is empty *)
          gvs[sem_tables_def, match_tbll_row_empty] >>
          Cases_on ‘tbll’ >> gvs[] >>
          
          simp[match_tbll_def, match_tbl_def] >>
          imp_res_tac simp_sub_empty_then_min_index_tbl_none >>
          gvs[min_idx_till_def, check_all_rows_match_def, INDEX_FIND_def]
          ,
          (*case if the first table is not empty *)
          Cases_on ‘h’ >> gvs[] >|[
              (* case1: True case*)

                 
              (*case simplification returns True::t' *)
              (*if t' is empty or not, as in a final table with a final row *)
              Cases_on ‘t'’ >> gvs[simp_table_cannot_result2] >>
                (* case final table or not*)
              Cases_on ‘h2’ >> gvs[] >|[
                       
                  (*case returns action *)
                gvs[sem_tables_def] >>
                Cases_on ‘tbll’ >> gvs[] >|[
                  (* case the list contains one single table *)
                  gvs[simp_tables_def, match_tbll_def, fv_tbll_def] >>
                  imp_res_tac prop1_mini_subcases >>
                  gvs[]
                  ,
                  (*prove to be none here ... none *)
                  gvs[sem_tables_def, simp_tables_sub_not_empty_table,
                      match_tbll_final_before_ending_none] >>
                  gvs[match_tbll_def] >>
                  
                  imp_res_tac prop1_mini_subcases >> gvs[] >>
                  imp_res_tac simp_table_final_case >> gvs[] >>
                  gvs[match_tbl_def, check_all_rows_match_def, is_match_row_def,
                     is_atoml_true_def, sem_var_atom_def, min_idx_till_def, INDEX_FIND_def]
                  ]
                ,
                        
                  (* case returns state not action *)
                  gvs[sem_tables_def] >>
                  Cases_on ‘tbll’ >> gvs[] >|[
                      (* trivial case *)
                      gvs[simp_tables_def, match_tbll_def, fv_tbll_def] >>
                      imp_res_tac prop1_mini_subcases >>
                      gvs[]
                      ,
                      gvs[match_tbll_def] >>
                      (* prove for head, then use IH *)
                      Cases_on ‘simp_tables
                                (mk_substitute_tbl h x b::MAP (λt. mk_substitute_tbl t x b) t')
                                (SOME n)’ >> gvs[] >>
                      gvs[simp_tables_sub_not_empty_table] >>
                      gvs[match_tbll_def] >>
                      
                      gvs[simp_tables_sub_not_empty_table] >>
                      imp_res_tac prop1_mini_subcases >>
                      gvs[] >>
                      
                      Cases_on ‘match_tbl [([True],h1,state n)] mv s_in’ >> gvs[] >>
                      Cases_on ‘x'’ >> gvs[] >|[
                          
                          gvs[match_tbl_def, check_all_rows_match_def, is_match_row_def,
                              is_atoml_true_def, sem_var_atom_def, min_idx_till_def, INDEX_FIND_def] >>
                          rpt (BasicProvers.FULL_CASE_TAC >> gvs[])
                          ,
                          
                          imp_res_tac match_tbl_simple_final_case >> gvs[] >>
                          res_tac >>
                          first_x_assum (strip_assume_tac o (Q.SPECL [‘n’])) >>
                          
                          Cases_on ‘simp_tables
                                    (mk_substitute_tbl h x b::MAP (λt. mk_substitute_tbl t x b) t')
                                    (SOME n)’ >> gvs[] >>
                          gvs[ match_tbll_def]
                             
                          ,
                          
                          
                          imp_res_tac match_tbl_simple_final_case >> gvs[] >>
                          res_tac >>
                          first_x_assum (strip_assume_tac o (Q.SPECL [‘n’])) >>
                          metis_tac[]
                        ]
                  ]
              ]
                                       
              (* end of true case *)
              ,
              (* case 2: False case *)
              gvs[simp_table_impossible_case2]
              ,
              (* case 3: NotTrue case *)
              gvs[simp_table_impossible_case3]
              ,
              (* case 4: NotFalse case *)
              gvs[simp_table_impossible_case3]
              ,
              (* case 5: Var *)
              Cases_on ‘tbll’ >> gvs[] >>
              gvs[sem_tables_def, match_tbll_def] >|[
                  gvs[simp_tables_def, match_tbll_def, fv_tbll_def] >>
                  imp_res_tac prop1_mini_subcases >>
                  gvs[]
                  ,
                        
                  Cases_on ‘simp_tables
                            (mk_substitute_tbl h x b::MAP (λt. mk_substitute_tbl t x b) t'') NONE’ >> gvs[] >>
                                  
                  gvs[match_tbll_def] >>
                  gvs[simp_tables_sub_not_empty_table] >>
                  imp_res_tac prop1_mini_subcases >>
                  gvs[] >>
                  Cases_on ‘match_tbl [(Var s::t',h1,h2)] mv s_in’ >> gvs[] >>
                  Cases_on ‘x'’ >> gvs[] >>
                  res_tac >>
                  first_x_assum (strip_assume_tac o (Q.SPECL [‘n’])) >>

                  ‘match_tbll
                   (simp_tables (mk_substitute_tbl h x b::MAP (λt. mk_substitute_tbl t x b) t'')
                    (SOME n)) mv n
                   =
                   match_tbll
                   (simp_tables (mk_substitute_tbl h x b::MAP (λt. mk_substitute_tbl t x b) t'')
                    NONE) mv n ’
                    by gvs[match_tbll_simp_tables_eq_thm] >>
                  gvs[]
                ]

              ,
              (* case 6: Not *)
              Cases_on ‘tbll’ >> gvs[] >>
              gvs[sem_tables_def, match_tbll_def] >|[
                  gvs[simp_tables_def, match_tbll_def, fv_tbll_def] >>
                  imp_res_tac prop1_mini_subcases >>
                  gvs[]
                  ,
                  Cases_on ‘simp_tables
                            (mk_substitute_tbl h x b::MAP (λt. mk_substitute_tbl t x b) t'') NONE’ >> gvs[] >>
                  gvs[simp_tables_sub_not_empty_table] >>
                  gvs[match_tbll_def] >>

                  gvs[simp_tables_sub_not_empty_table] >>
                  imp_res_tac prop1_mini_subcases >>
                  gvs[] >>

                  Cases_on ‘match_tbl [(Not s::t',h1,h2)] mv s_in’ >> gvs[] >>
                  Cases_on ‘x'’ >> gvs[] >>
                  res_tac >>
                  first_x_assum (strip_assume_tac o (Q.SPECL [‘n’])) >>
                  
                  ‘match_tbll
                   (simp_tables (mk_substitute_tbl h x b::MAP (λt. mk_substitute_tbl t x b) t'')
                                    (SOME n)) mv n
                   =
                   match_tbll
                   (simp_tables (mk_substitute_tbl h x b::MAP (λt. mk_substitute_tbl t x b) t'')
                                    NONE) mv n ’
                    by gvs[match_tbll_simp_tables_eq_thm] >>
                  gvs[]
                ]
            ]
        ]
        ,
        (*IH case*)
        Cases_on ‘tbll’ >> gvs[] >>
        gvs[sem_tables_def, match_tbll_def] >|[
            simp[simp_tables_def,  match_tbll_def] >>
            imp_res_tac prop1_mini_subcases >>
            gvs[]
            ,
            Cases_on ‘simp_tables
               (mk_substitute_tbl h'' x b::
                                  MAP (λt. mk_substitute_tbl t x b) t') NONE’ >>
            gvs[simp_tables_sub_not_empty_table] >>

            rename1 ‘match_tbll ((r1::r2::r3)::tbl2::tbl3) mv s_in’ >>
                                                 
            simp[match_tbll_def] >>
            ‘match_tbl (r1::r2::r3) mv s_in = match_tbl t mv s_in’ by (
              imp_res_tac prop1_mini_subcases >>
              gvs[]) >>
            gvs[] >>

            rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
            res_tac >>
            first_x_assum (strip_assume_tac o (Q.SPECL [‘n’])) >>

                          
            ‘match_tbll
          (simp_tables
             (mk_substitute_tbl h'' x b::MAP (λt. mk_substitute_tbl t x b) t')
             (SOME n)) mv n
             =
             match_tbll
          (simp_tables
             (mk_substitute_tbl h'' x b::MAP (λt. mk_substitute_tbl t x b) t')
             NONE) mv n ’
              by gvs[match_tbll_simp_tables_eq_thm] >>
            
            gvs[]

          ]
      ]
  ]
QED




               
Theorem prop1_var_tables:
  prop1 table_structure
Proof
  rgs[prop1_def, table_structure_def, fv_in_p_def] >>

  rpt strip_tac >>
  Cases_on ‘p’ >>
  rename1 ‘(tbls, s_in)’ >>

  gvs[mk_substitute_tables_def, simp_tables_def, simp_tables_wrapper_def] >>
  gvs[mk_substitute_tbll_def] >>
  gvs[prop1_tables_verbose]
QED




(*******************************************)
(*                property 2               *)
(*******************************************)


Theorem final_row_final_result:
  ∀ atoms_list st res s_in q.
    final_row (atoms_list,st,res) s_in = SOME q ⇒
    (atoms_list = [True] ∧ st = s_in ∧ q = res)
Proof
  Cases >> rw[final_row_def] >>
  Cases_on ‘t’ >> gvs[] >>
  Cases_on ‘h’ >> gvs[final_row_def]
QED




        
        

Theorem property_final_imp_match_simp:
  ∀ tbl s_in q mv.
    final_tbl tbl s_in = SOME q ⇒
    match_tbl tbl mv s_in = SOME q
Proof
  Induct >-
   gvs[final_tbl_def] >>
  rw[] >>
  
  PairCases_on ‘h’ >>
  rename1 ‘((atoms_list,st,res)::t)’ >>
  
  gvs[final_tbl_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >|[
    
    gvs[match_tbl_def] >>
    res_tac >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘mv’])) >>
    
    Cases_on ‘min_idx_till (check_all_rows_match s_in t mv) T’ >> gvs[] >>
    PairCases_on ‘x’ >> gvs[] >>
    
    Cases_on ‘min_idx_till (check_all_rows_match s_in (([False],st,res)::t) mv) T’ >>
    
    (gvs[check_all_rows_match_def, is_match_row_def, is_atoml_true_def, sem_var_atom_def] >>
     gvs[min_idx_till_def, INDEX_FIND_def] >>
     imp_res_tac P_NONE_hold2 >> gvs[]) >>
    
    Cases_on ‘x’ >> gvs[] >>
    Cases_on ‘r’ >> gvs[] >>    
    imp_res_tac INDEX_FIND_some_eq_next >> gvs[]
    ,
    
    gvs[final_row_def]
    ,
    
    imp_res_tac final_row_final_result >> gvs[] >>
    gvs[final_row_def, match_tbl_def] >>
    gvs[check_all_rows_match_def, is_match_row_def, is_atoml_true_def, sem_var_atom_def] >>
    gvs[min_idx_till_def, INDEX_FIND_def]
  ]
QED




   
        
Theorem property_final_imp_sem_tbll_simp:
  ∀ tbll mv q s_in.
    final_tables (tbll,s_in) = SOME q
    ⇒
    sem_tables (tbll,s_in) mv = SOME q
Proof
  Induct >>
  rw[sem_tables_def] >|[
    gvs[final_tables_def, simp_tables_def, final_tbll_def]
    ,
    Cases_on ‘tbll’ >> gvs[] >|[

        gvs[final_tables_def, match_tbll_def, final_tbll_def] >>
        rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>

        imp_res_tac property_final_imp_match_simp >>
        first_x_assum (strip_assume_tac o (Q.SPECL [‘mv’])) >>
        Cases_on ‘match_tbl h mv s_in’ >> gvs[]                    
        ,
        
        gvs[final_tables_def, match_tbll_def, final_tbll_def] >>
        Cases_on ‘final_tbl h s_in’ >> gvs[] >>
        Cases_on ‘x’ >> gvs[] >>
                
        imp_res_tac property_final_imp_match_simp >>
        first_x_assum (strip_assume_tac o (Q.SPECL [‘mv’])) >>
        gvs[] >>
              
        res_tac >>
        gvs[sem_tables_def]
      ]
  ] 
QED





Theorem prop2_var_tables_verbose:
  ∀ tbll mv s_in h b q.
    ALOOKUP mv h = SOME b ∧
    final_tables (simp_tables (MAP (λtbl. mk_substitute_tbl tbl h b) tbll) (SOME s_in),s_in)
    = SOME q ⇒
    sem_tables (tbll,s_in) mv = SOME q
Proof
  rw[] >>
  imp_res_tac property_final_imp_sem_tbll_simp >>
  first_x_assum (strip_assume_tac o (Q.SPECL [‘mv’])) >>
  
  imp_res_tac prop1_tables_verbose >>
  first_x_assum (strip_assume_tac o (Q.SPECL [‘tbll’,‘s_in’])) >>
  metis_tac[]
QED

        

         
Theorem prop2_var_tables:
  prop2 table_structure
Proof
  rgs[prop2_def, table_structure_def, fv_in_p_def] >>

  rpt strip_tac >>
  Cases_on ‘p’ >>
  rename1 ‘(tbls, s_in)’ >>

  gvs[mk_substitute_tables_def, simp_tables_def, simp_tables_wrapper_def] >>
  gvs[mk_substitute_tbll_def] >>
  metis_tac[prop2_var_tables_verbose]
QED



         
Theorem prop3_var_tables:
  prop3 table_structure
Proof
  rgs[prop3_def, table_structure_def, fv_in_p_def] >>

  rpt strip_tac >>
  Cases_on ‘p’ >>
  rename1 ‘(tbls, s_in)’ >>

  gvs[mk_substitute_tables_def, simp_tables_def, simp_tables_wrapper_def] >>
  gvs[mk_substitute_tbll_def] >>
  metis_tac[property_final_imp_sem_tbll_simp]
QED


        
Theorem fv_atom_sub_single:
  ∀ h x b x'.
    MEM x' (fv_atom (mk_substitute_atom h x b)) ⇒
    MEM x' (fv_atom h)
Proof
  Induct >>
  rw[mk_substitute_atom_def, fv_atom_def]
QED
       

Theorem fv_atoml_row_single:
  ∀ atoml x' x b.
    MEM x' (fv_row (mk_substitute_row atoml x b)) ⇒
    MEM x' (fv_row atoml) 
Proof
  
  Induct >>
  rw[mk_substitute_row_def] >>
  gvs[fv_row_def] >>
  imp_res_tac fv_atom_sub_single >> gvs[] >>
  first_x_assum (strip_assume_tac o (Q.SPECL [‘x'’, ‘x’, ‘b’])) >>
  gvs[mk_substitute_row_def]
QED

        
Theorem fv_tbl_sub_single:
  ∀ tbl x' h' b.
    MEM x' (fv_tbl (mk_substitute_tbl tbl h' b)) ⇒
    MEM x' (fv_tbl tbl)
Proof
  Induct >>
  rw[mk_substitute_tbl_def] >>
  PairCases_on ‘h’ >> gvs[] >>
  gvs[fv_tbl_def] >>
  imp_res_tac fv_atoml_row_single >> gvs[] >>
  gvs[mk_substitute_tbl_def] >>
  res_tac >> gvs[]
QED        

Triviality mem_head_fv_tbll_triv:
  ∀ varslist h tbl x' tbls.
    (∀x. MEM x (fv_tbll (h::tbls)) ⇒ MEM x varslist) ∧
    MEM x' (fv_tbl h) ⇒
    MEM x' varslist
Proof
  rw[fv_tbll_def]
QED

        

Theorem fv_tbls_in_sub_varslist_thm:
  ∀ tbls varslist h b.
    (∀x. MEM x (fv_tbll tbls) ⇒ MEM x varslist) ⇒
    (∀x'. MEM x' (fv_tbll (MAP (λtbl. mk_substitute_tbl tbl h b) tbls)) ⇒ MEM x' varslist)
Proof

  Induct >>
  rw[] >>
  
  imp_res_tac fv_mem_tbll_varslist_thm >>
  res_tac >>
  
  Cases_on ‘MEM x' (fv_tbl (mk_substitute_tbl h h' b)) ’ >>
  
  imp_res_tac fv_tbl_sub_single >>
  imp_res_tac mem_head_fv_tbll_triv >>
  
  gvs[fv_tbll_def] >>
  res_tac 
QED  


     
Triviality simp_atom_fv_atom_triv:
  ∀ atom s.
    simp_atom atom = Var s ⇒ MEM s (fv_atom atom)
Proof
  Induct >> gvs[simp_atom_def, fv_atom_def]
QED


Theorem mem_flat_fv_row:
  ∀ row row' x .
    simp_row row = row' ∧
    MEM x (FLAT (MAP (λatom. fv_atom atom) row')) ⇒
    MEM x (FLAT (MAP (λatom. fv_atom atom) row))
Proof
  
  Induct >>
  gvs[simp_row_def] >> rw[]  >>
  
  (Cases_on ‘h’ >> gvs[simp_atom_def, fv_atom_def, is_not_true_var_atom_def] >>
   rpt (BasicProvers.FULL_CASE_TAC >> gvs[])) >>
  
  fs[fv_atom_def]
QED
                     

     

Theorem mem_fv_tbl_simp_mem:
  ∀ tbl tbl' x.
    MEM x ( fv_tbl tbl') ∧
    simp_table tbl NONE = tbl' ⇒
    MEM x ( fv_tbl tbl)
Proof
  Induct >>
  rw[simp_table_def] >>
  gvs[fv_tbl_def] >>
  PairCases_on ‘h’ >> 
  
  gvs[simp_table_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[fv_tbl_def, fv_row_def, fv_atom_def] >>
  res_tac >> gvs[simp_row_cannot_result1] >>
                                                 
  imp_res_tac mem_flat_fv_row >>
  gvs[fv_atom_def]
QED     
        



Theorem fv_simp_tables_some_in_varlist:
  ∀ t x s_in varslist.
    (∀x'. MEM x' (fv_tbl t) ⇒ MEM x' varslist) ∧
    MEM x (fv_tbl (simp_table t (SOME s_in))) ⇒
    MEM x varslist
Proof
  
  Induct >>
  rw[simp_table_def] >>
  PairCases_on ‘h’ >> gvs[] >>
  rename1 ‘fv_tbl ((atoml, st, res)::t)’ >>
  gvs[fv_tbl_def] >>
  
  ‘∀x'. MEM x' (fv_row atoml) ⇒ MEM x' varslist’ by gvs[] >>
  
  gvs[simp_table_def] >>
  Cases_on ‘s_in ≠ st’ >> gvs[] >-
   (
   res_tac >> gvs[]
   ) >>
  
  Cases_on ‘simp_row atoml’ >> gvs[] >-
   gvs[fv_row_def] >>
  res_tac >> gvs[] >>
  
  Cases_on ‘t'’ >> gvs[] >|[
    Cases_on ‘h’ >> gvs[] >>
    imp_res_tac mem_flat_fv_row >>
    gvs[simp_row_cannot_result1] >>
    res_tac >> gvs[] >>
    gvs[fv_row_def]
    ,
    gvs[fv_row_def] >>
    imp_res_tac mem_flat_fv_row >>
    gvs[]
    ,
    res_tac >> gvs[]
  ]        
QED



Theorem mem_fv_tbl_simp_imp:
  ∀ t n x.  MEM x (fv_tbl (simp_table t (SOME n))) ⇒
            MEM x (fv_tbl (simp_table t NONE))
Proof
  Induct >>
  rw[simp_table_def] >>
  PairCases_on ‘h’ >>
  rename1 ‘((atoml,st,res)::t)’ >>
  gvs[simp_table_def] >>
  
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[fv_tbl_def, fv_row_def, fv_atom_def] >>
  gvs[simp_row_cannot_result1] >>
  res_tac >> gvs[]
QED



   
Theorem mem_var_list_simp_tables_fv_tbll:
  ∀ tbls s_in  h b x varslist.
    (∀x'. MEM x' (fv_tbll tbls) ⇒ MEM x' varslist) ∧
    (MEM x (fv_tbll (simp_tables tbls (SOME s_in))) ∨
      MEM x (fv_tbll (simp_tables tbls NONE))   )⇒
    MEM x varslist
Proof
  gvs[simp_tables_eq] >>
  Induct >>
  rw[simp_tables2_def] >>
  gvs[fv_tbll_def] >>

  
  imp_res_tac fv_simp_tables_some_in_varlist >> gvs[] >>
  imp_res_tac mem_fv_tbl_simp_mem >> gvs[] >|[

    Cases_on ‘next_state (simp_table h (SOME s_in))’ >> gvs[] >>
    res_tac >> gvs[]
    ,
        
    Cases_on ‘next_state (simp_table h NONE)’ >> gvs[] >>
    res_tac >> gvs[]
  ]
QED

        

Theorem prop4_var_tables:
  prop4 table_structure
Proof
  rgs[prop4_def, table_structure_def, fv_in_p_def, fv_in_vars_def] >>

  rpt strip_tac >>
  Cases_on ‘prop_parent’ >>
  rename1 ‘(tbls, s_in)’ >>
          
  gvs[fv_tables_def, simp_tables_def, mk_substitute_tables_def, mk_substitute_tbll_def,
      simp_tables_wrapper_def] >>

  imp_res_tac fv_tbls_in_sub_varslist_thm >>
  imp_res_tac mem_var_list_simp_tables_fv_tbll >>
  res_tac >> gvs[] >>

  metis_tac[]
                        
QED






        
        

        
val _ = export_theory ();

    
