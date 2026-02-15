open HolKernel boolLib simpLib Parse bossLib;

open pairTheory;
open listTheory;
open rich_listTheory;
open alistTheory;
open arithmeticTheory;

open p4_auxTheory;

open bdd_genTheory;
open policy_specTheory;


val _ = new_theory "tables_spec_old";



(* atomic variable based predicates predicates*)
Datatype:
     atom_var = True
                | False
                | NotTrue
                | NotFalse
                | Var  string
                | Not string
End

Datatype:
  action_expr = action 'a | state num
End


Type var_line = “:(atom_var list # num # 'a action_expr)”;
Type var_table = “: ('a var_line) list”
Type var_table_list = “: ('a var_table) list”




(***************************************************)
(* some work for the variable based atoms          *)
(***************************************************)



Definition sem_var_atom_def:
  (sem_var_atom ((Var x): atom_var) mv = (ALOOKUP mv x)) ∧
  (sem_var_atom True _ = SOME T) ∧
  (sem_var_atom False _ = SOME F) ∧
  (sem_var_atom NotTrue _ = SOME F) ∧
  (sem_var_atom NotFalse _ = SOME T) ∧
  (sem_var_atom (Not x) mv =
   case (ALOOKUP mv x) of
   | SOME b => SOME (~b)
   | _ => NONE
  )
End


Definition mk_substitute_atom_def:
  (mk_substitute_atom (True:atom_var) x b = True) ∧
  (mk_substitute_atom False x b = False) ∧
  (mk_substitute_atom NotTrue x b = NotTrue) ∧
  (mk_substitute_atom NotFalse x b = NotFalse) ∧
  (mk_substitute_atom (Var x') x b =
   if (x=x') then (if b then True else False) else (Var x')) ∧
  (mk_substitute_atom (Not x') x b =
   if (x=x') then (if b then NotTrue else NotFalse) else (Not x'))
End


Definition simp_atom_def:
  (simp_atom ((Var x):atom_var) = Var x) ∧
  (simp_atom True = True) ∧
  (simp_atom False = False) ∧
  (simp_atom NotTrue = False) ∧
  (simp_atom NotFalse = True) ∧
  (simp_atom (Not x) = Not x)
End


Definition final_atom_def:
  final_atom (p:atom_var) =
  case p of
  | True => SOME T
  | False => SOME F
  | NotTrue => SOME F
  | NotFalse => SOME T
  | _ => NONE
End


Definition fv_atom_def:
  (fv_atom ((Var x):atom_var) = [x]) ∧
  (fv_atom True = []) ∧
  (fv_atom False = []) ∧
  (fv_atom NotTrue = []) ∧
  (fv_atom NotFalse = []) ∧
  (fv_atom (Not x) = [x])
End



(***************************************************)
(* specialized definitions for a predicate record. *)
(*   here 'a would be policy and 'b would be       *)
(*          action wrt record data type            *)
(***************************************************)



(* Check if all predicates in list evaluate to true *)
Definition is_atoml_true_def:
  is_atoml_true atoml mv =
  EVERY (\minipred. sem_var_atom minipred mv = SOME T) atoml
End


(* Check if row matches current state and guard conditions *)
Definition is_match_row_def:
  is_match_row st_in st_num atoml mv =
    ((st_in = st_num) ∧ is_atoml_true atoml mv ∧ atoml ≠ [])
End


Definition check_all_rows_match_def:
  check_all_rows_match st_in tbl mv =
  MAP (\(atoml,st_num,res). (is_match_row st_in st_num atoml mv, res)) tbl
End



(* Find first matching line in a single table *)
Definition match_tbl_def:
  match_tbl (tbl: 'a var_table) mv st_in =
  let lines_res = (check_all_rows_match st_in tbl mv) in
    case min_idx_till lines_res T of
    | SOME (idx, line) => SOME (SND line)
    | NONE => NONE
End





(* Process table list with state propagation *)
Definition match_tbll_def:
  match_tbll ([]: 'a var_table_list) mv st_in = NONE ∧
  match_tbll [tbl] mv st_in =
  ( case match_tbl tbl mv st_in of
    | SOME (action a) => SOME (action a)
    | _ => NONE
  )∧
  match_tbll (tbl::tbls) mv st_in =
  ( case match_tbl tbl mv st_in of
    | SOME (state n) => match_tbll tbls mv n
    | _ => NONE
  )
End


(* Top-level table semantics, return the starting state as well*)
Definition sem_tables_def:
  sem_tables ((tbll: 'a var_table_list),st_in) mv =
   match_tbll tbll mv st_in
End


(*
EVAL “match_tbl [([False], 0 , action "s")] [] 0”;
EVAL “match_tbl [([True], 0 , action "s")] [] 0”;
EVAL “match_tbl [([Var "a"], 0 , action "s1");([True], 0 , action "s2")] [("a",T)] 0”;
EVAL “match_tbl [([Var "a"; True], 0 , action "s1"); ([True], 0 , action "s2")] [("a",T)] 0”;


EVAL “match_tbl [([False;True],0,state 2); ([False],0,state 3);([True],0,state 3)] [] 0”;
EVAL “match_tbl [([True],3,state 4); ([False],3,state 5); ([True],2,state 2)] [] 3”;
EVAL “match_tbl [([True],2,action ("fwd",[(1:num)])); ([True],4,action ("fwd",[2])); ([True],5,action ("drop",[]))] [] 4”;


EVAL “sem_tables ([[([False],0,state 2); ([False],0,state 3);([True],0,state 3)];
                  [([True],3,state 4); ([False],3,state 5); ([True],2,state 2)];
                  [([True],2,action ("fwd",[1])); ([True],4,action ("fwd",[2])); ([True],5,action ("drop",[]))]],0) []”
*)


(* table substitute *)

Definition mk_substitute_row_def:
  mk_substitute_row atoml x b =
    MAP (\atom. mk_substitute_atom atom x b) atoml
End

Definition mk_substitute_tbl_def:
  mk_substitute_tbl (tbl: 'a var_table) x b =
  ((MAP (\(atoml,st_num,res). (mk_substitute_row atoml x b, st_num, res)) tbl) :'a var_table)
End


Definition mk_substitute_tbll_def:
  mk_substitute_tbll (tbll: 'a var_table_list) x b =
  MAP (\(tbl). mk_substitute_tbl (tbl: 'a var_table) x b) tbll
End


Definition mk_substitute_tables_def:
  mk_substitute_tables ((tbll: 'a var_table_list), st_in) x b =
   (mk_substitute_tbll tbll x b, st_in:num)
End

(* table simplifications *)

Definition simp_row_old_def:
  simp_row_old atoml =
  let simplified_row = MAP (\atom. simp_atom atom) atoml in
    case MEM False simplified_row of
    | T => MAP (\a. False) atoml
    | F => simplified_row
End


Definition simp_tbl_def:
  simp_tbl (tbl: 'a var_table) =
  MAP (\(atoml,st_num,res). simp_row_old atoml,st_num,res) tbl
End


Definition simp_tbll_def:
  simp_tbll (tbll: 'a var_table_list) =
  MAP (\tbl. simp_tbl tbl) tbll
End


Definition simp_tables_old_def:
  simp_tables_old ((tbll: 'a var_table_list), st_in) =
   (simp_tbll tbll, st_in:num)
End


(*
EVAL “simp_tbl [([False], 0 , action "s")]”;
EVAL “simp_tbl [([True; False], 0 , action "s")]”;
EVAL “simp_tbl [([Var "a"], 0 , action "s1");([True;False], 0 , action "s2")]”;
EVAL “simp_tbl [([Var "a"; False], 0 , action "s1"); ([True], 0 , action "s2")]”;

EVAL “simp_tbll   ([[([False; Var "a"],0,state 2); ([False],0,state 3);([True],0,state 3)];
                  [([True],3,state 4); ([False],3,state 5); ([True],2,state 2)];
                  [([Var "a"; False], 0 , action "s1"); ([True], 0 , action "s2")]]) ”
*)



(* table final *)

Definition all_true_def:
  all_true atoml =
  EVERY (\atom. atom = True) atoml
End


Definition all_false_def:
  all_false atoml =
  EVERY (\atom. atom = False) atoml
End


Definition is_hit_def:
  is_hit st_in st_num atoml =
    ((st_in = st_num) ∧ all_true atoml ∧ atoml ≠ [])
End


Definition is_hit_tbl_check_def:
  is_hit_tbl_check (tbl: 'a var_table) st_in =
  MAP (\(atoml, st_num, res). is_hit st_in st_num atoml, st_num, res) tbl
End



Definition pre_lines_are_fail_def:
  pre_lines_are_fail (tbl: 'a var_table) idx st_in =
  EVERY (\(atoml, st_num, res).  if st_num = st_in then all_false atoml else T) (SEG idx 0 tbl)
End


Definition final_tbl_old_def:
  final_tbl_old  (tbl: 'a var_table) st_in =
  let lines_res = is_hit_tbl_check tbl st_in in
    case min_idx_till lines_res T of
    | SOME (idx, b, st_num, res) =>
        ( case pre_lines_are_fail tbl idx st_in of
          | T => SOME res
          | F => NONE
        )
    | _ => NONE
End

(*
EVAL “final_tbl_old  [([False], 0 , action "s")] 0” (*must fail *)
EVAL “final_tbl_old  [([True], 0 , action "s")] 0”
EVAL “final_tbl_old  [([False], 0 , action "s1");([True], 0 , action "s2")] 0”
EVAL “final_tbl_old  [([Var "a"], 0 , action "s1");([True], 1 , action "s2")] 1”
EVAL “final_tbl_old  [([Var "a"], 0 , action "s1");([True], 0 , action "s2")] 0” (* must fail *)
*)


Definition final_tbll_old_def:
  final_tbll_old ([]: 'a var_table_list) st_in = NONE ∧
  final_tbll_old [tbl] st_in =
  ( case final_tbl_old  tbl st_in of
    | SOME (action a) => SOME (action a)
    | _ => NONE
  )∧
  final_tbll_old (tbl::tbls) st_in =
  ( case final_tbl_old  tbl st_in of
    | SOME (state n) => final_tbll_old tbls n
    | _ => NONE
  )
End



Definition final_tables_old_def:
  final_tables_old (tbll, st_in) =
  final_tbll_old tbll st_in
End


(*

EVAL “final_tbll_old [[([False],0,state 2); ([False],0,state 3); ([True],0,state 3)];
                  [([True],3,state 4); ([False],3,state 5); ([True],2,state 2)];
                  [([True],2,action ("fwd",[1])); ([True],4,action ("fwd",[2]));
               ([True],5,action ("drop",[]))]] 0 ”

EVAL “final_tbll_old [[([False],0,state 2); ([False],0,state 3); ([False],0,state 3)];
                  [([True],3,state 4); ([False],3,state 5); ([True],2,state 2)];
                  [([True],2,action ("fwd",[1])); ([True],4,action ("fwd",[2]));
               ([True],5,action ("drop",[]))]] 0 ”
*)

(*  free variables tables *)


Definition fv_row_def:
  fv_row atoml =
  let fv_in_row = MAP (\atom. fv_atom atom) atoml in
    nub(FLAT fv_in_row)
End


Definition fv_tbl_def:
  fv_tbl (tbl: 'a var_table) =
  (let fv_in_tbl = MAP(\(atom,st_num,res). fv_row atom) tbl in
      nub (FLAT fv_in_tbl))
End




Definition fv_tbll_def:
  fv_tbll (tbll: 'a var_table_list) =
  let fv_in_tbll = MAP (\tbl. fv_tbl tbl) tbll in
    nub(FLAT fv_in_tbll)
End



Definition fv_tables_def:
  fv_tables (tbll, st_in) =
  fv_tbll tbll
End





Definition table_structure_old_def:
  table_structure_old =
  <|
    sem := sem_tables;
    sub := mk_substitute_tables;
    simp := simp_tables_old;
    final := final_tables_old;
    fv := fv_tables;
  |>
End




Theorem fv_mem_tbll_thm:
  ∀ tbll tbl mv.
    (∀x. MEM x (fv_tbll (tbl::tbll)) ⇒ ∃b. ALOOKUP mv x = SOME b) ⇒
    (∀x. MEM x (fv_tbll  tbll) ⇒ ∃b. ALOOKUP mv x = SOME b)
Proof
  gvs[fv_tbll_def]
QED


Theorem fv_mem_tbll_hd_thm:
  ∀ tbll tbl mv.
    (∀x. MEM x (fv_tbll (tbl::tbll)) ⇒ ∃b. ALOOKUP mv x = SOME b) ⇒
    (∀x. MEM x (fv_tbl  tbl) ⇒ ∃b. ALOOKUP mv x = SOME b)
Proof
  gvs[fv_tbll_def, fv_tbl_def]
QED


Theorem fv_mem_tbl_thm:
  ∀ tbl h mv.
    (∀x. MEM x (fv_tbl (h::tbl)) ⇒ ∃b. ALOOKUP mv x = SOME b) ⇒
    (∀x. MEM x (fv_tbl  tbl) ⇒ ∃b. ALOOKUP mv x = SOME b)
Proof
  gvs[fv_tbl_def]
QED


Theorem fv_mem_tbl_h_thm:
  ∀ tbl h mv.
    (∀x. MEM x (fv_tbl (h::tbl)) ⇒ ∃b. ALOOKUP mv x = SOME b) ⇒
    (∀x. MEM x (fv_tbl  [h]) ⇒ ∃b. ALOOKUP mv x = SOME b)
Proof
  gvs[fv_tbl_def]
QED



Theorem fv_mem_row_thm:
  ∀ atoml h mv.
    (∀x. MEM x (fv_row (h::atoml)) ⇒ ∃b. ALOOKUP mv x = SOME b) ⇒
    (∀x. MEM x (fv_row atoml) ⇒ ∃b. ALOOKUP mv x = SOME b)
Proof
  gvs[fv_row_def]
QED



Theorem fv_mem_row_h_thm:
  ∀ atoml h mv.
    (∀x. MEM x (fv_row (h::atoml)) ⇒ ∃b. ALOOKUP mv x = SOME b) ⇒
    (∀x. MEM x (fv_row [h]) ⇒ ∃b. ALOOKUP mv x = SOME b)
Proof
  gvs[fv_row_def]
QED


Theorem mk_substitute_tbl_normalize1:
  ∀h rows x b.
       mk_substitute_tbl (h::rows) x b =
       mk_substitute_tbl [h] x b ⧺ mk_substitute_tbl rows x b
Proof
  gvs[mk_substitute_tbl_def]
QED


Theorem mk_substitute_tbl_normalize2:
  ∀atoml st_num res rows x b.
       mk_substitute_tbl ((atoml,st_num,res)::rows) x b =
       (mk_substitute_row atoml x b,st_num,res)::mk_substitute_tbl rows x b
Proof
  gvs[mk_substitute_tbl_def]
QED


Theorem simp_tbl_normalize1:
  ∀atoml st_num res rows x b.
       simp_tbl ((atoml,st_num,res)::rows) =
       (simp_row_old atoml,st_num,res)::simp_tbl rows
Proof
  gvs[simp_tbl_def]
QED



Theorem sub_then_simp_answer_indeed_in_fv:
  ∀ atom h' b s.
    (simp_atom (mk_substitute_atom atom h' b) = Var s) ⇒
    MEM s (fv_atom atom)
Proof
  Cases >>
  rpt strip_tac >>
  gvs[fv_atom_def, mk_substitute_atom_def, simp_atom_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[fv_atom_def, mk_substitute_atom_def, simp_atom_def]
QED


Triviality mem_fv_sub_simp_tbl_triv1:
  ∀ atom h' b x.
    MEM x (fv_atom (simp_atom (mk_substitute_atom atom h' b))) ⇒
    MEM x (fv_atom atom)
Proof
  Cases >>
  rpt strip_tac >>
  gvs[fv_atom_def, mk_substitute_atom_def, simp_atom_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[fv_atom_def, mk_substitute_atom_def, simp_atom_def]
QED



Theorem mem_imp_sem_tbl:
  ∀ atom mv.
    (∀x. MEM x (fv_atom atom) ⇒ ∃b. ALOOKUP mv x = SOME b) ⇒
    sem_var_atom atom mv ≠ NONE ∧ ∃ b' . sem_var_atom atom mv = SOME b'
Proof
  Cases >>
  rw[fv_atom_def] >> gvs[AllCaseEqs()] >>
  gvs[sem_var_atom_def, simp_atom_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[])
QED


Triviality non_empty_line_simp_not_empty:
  ∀ atoml h' b.
    atoml ≠ [] ⇔  simp_row_old (mk_substitute_row atoml h' b) ≠ []
Proof
  Induct >> gvs[mk_substitute_row_def, simp_row_old_def] >>
  rpt strip_tac >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[])
QED



Theorem lookup_implies_sem_var_atoms_same:
  ∀ atom h' b bool mv.
    ALOOKUP mv h' = SOME b  ⇒
    (sem_var_atom atom mv = SOME bool ⇔ sem_var_atom (simp_atom (mk_substitute_atom atom h' b)) mv = SOME bool)
Proof
  Cases >>
  rpt strip_tac >>
  rpt (gvs[mk_substitute_atom_def, simp_atom_def, sem_var_atom_def] >>
       BasicProvers.FULL_CASE_TAC >>
       res_tac >>
       gvs[])
QED



Theorem sem_var_atom_failure_from_simp_atom_false:
  ∀ atoml h' b mv.
    atoml ≠ [] ∧
    ALOOKUP mv h' = SOME b ∧
    MEM False (MAP (λatom. simp_atom atom) (MAP (λatom. mk_substitute_atom atom h' b) atoml)) ⇒
    ~ EVERY (λminipred. sem_var_atom minipred mv = SOME T) atoml
Proof
  Induct >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac lookup_implies_sem_var_atoms_same >> gvs[sem_var_atom_def] >>
  res_tac >>
  Cases_on ‘atoml = []’ >> gvs[] >>
  imp_res_tac NOT_EVERY
QED



Theorem subst_simp_sound_for_atom:
  ∀atom h' b mv.
    ALOOKUP mv h' = SOME b ⇒
    (simp_atom (mk_substitute_atom atom h' b) = True ⇒
     sem_var_atom atom mv = SOME T) ∧
    (simp_atom (mk_substitute_atom atom h' b) = False ⇒
     sem_var_atom atom mv = SOME F)
Proof
  Cases >>
  gvs[simp_atom_def, mk_substitute_atom_def, sem_var_atom_def] >>
  rpt strip_tac >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[simp_atom_def, mk_substitute_atom_def, sem_var_atom_def])
QED




Theorem lookup_implies_sem_var_atoml_same2:
  ∀ atoml h' b mv.
    ALOOKUP mv h' = SOME b ∧
    atoml ≠ [] ∧
    EVERY ((λminipred. sem_var_atom minipred mv = SOME T)) (simp_row_old (mk_substitute_row atoml h' b)) ⇒
    EVERY (λminipred. sem_var_atom minipred mv = SOME T) atoml
Proof
  Induct >>
  rpt strip_tac >>
  gvs[mk_substitute_row_def, simp_row_old_def] >>

  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[sem_var_atom_def] >>

  imp_res_tac lookup_implies_sem_var_atoms_same >> gvs[] >> res_tac >>
  gvs[] >>
  Cases_on ‘atoml = []’ >> gvs[]
QED






Theorem simp_sub_mem_normalization:
  ∀ atoml h h' b atom.
    atom ≠ simp_atom (mk_substitute_atom h h' b) ∧
    MEM atom (simp_row_old (mk_substitute_row (h::atoml) h' b)) ⇒
    MEM atom (simp_row_old (mk_substitute_row atoml h' b))
Proof
  rpt strip_tac >>
  gvs[mk_substitute_row_def, simp_row_old_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[MEM_MAP] >> metis_tac[]
QED





Theorem is_match_row_substitute_preserve1:
  ∀ atoml mv h' b s_in st_num.
    ALOOKUP mv h' = SOME b ∧
    is_match_row s_in st_num atoml mv ⇒
    is_match_row s_in st_num (simp_row_old (mk_substitute_row atoml h' b)) mv
Proof
  Induct >>
  gvs[is_match_row_def] >>
  rpt strip_tac >>
  gvs[is_atoml_true_def] >>

  Cases_on ‘atoml = []’ >> gvs[] >|[
    simp[mk_substitute_row_def, simp_row_old_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[sem_var_atom_def]) >>
    imp_res_tac subst_simp_sound_for_atom >> gvs[] >>
    imp_res_tac lookup_implies_sem_var_atoms_same >> gvs[]
    ,
    res_tac >>
    rgs[] >>
    gvs[Once EVERY_NOT_EXISTS] >>
    gvs[EVERY_MEM] >>
    gvs[EVERY_MAP] >>
    rpt strip_tac >>

    Cases_on ‘minipred = simp_atom(mk_substitute_atom h h' b)’ >> gvs[] >>
    res_tac >|[
        imp_res_tac lookup_implies_sem_var_atoms_same >> gvs[]
        ,
        imp_res_tac simp_sub_mem_normalization >>
        res_tac
      ]
    ,

    gvs[mk_substitute_row_def, simp_row_old_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[])
    ,

    res_tac >>
    rgs[] >>
    gvs[mk_substitute_row_def, simp_row_old_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[])
  ]
QED



Theorem is_match_row_substitute_preserve2:
  ∀ atoml mv h' b s_in st_num.
    ALOOKUP mv h' = SOME b ∧
    is_match_row s_in st_num (simp_row_old (mk_substitute_row atoml h' b)) mv ⇒
    is_match_row s_in st_num atoml mv
Proof
  Induct >>
  gvs[is_match_row_def] >>
  rpt strip_tac >>
  gvs[is_atoml_true_def] >>
  (
  imp_res_tac lookup_implies_sem_var_atoml_same2 >>
  gvs[mk_substitute_row_def, simp_row_old_def]
  )
QED



Theorem is_match_row_substitute_preserve:
  ∀ atoml mv h' b (s_in:num) st_num.
    ALOOKUP mv h' = SOME b ⇒
    (is_match_row s_in st_num (simp_row_old (mk_substitute_row atoml h' b)) mv =
    is_match_row s_in st_num atoml mv)
Proof
  rpt strip_tac >>
  EQ_TAC >>
  metis_tac[is_match_row_substitute_preserve1, is_match_row_substitute_preserve2]
QED



Theorem exists_is_match_row_after_subst_simp:
  ∀ tbl s_in h' b mv.
    ALOOKUP mv h' = SOME b ∧
    EXISTS (λ(p,a). p) (MAP (λ(atoml,st_num,res). (is_match_row s_in st_num atoml mv,res)) tbl) ⇒
    EXISTS (λ(p,a). p) (MAP (λ(atoml,st_num,res). (is_match_row s_in st_num atoml mv,res))
                            (simp_tbl (mk_substitute_tbl tbl h' b)))
Proof
  Induct >-
   gvs[mk_substitute_tbl_def, simp_tbl_def] >>
  rpt strip_tac >>
  simp[mk_substitute_tbl_def, simp_tbl_def] >>
  gvs[] >|[

    PairCases_on ‘h’ >>
    rename1 ‘(atoml, st_num, res)’ >>
    gvs[MAP_MAP_o] >>
    gvs[EXISTS_MAP] >>
    imp_res_tac is_match_row_substitute_preserve1 >> gvs[]
    ,
    res_tac >>
    gvs[mk_substitute_tbl_def, simp_tbl_def]
  ]
QED


Theorem exists_is_match_row_before_subst_simp:
  ∀ tbl s_in h' b mv.
    ALOOKUP mv h' = SOME b ∧
    EXISTS (λ(p,a). p) (MAP (λ(atoml,st_num,res). (is_match_row s_in st_num atoml mv,res))
                            (simp_tbl (mk_substitute_tbl tbl h' b))) ⇒
    EXISTS (λ(p,a). p) (MAP (λ(atoml,st_num,res). (is_match_row s_in st_num atoml mv,res)) tbl)
Proof
  Induct >-
   gvs[mk_substitute_tbl_def, simp_tbl_def] >>
  rpt strip_tac >>
  gvs[mk_substitute_tbl_def, simp_tbl_def] >>
  gvs[] >|[

    PairCases_on ‘h’ >>
    rename1 ‘(atoml, st_num, res)’ >>
    gvs[MAP_MAP_o] >>
    gvs[EXISTS_MAP] >>
    imp_res_tac is_match_row_substitute_preserve2 >> gvs[]
    ,
    res_tac >>
    gvs[mk_substitute_tbl_def, simp_tbl_def]
  ]
QED




Theorem is_match_row_lists_subst_simp_eq:
∀tbl h' b mv s_in.
       ALOOKUP mv h' = SOME b ⇒
       MAP (λ(atoml,st_num,res). (is_match_row s_in st_num atoml mv,res))
         (simp_tbl (mk_substitute_tbl tbl h' b)) =
       MAP (λ(atoml,st_num,res). (is_match_row s_in st_num atoml mv,res)) tbl
Proof
  Induct >>
  rpt strip_tac >>
  gvs[mk_substitute_tbl_def,simp_tbl_def] >>
  PairCases_on ‘h’ >>
  rename1 ‘(atoml, st_num, res)’ >>
  gvs[MAP_MAP_o] >>
  gvs[EXISTS_MAP] >>
  res_tac >>

  imp_res_tac is_match_row_substitute_preserve >>
  gvs[]
QED




Theorem subst_simp_sem_tables_INDEX_FIND_congruence:
  ∀ tbl mv s_in h' b i.
    ALOOKUP mv h' = SOME b  ⇒
    INDEX_FIND i (λ(p,a). p)
               (MAP (λ(atoml,st_num,res). (is_match_row s_in st_num atoml mv,res)) (simp_tbl (mk_substitute_tbl tbl h' b))) =
    INDEX_FIND i (λ(p,a). p)
               (MAP (λ(atoml,st_num,res). (is_match_row s_in st_num atoml mv,res)) tbl)

Proof
  rpt strip_tac >>
  imp_res_tac is_match_row_lists_subst_simp_eq >>
  gvs[]
QED



Theorem subst_check_rows_sem_tables_INDEX_FIND_congruence:
  ∀ tbl mv s_in h' b.
    ALOOKUP mv h' = SOME b  ⇒
    (check_all_rows_match s_in(simp_tbl (mk_substitute_tbl tbl h' b)) mv) =
    (check_all_rows_match s_in tbl mv)
Proof
  gvs[check_all_rows_match_def] >>
  rpt strip_tac >>
  imp_res_tac is_match_row_lists_subst_simp_eq >>
  gvs[]
QED


Theorem min_idx_till_subst_simp_invariant1:
  ∀ tbl mv s_in h' b atoml st_num res .
      ALOOKUP mv h' = SOME b  ⇒
      min_idx_till (check_all_rows_match s_in (simp_tbl (mk_substitute_tbl ((atoml,st_num,res)::tbl) h' b)) mv) T =
      min_idx_till (check_all_rows_match s_in ((atoml,st_num,res)::tbl) mv) T
Proof
  rpt strip_tac >>
  gvs[min_idx_till_def] >>
  imp_res_tac subst_check_rows_sem_tables_INDEX_FIND_congruence >>
  gvs[]
QED


Theorem min_idx_till_subst_simp_invariant2:
  ∀ tbl mv s_in h' b  .
      ALOOKUP mv h' = SOME b  ⇒
      min_idx_till (check_all_rows_match s_in (simp_tbl (mk_substitute_tbl (tbl) h' b)) mv) T =
      min_idx_till (check_all_rows_match s_in (tbl) mv) T
Proof
  rpt strip_tac >>
  gvs[min_idx_till_def] >>
  imp_res_tac subst_check_rows_sem_tables_INDEX_FIND_congruence >>
  gvs[]
QED


Theorem sem_tables_subst_simp_invariant:
  ∀ tbl mv s_in h' b row .
    ALOOKUP mv h' = SOME b   ⇒
    sem_tables ([simp_tbl (mk_substitute_tbl (row::tbl) h' b)],s_in) mv =
    sem_tables ([row::tbl],s_in) mv
Proof
  rpt strip_tac >>
  PairCases_on ‘row’ >> rename1 ‘(atoml,st_num,res)’ >>
  gvs[] >>

  simp[sem_tables_def, match_tbll_def] >>
  gvs[match_tbl_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>

  imp_res_tac min_idx_till_subst_simp_invariant1 >> gvs[]
QED



Theorem prop1_var_single_tbl_verbose:
  ∀ tbl mv h' b s_in.
    ALOOKUP mv h' = SOME b ⇒
    sem_tables (simp_tbll (mk_substitute_tbll [tbl] h' b),s_in) mv =
    sem_tables ([tbl],s_in) mv
Proof
  Cases >-
   (gvs[fv_tbll_def, mk_substitute_tbll_def, simp_tbll_def] >>
   gvs[fv_tbl_def, mk_substitute_tbl_def, simp_tbl_def]) >>

  rpt strip_tac >>
  gvs[mk_substitute_tbll_def, simp_tbll_def] >>
  imp_res_tac sem_tables_subst_simp_invariant >>
  gvs[]
QED




Theorem prop1_var_tables_old_verbose:
  ∀ tbls h b mv s_in.
    ALOOKUP mv h = SOME b
    ⇒
    sem_tables (simp_tbll (mk_substitute_tbll tbls h b),s_in) mv =
    sem_tables (tbls,s_in) mv
Proof

  Induct_on ‘tbls’ >> rpt strip_tac >-
   gvs[fv_tbll_def, mk_substitute_tbll_def, simp_tbll_def] >>
  rename1 ‘(tbl::tbll)’ >>

  imp_res_tac prop1_var_single_tbl_verbose >>
  first_x_assum (strip_assume_tac o (Q.SPECL [‘tbl’, ‘s_in’])) >>

  Cases_on ‘tbll’ >> gvs[] >>
  rename1 ‘(tbl::nexttbl::tbll)’ >>

  gvs[sem_tables_def, match_tbll_def] >>
  Cases_on ‘match_tbl tbl mv s_in’ >> gvs[] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>

  gvs[mk_substitute_tbll_def, simp_tbll_def] >>
  gvs[match_tbll_def] >>
  Cases_on ‘match_tbl (simp_tbl (mk_substitute_tbl tbl h' b)) mv s_in’ >> gvs[] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>

  gvs[match_tbl_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  imp_res_tac min_idx_till_subst_simp_invariant2 >> gvs[]
QED



Theorem prop1_var_tables_old:
  prop1 table_structure_old
Proof
  rgs[prop1_def, table_structure_old_def, fv_in_p_def] >>

  rpt strip_tac >>
  Cases_on ‘p’ >>
  rename1 ‘(tbls, s_in)’ >>

  gvs[fv_tables_def, mk_substitute_tables_def, simp_tables_old_def] >>
  imp_res_tac prop1_var_tables_old_verbose >> gvs[]
QED


Theorem is_hit_true_atoml_not_empty:
  ∀ atoml h' b s_in st_num.
    is_hit s_in st_num (simp_row_old (mk_substitute_row atoml h' b)) ⇒
    atoml ≠ []
Proof
  gvs[is_hit_def, all_true_def, mk_substitute_row_def, simp_row_old_def]
QED




Theorem hit_implies_match_after_subst:
  ∀ atoml s_in st_num h' b mv.
    ALOOKUP mv h' = SOME b ∧
    is_hit s_in st_num (simp_row_old (mk_substitute_row atoml h' b)) ⇒
    is_match_row s_in st_num atoml mv
Proof
  Induct_on ‘atoml’ >>
  rpt strip_tac >>
  imp_res_tac is_hit_true_atoml_not_empty >>
  gvs[is_hit_def, is_match_row_def] >>
  gvs[is_atoml_true_def, mk_substitute_row_def, simp_row_old_def, all_true_def] >>
  res_tac >>

  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[sem_var_atom_def] >>


  Cases_on ‘atoml=[]’ >> gvs[] >>
  imp_res_tac subst_simp_sound_for_atom
QED




Theorem row_miss_preserved_by_subst_simp:
  ∀ tbl s_in h' b mv.
    ALOOKUP mv h' = SOME b ∧
    EVERY ($¬ ∘ (λ(p,a). p)) (MAP (λ(atoml,st_num,res). (is_match_row s_in st_num atoml mv,res)) tbl)
    ⇒
    ¬ EXISTS (λx. (λ(p,a). p) ((λ(atoml,st_num,res). (is_hit s_in st_num atoml,st_num,res))
                               ((λ(atoml,st_num,res). (simp_row_old atoml,st_num,res))
                                ((λ(atoml,st_num,res). (mk_substitute_row atoml h' b,st_num,res)) x)))) tbl
Proof
Induct >> gvs[] >>
rpt strip_tac >>
PairCases_on ‘h’ >> gvs[] >>
imp_res_tac hit_implies_match_after_subst >>
res_tac
QED



Theorem pre_lines_are_fail_normalize:
  ∀ l h idx st_num.
    idx > 0 ∧
    idx < LENGTH (h::l) ∧
    pre_lines_are_fail (h::l) idx st_num ⇒
    pre_lines_are_fail l (idx-1) st_num
Proof
  rpt strip_tac >>
  gvs[pre_lines_are_fail_def] >>
  imp_res_tac every_seg_property_1 >>
  Cases_on ‘idx’ >> gvs[SUC_ADD_ONE] >>
  res_tac >>
  imp_res_tac every_seg_property_1 >>
  ‘n < LENGTH l’ by gvs[] >>
  gvs[]
QED




Theorem index_find_not_prev:
  ∀ l P r.
    INDEX_FIND 1 P l ≠ SOME (0,r)
Proof
  Induct >> gvs[INDEX_FIND_def] >>
  rpt strip_tac >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  assume_tac P_hold_on_next >>
  first_x_assum (strip_assume_tac o (Q.SPECL [‘(1:num)’, ‘l’, ‘P’, ‘(0,r)’])) >>
  gvs[SUC_ADD_ONE]
QED



Theorem index_find_not_prev_gen:
  ∀ i l P r .
    i > 1 ∧
    0 < LENGTH l ⇒
    INDEX_FIND i P l ≠ SOME (i-1,r)
Proof
  Induct >> gvs[INDEX_FIND_def] >>
  rpt strip_tac >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  assume_tac P_hold_on_next >>
  first_x_assum (strip_assume_tac o (Q.SPECL [‘(i:num)’, ‘l’, ‘P’, ‘(i,r)’])) >>
  gvs[SUC_ADD_ONE] >>

  Cases_on ‘i > 1’ >> gvs[] >>
  Cases_on ‘i=1’ >> gvs[] >>
  imp_res_tac index_find_not_prev
QED





Theorem every_seg_property_3:
  ∀ n l h p.
    0 < n ∧
    EVERY p (SEG n 0 (h::l)) ⇒
    EVERY p (SEG (n-1) 0 l)
Proof
  Induct >>
  rpt strip_tac >>
  gvs[SEG, SUC_ADD_ONE] >>
  gvs[GSYM TAKE_SEG]
QED



Theorem every_simp_false_imp_sem_false:
  ∀ atoml h' b mv.
    atoml ≠ [] ∧
    ALOOKUP mv h' = SOME b ∧
    EVERY (λatom. atom = False) (simp_row_old (mk_substitute_row atoml h' b)) ⇒
    ~ EVERY (λminipred. sem_var_atom minipred mv = SOME T) atoml
Proof
  Induct >-
   gvs[mk_substitute_row_def, simp_row_old_def] >>
  rpt strip_tac >>

  Cases_on ‘atoml=[]’ >> gvs[] >| [
    gvs[EVERY_MEM] >>
    gvs[mk_substitute_row_def, simp_row_old_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
    imp_res_tac subst_simp_sound_for_atom >> gvs[]
    ,

    rgs[Once mk_substitute_row_def, Once simp_row_old_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >|[
        imp_res_tac subst_simp_sound_for_atom >> gvs[]
        ,
        gvs[EVERY_MAP] >>
        imp_res_tac sem_var_atom_failure_from_simp_atom_false
      ]
  ]
QED




Theorem subst_simp_miss_implies_sem_miss:
  ∀ atoml h' b mv st_num s_in.
    ALOOKUP mv h' = SOME b ∧
    ¬is_hit s_in st_num (simp_row_old (mk_substitute_row atoml h' b)) ∧
    all_false (simp_row_old (mk_substitute_row atoml h' b)) ⇒
    ¬is_match_row s_in st_num atoml mv
Proof
  rpt strip_tac >>
  gvs[all_false_def, is_match_row_def, is_hit_def] >>
  gvs[is_atoml_true_def] >-
   imp_res_tac every_simp_false_imp_sem_false >>
  gvs[mk_substitute_row_def, simp_row_old_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[])
QED





Theorem index_find_agreement_under_subst_and_all_false_prefix:
∀ tbl (s_in:num) n st_num st_num' res q (res':'a action_expr) h' b mv.
  ALOOKUP mv h' = SOME b ∧
EVERY (λ(atoml,st_num',res'). st_num' = s_in ⇒ all_false atoml)
               (SEG n 0
                  (MAP
                     ((λ(atoml,st_num,res). (simp_row_old atoml,st_num,res)) ∘
                      (λ(atoml,st_num,res).
                           (mk_substitute_row atoml h' b,st_num,res))) tbl)) ∧
INDEX_FIND 0 (λ(p,a). p)
               (MAP
                  (λ(atoml,st_num,res).
                       (is_match_row s_in st_num atoml mv,res)) tbl) =
             SOME (q − 1,T,res') ∧
INDEX_FIND 0 (λ(p,a). p)
               (MAP
                  ((λ(atoml,st_num,res).
                        (is_hit s_in st_num atoml,st_num,res)) ∘
                   (λ(atoml,st_num,res). (simp_row_old atoml,st_num,res)) ∘
                   (λ(atoml,st_num,res).
                        (mk_substitute_row atoml h' b,st_num,res))) tbl) =
             SOME (n,T,st_num,res) ⇒
res=res'
Proof

Induct >|[
    gvs[INDEX_FIND_def]
    ,
    rpt strip_tac >>
    PairCases_on ‘h’ >>
    gvs[INDEX_FIND_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >|[

        imp_res_tac hit_implies_match_after_subst
        ,
        Cases_on ‘h1 = s_in’ >|[
              Cases_on ‘q=0’ >> gvs[] >|[
                Cases_on ‘n’ >>
                gvs[SEG, SUC_ADD_ONE] >>
                gvs[GSYM TAKE_SEG] >>
                gvs[index_find_not_prev] >>
                imp_res_tac subst_simp_miss_implies_sem_miss
                ,
                ‘q=1’ by gvs[] >>
                gvs[] >>
                Cases_on ‘n’ >>
                gvs[SEG, SUC_ADD_ONE] >>
                gvs[GSYM TAKE_SEG] >>
                gvs[index_find_not_prev] >>
                imp_res_tac subst_simp_miss_implies_sem_miss
              ]

            ,
            gvs[is_hit_def, is_match_row_def]
          ]

        ,


        assume_tac (INST_TYPE [“:'a” |-> “:(bool # 'a action_expr)”,
                               “:'b” |-> “:num”] P_hold_on_next)  >>
        first_x_assum (strip_assume_tac o (Q.SPECL [‘0’,
         ‘(MAP (λ(atoml,st_num,res). (is_match_row (s_in:num) st_num atoml mv,res)) tbl)’,
         ‘(λ(p,a). p)’, ‘(q − 1,T,(res':α action_expr))’])) >>
        gvs[] >>





        assume_tac (INST_TYPE [“:'a” |-> “:(bool # num # 'a action_expr)”] P_hold_on_next)  >>
        first_x_assum (strip_assume_tac o (Q.SPECL [‘0’,
         ‘(MAP ((λ(atoml,st_num,res). (is_hit s_in st_num atoml,st_num,res)) ∘
                (λ(atoml,st_num,res). (simp_row_old atoml,st_num,res)) ∘
                (λ(atoml,st_num,res). (mk_substitute_row atoml h' b,st_num,res))) tbl)’,
         ‘(λ(p,a). p)’, ‘(n,T,st_num,res)’])) >>
        gvs[] >>



        imp_res_tac every_seg_property_3 >>
        last_x_assum (strip_assume_tac o (Q.SPECL [‘s_in’, ‘n-1’, ‘st_num’, ‘res’,
                                                   ‘q-1’ ,‘res'’, ‘h'’, ‘b’, ‘mv’])) >>
        gvs[]
      ]
]
QED








Theorem prop2_var_single_tbl_verbose:
  ∀ tbl mv h' b res s_in.
    ALOOKUP mv h' = SOME b ∧
    final_tbl_old  (simp_tbl (mk_substitute_tbl tbl h' b)) s_in = SOME res ⇒
    match_tbl tbl mv s_in = SOME res
Proof

  Cases_on ‘tbl’ >| [
    gvs[fv_tbl_def, mk_substitute_tbl_def, simp_tbl_def, final_tbl_old_def,
        min_idx_till_def, is_hit_tbl_check_def, INDEX_FIND_def]
    ,
    rpt strip_tac >>
    gvs[mk_substitute_tbl_def, simp_tbl_def, final_tbl_old_def] >>
    gvs[match_tbl_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>

    rename1 ‘(idx,bool,st_num,res)’ >>
    PairCases_on ‘h’ >>
    gvs[is_hit_tbl_check_def, check_all_rows_match_def] >>
    gvs[min_idx_till_def] >|[


        gvs[INDEX_FIND_def] >>
        rpt (BasicProvers.FULL_CASE_TAC >> gvs[])  >|[
          imp_res_tac hit_implies_match_after_subst
          ,
          imp_res_tac INDEX_FIND_NONE_EXISTS >>
          imp_res_tac exists_index_some >>
          gvs[EXISTS_MAP] >>
          gvs[MAP_MAP_o] >>
          imp_res_tac row_miss_preserved_by_subst_simp
        ]
        ,


        gvs[INDEX_FIND_def] >>
        rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >|[
            imp_res_tac hit_implies_match_after_subst
            ,

            gvs[pre_lines_are_fail_def] >>
            Cases_on ‘idx’ >>
            gvs[SEG, SUC_ADD_ONE] >>
            gvs[GSYM TAKE_SEG] >| [
                gvs[index_find_not_prev]
                ,
                Cases_on ‘h1 = s_in’ >|[
                    imp_res_tac subst_simp_miss_implies_sem_miss >>
                    gvs[]
                    ,
                    gvs[is_hit_def, is_match_row_def]
                  ]
              ]
            ,


            gvs[pre_lines_are_fail_def] >>
            Cases_on ‘idx’ >>
            gvs[SEG, SUC_ADD_ONE] >>
            gvs[GSYM TAKE_SEG] >>
            gvs[index_find_not_prev] >>
            PairCases_on ‘r’ >> gvs[] >>

            Cases_on ‘h1=s_in’ >|[


                assume_tac (INST_TYPE [“:'a” |-> “:(bool # 'a action_expr)”,
                                       “:'b” |-> “:num”] P_hold_on_next)  >>
                first_x_assum (strip_assume_tac o (Q.SPECL [‘0’,
                               ‘(MAP (λ(atoml,st_num,res). (is_match_row (h1:num) st_num atoml mv,res)) t)’,
                               ‘(λ(p,a). p)’, ‘(q,r0,r1)’])) >>
                gvs[] >>

                assume_tac (INST_TYPE [“:'a” |-> “:(bool # num # 'a action_expr)”] P_hold_on_next)  >>
                first_x_assum (strip_assume_tac o (Q.SPECL [‘0’,
                               ‘(MAP (λ(atoml,st_num,res). (is_hit h1 st_num atoml,st_num,res))
                                (MAP (λ(atoml,st_num,res). (simp_row_old atoml,st_num,res))
                                (MAP (λ(atoml,st_num,res). (mk_substitute_row atoml h' b,st_num,res)) t)))’,
                               ‘(λ(p,a). p)’, ‘(n + 1,bool,st_num,res)’])) >>


                gvs[] >>


                ‘(λ(p,a). p) (bool,st_num,res)’ by imp_res_tac INDEX_FIND_EQ_SOME_0 >>
                ‘(λ(p,a). p) (r0,r1)’ by imp_res_tac INDEX_FIND_EQ_SOME_0 >>

                gvs[] >>


                gvs[MAP_MAP_o] >>
                imp_res_tac index_find_agreement_under_subst_and_all_false_prefix >>
                gvs[]

                ,

                assume_tac (INST_TYPE [“:'a” |-> “:(bool # 'a action_expr)”,
                                       “:'b” |-> “:num”] P_hold_on_next)  >>
                first_x_assum (strip_assume_tac o (Q.SPECL [‘0’,
                               ‘(MAP (λ(atoml,st_num,res). (is_match_row (s_in:num) st_num atoml mv,res)) t)’,
                               ‘(λ(p,a). p)’, ‘(q,r0,r1)’])) >>
                gvs[] >>

                assume_tac (INST_TYPE [“:'a” |-> “:(bool # num # 'a action_expr)”] P_hold_on_next)  >>
                first_x_assum (strip_assume_tac o (Q.SPECL [‘0’,
                           ‘(MAP (λ(atoml,st_num,res). (is_hit s_in st_num atoml,st_num,res))
                            (MAP (λ(atoml,st_num,res). (simp_row_old atoml,st_num,res))
                            (MAP (λ(atoml,st_num,res). (mk_substitute_row atoml h' b,st_num,res)) t)))’,
                           ‘(λ(p,a). p)’, ‘(n + 1,bool,st_num,res)’])) >>


                gvs[] >>


                ‘(λ(p,a). p) (bool,st_num,res)’ by imp_res_tac INDEX_FIND_EQ_SOME_0 >>
                ‘(λ(p,a). p) (r0,r1)’ by imp_res_tac INDEX_FIND_EQ_SOME_0 >>

                gvs[] >>


                gvs[MAP_MAP_o] >>
                imp_res_tac index_find_agreement_under_subst_and_all_false_prefix >>
                gvs[]
              ]
          ]
      ]
  ]
QED






Theorem prop2_var_tables_old_verbose:
  ∀ tbls h b mv s_in res.
    ALOOKUP mv h = SOME b ∧
    final_tbll_old (simp_tbll (mk_substitute_tbll tbls h b)) s_in = SOME res ⇒
    sem_tables (tbls,s_in) mv = SOME res
Proof

  Induct_on ‘tbls’ >> rpt strip_tac >-
   gvs[mk_substitute_tbll_def, simp_tbll_def, final_tbll_old_def] >>
  rename1 ‘(tbl::tbll)’ >>


  Cases_on ‘tbll’ >> gvs[] >|[

    gvs[sem_tables_def, match_tbll_def] >>
    gvs[mk_substitute_tbll_def, simp_tbll_def, final_tbll_old_def] >>
    gvs[] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>

    imp_res_tac prop2_var_single_tbl_verbose >> gvs[]
    ,
    rename1 ‘(tbl::nexttbl::tbll)’ >>
    rgs[Once mk_substitute_tbll_def, Once simp_tbll_def] >>
    rgs[Once final_tbll_old_def] >>

    Cases_on ‘final_tbl_old  (simp_tbl (mk_substitute_tbl tbl h' b)) s_in’ >>
    gvs[] >>
    Cases_on ‘x’ >>
    gvs[] >>

    rgs[Once mk_substitute_tbll_def, Once simp_tbll_def] >>
    rgs[Once final_tbll_old_def] >>
    res_tac >>

    gvs[sem_tables_def, match_tbll_def] >>
    gvs[mk_substitute_tbll_def, simp_tbll_def, final_tbll_old_def] >>
    gvs[] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>

    imp_res_tac prop2_var_single_tbl_verbose >> gvs[]
  ]
QED



Theorem prop2_var_tables_old:
  prop2 table_structure_old
Proof
  rgs[prop2_def, table_structure_old_def, fv_in_p_def] >>

  rpt strip_tac >>
  Cases_on ‘p’ >>
  rename1 ‘(tbls, s_in)’ >>

  gvs[final_tables_old_def, fv_tables_def, mk_substitute_tables_def, simp_tables_old_def] >>
  imp_res_tac prop1_var_tables_old_verbose >> gvs[] >>
  imp_res_tac prop2_var_tables_old_verbose >> gvs[]
QED



Theorem hit_implies_match_after_all:
  ∀ atoml s_in st_num h' b mv.
    is_hit s_in st_num atoml ⇒
    is_match_row s_in st_num atoml mv
Proof
  Induct_on ‘atoml’ >>
  rpt strip_tac >>
  gvs[is_hit_def, is_match_row_def] >>
  gvs[is_atoml_true_def,all_true_def] >>
  res_tac >>
  Cases_on ‘atoml=[]’ >>
  gvs[sem_var_atom_def]
QED



Theorem subst_simp_miss_implies_sem_miss_full:
  ∀ atoml h' b mv s_in st_num .
    ¬is_hit s_in st_num (simp_row_old (mk_substitute_row atoml h' b)) ∧
    all_false (simp_row_old (mk_substitute_row atoml h' b)) ⇒
    ¬is_match_row s_in st_num  (simp_row_old (mk_substitute_row atoml h' b)) mv
Proof
  Induct >>
  rpt strip_tac >>
  gvs[all_false_def, is_match_row_def, is_hit_def] >>
  gvs[is_atoml_true_def, all_true_def] >>
  gvs[mk_substitute_row_def, simp_row_old_def] >>
  res_tac >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[mk_substitute_row_def, simp_row_old_def, sem_var_atom_def]
QED





Theorem match_follows_hit_at_minimal_index:
  ∀ tbl s_in idx  bool  st_num res mv h' b.
    pre_lines_are_fail (simp_tbl (mk_substitute_tbl tbl h' b)) idx s_in ∧
    min_idx_till (is_hit_tbl_check (simp_tbl (mk_substitute_tbl tbl h' b)) s_in) T =
    SOME (idx,bool,st_num,res)  ⇒
    min_idx_till (check_all_rows_match s_in (simp_tbl (mk_substitute_tbl tbl h' b)) mv) T =
    SOME (idx,bool,res)
Proof
  gvs[min_idx_till_def] >>
  Induct >>
  rpt strip_tac >-
   gvs[mk_substitute_tbl_def, check_all_rows_match_def, simp_tbl_def,
       is_hit_tbl_check_def, INDEX_FIND_def] >>


  PairCases_on ‘h’ >>
  gvs[simp_tbl_def, mk_substitute_tbl_def, is_hit_tbl_check_def] >>
  gvs[INDEX_FIND_def]>>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >|[

    gvs[check_all_rows_match_def, INDEX_FIND_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[])>>
    imp_res_tac hit_implies_match_after_all >>
    gvs[]
    ,

    gvs[check_all_rows_match_def, INDEX_FIND_def]>>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >|[

        gvs[pre_lines_are_fail_def] >>
        Cases_on ‘idx’ >>
        gvs[SEG, SUC_ADD_ONE] >>
        gvs[GSYM TAKE_SEG] >>
        gvs[index_find_not_prev] >>

        Cases_on ‘h1 = s_in’ >> gvs[] >>
        imp_res_tac subst_simp_miss_implies_sem_miss_full >> gvs[is_hit_def, is_match_row_def]

        ,
        gvs[MAP_MAP_o] >>
        gvs[pre_lines_are_fail_def] >>
        Cases_on ‘idx’ >>
        gvs[SEG, SUC_ADD_ONE] >>
        gvs[GSYM TAKE_SEG] >>
        gvs[index_find_not_prev] >>



        assume_tac (INST_TYPE [“:'a” |-> “:(bool # num # 'a action_expr)”] P_hold_on_next)  >>
        first_x_assum (strip_assume_tac o (Q.SPECL [‘0’,
            ‘(MAP ((λ(atoml,st_num,res). (is_hit s_in st_num atoml,st_num,res)) ∘
              (λ(atoml,st_num,res). (simp_row_old atoml,st_num,res)) ∘
              (λ(atoml,st_num,res). (mk_substitute_row atoml h' b,st_num,res))) tbl)’,
            ‘(λ(p,a). p)’, ‘(n + 1,bool,st_num,res)’])) >>
          gvs[] >>


        res_tac >>
        first_x_assum (strip_assume_tac o (Q.SPECL [‘mv’])) >>
        drule P_implies_next >>
        gvs[]
  ]
]
QED




Theorem final_tbl_old_yields_match_tbl:
  ∀ tbl s_in mv res h' b.
    final_tbl_old  (simp_tbl (mk_substitute_tbl tbl h' b)) s_in = SOME res ⇒
    match_tbl (simp_tbl (mk_substitute_tbl tbl h' b)) mv s_in = SOME res
Proof
  rpt strip_tac >>
  gvs[final_tbl_old_def, match_tbl_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  imp_res_tac match_follows_hit_at_minimal_index >> gvs[]
QED


Theorem final_tbll_old_yields_match_tbll:
  ∀ tbll s_in h b mv q .
    final_tbll_old (simp_tbll (mk_substitute_tbll tbll h b)) s_in = SOME q ⇒
    match_tbll (simp_tbll (mk_substitute_tbll tbll h b))  mv s_in = SOME q
Proof

  Induct >-
   (gvs[mk_substitute_tbll_def, simp_tbll_def, final_tbll_old_def]) >>


  rpt strip_tac >>
  Cases_on ‘tbll’ >|[
    simp[match_tbll_def] >>
    gvs[mk_substitute_tbll_def, simp_tbll_def, final_tbll_old_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
    imp_res_tac final_tbl_old_yields_match_tbl >> gvs[match_tbll_def]
    ,

    gvs[mk_substitute_tbll_def, simp_tbll_def, final_tbll_old_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
    res_tac >>

    gvs[match_tbll_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
    imp_res_tac final_tbl_old_yields_match_tbl >> gvs[match_tbll_def]
  ]
QED




Theorem prop3_var_tables_old:
  prop3 table_structure_old
Proof
  rgs[prop3_def, table_structure_old_def, fv_in_p_def] >>

  rpt strip_tac >>
  Cases_on ‘p’ >>
  rename1 ‘(tbls, s_in)’ >>
  gvs[final_tables_old_def, simp_tables_old_def, mk_substitute_tables_def, sem_tables_def] >>
  imp_res_tac final_tbll_old_yields_match_tbll >> gvs[]
QED






Theorem fv_mem_tbll_varslist_thm:
  ∀ tbll tbl varslist.
    (∀x. MEM x (fv_tbll (tbl::tbll)) ⇒ MEM x varslist) ⇒
    (∀x. MEM x (fv_tbll  tbll) ⇒  MEM x varslist)
Proof
  gvs[fv_tbll_def]
QED



Theorem free_vars_simp_subst_in_original:
  ∀ atom h' b x.
    MEM x (fv_atom (simp_atom (mk_substitute_atom atom h' b))) ⇒
    MEM x (fv_atom atom)
Proof
  Induct >>
  gvs[fv_atom_def, simp_atom_def, mk_substitute_atom_def] >>
  rpt strip_tac >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[fv_atom_def, simp_atom_def, mk_substitute_atom_def]
QED



Theorem free_vars_simp_subst_row_in_original:
  ∀ row h' b x.
    MEM x (fv_row (simp_row_old (mk_substitute_row row h' b))) ⇒
    MEM x (fv_row row)
Proof
  Induct >>
  gvs[fv_row_def, simp_row_old_def, mk_substitute_row_def] >>
  rpt strip_tac >>
  gvs[MEM_FLAT] >>
  res_tac >>
  first_x_assum (strip_assume_tac o (Q.SPECL [‘h'’, ‘b’])) >>
  gvs[] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[fv_atom_def]) >>
  gvs[MEM_MAP] >> gvs[fv_atom_def] >>
  imp_res_tac free_vars_simp_subst_in_original >> gvs[] >>
  DISJ2_TAC >> gvs[] >>
  metis_tac[]
QED




Theorem free_vars_simp_subst_tbl_in_original:
  ∀ tbl x h' b.
    MEM x (fv_tbl (simp_tbl (mk_substitute_tbl tbl h' b))) ⇒
    MEM x (fv_tbl tbl)
Proof
  Induct >>
  rpt strip_tac >>
  gvs[fv_tbl_def, mk_substitute_tbl_def, simp_tbl_def] >|[
    PairCases_on ‘h’ >> gvs[] >>
    imp_res_tac free_vars_simp_subst_row_in_original >>
    gvs[]
    ,
    res_tac >> gvs[]
  ]
QED


Theorem free_vars_simp_subst_tbll_in_original:
  ∀ tbls h b x varslist.
    (∀x'. MEM x' (fv_tbll tbls) ⇒ MEM x' varslist) ∧
    MEM x (fv_tbll (simp_tbll (mk_substitute_tbll tbls h b))) ⇒
    MEM x varslist
Proof
  Induct >-
   (gvs[fv_tbll_def, mk_substitute_tbll_def, simp_tbll_def]) >>

  rpt strip_tac >>
  gvs[mk_substitute_tbll_def, simp_tbll_def] >>
  imp_res_tac fv_mem_tbll_varslist_thm >>
  res_tac >>
  gvs[fv_tbll_def] >|[
    imp_res_tac free_vars_simp_subst_tbl_in_original >>
    gvs[]
    ,
    metis_tac[]
  ]
QED



Theorem prop4_var_tables_old:
  prop4 table_structure_old
Proof
  rgs[prop4_def, table_structure_old_def, fv_in_p_def, fv_in_vars_def] >>

  rpt strip_tac >>
  Cases_on ‘prop_parent’ >>
  rename1 ‘(tbls, s_in)’ >>
  gvs[fv_tables_def, simp_tables_old_def, mk_substitute_tables_def] >>
  imp_res_tac free_vars_simp_subst_tbll_in_original
QED





val _ = export_theory ();


