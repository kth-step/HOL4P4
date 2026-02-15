open HolKernel boolLib simpLib Parse bossLib;

open p4_auxTheory;

open listTheory;
open rich_listTheory;
open alistTheory;
open arithmeticTheory;

open bdd_genTheory;
open pred_specTheory;



val _ = new_theory "policy_spec";


(* rule datatype *)
Type rule = “:(pred#'a)”;
Type policy = “: ('a rule) list”



(**************************************************)
(* specialized definitions for a predicate record *)
(*   here 'a would be policy and 'b would be action *)
(**************************************************)

Definition check_sem_pred_def:
  check_sem_pred (policy: 'a policy) mv =
  MAP (\(pred,a). (sem_pred pred mv, a) )  policy
End


Definition min_idx_till_def:
  min_idx_till res t =
  INDEX_FIND 0 (\(p,a). p = t) res
End


Definition sem_policy_def:
  sem_policy (policy: 'a policy) mv =
  let res = check_sem_pred policy mv in
    case min_idx_till res (SOME T) of
    | SOME (idx,rule) => SOME (SND rule)
    | NONE => NONE
End


(* policy substitute *)
Definition mk_substitute_policy_def:
  mk_substitute_policy (policy: 'a policy) x b =
  MAP (\(pred,a). (mk_substitute_pred pred x b,a)) policy
End


(* policy simplifications *)
Definition simp_policy_def:
  simp_policy (policy: 'a policy) =
  MAP (\(pred,a). (simp_pred pred,a)) policy
End


Definition pre_are_fail_def:
  pre_are_fail (policy: 'a policy) idx =
  EVERY (\(pred,a). pred = False)  (SEG idx 0 policy)
End


Definition final_policy_def:
  final_policy (policy: 'a policy) =
  case min_idx_till policy (True) of
  | SOME (idx,a) => (
    case (pre_are_fail (policy: 'a policy) idx) of
      | T  => SOME (SND a)
      | F => NONE
    )
  | NONE => NONE
End


(*
EVAL “SEG 3 0 [T;T;T;F]”
EVAL “sem_policy [(False,"a1"); (Or True False,"a2"); (True,"a3")] []”
EVAL “final_policy [(False,"a1"); (Or True False,"a2"); (True,"a3")]”
EVAL “final_policy (simp_policy ([(False,"a1"); (Or True False,"a2"); (True,"a3")]))”
*)

Definition fv_policy_def:
  fv_policy (policy: 'a policy) =
  let fv_rules = MAP (\(pred,a). fv_pred pred) policy in
    nub(FLAT fv_rules)
End


Definition policy_structure_def:
  policy_structure =
  <|
    sem := sem_policy;
    sub := mk_substitute_policy;
    simp := simp_policy;
    final := final_policy;
    fv := fv_policy;
  |>
End


(*
EVAL “mk_BDDPred pred_structure (0,[],[(0, non_termn (NONE, (Or (Var "a") (Not (Var "a")))))]) [] ["a"] 1”;
EVAL “mk_BDDPred pred_structure (0,[],[(0, non_termn (NONE, True))]) [] ["a"] 1”;
*)


Theorem fv_mem_policy:
  ∀ pl pred action x.
    MEM x (fv_policy pl) ⇒
    MEM x (fv_policy ((pred,action)::pl))
Proof
  rpt strip_tac >>
  gvs[fv_policy_def]
QED



Theorem fv_mem_pred_policy:
  ∀ pl pred action x.
    MEM x (fv_policy [(pred,action)]) ⇒
    MEM x (fv_policy ((pred,action)::pl))
Proof
  rpt strip_tac >>
  gvs[fv_policy_def]
QED



Theorem fv_mem_policy_thm:
  ∀ pl pred action mv.
    (∀x. MEM x (fv_policy ((pred,action)::pl)) ⇒ ∃b. ALOOKUP mv x = SOME b) ⇒
    (∀x. MEM x (fv_policy pl) ⇒ ∃b. ALOOKUP mv x = SOME b)
Proof
  rpt strip_tac >>
  gvs[fv_mem_policy]
QED



Theorem fv_mem_policy_hd_thm:
  ∀ pl pred action mv.
    (∀x. MEM x (fv_policy ((pred,action)::pl)) ⇒ ∃b. ALOOKUP mv x = SOME b) ⇒
    (∀x. MEM x (fv_policy [(pred,action)]) ⇒ ∃b. ALOOKUP mv x = SOME b)
Proof
  rpt strip_tac >>
  first_x_assum (strip_assume_tac o (Q.SPECL [‘x’])) >>
  imp_res_tac fv_mem_pred_policy >>
  metis_tac[]
QED



Triviality fv_mem_single_policy_imp_pred:
  ∀ pl pred action mv.
    (∀x. MEM x (fv_policy [(pred,action)]) ⇒ ∃b. ALOOKUP mv x = SOME b) ⇒
    (∀x. MEM x (fv_pred pred) ⇒ ∃b. ALOOKUP mv x = SOME b)
Proof
  gvs[fv_policy_def]
QED



Theorem sem_policy_all_none:
  ∀ rules pred action mv.
    sem_policy ((pred,action)::rules) mv = NONE ⇒
    sem_policy [(pred,action)] mv = NONE ∧
    sem_policy rules mv = NONE
Proof
  rpt strip_tac >>
  gvs[sem_policy_def, min_idx_till_def, check_sem_pred_def, sem_pred_def] >>
  gvs[AllCaseEqs()] >>
  gvs[INDEX_FIND_def] >>
  gvs[AllCaseEqs()] >>
  imp_res_tac P_NONE_hold2
QED



Theorem sem_policy_some_before_imp_exsists:
  ∀ rules pred action mv b.
    sem_policy rules mv = SOME b ⇒
    ∃b'. sem_policy ((pred,action)::(rules)) mv = SOME b'
Proof
  rpt strip_tac >>
  gvs[sem_policy_def, min_idx_till_def, check_sem_pred_def, sem_pred_def] >>
  gvs[AllCaseEqs()] >>
  gvs[INDEX_FIND_def] >>
  gvs[AllCaseEqs()] >>
  Cases_on ‘sem_pred pred mv’ >> gvs[] >>
  imp_res_tac P_implies_next >>
  gvs[ADD1] >>
  Cases_on ‘x’ >> gvs[]
QED



(* We have to assume that indeed we have drop at the end in case nothing matches*)
Theorem mem_imp_sem_policy:
  ∀pl pl' a mv.
    pl = pl'++[(True,a)] ∧
    (∀x. MEM x (fv_policy pl) ⇒ (∃b. ALOOKUP mv x = SOME b)) ⇒
         sem_policy pl mv ≠ NONE ∧ ∃ b' . sem_policy pl mv = SOME b'
Proof
  Induct >-
   rw[simp_policy_def, fv_policy_def, sem_policy_def, check_sem_pred_def, min_idx_till_def] >>
  gvs[AllCaseEqs()] >>
  rpt strip_tac >>

  PairCases_on ‘h’ >>
  rename1‘(pred,action)::pl’ >>
  imp_res_tac fv_mem_policy_thm >>
  res_tac >>

  (Cases_on ‘pl'’ >> gvs[] >|[
      gvs[sem_policy_def, min_idx_till_def, check_sem_pred_def, sem_pred_def] >>
      gvs[AllCaseEqs()] >>
      gvs[INDEX_FIND_def]
      ,
      res_tac >>
      imp_res_tac sem_policy_all_none >>
      imp_res_tac sem_policy_some_before_imp_exsists >>
      metis_tac[]
    ])

QED



Theorem simp_policy_cons:
  ∀ pl pred action .
    simp_policy ((pred,action)::pl) = simp_policy [(pred,action)] ++ simp_policy pl
Proof
  rpt strip_tac >>
  gvs[simp_policy_def]
QED



Theorem check_sem_pred_cons:
  ∀ pl pred action mv.
    check_sem_pred ((pred,action)::pl) mv = (check_sem_pred [(pred,action)] mv) ++ (check_sem_pred pl mv)
Proof
  rpt strip_tac >>
  gvs[check_sem_pred_def]
QED



Theorem check_sem_pred_concat:
  ∀ pl pl' mv.
    check_sem_pred (pl ++ pl') mv = (check_sem_pred pl mv) ++ (check_sem_pred pl' mv)
Proof
  rpt strip_tac >>
  gvs[check_sem_pred_def]
QED



Triviality mk_substitute_policy_normalize:
  ∀ pred action pl h b.
    mk_substitute_policy ((pred,action)::pl) h b =
    (mk_substitute_pred pred h b,action)::(mk_substitute_policy pl h b)
Proof
  gvs[mk_substitute_policy_def]
QED



Triviality simp_policy_normalize:
  ∀ pred action pl.
  simp_policy ((pred,action)::pl) = (simp_pred pred,action)::(simp_policy pl)
Proof
  gvs[simp_policy_def]
QED



Theorem property_1_policy_reverse_normalize:
  ∀ pred action pl h' b mv.
    (sem_pred (simp_pred (mk_substitute_pred pred h' b)) mv = sem_pred pred mv) ∧
    (sem_policy (simp_policy (mk_substitute_policy pl h' b)) mv =  sem_policy pl mv) ⇒
    (sem_policy
     ((simp_pred (mk_substitute_pred pred h' b),action):: simp_policy (mk_substitute_policy pl h' b)) mv =
     sem_policy ((pred,action)::pl) mv)
Proof
  rpt strip_tac >>
  gvs[sem_policy_def] >>
  gvs[min_idx_till_def, check_sem_pred_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  (gvs[INDEX_FIND_def] >>
   rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
   gvs[P_NONE_hold] >>
   imp_res_tac P_NONE_hold2 >>
   gvs[] ) >>

  PairCases_on ‘r’ >>
  PairCases_on ‘r'’ >>
  PairCases_on ‘r''’ >>
  PairCases_on ‘r'''’ >>

  imp_res_tac P_current_next_same >>
  gvs[]
QED




Theorem prop1_policy:
  prop1 policy_structure
Proof
  gvs[prop1_def] >>
  gvs[fv_in_p_def, policy_structure_def] >>
  Induct_on ‘p’ >-
   gvs[mk_substitute_policy_def, simp_policy_def] >>
  rpt strip_tac >>
  Cases_on ‘h’ >> gvs[] >>
  rename1 ‘(pred,action)’ >>
  imp_res_tac fv_mem_policy_thm >>
  res_tac >>

  imp_res_tac fv_mem_policy_hd_thm >>
  imp_res_tac fv_mem_single_policy_imp_pred >>


  rename1 ‘sem_policy ((pred,action)::pl) mv’ >>
  simp[mk_substitute_policy_normalize] >>
  simp[simp_policy_normalize] >>


  assume_tac prop1_pred >>
  gvs[prop1_def, pred_structure_def] >>
  gvs[fv_in_p_def] >>

  res_tac >>
  gvs[property_1_policy_reverse_normalize]
QED




Triviality neg_neg_prop:
  ∀ p. ($¬ ∘ $¬ ∘ p) = p
Proof
gvs[combinTheory.o_DEF] >>
gvs[ETA_THM]
QED



Triviality index_of_simp_sub_add1:
  ∀ l q' q r r'.
    INDEX_FIND 1 (λ(p,a). p = True) l = SOME (q',r') ∧
    INDEX_FIND 0 (λ(p,a). p = True) l = SOME (q,r) ⇒
    (q' = q + 1)
Proof
  rpt strip_tac >>
  imp_res_tac P_implies_next >>
  gvs[SUC_ADD_ONE]
QED



Theorem every_seg_property_1:
  ∀ i l h p.
    i < LENGTH l ∧
    EVERY p (SEG (i + 1) 0 (h::l)) ⇒
    EVERY p (SEG i 0 l)
Proof
  Induct >>
  rpt strip_tac >>
  gvs[SEG, SUC_ADD_ONE] >>
  gvs[GSYM TAKE_SEG]
QED



Theorem every_seg_property_2:
  ∀ i l h p.
    i < LENGTH l ∧
    EVERY p (SEG (i + 1) 0 (h::l)) ⇒
    p h
Proof
  Induct >>
  rpt strip_tac >>
  gvs[SEG, SUC_ADD_ONE] >>
  gvs[GSYM TAKE_SEG]
QED



Triviality every_not_exsists_false_local:
  ∀ l .
    EVERY (λ(pred,a). pred = False) l ⇒
    ¬ EXISTS ($¬ ∘ (λ(pred,a). pred = False)) l
Proof
  Induct >>
  gvs[]
QED



Theorem index_find_in_seg_not_exists:
  ∀ l q r.
    q < LENGTH l ∧
    INDEX_FIND 0 (λ(p,a). p = True) l = SOME (q,r) ∧
    EVERY (λ(pred,a). pred = False) (SEG q 0 l)  ⇒
    ~ EXISTS ($¬ ∘ (λ(pred,a). pred = False)) (SEG q 0 l)
Proof
  rpt strip_tac >>
  gvs[NOT_EXISTS] >>
  gvs[] >>
  gvs[neg_neg_prop] >>
  gvs[every_not_exsists_false_local]
QED



Triviality idx_find_indeed_inp_not_empty:
  ∀ l p b i.
    INDEX_FIND 0 p l = SOME (i,b) ⇒
    l ≠ []
Proof
  Induct >>
  gvs[INDEX_FIND_def]
QED



(* TODO: make it a bit smaller -.- *)
Theorem property_2_policy_reverse_normalize:
  ∀ pl pred action h' b q mv.
    (final_policy (simp_policy (mk_substitute_policy ((pred,action)::pl) h' b)) = SOME q) ∧
    (∀q'. final_policy (simp_policy (mk_substitute_policy pl h' b)) = SOME q' ⇒
         SOME q' = sem_policy pl mv) ∧
    (∀q''. final_pred (simp_pred (mk_substitute_pred pred h' b)) = SOME q'' ⇒
           SOME q'' = sem_pred pred mv)
    ⇒
    SOME q = sem_policy ((pred,action)::pl) mv

Proof

  rpt strip_tac >>

  gvs[mk_substitute_policy_normalize] >>
  gvs[simp_policy_normalize] >>


  gvs[sem_policy_def, final_policy_def] >>
  gvs[min_idx_till_def, check_sem_pred_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs [pre_are_fail_def] >|[

    gvs[INDEX_FIND_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >-
     gvs[final_pred_def] >>
    gvs[P_NONE_hold]
    ,

    gvs[INDEX_FIND_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >-
     gvs[final_pred_def] >>
    imp_res_tac index_of_simp_sub_add1 >>
    gvs[] >>
    ‘q' < LENGTH (simp_policy (mk_substitute_policy pl h' b))’ by gvs[INDEX_FIND_EQ_SOME_0] >>
    imp_res_tac every_seg_property_1 >>
    imp_res_tac index_find_in_seg_not_exists
    ,

    gvs[INDEX_FIND_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >-
     gvs[final_pred_def] >>
    imp_res_tac P_NONE_hold2 >>
    gvs[]
    ,

    gvs[INDEX_FIND_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >-
     gvs[final_pred_def] >>
    gvs[P_NONE_hold]
    ,

    gvs[INDEX_FIND_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >-
     gvs[final_pred_def] >>

    (imp_res_tac index_of_simp_sub_add1 >>
     gvs[] >>
     imp_res_tac P_implies_next >>
     gvs[SUC_ADD_ONE] >>
     ‘q'' < LENGTH (simp_policy (mk_substitute_policy pl h' b))’ by gvs[INDEX_FIND_EQ_SOME_0] >>
     imp_res_tac every_seg_property_1 >>
     imp_res_tac index_find_in_seg_not_exists
    )
    ,

    gvs[INDEX_FIND_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >-
     gvs[final_pred_def] >>

    imp_res_tac index_of_simp_sub_add1 >>
    gvs[] >>
    imp_res_tac P_implies_next >>
    gvs[SUC_ADD_ONE] >>
    ‘q'' < LENGTH (simp_policy (mk_substitute_policy pl h' b))’ by gvs[INDEX_FIND_EQ_SOME_0] >>
    imp_res_tac every_seg_property_1 >>
    res_tac >>

    PairCases_on ‘r'’ >>
    PairCases_on ‘r''’ >>
    gvs[] >>

    ‘(λ(p,a). p = SOME T) (r''0,r''1)’ by  imp_res_tac INDEX_FIND_EQ_SOME_0 >>
    ‘(λ(p,a). p = True) (r'0,r''1)’ by  imp_res_tac INDEX_FIND_EQ_SOME_0 >>
    gvs[] >>

    first_x_assum (strip_assume_tac o (Q.SPECL [‘F’])) >> gvs[] >>
    imp_res_tac every_seg_property_2 >>
    gvs[final_pred_def]

  ]
QED




Theorem prop2_policy:
  prop2 policy_structure
Proof
  gvs[prop2_def] >>
  gvs[fv_in_p_def, policy_structure_def] >>
  Induct_on ‘p’ >-
   gvs[sem_policy_def, check_sem_pred_def, min_idx_till_def, INDEX_FIND_def,
       mk_substitute_policy_def, simp_policy_def, simp_policy_def,
       final_policy_def] >>

  rpt strip_tac >>
  Cases_on ‘h’ >> gvs[] >>
  rename1 ‘(pred,action)’ >>
  imp_res_tac fv_mem_policy_thm >>
  res_tac >>


  imp_res_tac fv_mem_policy_hd_thm >>
  imp_res_tac fv_mem_single_policy_imp_pred >>


  rename1 ‘sem_policy ((pred,action)::pl) mv’ >>

  assume_tac prop2_pred >>
  gvs[prop2_def, pred_structure_def] >>
  gvs[fv_in_p_def] >>

  res_tac >>
  imp_res_tac property_2_policy_reverse_normalize
QED




Theorem property_3_policy_reverse_normalize:
  ∀ l mv q.
    final_policy l = SOME q ⇒
    sem_policy l mv = SOME q
Proof
  Induct >>
  rpt strip_tac >-
   gvs[sem_policy_def, check_sem_pred_def, min_idx_till_def, INDEX_FIND_def,
       mk_substitute_policy_def, simp_policy_def, simp_policy_def,
       final_policy_def] >>


  gvs[final_policy_def, sem_policy_def] >>
  gvs[check_sem_pred_def, min_idx_till_def, pre_are_fail_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >| [

    Cases_on ‘h’ >> gvs[] >>
    rename1 ‘(pred,action)’ >>

    gvs[INDEX_FIND_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >-
     gvs[SEG,sem_pred_def] >>
    gvs[P_NONE_hold]
    ,

    Cases_on ‘h’ >> gvs[] >>
    rename1 ‘(pred,action)::l’ >>

    gvs[INDEX_FIND_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >-
     gvs[SEG,sem_pred_def] >>

    ‘q < LENGTH l’ by imp_res_tac INDEX_FIND_EQ_SOME_0 >>
    imp_res_tac index_of_simp_sub_add1 >> gvs[] >>
    imp_res_tac every_seg_property_1 >> gvs[] >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘mv’])) >>

    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>

    imp_res_tac P_NONE_hold2 >>
    gvs[]
    ,

    Cases_on ‘h’ >> gvs[] >>
    rename1 ‘(pred,action)’ >>

    gvs[INDEX_FIND_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >-
     gvs[SEG,sem_pred_def] >>
    gvs[P_NONE_hold]
    ,

    Cases_on ‘h’ >> gvs[] >>
    rename1 ‘(pred,action)::l’ >>

    gvs[INDEX_FIND_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >-
     gvs[SEG,sem_pred_def] >>

    ‘q < LENGTH l’ by imp_res_tac INDEX_FIND_EQ_SOME_0 >>
    imp_res_tac index_of_simp_sub_add1 >> gvs[] >>
    imp_res_tac every_seg_property_1 >> gvs[] >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘mv’])) >>

    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>

    PairCases_on ‘r’ >>
    PairCases_on ‘r'’ >>
    PairCases_on ‘r''’ >>
    gvs[] >| [

        ‘(λ(p,a). p = SOME T) (r0,r''1)’ by  imp_res_tac INDEX_FIND_EQ_SOME_0 >>
        ‘(λ(p,a). p = True) (r''0,r''1)’ by  imp_res_tac INDEX_FIND_EQ_SOME_0 >>
        gvs[] >>

        imp_res_tac every_seg_property_2 >>
        gvs[sem_pred_def]
        ,

        ‘(λ(p,a). p = SOME T) r'³'’ by  imp_res_tac INDEX_FIND_EQ_SOME_0 >>
        ‘(λ(p,a). p = True) (r''0,SND r'³')’ by  imp_res_tac INDEX_FIND_EQ_SOME_0 >>
        gvs[] >>
        PairCases_on ‘r'''’ >> gvs[] >>

        imp_res_tac index_of_simp_sub_add1 >> gvs[] >>
        imp_res_tac P_implies_next >>
        gvs[]
      ]
  ]
QED




Theorem prop3_policy:
  prop3 policy_structure
Proof
  gvs[prop3_def] >>
  gvs[fv_in_p_def, policy_structure_def] >>
  Induct_on ‘p’ >-
   gvs[sem_policy_def, check_sem_pred_def, min_idx_till_def, INDEX_FIND_def,
       mk_substitute_policy_def, simp_policy_def, simp_policy_def,
       final_policy_def] >>

  rpt strip_tac >>
  Cases_on ‘h’ >> gvs[] >>
  rename1 ‘(pred,action)’ >>
  imp_res_tac fv_mem_policy_thm >>
  res_tac >>

  rename1 ‘mk_substitute_policy ((pred,action)::pl) h' b’ >>

  assume_tac prop3_pred >>
  gvs[prop3_def, pred_structure_def] >>
  gvs[fv_in_p_def] >>

  res_tac >>
  imp_res_tac property_3_policy_reverse_normalize >> metis_tac[]
QED




Theorem fv_mem_policy_in_mv_thm:
  ∀ pl pred varslist action mv.
    (∀x. MEM x (fv_policy ((pred,action)::pl)) ⇒ MEM x varslist) ⇒
    (∀x'. MEM x' (fv_policy pl) ⇒ MEM x' varslist)
Proof
  rpt strip_tac >>
  gvs[fv_mem_policy]
QED



Theorem fv_mem_policy_in_mv_hd_thm:
  ∀ pl pred varslist action mv.
    (∀x. MEM x (fv_policy ((pred,action)::pl)) ⇒ MEM x varslist) ⇒
    (∀x'. MEM x' (fv_pred pred) ⇒ MEM x' varslist)
Proof
  rpt strip_tac >>
  gvs[fv_mem_policy, fv_policy_def]
QED



Theorem property_4_policy_reverse_normalize:
  ∀ pl pred action h x b varslist.
    MEM x (fv_policy (simp_policy (mk_substitute_policy ((pred,action)::pl) h b))) ∧
    (∀x' h b.    MEM x' (fv_policy (simp_policy (mk_substitute_policy pl h b))) ⇒
                MEM x' varslist) ∧
    (∀x'' h' b'.  MEM x'' (fv_pred (simp_pred (mk_substitute_pred pred h' b'))) ⇒
                MEM x'' varslist) ⇒
    MEM x varslist
Proof
  rpt strip_tac >>
  gvs[fv_policy_def] >>
  gvs[mk_substitute_policy_normalize] >>
  gvs[simp_policy_normalize] >>
  metis_tac[]
QED



Theorem prop4_policy:
  prop4 policy_structure
Proof
  gvs[prop4_def] >>
  rgs[prop4_def, policy_structure_def, fv_in_vars_def] >>
  Induct_on ‘prop_parent’ >-
   gvs[fv_policy_def, mk_substitute_policy_def, simp_policy_def] >>

  rpt strip_tac >>
  Cases_on ‘h’ >> gvs[] >>
  rename1 ‘(pred,action)::pl’ >>
  imp_res_tac fv_mem_policy_in_mv_thm >>
  res_tac >>

  imp_res_tac fv_mem_policy_in_mv_hd_thm >>

  assume_tac prop4_pred >>
  gvs[prop4_def, pred_structure_def] >>
  gvs[fv_in_vars_def] >>

  res_tac >>
  imp_res_tac property_4_policy_reverse_normalize
QED




val _ = export_theory ();


