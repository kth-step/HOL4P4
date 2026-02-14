open HolKernel boolLib simpLib Parse bossLib;

open p4_auxTheory;
open pairTheory;
open listTheory;
open rich_listTheory;
open alistTheory;

open pred_specTheory;
open policy_specTheory;
open policy_arith_to_varTheory;

val _ = new_theory "policy_var_to_arith";

(* mainly to create a minimal policy, 
we need policy to be output as well,
this file translate it from var-based, or ILR to output.
we need this file to translate back to arithmetic*)



Definition pred_v2a_def:
  (pred_v2a me (Var v) =
    case ALOOKUP me v of
      SOME atom => SOME (arith_a atom)
    | NONE => NONE) ∧
  (pred_v2a me (True) = SOME (arith_a a_True)) ∧
  (pred_v2a me (False) = SOME (arith_a a_False)) ∧
  (pred_v2a me (Not p) =
    case pred_v2a me p of
      SOME p' => SOME (arith_not p')
    | NONE => NONE) ∧
  (pred_v2a me (And p1 p2) =
    case (pred_v2a me p1, pred_v2a me p2) of
      (SOME p1', SOME p2') => SOME (arith_and p1' p2')
    | _ => NONE) ∧
  (pred_v2a me (Or p1 p2) =
    case (pred_v2a me p1, pred_v2a me p2) of
      (SOME p1', SOME p2') => SOME (arith_or p1' p2')
    | _ => NONE) ∧
  (pred_v2a me (Implies p1 p2) =
    case (pred_v2a me p1, pred_v2a me p2) of
      (SOME p1', SOME p2') => SOME (arith_imp p1' p2')
    | _ => NONE)
End


Definition all_convertable_to_arith_def:
  all_convertable_to_arith m_e policy =
  EVERY (λ(pred,_). pred_v2a m_e pred ≠ NONE) policy
End


Definition convert_var_to_arith_policy_def:
  convert_var_to_arith_policy policy m_e =
    if all_convertable_to_arith m_e policy then
      SOME (MAP (λ(pred,act). (THE (pred_v2a m_e pred), act)) policy)
    else
      NONE
End


Theorem pred_conversion_preserves_semantics2_thm:
  ∀ arith_pred var_pred m_e packet_input m_v.
    ALL_DISTINCT (MAP FST m_e) ∧
    ALL_DISTINCT (MAP SND  m_e) ∧
    (∀var atom.
       ALOOKUP m_e var = SOME atom ⇒
       ALOOKUP m_v var = eval_arithm_atom packet_input atom) ∧
    pred_v2a m_e var_pred = SOME arith_pred
    ⇒
    eval_pred_w_str packet_input arith_pred = sem_pred var_pred m_v
Proof

  Induct_on ‘var_pred’ >> rw[pred_v2a_def, eval_pred_w_str_def] >>

   rpt (BasicProvers.FULL_CASE_TAC >>
        gvs[eval_arithm_atom_def, sem_pred_def, eval_pred_w_str_def]) >>

  res_tac >>
   rw[] >>
   gvs[eval_arithm_atom_def, sem_pred_def]
QED


Theorem policy_var_to_arith_sem_conversion_correct:
∀ arith_policy var_policy.
  ∀ m_e packet_input m_v.
    (ALL_DISTINCT (MAP FST m_e) ∧
     ALL_DISTINCT (MAP SND m_e)) ∧
    (∀var atom.
       ALOOKUP m_e var = SOME atom ⇒
       ALOOKUP m_v var = eval_arithm_atom packet_input atom) ∧
    (convert_var_to_arith_policy var_policy m_e = SOME arith_policy)
    ⇒
    sem_arith_policy arith_policy packet_input =
    sem_policy var_policy m_v
Proof
  rw[sem_arith_policy_def, sem_policy_def] >>

  ‘check_arith_pred_sem arith_policy packet_input = check_sem_pred var_policy m_v’
    suffices_by rw[] >>

  fs[convert_var_to_arith_policy_def] >>
  rw[check_arith_pred_sem_def, check_sem_pred_def] >>

  rw[MAP_MAP_o] >>
  rw[combinTheory.o_DEF] >>

  rw[MAP_EQ_f] >>
  Cases_on ‘x’ >> rw[] >>
  rename1 ‘(pred, act)’ >>

  ‘pred_v2a m_e pred ≠ NONE’ by (
    fs[all_convertable_to_arith_def, EVERY_MEM] >>
    rgs[ELIM_UNCURRY] >>
    res_tac >>
    fs[FST]
  ) >>

  Cases_on ‘pred_v2a m_e pred’ >> gvs[] >>
  metis_tac[pred_conversion_preserves_semantics2_thm]
QED



val _ = export_theory ();
