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


val _ = new_theory "policy_arith_to_var";



val _ = Hol_datatype ` 
arith_lv = 
   lv_x of string             (* variable name *)
 | lv_acc of arith_lv => string     (* field access *)
(* | lv_bs of arith_lv => num => num  (* bit slicing *) *)
`;



val _ = Hol_datatype `
  arithm_atom = 
     a_True               (* T *)
   | a_False              (* F *)
   | arithm_gt of arith_lv => bitv  (* lval > v *)
   | arithm_lt of arith_lv => bitv  (* lval < v *)
   (*| arithm_eq of arith_lv => num  (* lval = v *)*) (* this will be added to input policy *)
`;


val _ = Hol_datatype `
  arith_pred = 
     arith_a of arithm_atom          
   | arith_not of arith_pred          
   | arith_and of arith_pred => arith_pred 
   | arith_or of arith_pred => arith_pred  
   | arith_imp of arith_pred => arith_pred 
`;


Type arith_rule = “:(arith_pred#'a)”;
Type arith_policy = “: ('a arith_rule) list”




val _ = Hol_datatype `
  pd_val = 
     val_bs of bitv   
   | val_record of (string # pd_val) list  (* [f1:val1; ...; fn:valn] *)
`;

Type pd = “: (string # pd_val) list”; 



Definition resolve_lval_def:
  (resolve_lval pd (lv_x var) = ALOOKUP pd var ) ∧
  (resolve_lval pd (lv_acc lval var) = 
    case resolve_lval pd lval of
    | SOME (val_record fields) => ALOOKUP fields var
    | _ => NONE)
End




(* note that here the bv and the other bv must be of same length *)
Definition eval_arithm_atom_def:
  (eval_arithm_atom pd a_True = SOME T) ∧
  (eval_arithm_atom pd a_False = SOME F) ∧
  (eval_arithm_atom pd (arithm_gt lval bv) = 
    case resolve_lval pd lval of
    | SOME (val_bs bv') => bitv_binpred binop_lt bv' bv
    | _ => NONE) ∧
  (eval_arithm_atom pd (arithm_lt lval bv) = 
    case resolve_lval pd lval of
      SOME (val_bs bv') => bitv_binpred binop_gt bv' bv
    | _ => NONE)
End



        
(*

val ttl_bv = “(n2v 64, LENGTH (n2v 10))”;
val version_bs = “(n2v 4, LENGTH (n2v 4))”;
val ether_bs = “(n2v 4, LENGTH (n2v 0x8080))”;
        
val example_pd = “[ ("h", val_record [
  ("ip", val_record [
   ("ttl", val_bs ^ttl_bv );
    ("version", val_bs ^version_bs)
     ]);
   ("ether", val_bs ^ether_bs)
  ])
]”;

val sixty_bs = “(n2v 60, LENGTH (n2v 10))”; 


val h_ip_ttl = “lv_acc (lv_acc (lv_x "h") "ip") "ttl"”;
val result1 = EVAL “resolve_lval ^example_pd ^h_ip_ttl”;  

val h_eth_src = “lv_acc (lv_acc (lv_x "h") "eth") "src"”;
val result2 = EVAL “resolve_lval ^example_pd ^h_eth_src”;  

    
val p_ttl_gt_60 = “(arithm_gt (lv_acc (lv_acc (lv_x "h") "ip") "ttl") ^sixty_bs)”;
EVAL “eval_arithm_atom ^example_pd ^p_ttl_gt_60”;
(* T *)

val p_ttl_lt_60 = “(arithm_lt (lv_acc (lv_acc (lv_x "h") "ip") "ttl") ^sixty_bs)”;
EVAL “eval_arithm_atom ^example_pd ^p_ttl_lt_60”;
(* F *)    
*)        
        


Definition eval_pred_w_str_def:
  (eval_pred_w_str pd (arith_a atom) = 
    eval_arithm_atom pd atom) ∧
  (eval_pred_w_str pd (arith_not p) = 
    case eval_pred_w_str pd p of
    | SOME b => SOME (~b)
    | NONE => NONE) ∧
  (eval_pred_w_str pd (arith_and p1 p2) = 
    case (eval_pred_w_str pd p1, eval_pred_w_str pd p2) of
    | (SOME b, SOME b') => SOME (b ∧ b')
    | (_,_) => NONE
  ) ∧
  (eval_pred_w_str pd (arith_or p1 p2) = 
    case (eval_pred_w_str pd p1, eval_pred_w_str pd p2) of
   | (SOME b,SOME b') => SOME (b ∨ b')
   | (_,_) => NONE
  ) ∧
  (eval_pred_w_str pd (arith_imp p1 p2) =
   case (eval_pred_w_str pd p1, eval_pred_w_str pd p2) of
   | (SOME b,SOME b') => SOME (b ⇒ b')
   | (_,_) => NONE
  )
End



(*

(* Test predicates *)
EVAL “eval_pred_w_str ^example_pd (arith_a ^p_ttl_gt_60)”;
EVAL “eval_pred_w_str ^example_pd (arith_a ^p_ttl_lt_60)”;

EVAL “eval_pred_w_str ^example_pd (arith_not (arith_a ^p_ttl_gt_60))”;
EVAL “eval_pred_w_str ^example_pd (arith_and (arith_a ^p_ttl_gt_60) (arith_a ^p_ttl_lt_60))”;
EVAL “eval_pred_w_str ^example_pd (arith_or (arith_a ^p_ttl_gt_60) (arith_a ^p_ttl_lt_60))”;

*)


        


Definition check_arith_pred_sem_def:
  check_arith_pred_sem (arith_policy: 'a arith_policy) pd =
  MAP (\(arith_pred,a). (eval_pred_w_str pd arith_pred, a) )  arith_policy
End


Definition sem_arith_policy_def:
  sem_arith_policy (policy: 'a arith_policy) pd =
  let res = check_arith_pred_sem policy pd in 
    case min_idx_till res (SOME T) of
    | SOME (idx,rule) => SOME (SND rule)
    | NONE => NONE
End



(*
    (* eidhit those, old types here *)
val p1 = “arith_a ^p_ttl_gt_60)”;
val p2 = “arith_a (arithm_lt (lv_acc (lv_x "h") "flag") 0)”;
val p3 = “arith_a (arithm_eq (lv_acc (lv_x "h") "invalid") 1)”;


val policy1 = ``[ (^p1, "fwd"); (^p2, "drop") ]``;
EVAL ``check_arith_pred_sem ^policy1 ^test_pd``;
(*   [(SOME T, "fwd"); (SOME F, "drop")] *)

val policy2 = ``[ (^p1, "fwd"); (^p3, "log") ]``;
EVAL ``check_arith_pred_sem ^policy2 ^test_pd``;
(*  [(SOME T, "allow"); (NONE, "log")]  *)

val policy3 = ``[ (^p1, "allow_high_ttl"); (^p2, "deny_low_flag")]``;
EVAL ``sem_arith_policy ^policy3 ^test_pd``;
(* SOME "allow_high_ttl"  *)

val policy4 = ``[  (^p2, "deny_low_flag"); (^p1, "allow_high_ttl")]``;
EVAL ``sem_arith_policy ^policy4 ^test_pd``;
     
*)





        
(* conversion function *)

Definition inverse_list_def:
  inverse_list l =
  MAP (λ(k, v). (v, k)) l
End;

                
Definition lookup_atom_def:
  lookup_atom (me) (atom:arithm_atom) =
    case ALOOKUP (inverse_list me) atom of
      SOME var => SOME var
    | NONE => NONE
End

        
(* Core conversion functions *)
Definition pred_a2v_def:
  (pred_a2v me (arith_a atom) = 
    case lookup_atom me atom of
      SOME v => SOME (Var v)
    | NONE => 
        if atom = a_True then SOME True
        else if atom = a_False then SOME False
        else NONE) ∧
  (pred_a2v me (arith_not p) = 
    case pred_a2v me p of
      SOME p' => SOME (Not p')
    | NONE => NONE) ∧
  (pred_a2v me (arith_and p1 p2) = 
    case (pred_a2v me p1, pred_a2v me p2) of
      (SOME p1', SOME p2') => SOME (And p1' p2')
    | _ => NONE) ∧
  (pred_a2v me (arith_or p1 p2) = 
    case (pred_a2v me p1, pred_a2v me p2) of
      (SOME p1', SOME p2') => SOME (Or p1' p2')
    | _ => NONE) ∧
  (pred_a2v me (arith_imp p1 p2) =
    case (pred_a2v me p1, pred_a2v me p2) of
      (SOME p1', SOME p2') => SOME (Implies p1' p2')
    | _ => NONE)
End




Definition all_convertable_def:
  all_convertable m_e policy =
  EVERY (λ(pred,_). pred_a2v m_e pred ≠ NONE) policy
End
        

Definition convert_def:
  convert policy m_e =
    if all_convertable m_e policy then
      SOME (MAP (λ(pred,act). (THE (pred_a2v m_e pred), act)) policy)
    else
      NONE
End   



(*
val test_me = ``[
  ("x_gt_5", arithm_gt (lv_x "x") 5);
  ("y_lt_2", arithm_lt (lv_x "y") 2)
]``;

(* Sample policies *)
val empty_policy = ``[] : (arith_pred # string) list``;
val all_convertable_policy = ``[
  (arith_a (arithm_gt (lv_x "x") 5), "allow");
  (arith_a (arithm_lt (lv_x "y") 2), "deny")
]``;
val partially_convertable_policy = ``[
  (arith_a (arithm_gt (lv_x "x") 5), "allow");
  (arith_a (arithm_eq (lv_x "z") 1), "log")  (* Unmapped *)
]``;

EVAL ``convert ^empty_policy ^test_me``;
(*SOME []*)
EVAL ``convert ^all_convertable_policy ^test_me``;
(*[(Var "x_gt_5", "allow"); (Var "y_lt_2", "deny")]*)
EVAL ``convert ^partially_convertable_policy ^test_me``;
(*NONE*)

val complex_policy = ``[
  (arith_not (arith_a (arithm_gt (lv_x "x") 5)), "reject");
  (arith_and (arith_a a_True) (arith_a (arithm_lt (lv_x "y") 2)), "special")
]``;
EVAL ``convert ^complex_policy ^test_me``;

(*
   SOME [
     (Not (Var "x_gt_5"), "reject");
     (And a_True (Var "y_lt_2"), "special")
   ]
*)

         
     
*)




Theorem inverse_list_lookup_thm:
  ∀m_e var atom.
    (ALL_DISTINCT (MAP FST m_e) ∧
    ALL_DISTINCT (MAP SND  m_e)) ⇒
    (ALOOKUP (inverse_list m_e) atom = SOME var ⇔
    ALOOKUP m_e var = SOME atom)
Proof
  rw[inverse_list_def, EQ_IMP_THM] >|[
  
    ‘MEM (atom, var) (MAP (λ(k,v). (v,k)) m_e)’ by metis_tac[ALOOKUP_MEM] >>
    ‘ ∃y. MEM y m_e ∧ (atom, var) = (λ(k,v). (v,k)) y ’by metis_tac[MEM_MAP] >>
    Cases_on ‘y’ >> fs[] >>
    rw[] >>
    gvs[ALOOKUP_ALL_DISTINCT_MEM]   
    ,
    
    ‘MEM (var, atom) m_e’ by metis_tac[ALOOKUP_MEM] >>
    
    ‘MEM (atom, var) (MAP (λ(k,v). (v,k)) m_e)’ by (
      rw[MEM_MAP] >>
      qexists_tac ‘(var, atom) ’>>
      rw[]
      ) >>
    
    ‘ALL_DISTINCT (MAP FST (MAP (λ(k,v). (v,k)) m_e))’ by (
      rw[MAP_MAP_o, combinTheory.o_DEF] >>
      gvs[UNCURRY] >>
      fs[map_snd_EQ]
      ) >>
    metis_tac[ALOOKUP_MEM, ALOOKUP_ALL_DISTINCT_MEM]
  ]
QED




Theorem pred_conversion_preserves_semantics_thm:
  ∀ arith_pred pred m_e packet_input m_v.
    ALL_DISTINCT (MAP FST m_e) ∧
    ALL_DISTINCT (MAP SND  m_e) ∧
    (∀var atom. 
       ALOOKUP m_e var = SOME atom ⇒ 
       ALOOKUP m_v var = eval_arithm_atom packet_input atom) ∧
    pred_a2v m_e arith_pred = SOME pred
    ⇒
    eval_pred_w_str packet_input arith_pred = sem_pred pred m_v
Proof

  Induct_on ‘arith_pred’ >> rw[pred_a2v_def, eval_pred_w_str_def] >>
            
   rpt (BasicProvers.FULL_CASE_TAC >>
        gvs[eval_arithm_atom_def, sem_pred_def]>>
        gvs[lookup_atom_def, inverse_list_def]) >>

   imp_res_tac inverse_list_lookup_thm >>
   gvs[inverse_list_def] >>
   res_tac >>
   rw[] >>
   gvs[eval_arithm_atom_def]
   (*
   Cases_on `pred_a2v m_e arith_pred` >> gvs[] >>
   Cases_on `pred_a2v m_e arith_pred'` >> gvs[] >>
   first_x_assum (drule_all_then assume_tac) >>
   first_x_assum (drule_all_then assume_tac) >>
   gvs[sem_pred_def] >>
   rw[] >> fs[] 
   *)  
QED




        

Theorem policy_airth_to_var_sem_conversion_correct:
∀ arith_policy var_policy.
  ∀ m_e packet_input m_v.
    (ALL_DISTINCT (MAP FST m_e) ∧
     ALL_DISTINCT (MAP SND m_e)) ∧
    (∀var atom. 
       ALOOKUP m_e var = SOME atom ⇒ 
       ALOOKUP m_v var = eval_arithm_atom packet_input atom) ∧
    (convert arith_policy m_e = SOME var_policy)
    ⇒
    sem_arith_policy arith_policy packet_input = 
    sem_policy var_policy m_v
Proof
  rw[sem_arith_policy_def, sem_policy_def] >>

  ‘check_arith_pred_sem arith_policy packet_input = check_sem_pred var_policy m_v’ 
    suffices_by rw[] >>
  
  fs[convert_def] >>
  rw[check_arith_pred_sem_def, check_sem_pred_def] >>
  
  rw[MAP_MAP_o] >>
  rw[combinTheory.o_DEF] >>
  
  rw[MAP_EQ_f] >>
  Cases_on ‘x’ >> rw[] >>
  rename1 ‘(pred, act)’ >>
  
  (* Since all_convertable holds, pred_a2v m_e pred ≠ NONE *)
  ‘pred_a2v m_e pred ≠ NONE’ by (
    fs[all_convertable_def, EVERY_MEM] >>
    rgs[ELIM_UNCURRY] >>
    res_tac >>
    fs[FST]
  ) >>
  
  (* This requires a lemma about pred_a2v and eval_pred_w_str equivalence *)
  Cases_on ‘pred_a2v m_e pred’ >> gvs[] >>
  metis_tac[pred_conversion_preserves_semantics_thm]
QED



val _ = export_theory ();

    

