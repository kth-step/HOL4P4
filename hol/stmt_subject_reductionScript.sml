open HolKernel boolLib liteLib simpLib Parse bossLib;
open arithmeticTheory stringTheory containerTheory pred_setTheory
     listTheory finite_mapTheory;

open p4Lib;
open blastLib bitstringLib;
open p4Theory;
open p4_auxTheory;
open deterTheory;
open e_subject_reductionTheory;
open e_progressTheory;
     
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

  
     
(*tactics*)


fun OPEN_V_TYP_TAC v_term =
(Q.PAT_X_ASSUM `v_typ v_term t bll` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once v_typ_cases] thm)))


               
fun OPEN_EXP_RED_TAC exp_term =
(Q.PAT_X_ASSUM `e_red c scope scopest ^exp_term exp2 fr` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once e_red_cases] thm)))

fun OPEN_ANY_EXP_RED_TAC exp_term =
(Q.PAT_X_ASSUM `e_red c scope scopest exp_term exp2 fr` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once e_red_cases] thm)))

               
fun OPEN_EXP_TYP_TAC exp_term =
(Q.PAT_X_ASSUM ` e_typ (t1,t2) t ^exp_term ta bll` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once e_typ_cases] thm)))


fun OPEN_ANY_EXP_TYP_TAC exp_term =
(Q.PAT_X_ASSUM ` e_typ (t1,t2) t exp_term ta bll` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once e_typ_cases] thm)))

               
fun OPEN_STMT_TYP_TAC stmt_term =
(Q.PAT_X_ASSUM ` stmt_typ (t1,t2) q g ^stmt_term` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once stmt_typ_cases] thm)))


fun OPEN_STMT_RED_TAC stm_term =
(Q.PAT_X_ASSUM `stmt_red ct (ab, gsl,[(fun,[^stm_term],gam)],st) stat`
 (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once stmt_red_cases] thm)))

val OPEN_ANY_STMT_RED_TAC =
(Q.PAT_X_ASSUM `stmt_red ct (ab, gsl,[(fun,[stm_term],gam)],st) stat`
 (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once stmt_red_cases] thm)))
 
fun OPEN_FRAME_TYP_TAC frame_term =
(Q.PAT_X_ASSUM ` frame_typ (t1,t2) a b h d ^frame_term` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once frame_typ_cases] thm)))
   
fun OPEN_LVAL_TYP_TAC lval_term =
(Q.PAT_X_ASSUM `lval_typ (g1,q1) t (^lval_term) (tp)` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once lval_typ_cases] thm)))



         

val _ = new_theory "stmt_subject_reduction";

    
(* represent the definition of:
     ψlist_G  ψlist_local ⊢ Φ 
  is the programmable blocks names so it is the main  *)

val res_frame_typ_def = Define ‘
res_frame_typ (order, f, (delta_g, delta_b, delta_x, delta_t)) Prs_n t_scope_list_g t_scope_list gscope framel func_map b_func_map=
∀i. 0 <= i ∧ i < LENGTH framel ⇒
    ∃stmt_stack f_name local_scope_list passed_gscope passed_delta_b passed_delta_t passed_tslg.   
      EL i framel = (f_name,stmt_stack,local_scope_list) ∧
             order (order_elem_f f_name) (order_elem_f f) ∧ 
             t_passed_elem f_name delta_g delta_b delta_t t_scope_list_g = (SOME passed_delta_b,  SOME passed_delta_t , SOME passed_tslg) ∧
             scopes_to_pass f_name func_map b_func_map gscope = SOME passed_gscope ∧

             frame_typ (passed_tslg,t_scope_list) (order, f_name, (delta_g, passed_delta_b, delta_x, passed_delta_t))
                                                   Prs_n  passed_gscope local_scope_list stmt_stack
’;




val sr_stmt_def = Define `
 sr_stmt (stmt) (ty:'a itself) =
∀ stmtl ascope ascope' gscope gscope' (scopest:scope list) scopest' framel status status' t_scope_list t_scope_list_g T_e (c:'a ctx) order delta_g delta_b delta_t delta_x f Prs_n
apply_table_f ext_map func_map b_func_map pars_map tbl_map.
      
       type_scopes_list  (gscope)  (t_scope_list_g) ∧
       type_scopes_list  (scopest) (t_scope_list)   ∧
       star_not_in_sl (scopest) ∧
       parseError_in_gs t_scope_list_g [t_scope_list] ∧
       (c = ( apply_table_f , ext_map , func_map , b_func_map , pars_map , tbl_map ) ) ∧
                        
       (WT_c c order t_scope_list_g delta_g delta_b delta_x delta_t Prs_n) ∧
       (T_e = (order, f, (delta_g, delta_b, delta_x, delta_t))) ∧   
       (frame_typ  ( t_scope_list_g  ,  t_scope_list ) T_e Prs_n  gscope scopest [stmt] ) ∧
             
       (stmt_red c ( ascope ,  gscope  ,           [ (f, [stmt], scopest )] , status)
                   ( ascope',  gscope' , framel ++ [ (f, stmtl , scopest')] , status')) ⇒
        
       (∃ t_scope_list'.
          res_frame_typ T_e Prs_n t_scope_list_g t_scope_list' gscope framel func_map b_func_map) ∧
          
       (∃ t_scope_list''  .
         LENGTH t_scope_list'' = (LENGTH stmtl - LENGTH [stmt]) ∧
        frame_typ  ( t_scope_list_g  ,  t_scope_list''++t_scope_list ) T_e Prs_n  gscope' scopest' stmtl)
`;



val fr_len_exp_def = Define `
fr_len_exp (e) (ty:'a itself) =
     ∀ e' gscope (scopest:scope list) framel  (c:'a ctx).
       e_red c gscope scopest e e' framel ⇒
       ((LENGTH framel = 1 ∧ ∃f_called stmt_called copied_in_scope. framel = [(f_called,[stmt_called],copied_in_scope)]) ∨
        (LENGTH framel = 0))
`;



val fr_len_exp_list_def = Define `
 fr_len_exp_list (l : e list) (ty:'a itself) = 
       ∀(e : e). MEM e l ==> fr_len_exp (e) (ty:'a itself)
`;


val fr_len_strexp_list_def = Define `
    fr_len_strexp_list (l : (string#e) list) (ty:'a itself) =
      ∀ (e:e) . MEM e (SND (UNZIP l)) ==> fr_len_exp(e) (ty:'a itself)
`;


val fr_len_strexp_tup_def = Define ` 
                                   fr_len_strexp_tup (tup : (string#e)) (ty:'a itself) =
                                   fr_len_exp ((SND tup)) (ty:'a itself)
`;



fun FR_LEN_IND_CASE exp = OPEN_EXP_RED_TAC (exp) >>
                          gvs[] >>
                          METIS_TAC[]
        
(* The expression reduction can create a frame of length 1 or nothing [] *)      
Theorem fr_len_from_e_theorem:
! (ty:'a itself) .
(!e. fr_len_exp e ty) /\
(! (l1: e list). fr_len_exp_list l1 ty) /\
(! (l2: (string#e) list) .  fr_len_strexp_list l2 ty) /\
(! tup. fr_len_strexp_tup tup ty)
Proof
STRIP_TAC >>   
Induct >>
fs[fr_len_exp_def] >>
REPEAT STRIP_TAC >| [
 fs[Once e_red_cases]
 ,
 fs[Once e_red_cases]
 ,
 fs[Once e_red_cases]
 ,
 FR_LEN_IND_CASE “e_acc e s”
 ,
 FR_LEN_IND_CASE “e_unop u e”
 ,
 FR_LEN_IND_CASE “e_binop e b e'”
 ,
 FR_LEN_IND_CASE “e_concat e e'” 
 ,
 FR_LEN_IND_CASE “e_slice e e' e''” 
 ,
 OPEN_EXP_RED_TAC “e_call f l” >>
 gvs[fr_len_exp_list_def] >>

 IMP_RES_TAC unred_arg_index_in_range >>
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`EL i (MAP (λ(e_,e'_,x_,d_). e_) (e_e'_x_d_list : (e # e # string # d) list)) `])) >>

 gvs[EL_MEM] >>
 fs[fr_len_exp_def] >>      
 RES_TAC >>
 gvs[]
 ,
 FR_LEN_IND_CASE “(e_select e l s)” 
 ,
 OPEN_EXP_RED_TAC “(e_struct l2)” >>
 gvs[] >>
 gvs[fr_len_strexp_list_def] >>

 IMP_RES_TAC unred_mem_index_in_range >>

 subgoal `fr_len_exp (EL i (MAP (λ(f_,e_,e'_). e_) f_e_e'_list)) ty ` >-
   (FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
    [`EL i (MAP (λ(f_,e_,e'_). e_) (f_e_e'_list : (string # e # e) list)) `])) >>

    IMP_RES_TAC EL_MEM >>
    IMP_RES_TAC mem_el_map2 >>
    gvs[] ) >>
            
 fs[fr_len_exp_def] >>      
 RES_TAC >>
 gvs[]       
 ,

 OPEN_EXP_RED_TAC “(e_header b l2)” >>
 gvs[fr_len_strexp_list_def] >>

 IMP_RES_TAC unred_mem_index_in_range >>


 subgoal `fr_len_exp (EL i (MAP (λ(f_,e_,e'_). e_) f_e_e'_list)) ty ` >-
  (FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`EL i (MAP (λ(f_,e_,e'_). e_) (f_e_e'_list : (string # e # e) list)) `])) >>

   IMP_RES_TAC EL_MEM >>
   IMP_RES_TAC mem_el_map2 >>
   gvs[] ) >>
            
 fs[fr_len_exp_def] >>      
 RES_TAC >>
 gvs[]
 ,
 fs[fr_len_strexp_list_def]
 ,

 fs[fr_len_strexp_list_def, fr_len_strexp_tup_def] >>
 REPEAT STRIP_TAC >>
 PairCases_on ‘tup’ >> gvs[] >> gvs[]
 ,       
 fs[fr_len_strexp_tup_def, fr_len_exp_def] >>
 gvs[]
 ,
 fs[fr_len_exp_list_def]
 ,
 fs[fr_len_exp_list_def] >>
 REPEAT STRIP_TAC >>
 gvs[] >>
 gvs[fr_len_exp_def] >>
 rfs[]
]   
QED


fun FR_LEN_STMT_IND_CASE stm =  OPEN_STMT_RED_TAC stm >>
                           gvs[] >>
                           ASSUME_TAC fr_len_from_e_theorem >>
                           FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`ty`])) >>
                           LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`e`])) >>                  
                           fs[fr_len_exp_def] >> gvs[] >>
                           RES_TAC >> gvs[]        

(* the statement reduction can create a framel of length 1 or 0 *)
Theorem fr_len_from_a_frame_theorem:
  ∀ stmt stmtl ascope ascope' gscope gscope' scopest scopest' f c status status' framel.
(stmt_red c ( ascope ,  gscope  , [ (f, [stmt], scopest )]            , status)
            ( ascope',  gscope' , framel ++ [ (f, stmtl , scopest')] , status')) ⇒
      ((LENGTH framel = 1 ∧ ∃f_called stmt_called copied_in_scope. framel = [(f_called,[stmt_called],copied_in_scope)]) ∨ (LENGTH framel = 0))  
Proof
Induct >>
REPEAT GEN_TAC >>
STRIP_TAC >| [
 fs[Once stmt_red_cases]
 ,
 FR_LEN_STMT_IND_CASE “stmt_ass l e”
 ,
 FR_LEN_STMT_IND_CASE “stmt_cond e stmt stmt'” 
 ,
 FR_LEN_STMT_IND_CASE “stmt_block l stmt”
 ,
 FR_LEN_STMT_IND_CASE “stmt_ret e” 
 ,
 OPEN_STMT_RED_TAC “stmt_seq stmt stmt'” >>
 gvs[] >>
 RES_TAC >>
 gvs[]
 ,
 FR_LEN_STMT_IND_CASE “stmt_verify e e0” >>
 gvs[] >>
 ASSUME_TAC fr_len_from_e_theorem >>
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`ty`])) >>
 fs[fr_len_exp_def] >> gvs[] >>
 RES_TAC >> gvs[]
 ,
 FR_LEN_STMT_IND_CASE “stmt_trans e” 
 ,
 OPEN_STMT_RED_TAC “stmt_app s l” >>
 gvs[] >>
 ASSUME_TAC fr_len_from_e_theorem >>
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`ty`])) >>
 fs[fr_len_exp_def] >> gvs[] >>
 RES_TAC >> gvs[]
 ,
 fs[Once stmt_red_cases]
 ]        
QED

        
(* NOTE that in the res_frame, we take the previous T_e to calculate the new T_e *)
val frame_typ_imp_res_frame_single = prove (
  “ ∀ tsgl tscl c Prs_n gscope t_scope_list_g t_scope_list_fr (f_called:funn) copied_in_scope stmt_called
           func_map b_func_map passed_gscope passed_delta_b passed_delta_t passed_tslg order delta_g delta_b delta_x delta_t f.
        order (order_elem_f f_called) (order_elem_f f) ∧   
        scopes_to_pass f_called func_map b_func_map gscope = SOME passed_gscope ∧
        t_passed_elem f_called delta_g delta_b delta_t t_scope_list_g = (SOME passed_delta_b,SOME passed_delta_t,SOME passed_tslg) ∧               
         frame_typ (passed_tslg,t_scope_list_fr) (order,f_called,delta_g,passed_delta_b,delta_x,passed_delta_t) Prs_n
               passed_gscope copied_in_scope [stmt_called] ⇒
        res_frame_typ (order,f,delta_g,delta_b,delta_x,delta_t) Prs_n t_scope_list_g t_scope_list_fr gscope [(f_called,[stmt_called],copied_in_scope)] func_map b_func_map ”,

fs[res_frame_typ_def] >>
REPEAT STRIP_TAC >>
‘i=0’ by fs[] >>       
fs[Once EL] >>
Q.EXISTS_TAC ‘Prs_n’ >>              
gvs[] 
);






Theorem fr_len_from_a_stmtl_theorem:
  ∀ stmtl stmtl' ascope ascope' gscope gscope' scopest scopest' f c status status' framel.
(stmt_red c ( ascope ,  gscope  , [ (f, stmtl, scopest )]            , status)
            ( ascope',  gscope' , framel ++ [ (f, stmtl' , scopest')] , status')) ⇒
      ((LENGTH framel = 1 ∧ ∃f_called stmt_called copied_in_scope. framel = [(f_called,[stmt_called],copied_in_scope)]) ∨ (LENGTH framel = 0))  
Proof
Induct >>
REPEAT GEN_TAC >-
gvs[Once stmt_red_cases] >>
REPEAT STRIP_TAC >>
gvs[Once stmt_red_cases] >>
IMP_RES_TAC fr_len_from_a_frame_theorem >> gvs[]>>

ASSUME_TAC fr_len_from_e_theorem >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`ty`])) >>
LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`e`])) >>                  
fs[fr_len_exp_def] >> gvs[] >>
RES_TAC >> gvs[] 
QED





        
 fun OPEN_FRAME_TYP_TAC frame_term =
(Q.PAT_X_ASSUM ` frame_typ (t1,t2) a b h d ^frame_term` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once frame_typ_cases] thm)))       


fun EXP_IS_WT_IN_FRAME_TAC frm = OPEN_FRAME_TYP_TAC frm >>
                               fs[stmtl_typ_cases, type_ith_stmt_def] >>
                               FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`0`])) >>
                               gvs[] >>
                               rfs[Once stmt_typ_cases]      


fun ASSUME_SR_EXP_FOR e =  ASSUME_TAC SR_e >>
                           FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`ty`])) >>
                           PAT_ASSUM ``∀e. sr_exp e ty`` ( STRIP_ASSUME_TAC o (Q.SPECL [e])) >>
                           fs[sr_exp_def]

                          
fun INST_SR_EXP_FOR (e', tau, b) = FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [e', ‘gscope’, ‘scopest’,
                          ‘[(f_called,[stmt_called],copied_in_scope)]’, ‘t_scope_list’, ‘t_scope_list_g’,
                          tau,b, ‘order’,‘delta_g’,‘delta_b’, ‘delta_t’,‘delta_x’,‘f’,‘f_called’,
                          ‘stmt_called’,‘copied_in_scope’, ‘Prs_n’ ,‘apply_table_f’, ‘ext_map’, ‘func_map’, ‘b_func_map’,
                          ‘pars_map’, ‘tbl_map’])) >>
                          gvs[]
                                                               

(* here we knwo that also teh frame we create and trying to type, the  is empty*)
val SR_stmt_newframe = prove (“
∀ stmt stmtl ascope ascope' gscope gscope' (scopest:scope list) scopest' framel status status' t_scope_list t_scope_list_g T_e
   (c:'a ctx) order delta_g delta_b delta_t delta_x f Prs_n apply_table_f ext_map func_map b_func_map pars_map tbl_map.
       type_scopes_list  (gscope)  (t_scope_list_g) ∧
       type_scopes_list  (scopest) (t_scope_list)   ∧
       star_not_in_sl (scopest) ∧
       (c = ( apply_table_f , ext_map , func_map , b_func_map , pars_map , tbl_map ) ) ∧
       (WT_c c order t_scope_list_g delta_g delta_b delta_x delta_t Prs_n) ∧
       (T_e = (order, f, (delta_g, delta_b, delta_x, delta_t))) ∧   
       (frame_typ  ( t_scope_list_g  ,  t_scope_list ) T_e Prs_n  gscope scopest [stmt] ) ∧
       (stmt_red c ( ascope ,  gscope  ,           [ (f, [stmt], scopest )] , status)
                   ( ascope',  gscope' , framel ++ [ (f, stmtl , scopest')] , status')) ⇒
       (∃ t_scope_list'. res_frame_typ (order,f,(delta_g, delta_b, delta_x, delta_t)) Prs_n t_scope_list_g t_scope_list' gscope framel func_map b_func_map) ”,

                                  
Induct >>
REPEAT STRIP_TAC >| [
 fs[Once stmt_red_cases]
 ,
 (** assignment case **)   
 (* we know that the length of the frame framel is either 0 or one from :*)
 IMP_RES_TAC fr_len_from_a_frame_theorem >|[      
   (* if 1, then we also know that e made a reduction*)
   OPEN_ANY_STMT_RED_TAC >>
   gvs[] >>
        
   (* we also know that e is well typed from frame typ *)  
   EXP_IS_WT_IN_FRAME_TAC “[stmt_ass l e]” >>     
            
   (* from sr we know that this frame is well typed, we need to know the
      typing scope for the body *)    
   ASSUME_SR_EXP_FOR ‘e’ >>
   INST_SR_EXP_FOR (‘e''’,‘(t_tau tau')’,‘b’) >>
            
   qexistsl_tac [‘t_scope_list_fr’] >>
   drule  frame_typ_imp_res_frame_single >> gvs[]                 
   ,
   fs[res_frame_typ_def]
   ]
 ,
 (* condition case *)
 schneiderUtils.POP_NO_TAC 7 >>
 schneiderUtils.POP_NO_TAC 7 >>                             
 IMP_RES_TAC fr_len_from_a_frame_theorem >|[      
   OPEN_ANY_STMT_RED_TAC >>
   gvs[] >>
   EXP_IS_WT_IN_FRAME_TAC “[stmt_cond e stmt stmt']” >>     
            
   ASSUME_SR_EXP_FOR ‘e’ >>
   INST_SR_EXP_FOR (‘e''’,‘(t_tau tau_bool)’,‘b’) >>
                        
   qexistsl_tac [‘t_scope_list_fr’] >>
   drule frame_typ_imp_res_frame_single >> gvs[]                 
   ,
   fs[res_frame_typ_def]
   ]
 ,
 (* stmt_block can never create a frame *)
 OPEN_ANY_STMT_RED_TAC >>
 gvs[] >>
 fs[res_frame_typ_def]      
 ,
 (* return *)
 IMP_RES_TAC fr_len_from_a_frame_theorem >|[      
   OPEN_ANY_STMT_RED_TAC >>
   gvs[] >>  
   EXP_IS_WT_IN_FRAME_TAC “[stmt_ret e]” >>     
   
   ASSUME_SR_EXP_FOR ‘e’ >>
   INST_SR_EXP_FOR (‘e''’,‘(t_tau tau')’,‘b’) >>
                        
   qexistsl_tac [‘t_scope_list_fr’] >>
   drule frame_typ_imp_res_frame_single >> gvs[]                 
   ,
   fs[res_frame_typ_def]
   ]
 ,
 (* only seq 1 create a frame *)
 schneiderUtils.POP_NO_TAC 8 >>   
 IMP_RES_TAC fr_len_from_a_frame_theorem >| [
   OPEN_ANY_STMT_RED_TAC >>
   gvs[] >>

   (* use IH *)
   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘stmt_stack' ⧺ [stmt1']’, ‘ascope’, ‘ascope'’, ‘gscope’, ‘gscope'’,
                                   ‘scopest’, ‘scopest'’,‘[(f_called,[stmt_called],copied_in_scope)]’,‘status_running’,
                                   ‘status_running’,‘t_scope_list’,‘t_scope_list_g’, ‘order’,‘delta_g’,‘delta_b’,
                                   ‘delta_t’,‘delta_x’,‘f’,‘Prs_n’])) >> gvs[] >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘apply_table_f’, ‘ext_map’, ‘func_map’, ‘b_func_map’, ‘pars_map’, ‘tbl_map’])) >> gvs[] >>

                 
   (* we know that [stmt] is well typed from frame_typ*)
   subgoal ‘frame_typ (t_scope_list_g,t_scope_list)
            (order,f,delta_g,delta_b,delta_x,delta_t) Prs_n  gscope scopest [stmt]’ >-
     ( OPEN_FRAME_TYP_TAC “[stmt_seq stmt stmt']” >>
       SIMP_TAC list_ss [Once frame_typ_cases] >>

       fs[stmtl_typ_cases, type_ith_stmt_def] >>
       FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`0`])) >>
       gvs[] >>

       OPEN_STMT_TYP_TAC “stmt_seq stmt stmt'” >>
       gvs[] >>
                        
       qexistsl_tac [‘tau_d_list’,‘tau’] >> gvs[] >>
       REPEAT STRIP_TAC >> gvs[] >>            
       REPEAT STRIP_TAC >>             
       ‘i=0’ by fs[] >>       
       fs[Once EL]  ) >>
          
   gvs[] >>
   srw_tac [SatisfySimps.SATISFY_ss][]          
   ,
   fs[res_frame_typ_def]                
   ]

 ,
 (* verify statement *)
 IMP_RES_TAC fr_len_from_a_frame_theorem >| [
   OPEN_ANY_STMT_RED_TAC >>
   gvs[] >|[
     (* verify e1 *)                    
     EXP_IS_WT_IN_FRAME_TAC “[stmt_verify e e0]” >>     
     ASSUME_SR_EXP_FOR ‘e’ >>
     INST_SR_EXP_FOR (‘e'''’,‘(t_tau tau_bool)’,‘b’) >>
     qexistsl_tac [‘t_scope_list_fr’] >>
     drule frame_typ_imp_res_frame_single >> gvs[]  
     ,
     (* verify e2 *)

     fs[Once frame_typ_cases, stmtl_typ_cases, type_ith_stmt_def] >>
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`0`])) >>
     gvs[] >>
     rfs[Once stmt_typ_cases] >> 

     ASSUME_SR_EXP_FOR ‘e0’ >>
     INST_SR_EXP_FOR (‘e''’,‘(t_tau tau_err)’,‘b''’) >>
     qexistsl_tac [‘t_scope_list_fr’] >>
     drule frame_typ_imp_res_frame_single >> gvs[] 
     ]     
   ,
   fs[res_frame_typ_def]
   ]
 ,
 (** statement trans **)
 IMP_RES_TAC fr_len_from_a_frame_theorem >| [
   OPEN_ANY_STMT_RED_TAC >> gvs[] >>
   EXP_IS_WT_IN_FRAME_TAC “[stmt_trans e]” >>     
   ASSUME_SR_EXP_FOR ‘e’ >>
   INST_SR_EXP_FOR (‘e''’,‘t_string_names_a x_list’,‘b’) >>
   qexistsl_tac [‘t_scope_list_fr’] >>
   drule frame_typ_imp_res_frame_single >> gvs[]  
   ,
   fs[res_frame_typ_def]             
  ]
 ,
 (* statement apply s l *)
 IMP_RES_TAC fr_len_from_a_frame_theorem >| [
   OPEN_ANY_STMT_RED_TAC >>
   gvs[] >>
   EXP_IS_WT_IN_FRAME_TAC “[stmt_app s l]” >>     

   (* we know that i is indeed less than the list *)
   subgoal ‘i < LENGTH e_tau_b_list’ >- (
        IMP_RES_TAC index_not_const_in_range >> 
         gvs[LIST_EQ_REWRITE] )>>

   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`i`])) >>
   gvs[] >>
        
   ASSUME_SR_EXP_FOR ‘(EL i (MAP (λ(e_,e'_). e_) (e_e'_list : (e # e) list)))’ >>
   INST_SR_EXP_FOR (‘e'’,‘(t_tau (EL i (MAP (λ(e_,tau_,b_). tau_) (e_tau_b_list: (e # tau # bool) list))))’,
                   ‘(EL i (MAP (λ(e_,tau_,b_). b_) (e_tau_b_list : (e # tau # bool) list)))’) >>
       
   qexistsl_tac [‘t_scope_list_fr’] >>
   drule frame_typ_imp_res_frame_single >> gvs[]  
   ,
   fs[res_frame_typ_def]
   ]
 ,
(* statement extern would never create a frame *)
 OPEN_ANY_STMT_RED_TAC >>
 gvs[] >>
 fs[res_frame_typ_def]   
  ]
       
);



(*
EVAL “declare_list_in_fresh_scope [(varn_name "x",tau_bot)]”
EVAL “ type_scopes_list [[(varn_name "x",v_bot,NONE)]] [[(varn_name "x",tau_bot)]] ”
*)





val tsl_singletone_exsists = prove (“
 ∀ scopest ts .        
 type_scopes_list scopest [ts] ⇒
 (LENGTH scopest = 1 ∧ ∃ sc . scopest  = [sc] ∧
 type_scopes_list [sc] [ts] )
                                               ”,
 REPEAT GEN_TAC >>
 STRIP_TAC >>
           
 IMP_RES_TAC type_scopes_list_LENGTH >>
 ‘LENGTH [ts] = 1’ by fs[] >>
 gvs[] >>

 fs[type_scopes_list_def] >>
 gvs[similarl_def]
);
        



val similar_normalize2 = prove ( ``
∀ R l l' h h'.
       similar R (h::l) (h'::l') ⇔
       similar R [h] [h'] ∧
       similar R l l'``,

REPEAT STRIP_TAC >>
fs[similar_def]
);




val similar_ext_out_scope_lemma = prove (“
∀ sc sc' varnl varnl' tl.
similar (λsi so. SND si = SND so ∧ SND si = NONE) sc sc' ∧
similar (λx y. v_typ (FST x) (t_tau y) F) sc' (ZIP (varnl,tl)) ∧
similar (λx y. v_typ (FST x) (t_tau y) F) sc (ZIP (varnl',tl)) ⇒
similar (λx y. v_typ (FST x) (t_tau y) F) sc' (ZIP (varnl',tl))

                                     ”,
reverse (               
Induct_on ‘sc’ >>
Induct_on ‘sc'’ >>
Induct_on ‘tl’ >>
Induct_on ‘varnl’ >>
Induct_on ‘varnl'’ >>
REPEAT STRIP_TAC) >-
 (
 SIMP_TAC list_ss [Once similar_normalize2] >> gvs[] >> CONJ_TAC >| [
     (*head case*)
     gvs[Once similar_normalize2] >>
     PairCases_on ‘h'’ >>
     PairCases_on ‘h''''’ >>
     gvs[similar_def]                                 
     ,
     (*IH case*)
     rfs[Once similar_normalize2] >> 
     RES_TAC
   ]
 ) >>

srw_tac [][ZIP, ZIP_def] >>       
gvs[similar_def] >>
 TRY (PairCases_on ‘h’) >>
 TRY (PairCases_on ‘h'’) >>
 TRY(PairCases_on ‘y’) >>
 fsrw_tac [][LENGTH_ZIP_MIN] >>
 rfs[ZIP_def]
);
        


           

val typ_ext_out_scope_lemma = prove (“
∀ sc sc' tl varnl varnl'.
ext_sc_same_as_input [sc] [sc'] ∧
type_scopes_list [sc'] [ZIP (varnl, tl)] ∧
type_scopes_list [sc]  [ZIP(varnl', tl)] ⇒
type_scopes_list [sc'] [ZIP(varnl', tl)] ”,
REPEAT STRIP_TAC >>
gvs[ext_sc_same_as_input_def] >>
gvs[type_scopes_list_def] >>
gvs[similarl_def] >>
IMP_RES_TAC similar_ext_out_scope_lemma
);


val ext_sc_same_as_input_LENGTH = prove (“
∀ scopest tsl .
ext_sc_same_as_input scopest tsl ⇒
LENGTH scopest =  LENGTH tsl”,

gvs[ext_sc_same_as_input_def] >>
fs[type_scopes_list_def, similarl_def, similar_def] >>
REPEAT STRIP_TAC >>
IMP_RES_TAC LIST_REL_LENGTH
);




        
val typ_scope_list_ext_out_scope_lemma = prove (
  “ ∀ f apply_table_f ext_map func_map b_func_map pars_map tbl_map
    order tslg delta_g delta_b delta_x ascope ascope'
          gscope scopest  scopest' v ext_fun tsl tau tdl delta_t Prs_n.
          
WT_c (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)
     order tslg delta_g delta_b delta_x delta_t Prs_n ∧
SOME (tdl,tau) = t_lookup_funn f delta_g delta_b delta_x ∧
args_t_same (MAP FST tdl) tsl ∧    
type_scopes_list scopest tsl ∧
type_scopes_list gscope tslg ∧
star_not_in_sl scopest ∧
SOME ext_fun = lookup_ext_fun f ext_map ∧
SOME (ascope',scopest',v) = ext_fun (ascope,gscope,scopest) ⇒
   (type_scopes_list scopest' tsl ∧ star_not_in_sl scopest')”,                
                     
Cases_on ‘f’ >>
fs[lookup_ext_fun_def] >>
REPEAT GEN_TAC >>
STRIP_TAC  >| [
    (* we know that the length of scopest is one,*)
    (* and if the length is one, we know that there exists only one element there via *)
    (*inst*)

 Cases_on ‘ALOOKUP ext_map s’ >> gvs[] >>
 PairCases_on ‘x’ >> gvs[] >>
 Cases_on ‘x0’ >> gvs[] >>
 PairCases_on ‘x’ >> gvs[] >>
        
 fs[WT_c_cases] >>
 fs[WTX_cases] >>
 fs[extern_map_IoE_typed_def] >>
                                
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`x0`, `s`, ‘ext_fun’,‘x1’])) >>
 gvs[] >>
      
                                    
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`ascope`, `gscope`, ‘scopest’])) >>
 gvs[] >>

 Cases_on ‘ext_fun (ascope,gscope,scopest)’ >> gvs[] >>

 (* the output scope sc is only of length 1*)
 IMP_RES_TAC tsl_singletone_exsists >>
 gvs[] >>


 (* show that tdl and tdl ' are the same *) 
 IMP_RES_TAC t_lookup_funn_ext_lemma >>                  
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`delta_g`, `delta_b`])) >>
 gvs[] >>
 Cases_on ‘t_lookup_funn (funn_inst s) delta_g delta_b delta_x’ >> gvs[] >>
          
 (* we know that the scopest (initial one) must be of size 1 *)
 IMP_RES_TAC ext_sc_same_as_input_LENGTH >>
 ‘LENGTH scopest = 1’ by gvs[] >>
 ‘∃ outsc. scopest = [outsc]’ by  fs[quantHeuristicsTheory.LIST_LENGTH_1] >>

 (* same for the typing scope*)
 ‘LENGTH tsl = 1’ by (IMP_RES_TAC type_scopes_list_LENGTH >>   gvs[]) >>
 ‘∃ tsc. tsl = [tsc]’ by  fs[quantHeuristicsTheory.LIST_LENGTH_1] >>
 gvs[] >>


 fs[args_t_same_def, same_dir_def] >> 
 gvs[mk_tscope_def] >>
 srw_tac [] [] >>
     
 (* we know that ts contains the same types as the input*)
 subgoal ‘  [tsc] = [ZIP (MAP FST tsc ,MAP FST tdl)]’ >-
     ( gvs[] >> ‘ZIP (MAP FST tsc,MAP SND tsc) = tsc’ by SIMP_TAC list_ss [GSYM ZIP_MAP_FST_SND] >>
       rfs[] ) >>
                 
 IMP_RES_TAC typ_ext_out_scope_lemma >>
 rfs[] >>
     
 LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`MAP FST (tsc : (varn # tau) list)`])) >>
 srw_tac [][] >>    
 METIS_TAC []
 ,
        
 (*ext methods *)
 Cases_on ‘ALOOKUP ext_map s’ >> gvs[] >>
 PairCases_on ‘x’ >> gvs[] >>
 Cases_on ‘ALOOKUP x1 s0’ >> gvs[] >>
 PairCases_on ‘x’ >> gvs[] >>
        
 fs[WT_c_cases] >>
 fs[WTX_cases] >>
 fs[extern_MoE_typed_def] >>
                                
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`x0'`, `s`, ‘s0’,‘x0’,‘x1’,‘ext_fun’])) >>
 gvs[] >>
      
                                    
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`ascope`, `gscope`, ‘scopest’])) >>
 gvs[] >>
 Cases_on ‘ext_fun (ascope,gscope,scopest)’ >> gvs[] >>

 IMP_RES_TAC tsl_singletone_exsists >>
 gvs[] >>
            
 IMP_RES_TAC t_lookup_funn_ext_lemma >>                  
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`delta_g`, `delta_b`])) >>
 gvs[] >>
 Cases_on ‘t_lookup_funn (funn_ext s s0) delta_g delta_b delta_x’ >> gvs[] >>
          
  (* we know that the scopest (initial one) must be of size 1 *)
 IMP_RES_TAC ext_sc_same_as_input_LENGTH >>
 ‘LENGTH scopest = 1’ by gvs[] >>
 ‘∃ outsc. scopest = [outsc]’ by  fs[quantHeuristicsTheory.LIST_LENGTH_1] >>

 (* same for the typing scope*)
 ‘LENGTH tsl = 1’ by (IMP_RES_TAC type_scopes_list_LENGTH >>   gvs[]) >>
 ‘∃ tsc. tsl = [tsc]’ by  fs[quantHeuristicsTheory.LIST_LENGTH_1] >>
  gvs[] >>


  fs[args_t_same_def, same_dir_def] >> 
  gvs[mk_tscope_def] >>
  srw_tac [] [] >>


            
  (* we know that ts contains the same types as the input*)
  subgoal ‘ [tsc] = [ZIP (MAP FST tsc ,MAP FST tdl)]’ >-
     ( gvs[] >> ‘ZIP (MAP FST tsc,MAP SND tsc) = tsc’ by SIMP_TAC list_ss [GSYM ZIP_MAP_FST_SND] >>
       rfs[] ) >>
                 
 IMP_RES_TAC typ_ext_out_scope_lemma >>
 rfs[] >>
     
 LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`MAP FST (tsc : (varn # tau) list)`])) >>
 srw_tac [][] >>    
 METIS_TAC []         
  ]
);
                



        



            

val directionless_lval_f = prove (“∀ dl.
is_directionless (dl) ⇒ out_is_lval (dl) (MAP (λd. F) dl)”,
Induct >>
gvs[is_d_out_def, out_is_lval_def] >>                                     
REPEAT STRIP_TAC >>
fs[Once EL_compute] >> Cases_on ‘i=0’ >> gvs[EL_CONS] >| [
  Cases_on ‘h’ >> gvs[is_d_out_def, is_directionless_def]
  ,
  ‘is_directionless dl’ by fs[is_directionless_def] >>
  gvs[] >>
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘i - 1’])) >>          
  gvs[numeralTheory.numeral_pre, PRE_SUB1, PRE_SUC_EQ] >>
   Cases_on `i = 1` >>
   fs[] >>

   `~ (i ≤ 1)` by fs[] >>
  gvs[] >>
  fs[GSYM EL] >> fs[ADD1] (* TODO add this everywherre i needed to show something about the tail*) ]
);     



Theorem ALOOKUP_not_empty:
 ∀ l s t . ALOOKUP l s = SOME t ⇒
         l ≠ []
Proof
Induct >>
fs[]
QED

              


Theorem assign_to_null_same_scl:
∀ scl scl' v .              
SOME scl' = assign (scl) v lval_null ⇔
scl' = scl
Proof        
gvs[assign_def]
QED



(*EVAL “oDROP 3 [a;b;c]”*)
(*EVAL “oTAKE 3 [a;b;c;d]”*)


Theorem oDROP_empty:        
∀l . oDROP (LENGTH l) l = SOME []
Proof                                 
Induct >>
gvs[oDROP_def]
QED



        
Theorem oDROP_is_not_empty:        
∀l l' h . ~ (oDROP (LENGTH l) (l++(h::l')) = SOME [])
Proof                                 
Induct >>
gvs[oDROP_def]
QED                               



Theorem oDROP_LENGTH_lemma1:                
∀ l1 l2 l3 .
SOME l3 = oDROP (LENGTH l1) (l1 ⧺ l2) ⇔
 l3 = l2
Proof
Induct_on ‘l1’ >>
fs[oDROP_def] >>
REPEAT STRIP_TAC >>
gvs[oDROP_empty, oDROP_is_not_empty]
QED        


Theorem oTAKE_is_not_empty:        
∀l l' h . ~ (oTAKE (LENGTH l) (l++l') = NONE)
Proof                                 
Induct >>
REPEAT STRIP_TAC >>
Cases_on ‘oTAKE (LENGTH l) (l ⧺ l')’ >>
gvs[oTAKE_def]
QED  

Theorem oTAKE_full:        
∀l . oTAKE (LENGTH l) l = SOME l
Proof                                 
Induct >>
gvs[oTAKE_def]
QED

           
Theorem oTAKE_LENGTH_lemma1:                
∀ l1 l2 l3 .
SOME l3 = oTAKE (LENGTH l1) (l1 ⧺ l2) ⇔
 l3 = l1
Proof
Induct_on ‘l1’ >>
fs[oTAKE_def] >>
REPEAT STRIP_TAC >>
Cases_on ‘oTAKE (LENGTH l1) (l1 ⧺ l2)’ >> gvs[] >>
gvs[oTAKE_full, oTAKE_is_not_empty] >>
METIS_TAC[]
QED            

        
Theorem assign_to_null_same_scl:
  ∀ scope_list scopest scopest' gscope gscope' v .
  LENGTH gscope = 2 ∧  
  SOME scope_list = assign (scopest ⧺ gscope) v lval_null ∧
  (SOME gscope',SOME scopest') = separate scope_list     
   ⇒
   gscope' = gscope ∧   scopest = scopest'   
Proof        
gvs[assign_def] >>
gvs[separate_def] >>
REPEAT GEN_TAC >>
REPEAT STRIP_TAC >>       
gvs[oDROP_LENGTH_lemma1] >>
gvs[oTAKE_LENGTH_lemma1]               
QED




Theorem v_typ_always_lval:
∀ v tau b.
v_typ v tau  b ⇒ (b = F)
Proof
Induct >>
gvs[Once v_typ_cases, clause_name_def]
QED



Theorem find_topmost_map_not_none:
∀ sl varn i scope.
find_topmost_map sl varn = SOME (i,scope) ⇒
~(ALOOKUP scope varn = NONE)
Proof
Induct >>         
fs[find_topmost_map_def] >>
gvs[INDEX_FIND_def] >>
REPEAT STRIP_TAC >>
       
Cases_on ‘ALOOKUP h varn’ >> gvs[] >>
Cases_on ‘INDEX_FIND 1 (λsc. IS_SOME (ALOOKUP sc varn)) sl’ >> gvs[] >>
         
ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:(varn#'a) list``] P_hold_on_next)  >>
LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`0`, `sl`, `(λsc. IS_SOME (ALOOKUP sc (varn)))`, `(i,scope)`])) >>
gvs[]            
QED      







val LUPDATE_abstract_def = Define ‘
 LUPDATE_abstract elem n l = ( TAKE n l ) ++ [elem] ++ ( DROP (SUC n) l) ’;

(*
EVAL “(AUPDATE [(1,a);(0,b)] ((0:num), c)) ”
*)

 
Theorem LUPDATE_eq: 
∀ l n elem . n < LENGTH l ⇒
             LUPDATE_abstract elem n l = LUPDATE elem n l
Proof                                                      
Induct >>
Induct_on ‘n’ >>
gvs[LUPDATE_def, LUPDATE_abstract_def]
QED



Theorem find_topmost_map_LENGTH:
∀ sl s scope i .
find_topmost_map sl s = SOME (i,scope) ⇒
i < LENGTH sl
Proof
rw[find_topmost_map_def] >>
Cases_on ‘INDEX_FIND 0 (λsc. IS_SOME (ALOOKUP sc s)) sl’ >>
gvs[] >>
IMP_RES_TAC INDEX_FIND_EQ_SOME_0
QED




Theorem find_topmost_map_HD:
∀ sl scope s.  
     find_topmost_map (sl) s = SOME (0,scope) ⇒
     HD(sl)=scope
Proof
  rw[find_topmost_map_def] >>
  Cases_on ‘INDEX_FIND 0 (λsc. IS_SOME (ALOOKUP sc s)) (sl)’ >>
  gvs[INDEX_FIND_EQ_SOME_0]
QED



Theorem DROP_1:
  ∀ l . DROP 1 l = TL l
Proof
Induct >> gvs[DROP_def]
QED        



           
Theorem LENGTH_imp_NULL:
 ∀ l1 l2 .          
LENGTH l1 = LENGTH l2 ⇒
(¬NULL l1 = ¬NULL l2)
Proof
Induct >> Induct_on ‘l2’ >> gvs[NULL]
QED








val map_tmp_lemma = prove (“
∀ (l: (x#v#tau) list ) l' .       
MAP (λ(x_,v_,tau_). (x_,tau_)) l' = MAP (λ(x_,v_,tau_). (x_,tau_)) l
⇔
(MAP (λ(x_,v_,tau_). (x_)) l' = MAP (λ(x_,v_,tau_). (x_)) l
 ∧
MAP (λ(x_,v_,tau_). (tau_)) l' = MAP (λ(x_,v_,tau_). (tau_)) l
)  ”,
Induct_on `l` >>
Induct_on `l'` >>
FULL_SIMP_TAC list_ss [] >>
REPEAT STRIP_TAC>>
PairCases_on `h` >>
PairCases_on `h'` >>
REV_FULL_SIMP_TAC list_ss [] >>
METIS_TAC []
);


        
(* this property is applied only on the base type. It does not include the parer names*)
val deter_v_typed_def = Define `
 deter_v_typed (v:v) (ty:'a itself) =
 ∀ tau tau'.           
v_typ v (t_tau tau) F  ∧
v_typ v (t_tau tau') F  ⇒
tau = tau'
`;


val deter_svl_typed_def = Define `
 deter_svl_typed (svl: (string # v) list ) (ty:'a itself) =
   !  (v:v) . MEM v (SND (UNZIP svl)) ==> deter_v_typed (v) (ty:'a itself)
`;

val deter_sv_tup_typed_def = Define `
 deter_sv_tup_typed (tup : (string#v) ) (ty:'a itself) =
     deter_v_typed ((SND tup)) (ty:'a itself)
`;



val EL_MEM_2 = prove (“
∀l x.
x < LENGTH l ⇒  
MEM (EL x (MAP (λ(a,b,c). a) l)) (MAP (λ(a,b,c). a) l) ∧
MEM (EL x (MAP (λ(a,b,c). b) l)) (MAP (λ(a,b,c). b) l) ∧
MEM (EL x (MAP (λ(a,b,c). c) l)) (MAP (λ(a,b,c). c) l) ”,       

REPEAT STRIP_TAC >>        
rfs[EL_MEM] 
);




        
Theorem v_typ_deter:
(! (ty:'a itself) .
(! v    . deter_v_typed v (ty:'a itself) ) /\
(! (svl). deter_svl_typed svl ty) /\
(! (sv) . deter_sv_tup_typed sv ty))  
Proof
  
STRIP_TAC >>
Induct >>
fs[deter_v_typed_def] >> 
REPEAT STRIP_TAC >| [
 (* all goals but not the struct and headers*)       
 fs[Once v_typ_cases]
 ,
 fs[Once v_typ_cases]
 ,
 fs[Once v_typ_cases]
 ,
 (* headers and structs *)
 fs[Once v_typ_cases] >>
 TRY(OPEN_V_TYP_TAC “any v”) >>
 gvs[] >> 

 ‘LENGTH (MAP (λ(x_,v_,tau_). (x_,v_)) x_v_tau_list) =
  LENGTH (MAP (λ(x_,v_,tau_). (x_,v_)) x_v_tau_list') ’ by fs[LENGTH_MAP, MAP_EQ_EVERY2] >>
 gvs[] >>

 ‘MAP (λ(x_,v_,tau_). x_) x_v_tau_list =
  MAP (λ(x_,v_,tau_). x_) x_v_tau_list'’ by IMP_RES_TAC lemma_MAP5 >> gvs[] >>                   
 ‘MAP (λ(x_,v_,tau_). v_) x_v_tau_list =
  MAP (λ(x_,v_,tau_). v_) x_v_tau_list'’ by IMP_RES_TAC lemma_MAP5 >> gvs[] >>

 SIMP_TAC list_ss [map_tmp_lemma] >> gvs[] >>

 SIMP_TAC list_ss [LIST_EQ_REWRITE] >> gvs[] >>
 REPEAT STRIP_TAC >>     

 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`x`])) >> gvs[] >>
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`x`])) >> gvs[] >>

 fs[deter_svl_typed_def] >>
 gvs[UNZIP_rw] >>

 subgoal `deter_v_typed (EL x (MAP (λ(x_,v_,tau_). v_) x_v_tau_list')) ty ` >-
    (FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`(EL x (MAP (λ(x_,v_,tau_). v_) (x_v_tau_list' : (string # v # tau) list)))`])) >>
     rfs[EL_MEM] ) >>
 fs[deter_v_typed_def]
 ,
 (* headers and structs *)
 fs[Once v_typ_cases] >>
 TRY(OPEN_V_TYP_TAC “any v”) >>
 gvs[] >> 

 ‘LENGTH (MAP (λ(x_,v_,tau_). (x_,v_)) x_v_tau_list) =
  LENGTH (MAP (λ(x_,v_,tau_). (x_,v_)) x_v_tau_list') ’ by fs[LENGTH_MAP, MAP_EQ_EVERY2] >>
 gvs[] >>

 ‘MAP (λ(x_,v_,tau_). x_) x_v_tau_list =
  MAP (λ(x_,v_,tau_). x_) x_v_tau_list'’ by IMP_RES_TAC lemma_MAP5 >> gvs[] >>                   
 ‘MAP (λ(x_,v_,tau_). v_) x_v_tau_list =
  MAP (λ(x_,v_,tau_). v_) x_v_tau_list'’ by IMP_RES_TAC lemma_MAP5 >> gvs[] >>

 SIMP_TAC list_ss [map_tmp_lemma] >> gvs[] >>

 SIMP_TAC list_ss [LIST_EQ_REWRITE] >> gvs[] >>
 REPEAT STRIP_TAC >>     

  
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`x`])) >> gvs[] >>
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`x`])) >> gvs[] >>

 fs[deter_svl_typed_def] >>
 gvs[UNZIP_rw] >>


 subgoal `deter_v_typed (EL x (MAP (λ(x_,v_,tau_). v_) x_v_tau_list')) ty ` >-
   (FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL[`(EL x (MAP (λ(x_,v_,tau_). v_) (x_v_tau_list' : (string # v # tau) list)))`])) >>
    rfs[EL_MEM] ) >>
 fs[deter_v_typed_def]
 ,
 fs[Once v_typ_cases]
 ,
 fs[Once v_typ_cases]
 ,
 fs[Once v_typ_cases]
 ,

      (* properties implications *)  
 fs[Once deter_svl_typed_def, deter_sv_tup_typed_def, deter_v_typed_def] >>
 REPEAT STRIP_TAC >>
 gvs[] >> METIS_TAC []
 ,
 fs[Once deter_svl_typed_def, deter_sv_tup_typed_def, deter_v_typed_def] >>
 REPEAT STRIP_TAC >>
 gvs[] >> METIS_TAC []
 ,
 fs[Once deter_svl_typed_def, deter_sv_tup_typed_def, deter_v_typed_def] >>
 REPEAT STRIP_TAC >>
 gvs[] >> METIS_TAC []                         
]        
QED  
        



        

Theorem AFUPDKEY_in_scope_typed_verbose:        
∀ scl tl  v v' s x tau .
similar (λx y. v_typ (FST x) (t_tau y) F) scl tl  ∧
v_typ v (t_tau tau) F ∧
v_typ v' (t_tau tau) F ∧
ALOOKUP scl s = SOME (v',x) ⇒
similar (λx y. v_typ (FST x) (t_tau y) F)
        (AFUPDKEY s (λold_v. (v,x)) scl) tl
Proof
Induct_on ‘tl’ >>
Induct_on ‘scl’ >>
gvs[] >>
REPEAT STRIP_TAC >| [
 fs[similar_def]
 ,  
 subgoal ‘∃ v''. SOME v'' = ALOOKUP (h'::tl) (s) ∧ v_typ v' (t_tau v'') F’ >-
  (IMP_RES_TAC R_implies_ALOOKUP_scopes >>
   gvs[] >>           
   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`s`, `(v',x)`])) >> gvs[] >>  srw_tac [SatisfySimps.SATISFY_ss][] ) >>

 gvs[] >>

(* we know that the types of v' are the same from *)
 subgoal ‘v'' = tau’ >- (
   ASSUME_TAC  v_typ_deter >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`ty`])) >> gvs[] >>
   gvs[deter_v_typed_def] >>
   RES_TAC >> gvs[] ) >>

 rw[] >>

       
 PairCases_on ‘h'’ >> gvs[] >>
 PairCases_on ‘h’ >> gvs[] >>

 subgoal ‘h0=h'0’ >- ( fs[similar_def] >> gvs[] ) >>
 rw[] >>
             
 Cases_on ‘h'0 = s’ >> gvs[] >| [
 
   fs[AFUPDKEY_def] >>
   SIMP_TAC list_ss [Once similar_normalize2] >>
   CONJ_TAC >>

   IMP_RES_TAC similar_normalize2 >>
   gvs[] >>
   fs[similar_def] >> gvs[]
   ,
   IMP_RES_TAC similar_normalize2 >>
   ‘similar (λx y. v_typ (FST x) (t_tau y) F) (AFUPDKEY s (λold_v. (v,x)) scl) tl’ by RES_TAC >>
               
   fs[AFUPDKEY_def] >>
   SIMP_TAC list_ss [Once similar_normalize2] >>
   gvs[]       
  ]
] 
QED
  




Theorem type_scopes_list_single_detr:
∀ h h' h''.
 type_scopes_list [h''] [h] ∧
 type_scopes_list [h''] [h'] ⇒
 h = h'
Proof        

gvs[type_scopes_list_def, similarl_def] >>
Induct_on ‘h’ >>
Induct_on ‘h'’ >>
Induct_on ‘h''’ >>
REPEAT STRIP_TAC >>
gvs[similar_def] >>

PairCases_on ‘h'⁴'’ >>
PairCases_on ‘h'⁵'’ >>
PairCases_on ‘h'³'’ >>
gvs[] >>

ASSUME_TAC  v_typ_deter >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`ty`])) >> gvs[] >>
gvs[deter_v_typed_def] >>
METIS_TAC []
QED




Theorem type_scopes_list_detr:
∀ sl tscl tscl' .
 type_scopes_list sl tscl ∧
 type_scopes_list sl tscl' ==>
 tscl = tscl'
Proof                
     
Induct_on ‘sl’ >>
Induct_on ‘tscl’ >>
Induct_on ‘tscl'’ >>

REPEAT STRIP_TAC >>
IMP_RES_TAC type_scopes_list_LENGTH >>
gvs[] >>

‘type_scopes_list [h''] [h] ∧
 type_scopes_list [h''] [h'] ∧
 type_scopes_list sl tscl' ∧
 type_scopes_list sl tscl ’ by (IMP_RES_TAC type_scopes_list_normalize >> gvs[]) >>

IMP_RES_TAC type_scopes_list_single_detr >> gvs[] >> METIS_TAC []
QED





                                  
Theorem AFUPDKEY_in_scope_typed:   
∀ h' h v v' varn x tau . 
type_scopes_list [h'] [h] ∧
v_typ v (t_tau tau) F ∧
v_typ v' (t_tau tau) F ∧
ALOOKUP h' (varn) = SOME (v',x) ⇒
type_scopes_list [AFUPDKEY (varn) (λold_v. (v,x)) h'] [h]           
Proof
fs[type_scopes_list_def, similarl_def] >>
REPEAT STRIP_TAC >>
IMP_RES_TAC AFUPDKEY_in_scope_typed_verbose
QED



Theorem find_topmost_map_SUC:
∀ sl h varn n scope.
find_topmost_map (h::sl) (varn) = SOME (SUC n,scope) ==>
find_topmost_map sl (varn) = SOME (n,scope)
Proof
REPEAT STRIP_TAC >>                                       
fs[find_topmost_map_def] >>
fs[INDEX_FIND_def] >>
Cases_on ‘(ALOOKUP h varn)’ >> gvs[] >>

Cases_on ‘INDEX_FIND 1 (λsc. IS_SOME (ALOOKUP sc varn)) sl’ >>
Cases_on ‘INDEX_FIND 0 (λsc. IS_SOME (ALOOKUP sc varn)) sl’ >>
gvs[] >>

IMP_RES_TAC P_NONE_hold >> gvs[] >>
PairCases_on ‘x'’ >> gvs[] >>
  
ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:(varn#'a)list``] P_hold_on_next)  >>
LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`0`])) >> RES_TAC >>
gvs[GSYM ADD1] 
QED



val lookup_same_in_topmost_lemma = prove (“
∀ sl varn n scope v' x.      
find_topmost_map sl (varn) = SOME (n,scope) ∧
ALOOKUP scope (varn) = SOME (v',x) ⇒     
lookup_map sl (varn) = SOME (v',x)  ”,                                 

REPEAT STRIP_TAC >>                                                                          
gvs[lookup_map_def] >>
gvs[topmost_map_def]
);   






Theorem AFUPDKEY_in_scopelist_typed_verbose:
∀tsl v v' tau x varn  sl i scope.
  LENGTH tsl > 0 ∧
  type_scopes_list sl tsl ∧ v_typ v (t_tau tau) F ∧
  lookup_map sl varn = SOME (v',x) ∧
  lookup_map tsl varn = SOME tau ∧
  find_topmost_map sl varn = SOME (i,scope) ∧
  v_typ v' (t_tau tau) F ∧ ALOOKUP scope varn = SOME (v',x) ∧
  i < LENGTH sl ⇒
  type_scopes_list (TAKE i sl ⧺ [AFUPDKEY varn (λold_v. (v,x)) scope] ⧺ DROP (SUC i) sl) tsl
Proof
Induct_on ‘sl’ >>
Induct_on ‘tsl’ >>

gvs[] >>
REPEAT STRIP_TAC >>
Cases_on ‘i’ >| [
 gvs[] >>
 IMP_RES_TAC find_topmost_map_HD >>   
 gvs[] >>

 SIMP_TAC list_ss [Once type_scopes_list_normalize] >>
 CONJ_TAC >| [
   ASSUME_TAC AFUPDKEY_in_scope_typed >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`h'`, `h`, `v`, `v'`, `varn`, ‘x’, ‘tau’])) >> gvs[] >>
   IMP_RES_TAC type_scopes_list_normalize >> rfs[]     
   ,
   IMP_RES_TAC type_scopes_list_normalize2 >>
   IMP_RES_TAC type_scopes_list_LENGTH   >>
   gvs[]            
  ]                 
 ,

 gvs[] >>
 SIMP_TAC list_ss [Once  type_scopes_list_normalize] >> CONJ_TAC >| [
   IMP_RES_TAC type_scopes_list_normalize2 >>
   gvs[]       
   ,
   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`tsl`,‘v’,‘v'’,‘tau’,‘x’,‘varn’, ‘n’, ‘scope’])) >> gvs[] >>     
      
   (* make many normalization functions to solve this one*)
   IMP_RES_TAC type_scopes_list_normalize2 >>
   gvs[] >>

   IMP_RES_TAC type_scopes_list_LENGTH   >>
   gvs[] >>
       
   IMP_RES_TAC find_topmost_map_SUC  >>  
   gvs[] >>
   IMP_RES_TAC lookup_same_in_topmost_lemma >>
   gvs[] >>

  
   ‘similarl (λx y. v_typ (FST x) (t_tau y) F) sl tsl’ by   gvs[type_scopes_list_def] >>

   drule (INST_TYPE [``:'a`` |-> ``:(v#lval option)``, ``:'b`` |-> ``:tau``] R_implies_lookup_map_scopesl)  >>
   gvs[] >> REPEAT STRIP_TAC >>
        
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘tau’,‘varn’, ‘(v',x)’])) >> gvs[] >>     
  
   (* we know that the types of v' are the same from *)
   subgoal ‘v'' = tau’ >- (
     ASSUME_TAC  v_typ_deter >>
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`ty`])) >> gvs[] >>
     gvs[deter_v_typed_def] >>
     RES_TAC >> gvs[] ) >>

  rw[] >> gvs[]         
]]
QED


        









          

Theorem AFUPDKEY_in_scopelist_typed:            
∀tsl v v' tau x varn sl i scope x'.
  type_scopes_list sl tsl ∧ v_typ v (t_tau tau) F ∧
  lookup_map sl (varn) = SOME (v',x) ∧
  lookup_map tsl (varn) = SOME tau ∧
  find_topmost_map sl (varn) = SOME (i,scope) ∧
  v_typ v' (t_tau tau) F ∧ ALOOKUP scope (varn) = SOME (v',x) ⇒
  type_scopes_list (LUPDATE (AFUPDKEY (varn) (λold_v. (v,x)) scope) i sl) tsl
Proof
REPEAT STRIP_TAC >>
IMP_RES_TAC find_topmost_map_LENGTH >>
gvs[GSYM LUPDATE_eq] >>
fs[LUPDATE_abstract_def] >>

‘LENGTH tsl > 0 ’ by (IMP_RES_TAC type_scopes_list_LENGTH >> fs[]) >>       
drule AFUPDKEY_in_scopelist_typed_verbose  >>
gvs[]
QED







val find_general_lemma = prove (“
∀ sl scope i x x' varn .
find_topmost_map sl varn = SOME (i,scope) ∧
lookup_map sl varn = SOME x ∧               
ALOOKUP scope varn = SOME x' ⇒
x = x' ”,
REPEAT STRIP_TAC >>
fs[lookup_map_def, topmost_map_def, find_topmost_map_def] >>
Cases_on ‘INDEX_FIND 0 (λsc. IS_SOME (ALOOKUP sc (varn_name s))) sl’ >> gvs[]
);



        

Theorem  assign_LUPDATE_typed:                                                        
∀ sl tsl v v' tau x varn sl sl' i scope.        
  type_scopes_list sl tsl ∧
  v_typ v (t_tau tau) F ∧
  sl' = (LUPDATE (AUPDATE scope (varn,v,x)) i sl) ∧
  lookup_map (sl) (varn) = SOME (v',x) ∧
  lookup_map (tsl) (varn) = SOME tau ∧
  find_topmost_map (sl) (varn) = SOME (i,scope) /\
  v_typ v' (t_tau tau) F ⇒
   type_scopes_list sl' tsl
Proof
REPEAT STRIP_TAC >>
fs[AUPDATE_def] >>
CASE_TAC >> gvs[]  >| [
 IMP_RES_TAC find_topmost_map_not_none
 ,    
 (* now show that ALOOKUP in scope result x' is the same as lookup map in sl *)
 ‘(v',x) = x'’ by IMP_RES_TAC find_general_lemma >>
 PairCases_on ‘x'’ >> gvs[] >>
 IMP_RES_TAC AFUPDKEY_in_scopelist_typed               
]
QED
                     



Theorem  separate_global_local_single:               
∀ l scopest ts tslg gscope  .                    
LENGTH tslg = 2 ∧
type_scopes_list (l) (ts::tslg) ∧                     
(SOME gscope,SOME scopest) = separate (l) ⇒
type_scopes_list gscope (tslg) ∧
type_scopes_list scopest [ts]
Proof
Induct >> gvs[] >-
 (REPEAT STRIP_TAC >> IMP_RES_TAC type_scopes_list_LENGTH >> gvs[]) >>

REPEAT STRIP_TAC >>
IMP_RES_TAC type_scopes_list_LENGTH >> gvs[] >>
       
‘type_scopes_list [h] [ts] ∧
type_scopes_list l tslg’  by  (IMP_RES_TAC type_scopes_list_normalize >> gvs[]) >>
                                          
fs[separate_def] >>
‘SOME gscope = oDROP (SUC 0) (h::l)’ by fs[] >>
gvs[oDROP_def] >>

‘SOME scopest = oTAKE (SUC 0) (h::gscope)’ by fs[] >>
gvs[oTAKE_def]
QED        




(*
EVAL “oDROP 2 [a;b;c]”
EVAL “oDROP 0 [b;c]”
*)



val oDROP_l_2 = prove (“
∀ l i gl.
  LENGTH l >= 2 ∧ i = (LENGTH l − 2) ∧
  SOME gl = oDROP i l ⇒
  LENGTH gl = 2 ” ,
Induct >>            
Induct_on ‘i’ >>

gvs[oDROP_def] >> 
REPEAT STRIP_TAC >> gvs[] >>
gvs[ADD1] >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`gl`])) >> gvs[] >>

‘i = LENGTH l − 2’ by gvs[] >>
fs[]
);     


val oTAKE_l_2 = prove (“
∀ l i scl.
  LENGTH l >= 2 ∧ i = (LENGTH l − 2)  ∧
  SOME scl = oTAKE i l ⇒
  LENGTH scl = LENGTH l − 2”,

Induct >>            
Induct_on ‘i’ >>

gvs[oTAKE_def] >> 
REPEAT STRIP_TAC >> gvs[] >>
gvs[ADD1] >>


Cases_on ‘oTAKE i l’ >> gvs[] >>        
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`x`])) >> gvs[] >>
            
‘i = LENGTH l − 2’ by gvs[] >>
fs[]
);                          



     
val separate_LENGTH = prove (“
∀ l gl scl.
  LENGTH l >= 2 ∧ (SOME gl,SOME scl) = separate l ⇒
  LENGTH gl = 2 ∧ LENGTH scl = LENGTH l - 2 ”,
                             
REPEAT GEN_TAC >>
STRIP_TAC >>
fs[separate_def] >>
IMP_RES_TAC oTAKE_l_2 >>
IMP_RES_TAC oDROP_l_2 >>
gvs[]
);


val oDROP_lemma = prove (“
∀ l i h.        
LENGTH l ≥ 2 ∧
i = LENGTH l − 1 ⇒
oDROP i (h::l) = oDROP (i - 1) l  ” , 
            
Induct_on ‘i’ >>

gvs[oDROP_def] >> 
REPEAT STRIP_TAC >> gvs[] >>
gvs[ADD1]
);



val oTAKE_lemma = prove (“
∀ l i h h' scope.        
LENGTH l ≥ 2 ∧
i = LENGTH l − 1 ∧
SOME (h'::scope) = oTAKE i (h::l) ⇒              
SOME (scope) = oTAKE (i - 1) l  ” ,
                          
Induct_on ‘i’ >>

gvs[oTAKE_def] >> 
REPEAT STRIP_TAC >> gvs[] >>

Cases_on ‘oTAKE i l’ >>       
gvs[ADD1] 
);


        
val separate_normalize = prove (“
∀ gscope scopest h h'' l.
 LENGTH l ≥ 2 ∧ 
 (SOME gscope,SOME (h::scopest)) = separate (h''::l) ⇒
 (SOME gscope,SOME scopest) = separate l”,

gvs[separate_def] >>
REPEAT STRIP_TAC >>
gvs[ADD1] >>
gvs[oDROP_lemma] >>

IMP_RES_TAC oTAKE_lemma >>
gvs[] 
);
                                        



val oTAKE_head = prove (
“∀ l i h h' scopest.
 LENGTH l ≥ 2 ∧ i = LENGTH l − 1 ∧  
 SOME (h::scopest) = oTAKE i (h'::l) ⇒
 h=h' ”,

Induct_on ‘i’ >>

gvs[oTAKE_def] >> 
REPEAT STRIP_TAC >> gvs[] >>

Cases_on ‘oTAKE i l’ >>       
gvs[ADD1]
);


        


val separate_head = prove ( 
“ ∀ gscope scopest h h' l.
LENGTH l ≥ 2 ∧ 
(SOME gscope,SOME (h::scopest)) = separate (h'::l) ⇒
h = h'”,
gvs[separate_def] >>
REPEAT STRIP_TAC >>
gvs[ADD1] >>
IMP_RES_TAC oTAKE_head >>
gvs[]
);




        

Theorem  separate_global_local: 
∀ l scopest ts tslg gscope  .                    
LENGTH tslg = 2 ∧
type_scopes_list (l) (ts++tslg) ∧                     
(SOME gscope,SOME scopest) = separate (l) ⇒
type_scopes_list gscope (tslg) ∧
type_scopes_list scopest ts
Proof
  
Induct_on ‘l’ >> gvs[] >-
 (REPEAT STRIP_TAC >> IMP_RES_TAC type_scopes_list_LENGTH >> gvs[]) >>


Induct_on ‘ts’ >-
 (
 schneiderUtils.POP_NO_TAC 0 >>        
 REPEAT STRIP_TAC >>
 IMP_RES_TAC type_scopes_list_LENGTH >> gvs[] >>
 gvs[separate_def] >>
 gvs[oDROP_def] >>
 gvs[oTAKE_def] >>
 gvs[type_scopes_list_def, similarl_def] ) >>


Induct_on ‘scopest’  >-
 (
 schneiderUtils.POP_NO_TAC 0 >>
 schneiderUtils.POP_NO_TAC 0 >>
        
 REPEAT STRIP_TAC >>
 IMP_RES_TAC type_scopes_list_LENGTH >> gvs[] >>
 gvs[ADD1] >>
 subgoal ‘LENGTH l >= 2’ >- gvs[] >>
 IMP_RES_TAC separate_LENGTH >> 
 rfs[] ) >>


 schneiderUtils.POP_NO_TAC 1 >>
 schneiderUtils.POP_NO_TAC 0 >>  
 REPEAT STRIP_TAC >>
        


(subgoal ‘type_scopes_list [h''] [h'] ∧ type_scopes_list l (ts++tslg)’ >-
  (ASSUME_TAC type_scopes_list_normalize >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘l’, ‘ts ++ tslg’ , ‘h''’, ‘h'’ ])) >> 
   lfs[] ) >>

LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘scopest’, ‘ts’, ‘tslg’, ‘gscope’ ])) >> 
gvs[] >>

rfs[] >>
       
IMP_RES_TAC type_scopes_list_LENGTH >> gvs[] >>
gvs[ADD1] >>
subgoal ‘LENGTH l >= 2’ >- gvs[] >>

IMP_RES_TAC separate_normalize  >> gvs[] >>
SIMP_TAC list_ss [Once type_scopes_list_normalize] >> gvs[] >>
IMP_RES_TAC  separate_head >>
gvs[]  )              
QED       







val star_not_in_sl_normalization = prove (“
∀ h scl.
star_not_in_sl (h::scl) ⇔
star_not_in_sl [h] ∧
star_not_in_sl scl    ”,     
        
REPEAT STRIP_TAC >>
gvs[star_not_in_sl_def]
);






           

val star_not_in_ts_similar = prove (“
∀ sc ts f.
similar (λx y. v_typ (FST x) (t_tau y) F) sc ts ∧
star_not_in_sl [sc] ⇒
ALOOKUP ts (varn_star f) = NONE ”,          
                              
REPEAT STRIP_TAC >>
fs[star_not_in_sl_def, star_not_in_s_def] >>

FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`f`])) >>               

IMP_RES_TAC  R_ALOOKUP_NONE_scopes >>
gvs[]
);                



                  
val star_not_in_ts_typed = prove (“
∀ scopest ts f.              
type_scopes_list scopest [ts] ∧
star_not_in_sl scopest ⇒
ALOOKUP ts (varn_star f) = NONE ”,

REPEAT STRIP_TAC >>
IMP_RES_TAC type_scopes_list_LENGTH >>
fs[type_scopes_list_def] >>

fs[quantHeuristicsTheory.LIST_LENGTH_1] >>
gvs[similarl_def] >> IMP_RES_TAC star_not_in_ts_similar >> gvs[]
);




val star_not_in_tsl_head_typed = prove (“
∀ scopest tsl ts f.              
type_scopes_list scopest (ts::tsl) ∧
star_not_in_sl scopest ⇒
ALOOKUP ts (varn_star f) = NONE ”,

REPEAT STRIP_TAC >>
IMP_RES_TAC type_scopes_list_LENGTH >>
fs[type_scopes_list_def] >>
gvs[similarl_def] >>
IMP_RES_TAC star_not_in_sl_normalization >>       
IMP_RES_TAC star_not_in_ts_similar >> gvs[]
);



val star_not_in_tsl_INDEX_FIND = prove ( 
“∀ tsl scopest f. 
type_scopes_list scopest (tsl) ∧
star_not_in_sl scopest ⇒
INDEX_FIND 0 (λsc. IS_SOME (ALOOKUP sc (varn_star f))) (tsl) = NONE ”,

Induct >>
gvs[] >-
fs[INDEX_FIND_def] >>
 
Induct_on ‘scopest’ >-
gvs[type_scopes_list_def, similarl_def] >>

REPEAT STRIP_TAC >>
IMP_RES_TAC star_not_in_sl_normalization >>       
SIMP_TAC list_ss [INDEX_FIND_def] >>
CASE_TAC >| [
 IMP_RES_TAC type_scopes_list_normalize >>
 gvs[type_scopes_list_def, similarl_def] >>
 IMP_RES_TAC star_not_in_ts_similar >> gvs[]
 ,   
 RES_TAC >>
 IMP_RES_TAC type_scopes_list_normalize >>
 gvs[] >>
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`f`])) >>               
 IMP_RES_TAC P_NONE_hold >>
 gvs[]
]
);
                          










val star_not_in_sl_INDEX_FIND_cases = prove (“   
∀ tsl tslg scopest scope i f. 
 type_scopes_list scopest tsl ∧
 star_not_in_sl scopest ∧
 INDEX_FIND 0 (λsc. IS_SOME (ALOOKUP sc (varn_star f))) (tsl ⧺ tslg) = SOME (i,scope) ⇒
 (∃ i'. INDEX_FIND 0 (λsc. IS_SOME (ALOOKUP sc (varn_star f))) (tslg) = SOME (i',scope)) ∧
 INDEX_FIND 0 (λsc. IS_SOME (ALOOKUP sc (varn_star f))) (tsl) = NONE ”,
                                                                
REPEAT GEN_TAC >> STRIP_TAC >> gvs[] >>
IMP_RES_TAC star_not_in_tsl_INDEX_FIND >> gvs[] >>

FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`f`])) >>
                                                
Cases_on ‘INDEX_FIND 0 (λsc. IS_SOME (ALOOKUP sc (varn_star f))) tslg’ >> gvs[] >-
  (IMP_RES_TAC INDEX_FIND_concat3 >> gvs[]) >>
PairCases_on ‘x’ >> gvs[] >>
        
ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:(varn#tau)list``] index_find_concat2)  >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [‘tslg’,`tsl`, ‘(i,scope)’, ‘(x0,x1)’, ‘(λsc. IS_SOME (ALOOKUP sc (varn_star f)))’])) >>
gvs[]
);

        
        


Theorem lookup_map_in_gsl_lemma2:
∀ scopest tsl tslg f tau.
 type_scopes_list scopest tsl ∧
 star_not_in_sl scopest ∧
 lookup_map tslg (varn_star f) = SOME tau  ⇒
 lookup_map (tsl++tslg) (varn_star f) = SOME tau
Proof
gvs[lookup_map_def] >>
gvs[topmost_map_def] >>
gvs[find_topmost_map_def] >>
REPEAT STRIP_TAC >>
Cases_on ‘INDEX_FIND 0 (λsc. IS_SOME (ALOOKUP sc (varn_star f))) (tsl++tslg)’ >> gvs[] >| [

 Cases_on ‘INDEX_FIND 0 (λsc. IS_SOME (ALOOKUP sc (varn_star f))) tslg’ >>gvs[] >>
 PairCases_on ‘x’ >> gvs[] >>
 Cases_on ‘ALOOKUP x1 (varn_star f)’ >> gvs[] >>

 IMP_RES_TAC index_find_not_mem >>
 gvs[INDEX_FIND_concat3 ]
 ,

 PairCases_on ‘x’ >> gvs[] >>
 Cases_on ‘INDEX_FIND 0 (λsc. IS_SOME (ALOOKUP sc (varn_star f))) tslg’ >> gvs[] >>
 PairCases_on ‘x’ >> gvs[] >>
 Cases_on ‘ALOOKUP x1' (varn_star f)’ >> gvs[] >>
 Cases_on ‘ALOOKUP x1 (varn_star f)’ >> gvs[] >-
 gvs[INDEX_FIND_EQ_SOME_0] >>
 IMP_RES_TAC star_not_in_sl_INDEX_FIND_cases >> gvs[]                     
]
QED




                
val star_not_in_ts_scope_lemma = prove (“
∀ sc sc' ts.
type_scopes_list [sc] [ts] ∧
type_scopes_list [sc'] [ts] ∧
star_not_in_sl [sc] ⇒
star_not_in_sl [sc'] ”,

REPEAT STRIP_TAC >>

subgoal ‘∀f. ALOOKUP ts (varn_star f) = NONE’ >-
  (IMP_RES_TAC star_not_in_ts_similar >>
   gvs[type_scopes_list_def,similarl_def] >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`ts`]))) >>               
               
gvs[star_not_in_sl_def, star_not_in_s_def] >>
gvs[type_scopes_list_def, similarl_def] >>
IMP_RES_TAC R_ALOOKUP_NONE_scopes >> gvs[]
);
        
   



                
Theorem star_not_in_sl_lemma: 
∀ scopest scopest' ts ts' .
type_scopes_list scopest ts ∧
type_scopes_list scopest' ts ∧
star_not_in_sl scopest ⇒
star_not_in_sl scopest'
Proof

Induct_on ‘scopest’ >>
Induct_on ‘scopest'’ >>
Induct_on ‘ts’ >>

REPEAT STRIP_TAC >>
IMP_RES_TAC type_scopes_list_LENGTH >>
gvs[] >>
                               
rfs[Once type_scopes_list_normalize] >>
rfs[Once star_not_in_sl_normalization ] >>
SIMP_TAC list_ss [Once star_not_in_sl_normalization] >>
RES_TAC >> gvs[] >>
IMP_RES_TAC star_not_in_ts_scope_lemma  >> gvs[]
QED
         


        
Theorem assign_variables_typed:
∀ scopest ts gscope tslg T_e v tau v' assigned_sl gscope' scopest'.
 LENGTH tslg = 2 ∧
 type_scopes_list scopest ts ∧
 type_scopes_list gscope tslg ∧
 star_not_in_sl scopest ∧
 lval_typ (tslg,ts) T_e (lval_varname v) (t_tau tau) ∧
 v_typ v' (t_tau tau) F ∧
 SOME assigned_sl = assign (scopest ⧺ gscope) v' (lval_varname v) ∧
   (SOME gscope',SOME scopest') = separate assigned_sl ⇒
   type_scopes_list gscope' tslg ∧ type_scopes_list scopest' ts ∧
   star_not_in_sl scopest'
Proof
REPEAT GEN_TAC >> STRIP_TAC>>
Cases_on ‘v’ >> gvs[] >> 
gvs[Once lval_typ_cases] >>
OPEN_EXP_TYP_TAC “(e_var v)” >>
gvs[] >| [

 fs[assign_def] >>
 fs[lookup_tau_def] >>

 Cases_on ‘find_topmost_map (scopest ⧺ gscope) (varn_name s)’ >> gvs[] >>
 PairCases_on `x` >>
 gvs[] >>

 Cases_on ‘lookup_out (scopest ⧺ gscope) (varn_name s)’ >> gvs[] >>
 fs[lookup_out_def] >>
 Cases_on ‘lookup_map (scopest ⧺ gscope) (varn_name s)’ >> gvs[] >>

 PairCases_on `x'` >>
 gvs[] >>

 Cases_on ‘lookup_map (ts++tslg) (varn_name s)’ >> gvs[] >>

 ‘type_scopes_list (scopest ++ gscope) (ts++tslg)’ by fs[type_scopes_list_APPEND] >>

 subgoal ‘v_typ x'0 (t_tau tau) F’ >- (
   fs[type_scopes_list_def] >>
   drule (INST_TYPE [``:'a`` |-> ``:(v#lval option)``, ``:'b`` |-> ``:tau``] R_lookup_map_scopesl)>>
   STRIP_TAC>>           
   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`tau`, `(varn_name s)`, `(x'0,x)`])) >> gvs[]) >>
    
 drule assign_LUPDATE_typed >>
 STRIP_TAC >>
 gvs[] >>
      
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [‘v'’,‘x'0’,‘tau’,‘x’,‘(varn_name s)’, ‘x0’,‘x1’])) >> gvs[] >>
                                     
 ASSUME_TAC separate_global_local >>
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [‘(LUPDATE (AUPDATE x1 (varn_name s,v',x)) x0 (scopest ⧺ gscope))’,‘scopest'’,‘ts’,‘tslg’,‘gscope'’])) >> gvs[] >>

 IMP_RES_TAC star_not_in_sl_lemma >> gvs[]
 ,
 fs[assign_def] >>
 fs[find_star_in_globals_def] >>

 Cases_on ‘find_topmost_map (scopest ⧺ gscope) (varn_star f)’ >> gvs[] >>

 PairCases_on `x` >>
 gvs[] >>
 Cases_on ‘lookup_out (scopest ⧺ gscope) (varn_star f)’ >> gvs[] >>

 fs[lookup_out_def] >>
 Cases_on ‘lookup_map (scopest ⧺ gscope) (varn_star f)’ >> gvs[] >>

 PairCases_on `x'` >>
 gvs[] >>

 Cases_on ‘lookup_map tslg (varn_star f)’ >> gvs[] >>
 ‘type_scopes_list (scopest ++ gscope) (ts++tslg)’ by fs[type_scopes_list_APPEND] >>
 ‘lookup_map (ts++tslg) (varn_star f) = SOME tau’ by IMP_RES_TAC lookup_map_in_gsl_lemma2 >>
                   
  subgoal ‘v_typ x'0 (t_tau tau) F’ >- (
    fs[type_scopes_list_def] >>
    drule (INST_TYPE [``:'a`` |-> ``:(v#lval option)``,``:'b`` |-> ``:tau``] R_lookup_map_scopesl)  >>
    STRIP_TAC>>           
    LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL[`tau`, `(varn_star f)`, `(x'0,x)`])) >> gvs[]  ) >>
    

    
 drule assign_LUPDATE_typed >>
 STRIP_TAC >>
 gvs[] >>
      
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [‘v'’,‘x'0’,‘tau’,‘x’,‘(varn_star f)’, ‘x0’,‘x1’])) >> gvs[] >>
                                     
 ASSUME_TAC separate_global_local >>
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [‘(LUPDATE (AUPDATE x1 (varn_star f,v',x)) x0 (scopest ⧺ gscope))’,‘scopest'’,‘ts’,‘tslg’,‘gscope'’])) >> gvs[] >>
 IMP_RES_TAC star_not_in_sl_lemma >> gvs[]
]
QED





val lval_typ_strct_lemma1 = prove (“
∀ tslg ts l T_e x_tau_list struct_ty.
lval_typ (tslg,ts) T_e l (t_tau (tau_xtl struct_ty x_tau_list)) ⇒
∃ varn lval x. l = lval_varname varn ∨ l = lval_field lval x ”,
fs[Once lval_typ_cases] >>
REPEAT STRIP_TAC >>
gvs[]
);





Theorem map_simp_4:
! l1 l2.
  l1 = MAP FST (MAP (λ(a,b,c). (a,b)) l2) <=>
  l1 = MAP (λ(a,b,c). a) l2 
Proof
Induct_on `l1` >>
Induct_on `l2` >>
FULL_SIMP_TAC list_ss [] >>
REPEAT STRIP_TAC>>

PairCases_on `h` >>
fs[]
QED


Theorem map_simp_5:
! l1 l2.
  l1 = MAP FST (MAP (λ(a,b,c). (a,c)) l2) <=>
  l1 = MAP (λ(a,b,c). a) l2 
Proof
Induct_on `l1` >>
Induct_on `l2` >>
FULL_SIMP_TAC list_ss [] >>
REPEAT STRIP_TAC>>

PairCases_on `h` >>
fs[]
QED






Theorem lookup_lval_varn_is_wt:
∀ gsl sl gtsl tsl T_e s tau v .
 type_scopes_list gsl gtsl ∧
 type_scopes_list sl  tsl ∧
 star_not_in_sl sl ∧
 lval_typ (gtsl,tsl) T_e (lval_varname s) (t_tau tau) ∧
 lookup_lval (sl ⧺ gsl) (lval_varname s) = SOME v ⇒
  v_typ v (t_tau tau) F
Proof

REPEAT STRIP_TAC >>
fs[Once lval_typ_cases] >>
fs[Once e_typ_cases] >| [

 Cases_on ‘s’ >> gvs[] >>  
 fs[lookup_lval_def] >> gvs[] >>
                  
 fs[lookup_v_def] >>
 fs[lookup_tau_def] >>
                 
 Cases_on ‘lookup_map (tsl ⧺ gtsl) (varn_name s')’ >> gvs[] >>
 Cases_on ‘lookup_map (sl ⧺ gsl) (varn_name s')’ >> gvs[] >>

 PairCases_on ‘x’ >>
 fs[] >> rw[] >>

 subgoal `type_scopes_list (sl ⧺ gsl) (tsl ⧺ gtsl)` >-
 IMP_RES_TAC type_scopes_list_APPEND >>


 fs[type_scopes_list_def] >>
 IMP_RES_TAC R_lookup_map_scopesl >>

 LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`varn_name s'`,`tau`])) >>
 gvs[]
 ,

 gvs[clause_name_def] >>
 fs[lookup_lval_def] >> gvs[] >>

 fs[lookup_v_def] >>                    
 fs[find_star_in_globals_def] >>

 Cases_on ‘lookup_map gtsl (varn_star funn')’ >> gvs[] >>
 Cases_on ‘lookup_map (sl ⧺ gsl) (varn_star funn')’ >> gvs[] >>

 PairCases_on ‘x’ >>
 fs[] >> rw[] >>
 IMP_RES_TAC lookup_map_in_gsl_lemma >> rfs[] >>
 LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`v`,`x1`,‘gsl’,‘funn'’])) >>
 gvs[] >>

 fs[type_scopes_list_def] >>

 ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:(v#lval option)``, ``:'b`` |-> ``:tau``] R_lookup_map_scopesl)  >>      
     
 LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`(λx y. v_typ (FST x) (t_tau y) F)`, `(tau)`, `(varn_star funn')`,
  `(v,x1)`, `(gtsl)`, `(gsl)`])) >>
   gvs[]                              
]        
QED






        
    
val lookup_struct_is_wt = prove (“
∀l v tslg ts x_tau_list T_e struct_ty tsl gscope scopest.
 type_scopes_list gscope tslg ∧                                   
 type_scopes_list scopest tsl ∧
 star_not_in_sl scopest ∧
 lval_typ (tslg,tsl) T_e l (t_tau (tau_xtl struct_ty x_tau_list)) ∧                  
 lookup_lval (scopest ⧺ gscope) l  = SOME v ⇒
    ( v_typ v (t_tau (tau_xtl struct_ty x_tau_list)) F) ”,
Induct >>
REPEAT STRIP_TAC >>
IMP_RES_TAC lval_typ_strct_lemma1 >> gvs[] >| [
 IMP_RES_TAC lookup_lval_varn_is_wt              
 ,

 fs[lookup_lval_def] >> gvs[] >>
 Cases_on ‘lookup_lval (scopest ⧺ gscope) l’ >>  gvs[] >>
 OPEN_LVAL_TYP_TAC “(lval_field l s)” >> rfs[] >>

 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`x`, ‘tslg’, ‘x_tau_list'’, ‘T_e’, ‘struct_ty'’, ‘tsl’, ‘gscope’, ‘scopest’])) >> gvs[] >>

 IMP_RES_TAC acc_struct_val_typed 
]
);



val INDEX_FIND_exists_pair_lemma = prove (“
∀ x_v_tau_list i x s .
INDEX_FIND 0 (λxm. xm = s) (MAP (λ(x_,v_,tau_). x_) x_v_tau_list) =  SOME (i,x) ⇒
∃v. INDEX_FIND 0 (λ(xm,tm). xm = s) (MAP (λ(x_,v_,tau_). (x_,v_)) x_v_tau_list) =  SOME (i,x,v) ”,
Induct >>
gvs[INDEX_FIND_def] >>
REPEAT STRIP_TAC >>
PairCases_on ‘h’ >> gvs[] >>
Cases_on ‘h0 = s’ >> gvs[] >>

ASSUME_TAC P_hold_on_next  >>

LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`0`,`(MAP (λ(x_,v_,tau_). x_) x_v_tau_list)`, `(λxm. xm = s)`, `(i,x)`])) >>
gvs[GSYM ADD1] >> 
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`i-1`,`x`,‘s’])) >>
gvs[] >>

IMP_RES_TAC P_implies_next >>
gvs[GSYM ADD1] 
);  

                                                                                                



   
val LUPDATE_pair_lemma = prove (“
 ∀ l i s v .
i < LENGTH l ⇒
LUPDATE (s,v) i (MAP (λ(x_,v_,tau_). (x_,v_)) l) =
        ZIP (LUPDATE s i (MAP (λ(x_,v_,tau_). x_) l),
             LUPDATE v i (MAP (λ(x_,v_,tau_). v_) l)) ”, 
Induct >>
Induct_on ‘i’ >>
 gvs[LUPDATE_def] >|[
 subgoal ‘∀l . MAP (λ(x_,v_,tau_). (x_,v_)) l =
          ZIP (MAP (λ(x_,v_,tau_). x_) l,MAP (λ(x_,v_,tau_). v_) l)’ >-
   (Induct >> REPEAT STRIP_TAC >> gvs[] >> PairCases_on ‘h’ >> gvs[]) >>
 gvs[]
 ,
       
 REPEAT STRIP_TAC >>
 PairCases_on ‘h’ >> gvs[]
]
);




val LUPDATE_EL_lemma = prove (“
∀ l i s .
i < LENGTH l ∧  EL i l = s ⇒            
LUPDATE s i l = l”,  
Induct >>
Induct_on ‘i’ >>
gvs[] >| [
 STRIP_TAC >> gvs[LUPDATE_def]
 ,
 REPEAT STRIP_TAC >>
 gvs[] >>
 RES_TAC >> 
 gvs[LUPDATE_def]
]
);





Theorem LUPDATE_header_struct_v_typed:
∀ xtl xvl s v tau struct_ty n b.
 (correct_field_type xtl s tau /\
  INDEX_OF s (MAP FST xvl) = SOME n ∧
  v_typ v (t_tau tau) F) ⇒
     (v_typ (v_struct xvl) (t_tau (tau_xtl struct_ty xtl)) F ==>
      v_typ (v_struct (LUPDATE (s,v) n xvl)) (t_tau (tau_xtl struct_ty xtl)) F) 
     ∧
     (v_typ (v_header b xvl) (t_tau (tau_xtl struct_ty xtl)) F ==>
      v_typ (v_header b (LUPDATE (s,v) n xvl)) (t_tau (tau_xtl struct_ty xtl)) F)         
Proof

REPEAT STRIP_TAC >>
 (SIMP_TAC list_ss [Once v_typ_cases] >> gvs[] >>
  OPEN_V_TYP_TAC “any” >> gvs[] >>
       
  fs[correct_field_type_def, tau_in_rec_def] >>                   
  Cases_on ‘FIND (λ(xm,tm). xm = s) (MAP (λ(x_,v_,tau_). (x_,tau_)) x_v_tau_list)’ >> gvs[] >>
  fs[FIND_def] >> PairCases_on ‘z’ >> gvs[] >>
              
  Cases_on ‘z2 = tau’ >> gvs[] >>
  fs[INDEX_OF_def] >>

  (* show that the indexes are the exact same *)
 
  ‘$= s = ((λ(xm). xm = s)) ’ by METIS_TAC[] >>
  gvs[] >>

  ‘INDEX_FIND 0 (λxm. xm = s) (MAP (λ(x_,v_,tau_). (x_)) x_v_tau_list) = SOME z ’  by  METIS_TAC [map_simp_4] >>
          
  PairCases_on ‘z’ >>
  IMP_RES_TAC INDEX_FIND_exists_pair_lemma >>
  rfs[] >>
 
  IMP_RES_TAC INDEX_FIND_same_list_2 >> rfs[] >> rw[] >>

  (* now show that the s is *)
  subgoal ‘z1' = s’ >- (IMP_RES_TAC INDEX_FIND_EQ_SOME_0 >> gvs[]) >>
  gvs[] >>

  Q.EXISTS_TAC ‘ZIP ( LUPDATE (s) z0 (MAP (λ(x_,v_,tau_). (x_)) x_v_tau_list) ,
                ZIP ( LUPDATE (v) z0 (MAP (λ(x_,v_,tau_). (v_)) x_v_tau_list) ,
                        MAP (λ(x_,v_,tau_). (tau_)) x_v_tau_list  ))’ >> 
  rfs[map_distrub] >> rw[] >| [ 
    IMP_RES_TAC LUPDATE_pair_lemma >> gvs[]
    ,
    ‘EL z0 (MAP FST (MAP (λ(x_,v_,tau_). (x_,v_)) x_v_tau_list)) = s’ by IMP_RES_TAC INDEX_FIND_EQ_SOME_0>>
    ‘EL z0 (MAP (λ(x_,v_,tau_). (x_)) x_v_tau_list) = s’ by METIS_TAC [map_simp_4] >>
    IMP_RES_TAC LUPDATE_EL_lemma >> gvs[] >>

    subgoal ‘∀x_v_tau_list . MAP (λ(x_,v_,tau_). (x_,tau_)) x_v_tau_list =
          ZIP (MAP (λ(x_,v_,tau_). x_) x_v_tau_list,MAP (λ(x_,v_,tau_). tau_) x_v_tau_list)’ >-
      (Induct >> REPEAT STRIP_TAC >> gvs[] >> PairCases_on ‘h’ >> gvs[]) >>
    gvs[] >>
    METIS_TAC [map_rw1]
    ,
  
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`i`])) >> gvs[] >>
    Cases_on ‘i=z0’ >> gvs[EL_LUPDATE]
   ]
)
QED



val lookup_SLICE_is_wt = prove (“
∀l tslg T_e tsl gscope scopest w p.
  type_scopes_list gscope tslg ∧
  type_scopes_list scopest tsl ∧
  star_not_in_sl scopest ∧
  lval_typ (tslg,tsl) T_e l (t_tau (tau_bit w)) ∧
  lookup_lval (scopest ⧺ gscope) l = SOME (v_bit p) ⇒
       v_typ (v_bit p) (t_tau (tau_bit w))  F ”,
Induct >>
REPEAT STRIP_TAC >>
gvs[Once lval_typ_cases] >| [

 ASSUME_TAC lookup_lval_varn_is_wt  >>
 fs[Once lval_typ_cases] >>
 gvs[] >>
 RES_TAC               
 ,
 fs[lookup_lval_def] >> gvs[] >>
 Cases_on ‘lookup_lval (scopest ⧺ gscope) l’ >> gvs[] >>
 ‘v_typ x (t_tau (tau_xtl struct_ty x_tau_list)) F’ by IMP_RES_TAC lookup_struct_is_wt >>
 IMP_RES_TAC acc_struct_val_typed
 ,
 fs[lookup_lval_def] >> gvs[] >>
 Cases_on ‘lookup_lval (scopest ⧺ gscope) l’ >> gvs[] >>
 Cases_on ‘x’ >> gvs[] >> 
 PairCases_on ‘p'’ >> gvs[] >>

 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`tslg`, ‘T_e’, ‘tsl’, ‘gscope’, ‘scopest’,‘w'’,‘(p'0,p'1)’])) >> gvs[] >>

 fs[Once v_typ_cases] >>
 PairCases_on ‘bitv’ >>
 PairCases_on ‘bitv'’ >>       

 gvs[slice_lval_def] >>
 gvs[bits_length_check_def] >>
 gvs[slice_def] >>
 gvs[bitv_bitslice_def] >>
 gvs[vec_to_const_def, bs_width_def]
]
);







Theorem bit_slice_typed:
∀ p p' w bitv bitv' x.                                   
 v_typ (v_bit p) (t_tau (tau_bit (vec_to_const bitv − vec_to_const bitv' + 1))) F ∧
 bits_length_check w (vec_to_const bitv) (vec_to_const bitv') ∧
 assign_to_slice p p' (e_v (v_bit bitv)) (e_v (v_bit bitv')) = SOME x ∧
 v_typ (v_bit p') (t_tau (tau_bit w)) F ⇒
   v_typ x (t_tau (tau_bit w)) F
Proof
REPEAT STRIP_TAC >>
fs[Once v_typ_cases] >>
fs[assign_to_slice_def] >>
PairCases_on ‘bitv’ >>
PairCases_on ‘bitv'’ >>
gvs[] >>
gvs[vec_to_const_def] >>
gvs[bits_length_check_def] >>
PairCases_on ‘p’ >>
PairCases_on ‘p'’ >>
gvs[] >>
gvs[relpace_bits_def] >>
gvs[bs_width_def]
QED       








val assign_typed_verbose = prove (“
 ∀l scopest tsl gscope tslg T_e scopest' gscope' tau b assigned_sl v.
   LENGTH tslg = 2 ∧ type_scopes_list scopest tsl ∧
   star_not_in_sl scopest ∧
   type_scopes_list gscope tslg ∧
   lval_typ (tslg,tsl) T_e l (t_tau tau) ∧
   v_typ v (t_tau tau) F ∧
   SOME assigned_sl = assign (scopest ⧺ gscope) v l ∧
   (SOME gscope',SOME scopest') = separate assigned_sl ⇒
     type_scopes_list gscope' tslg ∧ type_scopes_list scopest' tsl ∧
     star_not_in_sl scopest'  ”,      
                    
Induct >>
REPEAT GEN_TAC>>
STRIP_TAC >| [
          
    (* lval_varname *)
 ASSUME_TAC assign_variables_typed >>
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [‘scopest’,‘tsl’,‘gscope’,‘tslg’,‘T_e’,‘v’,‘tau’,‘v'’,‘assigned_sl’,‘gscope'’,‘scopest'’])) >> gvs[]
 ,
        
   (* lval null *)
 ‘LENGTH tslg = 2’ by fs[WT_c_cases] >>
 ‘LENGTH gscope = 2’ by (IMP_RES_TAC type_scopes_list_LENGTH >> gvs[]) >>
 IMP_RES_TAC assign_to_null_same_scl >>
 gvs[]       
 ,
 
 (*lval feild access *)
 Q.PAT_X_ASSUM `lval_typ (tslg,tsl) T_e (lval_field l s) (t_tau tau)`
               (STRIP_ASSUME_TAC o  SIMP_RULE (srw_ss()) [Once lval_typ_cases] ) >>

        
 (* from assign, we know that the l val that we can access a feild of it, it a v_struct or a v_header*)
 (* two cases, the proof for should be identical *)

 Q.PAT_X_ASSUM `SOME assigned_sl = assign (scopest ⧺ gscope) v (lval_field l s)`
               (STRIP_ASSUME_TAC o  SIMP_RULE (srw_ss()) [assign_def] ) >>

 Cases_on ‘lookup_lval (scopest ⧺ gscope) l’ >> rfs[] >>
 Cases_on ‘x’ >> gvs[] >| [

   (* v_struct *)         
   Cases_on ‘INDEX_OF s (MAP FST l')’ >> gvs[] >>

   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`scopest`, ‘tsl’,‘gscope’, ‘tslg’, ‘T_e’, ‘scopest'’, ‘gscope'’, ‘(tau_xtl struct_ty x_tau_list)’,
   ‘assigned_sl’, ‘(v_struct (LUPDATE (s,v) x l'))’])) >>
   gvs[] >>


   (* we know that l' is well typed, then replacing something in it, that has the same type keeps it well typed *)       
   ASSUME_TAC lookup_struct_is_wt >>

   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [‘l’, ‘(v_struct l')’, ‘tslg’, ‘blah’, ‘x_tau_list’, ‘T_e’, ‘struct_ty’, ‘tsl’, ‘gscope’, ‘scopest’])) >> gvs[] >>


   IMP_RES_TAC LUPDATE_header_struct_v_typed >> gvs[]
   ,
   (* v_header same case as above*)
   Cases_on ‘INDEX_OF s (MAP FST l')’ >> gvs[] >>

   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [`scopest`, ‘tsl’,‘gscope’, ‘tslg’, ‘T_e’, ‘scopest'’, ‘gscope'’, ‘(tau_xtl struct_ty x_tau_list)’,
   ‘assigned_sl’, ‘(v_header b (LUPDATE (s,v) x l'))’])) >>
   gvs[] >>


   (* we know that l' is well typed, then replacing something in it, that has the same type keeps it well typed *)       
   ASSUME_TAC lookup_struct_is_wt >>

   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   [‘l’, ‘v_header b l'’, ‘tslg’, ‘blah’, ‘x_tau_list’, ‘T_e’, ‘struct_ty’, ‘tsl’, ‘gscope’, ‘scopest’])) >> gvs[] >>
   IMP_RES_TAC LUPDATE_header_struct_v_typed >> gvs[]
 ]
 ,

  (* lval slice *)

 Q.PAT_X_ASSUM `lval_typ (tslg,tsl) T_e (lval_slice l e0 e) (t_tau tau)`
               (STRIP_ASSUME_TAC o  SIMP_RULE (srw_ss()) [Once lval_typ_cases] ) >>
 gvs[] >>
      
 gvs[assign_def] >>
 Cases_on ‘v’ >> gvs[] >>               
 Cases_on ‘lookup_lval (scopest ⧺ gscope) l’ >> gvs[] >>
 Cases_on ‘x’ >> gvs[] >>               
 Cases_on ‘assign_to_slice p p' (e_v (v_bit bitv)) (e_v (v_bit bitv'))’ >> gvs[] >>
         
 ASSUME_TAC lookup_SLICE_is_wt >>
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`l`, ‘tslg’,‘T_e’, ‘tsl’,‘gscope’, ‘scopest’, ‘(w)’, ‘p'’])) >>
 gvs[] >>

    
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`scopest`, ‘tsl’,‘gscope’, ‘tslg’, ‘T_e’, ‘scopest'’, ‘gscope'’, ‘ (tau_bit w)’, ‘assigned_sl’, ‘x’])) >>
 gvs[] >>

 IMP_RES_TAC bit_slice_typed  >> gvs[]
 ,

 OPEN_LVAL_TYP_TAC “(lval_paren l)” >> rfs[]
]
);






val F_list_lemma = prove (“
∀ l i .
 i < LENGTH l ⇒ (EL i (MAP (λtd. F) l) = F) ”,
Induct_on ‘l’ >>
Induct_on ‘i’ >>
gvs[]
);



val vl_of_el_normalise = prove (“
∀ vl h .
vl_of_el (h::vl) = (THE (v_of_e h) :: (vl_of_el (vl))) ”,
gvs[vl_of_el_def]
);


val v_types_ev = prove (“
∀ v t tslg ts T_e .
v_typ v (t_tau t) F ⇒ e_typ (tslg,ts) T_e (e_v v) (t_tau t) F ”,
fs[Once e_typ_cases, clause_name_def]
);




val vl_types_evl_F = prove (“
∀ i vl tl T_e tslg ts.        
 i < LENGTH vl ∧ LENGTH vl = LENGTH tl ∧
 is_consts vl ∧
 v_typ (EL i (vl_of_el vl)) (t_tau (EL i tl)) F ⇒
  e_typ (tslg,ts) T_e (EL i vl) (t_tau (EL i tl)) F ”,                                 

Induct_on ‘vl’ >>
Induct_on ‘tl’ >>
Induct_on ‘i’ >>
gvs[] >>

REPEAT STRIP_TAC >| [
 gvs[vl_of_el_normalise] >>
 Cases_on ‘h’ >> gvs[v_of_e_def] >>
 fs[is_consts_def, is_const_def] >>
 IMP_RES_TAC v_types_ev >> gvs[]        
 ,
 gvs[vl_of_el_normalise] >>
 LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`i`,‘tl’,‘T_e’,‘tslg’,‘ts’])) >> gvs[is_consts_def]
]
);






        
Theorem assign_e_is_wt:
∀ l scopest ts gscope tslg T_e scopest' gscope' tau b assigned_sl v.
 LENGTH tslg = 2 ∧
 type_scopes_list scopest ts ∧
 type_scopes_list gscope tslg ∧
 star_not_in_sl scopest ∧

 lval_typ (tslg,ts) T_e l (t_tau tau) ∧
 e_typ (tslg,ts) T_e (e_v v) (t_tau tau) b ∧

 SOME assigned_sl = assign (scopest ⧺ gscope) v l ∧
 (SOME gscope',SOME scopest') = separate assigned_sl ⇒
   type_scopes_list gscope' tslg ∧
   type_scopes_list scopest' ts ∧
   star_not_in_sl scopest'
Proof               
fs[Once e_typ_cases] >>
REPEAT STRIP_TAC >>  
IMP_RES_TAC v_typ_always_lval >>
gvs[] >>
IMP_RES_TAC assign_typed_verbose 
QED

              

val lookup_map_gsl_only = prove ( 
“∀ tsl tslg varn x t .
 lookup_map tslg varn = SOME t ∧
 lookup_map tsl  varn  = NONE ∧
 lookup_map (tsl ⧺ tslg) varn = SOME x ⇒
  x = t ”,
REPEAT GEN_TAC >>
gvs[lookup_map_def] >>
REPEAT (CASE_TAC >> gvs[]) >>
REPEAT STRIP_TAC >>
gvs[] >>

gvs[topmost_map_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 

gvs[find_topmost_map_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 

IMP_RES_TAC index_find_concat2 >>
gvs[] >>
gvs[INDEX_FIND_EQ_SOME_0]     
);




    

val lookup_map_imp_gsl = prove ( 
“∀ tsl tslg varn x .
lookup_map tsl  varn  = NONE ∧
lookup_map (tsl ⧺ tslg) varn = SOME x ⇒
lookup_map tslg varn = SOME x ”,

REPEAT GEN_TAC >>
gvs[lookup_map_def] >>
REPEAT (CASE_TAC >> gvs[]) >>
REPEAT STRIP_TAC >>
gvs[] >>

gvs[topmost_map_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 

gvs[find_topmost_map_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>

IMP_RES_TAC index_find_concat1 >>      
IMP_RES_TAC index_find_concat2 >>
gvs[] >>
gvs[INDEX_FIND_EQ_SOME_0] 
);



Theorem ALOOKUP_imp_lookup_map_lemma:
∀ tslg varn t t'.
 LENGTH tslg = 2 /\
 ALOOKUP (EL 0 tslg) (varn) = NONE ∧
 ALOOKUP (EL 1 tslg) (varn) = SOME t ∧
 lookup_map tslg (varn) = SOME t' ⇒
  t = t'
Proof
gvs[lookup_map_def] >>
REPEAT STRIP_TAC >>
Cases_on ‘topmost_map tslg varn’ >> gvs[] >>
Cases_on ‘ALOOKUP x varn’ >> gvs[] >>

gvs[topmost_map_def] >>
Cases_on ‘find_topmost_map tslg varn’ >> gvs[] >>
PairCases_on ‘x'’ >> gvs[] >>
gvs[find_topmost_map_def] >>
 
Cases_on ‘INDEX_FIND 0 (λsc. IS_SOME (ALOOKUP sc varn)) tslg’>> gvs[] >>
gvs[INDEX_FIND_EQ_SOME_0] >>
fs[quantHeuristicsTheory.LIST_LENGTH_2] >> gvs[] >>
‘x'0 = 0 ∨ x'0 = 1’ by simp[] >> gvs[] 
QED



val ordered_apply_call = prove  ( 
“∀ order s f f'.
 WF_o order ∧  
 order (order_elem_t s) (order_elem_f f) ∧
 order (order_elem_f (funn_name f')) (order_elem_t s) ⇒
 order (order_elem_f (funn_name f')) (order_elem_f f) ”,
REPEAT STRIP_TAC >>                    
gvs[WF_o_def] >>
RES_TAC       
);

        


fun INST_SR2_EXP_FOR (e', tau, b, frl) = PairCases_on ‘c’ >> rename1 ‘WT_c (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)’ >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [e', ‘gscope’, ‘scopest’, frl, ‘tsl’, ‘tslg’, tau, b,
                                      ‘order’,‘delta_g’,‘delta_b’, ‘delta_t’,‘delta_x’,‘f’,‘f_called’,‘stmt_called’,‘copied_in_scope’])) >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘Prs_n’, ‘apply_table_f’, ‘ext_map’, ‘func_map’, ‘b_func_map’, ‘pars_map’, ‘tbl_map’])) >> gvs[] 


val stmt_to_stmt_single = prove (“
∀ stmt stmt'  c order delta_g delta_b delta_x  delta_t tslg tsl
       scopest scopest' gscope gscope' ascope ascope' status status'  framel f Prs_n 
       tdl tau.                                      
                                        
 WT_c c order tslg delta_g delta_b delta_x delta_t  Prs_n ∧                                
 type_scopes_list scopest tsl ∧
 type_scopes_list gscope tslg ∧
 star_not_in_sl scopest ∧
 parseError_in_gs tslg [tsl] ∧

 SOME (tdl,tau) = t_lookup_funn f delta_g delta_b delta_x ∧
 args_t_same (MAP FST tdl) tsl ∧
 stmt_red c (ascope ,gscope,           [(f,[stmt] , scopest )], status )
            (ascope',gscope',framel ⧺ [(f,[stmt'], scopest')], status') ∧
 stmt_typ (tslg,tsl) (order,f,delta_g,delta_b,delta_x,delta_t) Prs_n stmt ⇒

 stmt_typ (tslg,tsl) (order,f,delta_g,delta_b,delta_x,delta_t) Prs_n stmt' ∧   
 type_frame_tsl scopest' tsl ∧
 type_scopes_list gscope' tslg ”,

Induct >>
REPEAT GEN_TAC >>
STRIP_TAC >|  [
                                      
 (*****************************)
 (*   stmt_empty              *)
 (*****************************)
 fs[Once stmt_red_cases]
 ,                                      

 (*****************************)
 (*   stmt_assign             *)
 (*****************************)
 OPEN_STMT_RED_TAC “stmt_ass l e” >>
 gvs[] >| [
   
   SIMP_TAC list_ss [Once stmt_typ_cases] >>
   gvs[clause_name_def] >>
   fs[type_frame_tsl_def] >>
    
   OPEN_STMT_TYP_TAC “stmt_ass l e” >>
   fs[clause_name_def] >>
   gvs[] >| [
     (* any lval *)
     (* we know that v is well typed with tau' which is the same type that types the lval l
        what we need to show is that the result scope list after the assignment preserves the original type *)
     ‘LENGTH tslg = 2’ by fs[WT_c_cases] >>
     ‘LENGTH gscope = 2’ by (IMP_RES_TAC type_scopes_list_LENGTH >> gvs[]) >>
 
     drule assign_e_is_wt >> STRIP_TAC >> 
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
     [`l `, ‘scopest’, ‘tsl’,‘gscope’,‘ (order,f,delta_g,delta_b,delta_x,delta_t)’,‘scopest'’,‘gscope'’,
      ‘tau'’,‘b’, ‘scope_list'’,‘v’])) >>
     gvs[]  
     ,  
     ‘LENGTH tslg = 2’ by fs[WT_c_cases] >>
     ‘LENGTH gscope = 2’ by (IMP_RES_TAC type_scopes_list_LENGTH >> gvs[]) >>
     IMP_RES_TAC assign_to_null_same_scl >>
     gvs[]            
    ]                 
   ,
   (* SR_e case*)

   SIMP_TAC list_ss [Once stmt_typ_cases] >>
   gvs[Once stmt_typ_cases, clause_name_def] >>
   rfs[type_frame_tsl_def] >>
   ASSUME_SR_EXP_FOR ‘e’  >>
   INST_SR2_EXP_FOR (‘e''’, ‘t_tau tau'’, ‘b’, ‘framel’)  >>
   srw_tac [SatisfySimps.SATISFY_ss][]
 ]    
            
,

(*****************************)
(*   stmt_cond               *)
(*****************************)

(* remove the induction hypothesis *)
 schneiderUtils.POP_NO_TAC 10 >>
 schneiderUtils.POP_NO_TAC 9 >>

        
 (* we need to prove it directly from the IH *)
 (* first show that stmt makes a reduction and also it is well typed*)

 OPEN_STMT_RED_TAC “(stmt_cond e stmt stmt')” >>
 FIRST_X_ASSUM MP_TAC >>
 STRIP_TAC >| [ 
   OPEN_STMT_TYP_TAC “(stmt_cond e stmt stmt')” >>    
   srw_tac [boolSimps.DNF_ss][] >>
   fs[type_frame_tsl_def]
   ,
   OPEN_STMT_TYP_TAC “(stmt_cond e stmt stmt')” >>    
   srw_tac [boolSimps.DNF_ss][] >>
   fs[type_frame_tsl_def]
   ,
   SIMP_TAC list_ss [Once stmt_typ_cases] >>
   gvs[Once stmt_typ_cases, clause_name_def] >>
   rfs[type_frame_tsl_def] >>
   ASSUME_SR_EXP_FOR ‘e’  >>
   INST_SR2_EXP_FOR (‘e''’, ‘t_tau tau_bool’, ‘b’, ‘framel’)  >>
   srw_tac [SatisfySimps.SATISFY_ss][]                                 
   ] 
 ,
        
 (*****************************)
 (*   stmt_block              *)
 (*****************************)

 (* the block will never make a step to the same block, it should add 1 to the blocks *)
 OPEN_STMT_RED_TAC “stmt_block l stmt” >>
 gvs[]
 ,
        
 (*****************************)
 (*   stmt_ret                *)
 (*****************************)

 IMP_RES_TAC fr_len_from_a_frame_theorem >| [

   (* when the frame is being return *)            
            
   OPEN_STMT_TYP_TAC “stmt_ret e” >>
   fs[clause_name_def] >> 

   OPEN_STMT_RED_TAC “stmt_ret e” >>
   gvs[] >>

   (* when a single block return e , then use the SR_e *)

   SIMP_TAC list_ss [Once stmt_typ_cases] >>
   gvs[clause_name_def] >>
   ASSUME_SR_EXP_FOR ‘e’  >>
   INST_SR2_EXP_FOR (‘e''’, ‘t_tau tau'’, ‘b’, ‘[(f_called,[stmt_called],copied_in_scope)]’)  >>
   gvs[type_frame_tsl_def] >>              
   srw_tac [SatisfySimps.SATISFY_ss][]
   ,

   (* when a single block has a return v it reduces to stmt empty which is always well typed *)

      
   OPEN_STMT_TYP_TAC “stmt_ret e” >>
   fs[clause_name_def] >>

   OPEN_STMT_RED_TAC “stmt_ret e” >>
   gvs[] >>
     
   SIMP_TAC list_ss [Once stmt_typ_cases] >>
   gvs[clause_name_def] >>
   fs[type_frame_tsl_def] >>

   (* for just a reduction from e to e'' *)
   ASSUME_SR_EXP_FOR ‘e’  >>
   INST_SR2_EXP_FOR (‘e''’, ‘t_tau tau'’, ‘b’, ‘[]’)  >>

   gvs[type_frame_tsl_def] >>              
   srw_tac [SatisfySimps.SATISFY_ss][]
 ]                                               
 ,
        
(*****************************)
(*   stmt_seq                *)
(*****************************)
 schneiderUtils.POP_NO_TAC 9 >>

 OPEN_STMT_RED_TAC “stmt_seq stmt stmt'” >>
 FIRST_X_ASSUM MP_TAC >>
 STRIP_TAC >| [  
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`stmt1'`, ‘c’, ‘order’, ‘delta_g’, ‘delta_b’, ‘delta_x’, ‘delta_t’, ‘tslg’,‘tsl’,
                            ‘scopest’,‘scopest'’,‘gscope’, ‘gscope'’,‘ascope’,‘ascope'’,‘status_running’,‘status_running’,‘framel’,
                            ‘f’, ‘Prs_n’ ,‘tdl’,‘tau’])) >>
    gvs[] >>
    OPEN_STMT_TYP_TAC “stmt_seq stmt stmt'” >>
    rfs[] >> gvs[] >>
    SIMP_TAC list_ss [Once stmt_typ_cases] >> gvs[] 
    ,  
    OPEN_STMT_TYP_TAC “stmt_seq stmt stmt'” >>
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`stmt''`, ‘c’, ‘order’, ‘delta_g’, ‘delta_b’, ‘delta_x’, ‘delta_t’, ‘tslg’,‘tsl’,
                             ‘scopest’,‘scopest'’,‘gscope’, ‘gscope'’,‘ascope’,‘ascope'’,‘status_running’,‘status'’,‘[]’,‘f’,
                             ‘Prs_n’ ,‘tdl’,‘tau’])) >> 
    rfs[] >> gvs[type_frame_tsl_def]          
    ,
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`stmt''`, ‘c’, ‘order’, ‘delta_g’, ‘delta_b’, ‘delta_x’, ‘delta_t’, ‘tslg’,‘tsl’,
                             ‘scopest’,‘scopest'’,‘gscope’, ‘gscope'’,‘ascope’,‘ascope'’,‘status_running’,‘status'’,‘[]’,‘f’,
                             ‘Prs_n’ ,‘tdl’,‘tau’])) >>  

   gvs[] >>       
   OPEN_STMT_TYP_TAC “stmt_seq stmt stmt'” >>
   gvs[] 
 ]
 ,

(*****************************)
(*   stmt_verify             *)
(*****************************)

 IMP_RES_TAC fr_len_from_a_frame_theorem >| [
   (* whenever there is a frame, it means that there were a reduction in e or e' *)
   OPEN_STMT_TYP_TAC “stmt_verify e e0” >>
   fs[clause_name_def] >>

   OPEN_STMT_RED_TAC “stmt_verify e e0” >>
   gvs[] >>

   SIMP_TAC list_ss [Once stmt_typ_cases] >>
   gvs[clause_name_def] >>
   fs[type_frame_tsl_def]
     

   (* for both cases we use the SR_e *) >| [

     (*from e to e'''*)
     ASSUME_SR_EXP_FOR ‘e’ >>
     INST_SR2_EXP_FOR (‘e'''’, ‘t_tau tau_bool’, ‘b’, ‘[(f_called,[stmt_called],copied_in_scope)]’)  >>
     gvs[] >>             
     srw_tac [SatisfySimps.SATISFY_ss][]
     ,
     (*from e0 to e''*)
     ASSUME_SR_EXP_FOR ‘e0’ >>
     INST_SR2_EXP_FOR (‘e''’, ‘t_tau tau_err’, ‘b'’, ‘[(f_called,[stmt_called],copied_in_scope)]’)  >>
     gvs[] >>             
     srw_tac [SatisfySimps.SATISFY_ss][]
   ]
   ,
   (*when new frame is empty, then we do not have an exp reduction *)

   OPEN_STMT_TYP_TAC “stmt_verify e e0” >>
   fs[clause_name_def] >>

   OPEN_STMT_RED_TAC “stmt_verify e e0” >>
   gvs[] >| [
     fs[type_frame_tsl_def] >>
     SIMP_TAC list_ss [Once stmt_typ_cases] >>
     gvs[clause_name_def]
     ,      
     fs[type_frame_tsl_def] >>
     SIMP_TAC list_ss [Once stmt_typ_cases] >>
     gvs[clause_name_def] >>
                      
     SIMP_TAC list_ss [Once stmt_typ_cases] >>
     gvs[clause_name_def] >>
     CONJ_TAC >| [

      Q.EXISTS_TAC ‘tau_err’ >> 
      Q.EXISTS_TAC ‘b'’ >>
                 
      gvs[Once lval_typ_cases, clause_name_def] >>
      gvs[Once e_typ_cases, clause_name_def] >>
      gvs[parseError_in_gs_def] >>
      SIMP_TAC list_ss [Once e_typ_cases, clause_name_def] >> gvs[] >>
      gvs[lookup_tau_def] >>
    
      FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘0’])) >> gvs[] >>           
      Cases_on ‘lookup_map (tsl ⧺ tslg) (varn_name "parseError")’ >> gvs[lookup_map_concat_none] >| [
        ‘LENGTH tslg = 2 ’ by gvs[Once WT_c_cases] >>
        IMP_RES_TAC lookup_map_none_lemma1 >> gvs[]                                             
        ,
        ‘LENGTH tslg = 2 ’ by gvs[Once WT_c_cases] >>
        ‘∀t. lookup_map tslg (varn_name "parseError") = SOME t ⇒ x' = t’ by 
         (IMP_RES_TAC  (INST_TYPE [``:'a`` |-> ``:(tau)``] lookup_map_gsl_only))  >>
        FIRST_X_ASSUM MP_TAC >> SIMP_TAC list_ss [lookup_map_def] >>
        Cases_on ‘topmost_map tslg (varn_name "parseError")’ >> gvs[] >>              
        IMP_RES_TAC lookup_map_imp_gsl >>
        IMP_RES_TAC ALOOKUP_imp_lookup_map_lemma  >> gvs[]          
      ]     
     ,
     SIMP_TAC list_ss [Once stmt_typ_cases] >>
     gvs[clause_name_def] >>
                       
     SIMP_TAC list_ss [Once e_typ_cases] >>
     gvs[clause_name_def] >>  

     SIMP_TAC list_ss [Once v_typ_cases] >>
     gvs[clause_name_def] >>
     Q.EXISTS_TAC ‘["reject"]’ >> gvs[literials_in_P_state_def]           
   ]
   ,

   (* when e reduces but not creating any frames*)

   SIMP_TAC list_ss [Once stmt_typ_cases] >>
   gvs[clause_name_def] >> fs[type_frame_tsl_def] >>
   ASSUME_SR_EXP_FOR ‘e’ >>
   INST_SR2_EXP_FOR (‘e'''’, ‘t_tau tau_bool’, ‘b’, ‘[]’)  >>
   gvs[] >>             
   srw_tac [SatisfySimps.SATISFY_ss][]
   ,
 
   SIMP_TAC list_ss [Once stmt_typ_cases] >>
   gvs[clause_name_def] >> fs[type_frame_tsl_def] >>
   ASSUME_SR_EXP_FOR ‘e0’ >>
   INST_SR2_EXP_FOR (‘e''’, ‘t_tau tau_err’, ‘b'’, ‘[]’)  >>
   gvs[] >>             
   srw_tac [SatisfySimps.SATISFY_ss][]
  ]  
 ]                                        
 ,
 
 (*****************************)
 (*   stmt_trans              *)
 (*****************************)

 IMP_RES_TAC fr_len_from_a_frame_theorem >| [
 (* whenever there is a frame, it means that there were a reduction in e or e' *)
   OPEN_STMT_TYP_TAC “stmt_trans e” >>
   fs[clause_name_def] >>

   OPEN_STMT_RED_TAC “stmt_trans e” >>
   gvs[] >>
   
   SIMP_TAC list_ss [Once stmt_typ_cases] >>
   gvs[clause_name_def] >>
   fs[type_frame_tsl_def] >> 

   ASSUME_SR_EXP_FOR ‘e’ >>
   INST_SR2_EXP_FOR (‘e''’, ‘t_string_names_a x_list’, ‘b’, ‘[(f_called,[stmt_called],copied_in_scope)]’)  >>                
   gvs[] >>             
   srw_tac [SatisfySimps.SATISFY_ss][]                    
   ,

   OPEN_STMT_TYP_TAC “stmt_trans e” >>
   fs[clause_name_def] >>

   OPEN_STMT_RED_TAC “stmt_trans e” >>
   gvs[] >>

      
   SIMP_TAC list_ss [Once stmt_typ_cases] >>
   gvs[clause_name_def] >>
   fs[type_frame_tsl_def] >>

   ASSUME_SR_EXP_FOR ‘e’ >>
   INST_SR2_EXP_FOR (‘e''’, ‘t_string_names_a x_list’, ‘b’, ‘[]’)  >>  
   gvs[] >>             
   srw_tac [SatisfySimps.SATISFY_ss][]
 ]
 ,

 (*****************************)
 (*   stmt_app                *)
 (*****************************)  


 IMP_RES_TAC fr_len_from_a_frame_theorem >| [
   OPEN_STMT_TYP_TAC “stmt_app s l” >>
   fs[clause_name_def] >>

   OPEN_STMT_RED_TAC “stmt_app s l” >>
   gvs[] >>

   (*when all the args are not fully reduced, there might be a chance to create a framel *)

   SIMP_TAC list_ss [Once stmt_typ_cases] >>
   gvs[clause_name_def] >>
   fs[type_frame_tsl_def] >>
   IMP_RES_TAC index_not_const_in_range >>


   PairCases_on ‘c’ >> rename1 ‘WT_c (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)’ >>
                
   (* now we need to know what e has been updated, in order to ensure that it is well typed. *)
   ASSUME_SR_EXP_FOR ‘(EL i (MAP (λ(e_,e'_). e_) (e_e'_list : (e # e) list)))’ >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`e'`, ‘gscope’, ‘scopest’, ‘[(f_called,[stmt_called],copied_in_scope)]’, ‘tsl’,
    ‘tslg’, ‘ (t_tau (EL i (MAP (λ(e_,tau_,b_). tau_) (e_tau_b_list: (e # tau # bool) list))))’,
    ‘(EL i (MAP (λ(e_,tau_,b_). b_) (e_tau_b_list : (e # tau # bool) list)))’,‘order’,‘delta_g’,‘delta_b’, ‘delta_t’,
    ‘delta_x’,‘f’,‘f_called’,‘stmt_called’,‘copied_in_scope’])) >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘Prs_n’ ,‘apply_table_f’, ‘ext_map’, ‘func_map’, ‘b_func_map’, ‘pars_map’, ‘tbl_map’])) >> gvs[] >>
   gvs[] >>


   
   subgoal ‘e_typ (tslg,tsl) (order,f,delta_g,delta_b,delta_x,delta_t)
            (EL i (MAP (λ(e_,e'_). e_) e_e'_list))
            (t_tau (EL i (MAP (λ(e_,tau_,b_). tau_) e_tau_b_list)))
            (EL i (MAP (λ(e_,tau_,b_). b_) e_tau_b_list))’ >-
    (FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`i`])) >>
     gvs[] >>
     ‘LENGTH (MAP (λ(e_,tau_,b_). e_) e_tau_b_list) =
      LENGTH (MAP (λ(e_,e'_). e_) e_e'_list)’ by fs[MAP_EQ_EVERY2] >> 
     gvs[]) >>

   gvs[] >>
              
   Q.EXISTS_TAC ‘ZIP (MAP (λ(e_,e'_). e'_) e_e'_list,
                ZIP( (MAP (λ(e_,tau_,b_). tau_) e_tau_b_list),
                      LUPDATE b' i  (MAP (λ(e_,tau_,b_). b_) e_tau_b_list)  ))’ >>
   rw[] >>


   ‘LENGTH (MAP (λ(e_,tau_,b_). e_) e_tau_b_list) =
    LENGTH (MAP (λ(e_,e'_). e_) e_e'_list)’ by fs[MAP_EQ_EVERY2] >>
   gvs[] >>
   gvs[map_distrub, map_rw1, LENGTH_MAP] >> 
   Cases_on ‘i=i'’ >> gvs[] >>  SRW_TAC [] [EL_LUPDATE] 
   
   ,

   (* when all keys are const then transition to a state null=  call a func *)
   OPEN_STMT_TYP_TAC “stmt_app s l” >>
   fs[clause_name_def] >>

   OPEN_STMT_RED_TAC “stmt_app s l” >>
   gvs[] >| [

     SIMP_TAC list_ss [Once stmt_typ_cases] >>
     gvs[clause_name_def] >>
     fs[type_frame_tsl_def] >>

     DISJ2_TAC >>                       
                                
     SIMP_TAC list_ss [Once e_typ_cases] >>
     gvs[] >>
    
     fs[WT_c_cases] >>
     fs[table_map_typed_def] >>
                       
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
      [`s`, `MAP (λ(e_,mk_). mk_) (e_mk_list : (e # mk) list)`, ‘f''’,‘f'’,‘e'_list’,
       ‘MAP (λ(e_,mk_). e_) (e_mk_list : (e # mk) list)’,‘MAP (λv_. e_v v_) v_list’,‘ascope’])) >>    
     gvs[] >>
  
     Q.EXISTS_TAC ‘tau_bot’ >>
     Q.EXISTS_TAC ‘ZIP (MAP (λv_. e_v v_) v_list ,
                   ZIP (MAP FST tdl' , ZIP ( MAP SND tdl' , MAP (\(td) . F ) tdl')))’ >>                             
     gvs[] >>
     gvs[map_quad_zip112, LENGTH_MAP] >>    
     fs[LENGTH_MAP, clause_name_def] >> rw[] >>
     gvs[map_rw2] >>
     gvs[map_quad_zip112, LENGTH_MAP] >>
     gvs[MAP_ZIP] >>
     gvs[ZIP_MAP_FST_SND] >| [ 
         gvs[t_lookup_funn_def]
         ,
         subgoal ‘EL i (MAP (λtd. F) tdl') = F’ >-
          (  ‘i < LENGTH tdl'’ by gvs[] >>
             IMP_RES_TAC F_list_lemma >> gvs[]) >>
         rfs[] >>

         FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`i`])) >>       
         gvs[] >>
         
         IMP_RES_TAC vl_types_evl_F >> gvs[]
                             
         ,
         
         IMP_RES_TAC directionless_lval_f >>
         subgoal ‘∀ (l:(tau#d)list) . (MAP (λd. F) (MAP SND l)) = (MAP (λtd. F) l)’ >-
          (Induct >> gvs[]) >>

         
         FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘tdl'’])) >>
         gvs[]  
         ,
         (* tbl_map for s is defined, then delta_t is not empty*)
         (** and this because if tbl_map returns something, then indeed we
             can find something in the domain of delta_t, and if we find something
             in the dmain of delta_t, then indeed it is not empty*)            
         
         IMP_RES_TAC ordered_apply_call
       ]

     ,
     (*via SR*) (* i am repeating the proof of SR_stmt_newframe*)
     SIMP_TAC list_ss [Once stmt_typ_cases] >>
     gvs[clause_name_def] >>
     fs[type_frame_tsl_def] >>

     PairCases_on ‘c’ >> rename1 ‘WT_c (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)’ >>
     subgoal ‘ e_typ (tslg,tsl) (order,f,delta_g,delta_b,delta_x,delta_t)
               (EL i (MAP (λ(e_,e'_). e_) e_e'_list))
               (t_tau (EL i (MAP (λ(e_,tau_,b_). tau_) e_tau_b_list)))
               (EL i (MAP (λ(e_,tau_,b_). b_) e_tau_b_list)) ’ >-
      ((* we know that i is less than the length, then the pos of e is well typed*)
      IMP_RES_TAC index_not_const_in_range   >>
      FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`i`])) >>
      gvs[] >>
      
      (* we know that i is indeed less than the list *)
      subgoal ‘i < LENGTH e_tau_b_list’ >- (
        IMP_RES_TAC index_not_const_in_range >>
        gvs[LIST_EQ_REWRITE] )>> gvs[]) >>
     

     (* we know that we are ceating one single frame or nothing *)

     
     ASSUME_TAC SR_e >>
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`ty`])) >>
     LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`(EL i (MAP (λ(e_,tau_,b_). e_) (e_tau_b_list:(e # tau # bool) list)))`])) >>
     fs[sr_exp_def] >>           
     
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`e'`, ‘gscope’, ‘scopest’, ‘[]’, ‘tsl’, ‘tslg’,
                  ‘ (t_tau (EL i (MAP (λ(e_,tau_,b_). tau_) (e_tau_b_list: (e # tau # bool) list))))’,
                  ‘(EL i (MAP (λ(e_,tau_,b_). b_) (e_tau_b_list : (e # tau # bool) list)))’,
                  ‘order’,‘delta_g’,‘delta_b’, ‘delta_t’,‘delta_x’,‘f’,‘f_called’,‘stmt_called’,‘copied_in_scope’])) >>
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘Prs_n’, ‘apply_table_f’, ‘ext_map’, ‘func_map’, ‘b_func_map’, ‘pars_map’, ‘tbl_map’])) >> gvs[] >>

     gvs[] >>
     gvs[] >>             
     srw_tac [SatisfySimps.SATISFY_ss][] >>

     (*1*)        
     Q.EXISTS_TAC ‘ZIP(LUPDATE e' i (MAP (λ(e_,e'_). e_) e_e'_list),
                       ZIP( MAP (λ(e_,tau_,b_). tau_) e_tau_b_list,
                            LUPDATE b' i (MAP (λ(e_,tau_,b_). b_) e_tau_b_list)))’ >> rw[] >>
     rfs[map_distrub] >>

     ‘LENGTH (LUPDATE e' i (MAP (λ(e_,e'_). e_) e_e'_list)) =
      LENGTH (MAP (λ(e_,tau_,b_). tau_) e_tau_b_list)’ by (IMP_RES_TAC MAP_EQ_EVERY2 >> gvs[]) >>
     rfs[map_distrub] >>
                     
     Cases_on `i' = i` >> gvs[] >> SRW_TAC [] [EL_LUPDATE] 
   ]
 ]        
 ,

 (*****************************)
 (*   stmt_ext                *)
 (*****************************)
       
 fs[Once stmt_red_cases] >>
 SIMP_TAC list_ss [Once stmt_typ_cases] >>
 gvs[clause_name_def, type_frame_tsl_def] >>
 fs[Once stmt_typ_cases] >>
 ASSUME_TAC typ_scope_list_ext_out_scope_lemma >>
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
         [`f`, `apply_table_f`, ‘ext_map’,‘func_map’,‘b_func_map’,‘pars_map’,‘tbl_map’,‘order’,‘tslg’,‘delta_g’,‘delta_b’,‘delta_x’,
               ‘ascope’,‘ascope'’,‘gscope’,‘scopest’,‘scopest'’,‘v’,‘ext_fun’,‘tsl’,‘tau’,‘tdl’, ‘delta_t’, ‘Prs_n’])) >>
 gvs[]        
]                                                                          
);                                  






                            
Theorem stmtl_len_from_in_frame_theorem:
∀ stmt stmtl ascope ascope' gscope gscope' scopest scopest' f c status status' framel.
  (stmt_red c ( ascope ,  gscope  , [ (f, [stmt], scopest )]           , status)
              ( ascope',  gscope' , framel ++ [ (f, stmtl , scopest')] , status')) ⇒
                ((LENGTH stmtl = LENGTH [stmt] + 1 ∨ (LENGTH stmtl = LENGTH [stmt])))
Proof
Induct >>
REPEAT GEN_TAC >>
STRIP_TAC >~ [‘LENGTH stmtl = LENGTH [stmt_seq stmt stmt'] + 1 ∨
               LENGTH stmtl = LENGTH [stmt_seq stmt stmt']’] >-
( OPEN_STMT_RED_TAC “stmt_seq stmt stmt'” >>
  gvs[] >>
  RES_TAC >>
  gvs[] ) >> fs[Once stmt_red_cases]
QED

    








val stmtl_stmt_seq_typed_lemma = prove (“
∀ stmt_res stmt Prs_n T_e t_scope_list_g  t_scope_res t_scope_list.
stmtl_typ (t_scope_list_g,t_scope_res::t_scope_list) T_e Prs_n [stmt_res; stmt] ⇒
stmt_typ  (t_scope_list_g,t_scope_res::t_scope_list) T_e Prs_n  stmt_res ∧
stmt_typ  (t_scope_list_g,t_scope_list) T_e Prs_n  stmt ”,                                     
gvs[stmtl_typ_cases] >>
gvs[type_ith_stmt_def] >>
REPEAT STRIP_TAC >| [
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘0’])) >>
 gvs[] >>
 gvs[NOT_NIL_EQ_LENGTH_NOT_0]   
 ,
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘1’])) >>
 gvs[]     
]                
);





val arb_from_tau_typed_def = Define `
 arb_from_tau_typed (t) (ty:'a itself) =
 v_typ (arb_from_tau t) (t_tau t) F
`;


val arb_stl_from_tau_typed_def = Define `
 arb_stl_from_tau_typed l (ty:'a itself) =
    !(st : (string# tau)). MEM st l ==> arb_from_tau_typed (SND st) (ty:'a itself)
`;


        
val arb_st_tup_from_tau_typed_def = Define `
 arb_st_tup_from_tau_typed st_tup (ty:'a itself) =
    arb_from_tau_typed (SND st_tup) (ty:'a itself)
`;

     

            
val arb_EL_lemma = prove (“
∀ i l .
i < LENGTH l ⇒
 ( arb_from_tau (SND (EL i l)) = EL i (MAP (λ(x,tau). arb_from_tau tau) l)) ∧
        (t_tau (SND (EL i l)) = t_tau (EL i (MAP SND l))) ”, 
Induct_on ‘l’ >>
Induct_on ‘i’ >>
gvs[] >| [
 STRIP_TAC >> PairCases_on ‘h’ >> gvs[]
 ,
 STRIP_TAC >> gvs[EL_MAP]
]
);







      
Theorem arb_from_tau_is_typed:
! (ty:'a itself) .
  ( ∀ t .  arb_from_tau_typed t ty ) ∧
  ( ∀ l. arb_stl_from_tau_typed l ty) ∧
  ( ∀ (st: (string#tau)) . arb_st_tup_from_tau_typed st ty)  
Proof

STRIP_TAC >>        
Induct >~ [‘∀s. arb_from_tau_typed (tau_xtl s l) ty’] >- (
 STRIP_TAC >>
 gvs[arb_from_tau_typed_def] >>
 Cases_on ‘s’ >>
 Cases_on ‘l’ >>
 gvs[arb_from_tau_def, Once v_typ_cases, clause_name_def] >| [
        (* struct case *)         

   Q.EXISTS_TAC ‘ZIP(MAP(\(x,tau). x) (h::t),
                ZIP ((MAP (\ (x,tau). arb_from_tau tau) (h::t)) ,
                       MAP (\ (x,tau). tau) (h::t)))’ >>
         
   gvs[] >>
   PairCases_on ‘h’ >> gvs[] >>
   gvs[map_distrub] >>             
   rw[] >| [

     gvs[arb_from_tau_def] >>
                          
     subgoal ‘∀ (l:(string#tau)list) .  MAP (λ(x,t). (x,arb_from_tau t)) l =
             ZIP (MAP (λ(x,tau). x) l,MAP (λ(x,tau). arb_from_tau tau) l) ’  >-      
     (Induct >> gvs[] >> REPEAT STRIP_TAC >> PairCases_on ‘h’ >> gvs[]) >>
     gvs[]
     ,
     
     SIMP_TAC list_ss [lambda_FST, lambda_SND] >>
     fs[ZIP_MAP_FST_SND] 
     ,
     gvs[arb_stl_from_tau_typed_def] >>
     fs[Once EL_compute] >> Cases_on ‘i=0’ >> gvs[EL_CONS] >| [
       FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`(h0,h1)`])) >>
       gvs[arb_from_tau_typed_def]
       ,
       
       FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`EL (PRE i) t`])) >>
       subgoal ‘PRE i < LENGTH t’ >- rfs[] >>
       subgoal ‘MEM (EL (PRE i) t) t’ >- gvs[EL_MEM] >>
       gvs[] >>
       gvs[arb_from_tau_typed_def] >>
       gvs[lambda_SND] >>
       
       ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:(string)``] arb_EL_lemma) >>
       FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`PRE i`,`t`])) >>
       gvs[]
     ]                              
   ]
   ,

   (* header's bool*)
   gvs[Once v_typ_cases, clause_name_def]
   ,
   (* headers case *)
   Q.EXISTS_TAC ‘ZIP(MAP(\(x,tau). x) (h::t),
                 ZIP ((MAP (\ (x,tau). arb_from_tau tau) (h::t)) ,
                       MAP (\ (x,tau). tau) (h::t)))’ >>
   Q.EXISTS_TAC ‘ARB’ >>               
   gvs[] >>
   PairCases_on ‘h’ >> gvs[] >>
   gvs[map_distrub] >>             
   rw[] >| [
     gvs[arb_from_tau_def] >>
                          
     subgoal ‘∀ (l:(string#tau)list) .  MAP (λ(x,t). (x,arb_from_tau t)) l =
               ZIP (MAP (λ(x,tau). x) l,MAP (λ(x,tau). arb_from_tau tau) l) ’  >-      
     (Induct >> gvs[] >> REPEAT STRIP_TAC >> PairCases_on ‘h’ >> gvs[]) >>
     gvs[]
     ,  
     SIMP_TAC list_ss [lambda_FST, lambda_SND] >>
     fs[ZIP_MAP_FST_SND] 
     ,
     gvs[Once v_typ_cases, clause_name_def]
     ,        
     gvs[arb_stl_from_tau_typed_def] >>
     fs[Once EL_compute] >> Cases_on ‘i=0’ >> gvs[EL_CONS] >| [
         FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`(h0,h1)`])) >>
         gvs[arb_from_tau_typed_def]
         ,
                
         FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`EL (PRE i) t`])) >>
         subgoal ‘PRE i < LENGTH t’ >- rfs[] >>
         subgoal ‘MEM (EL (PRE i) t) t’ >- gvs[EL_MEM] >>
         gvs[] >>
         gvs[arb_from_tau_typed_def] >>
         gvs[lambda_SND] >> 

         ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:(string)``] arb_EL_lemma) >>
         FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`PRE i`,`t`])) >>
         gvs[]
       ]                              
   ]
 ] ) >> (

 TRY (
   gvs[arb_stl_from_tau_typed_def, arb_st_tup_from_tau_typed_def] >>
   REPEAT STRIP_TAC >> gvs[] ) >>

 gvs[arb_from_tau_typed_def] >>
 gvs[arb_from_tau_def, Once v_typ_cases, clause_name_def] >>
 gvs[bs_width_def] >>
 gvs[Once v_typ_cases, clause_name_def]
)
QED






        



Theorem declare_similar:
  ∀l. similar (λx y. v_typ (FST x) (t_tau y) F) (declare_list_in_fresh_scope l) l
Proof              
Induct >>
gvs[declare_list_in_fresh_scope_def, similar_def] >>
REPEAT STRIP_TAC >>
PairCases_on ‘h’ >> gvs[] >>
   
ASSUME_TAC arb_from_tau_is_typed >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`ty` ])) >>
LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`h1` ])) >>
fs[arb_from_tau_typed_def]
QED


        
Theorem declare_typed:
  ∀ l . type_scopes_list [declare_list_in_fresh_scope l] [l]
Proof
gvs[type_scopes_list_def] >>
gvs[similarl_def] >>
gvs[declare_similar]
QED


val v_decl_lookup_lemma = prove (“
∀ l varn .
ALOOKUP l varn = NONE ⇒
ALOOKUP (MAP (λ(x,t). (x,arb_from_tau t,NONE)) l) varn = NONE ”,
Induct >> gvs[] >>
REPEAT STRIP_TAC >>
PairCases_on ‘h’ >> gvs[] >>
Cases_on ‘h0 = varn ’ >> gvs[]
);


Theorem star_not_in_decl_ts:                       
∀ l . 
star_not_in_ts l ⇒
star_not_in_sl [declare_list_in_fresh_scope l]
Proof
gvs[star_not_in_ts_def, star_not_in_sl_def, star_not_in_s_def, declare_list_in_fresh_scope_def] >>
REPEAT STRIP_TAC >>
gvs[v_decl_lookup_lemma]
QED





        

fun STMT_STMT_SR_TAC stmt_term = 
      gvs[] >>
        
      (subgoal ‘stmtl ≠ []’ >-         
      (‘∀ (l:stmt list) . LENGTH l = 1 ⇒ l ≠ [] ’ by (Induct>> gvs[]) >> RES_TAC)) >> gvs[] >>
  
     (subgoal ‘∃ stmt_res. stmtl = [stmt_res]’ >-
     (Cases_on ‘stmtl’ >> gvs[]))  >>

      srw_tac [boolSimps.DNF_ss][] >>
      gvs[] >>
      Q.EXISTS_TAC  ‘tau_d_list’ >> gvs[] >>
      Q.EXISTS_TAC  ‘tau’ >> gvs[] >>

      drule (INST_TYPE [``:'a`` |-> ``:'b``] stmt_to_stmt_single)  >>
      STRIP_TAC >>

      FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [ stmt_term  , ‘stmt_res’, ‘t_scope_list’, ‘scopest’, ‘scopest'’,‘gscope’,‘gscope'’ , ‘ascope’, ‘ascope'’, ‘status’,‘status'’, ‘framel’,‘f’,‘tau_d_list’,‘tau’])) >>
    gvs[] >>      

      subgoal ‘args_t_same (MAP FST tau_d_list) t_scope_list’ >-
      (gvs[ELIM_UNCURRY] >> METIS_TAC []) >>
     
      gvs[] >>
      REPEAT STRIP_TAC >>
      ‘i=0’ by fs[] >>
      rw[]


(************************************)
(************************************)
(******      stmt -> stmtl     ******)
(************************************)        
(************************************)

val SR_single_block = prove (“
∀ ty stmt . sr_stmt stmt ty ”,
                     
STRIP_TAC >>
Induct >>
rw[sr_stmt_def] >>

srw_tac [SatisfySimps.SATISFY_ss][SR_stmt_newframe] >>

REPEAT STRIP_TAC >>
fs[Once frame_typ_cases] >>
fs[Once stmtl_typ_cases] >>
fs[Once type_ith_stmt_def] >>

FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`0`])) >>
gvs[] >| [
 (*****************************)
 (*   stmt_empty              *)
 (*****************************)
                                        
 fs[Once stmt_red_cases]
 ,                                      

 (*****************************)
 (*   stmt_assign             *)
 (*****************************)
        
 IMP_RES_TAC stmtl_len_from_in_frame_theorem >>
 gvs[] >| [
   fs[Once stmt_red_cases] >>
   gvs[] 
   ,
   STMT_STMT_SR_TAC ‘stmt_ass l e’
   ]
 ,

 (*****************************)
 (*   stmt_cond               *)
 (*****************************)

 IMP_RES_TAC stmtl_len_from_in_frame_theorem >>
 gvs[] >| [
  fs[Once stmt_red_cases] >>
  gvs[] 
  ,  
  STMT_STMT_SR_TAC ‘stmt_cond e stmt stmt'’
 ]               
 ,
        
 (*****************************)
 (*   stmt_block              *)
 (*****************************)

 IMP_RES_TAC stmtl_len_from_in_frame_theorem >>
 gvs[] >| [
       
   subgoal ‘stmtl ≠ []’ >-         
   (‘∀ (l:stmt list) . LENGTH l = 2 ⇒ l ≠ [] ’ by (Induct>> gvs[]) >> RES_TAC) >> rw[] >>

   (* requires induction *)
   (* here we should solve for only two cases, seq3 and block enter *)
   fs[Once stmt_red_cases] >>
   gvs[] >>
   
   OPEN_STMT_TYP_TAC “(stmt_block t_scope stmt')” >>
   srw_tac [boolSimps.DNF_ss][] >>
   qexistsl_tac [‘[l]’,‘tau_d_list’, ‘tau’] >>
   gvs[] >>

   fs[args_t_same_def] >>
   fs[type_frame_tsl_def] >>
   rw[] >| [
     Cases_on ‘t_scope_list’ >> gvs[]
                                   
     ,
     SIMP_TAC list_ss [Once type_scopes_list_normalize] >>
     gvs[declare_typed]
     ,
     SIMP_TAC list_ss [Once star_not_in_sl_normalization] >>
     gvs[star_not_in_decl_ts]         
     ,
     ‘i=0 ∨ i=1’ by fs[] >>
       gvs[] >> SIMP_TAC list_ss [Once stmt_typ_cases] >> gvs[clause_name_def]       
                                      
     ]            
    ,  
    STMT_STMT_SR_TAC ‘stmt_block l stmt’
 ]                
 ,
        
 (*****************************)
 (*   stmt_ret                *)
 (*****************************)

 IMP_RES_TAC stmtl_len_from_in_frame_theorem >>
 gvs[] >| [
   fs[Once stmt_red_cases] >>
   gvs[] 
   ,  
   STMT_STMT_SR_TAC ‘stmt_ret e’
 ]                                                  
,

(*****************************)
(*   stmt_seq                *)
(*****************************)

 IMP_RES_TAC stmtl_len_from_in_frame_theorem >>
 gvs[] >| [
       
   subgoal ‘stmtl ≠ []’ >-         
    (‘∀ (l:stmt list) . LENGTH l = 2 ⇒ l ≠ [] ’ by (Induct>> gvs[]) >> RES_TAC) >> rw[] >>

   (* requires induction *)
   (* here we should solve for only two cases, seq3 and block enter *)
   fs[Once stmt_red_cases] >>
   gvs[] >>

   OPEN_STMT_TYP_TAC “(stmt_seq stmt1 stmt2)” >>
   gvs[] >>
          
   srw_tac [boolSimps.DNF_ss][] >>
   ‘LENGTH stmt_stack' = 1 ’ by fs[] >>
  
   
   (subgoal ‘∃ stmt_res. stmt_stack' = [stmt_res]’ >-
     (Cases_on ‘stmt_stack'’ >> gvs[]))  >>
     
   srw_tac [][] >>
   Q.PAT_X_ASSUM `sr_stmt stmt ty` (STRIP_ASSUME_TAC o  SIMP_RULE (srw_ss()) [sr_stmt_def] ) >>
             
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [
         `[stmt_res] ⧺ [stmt1']`,
	 `ascope`, `ascope'`,`gscope`,`gscope'`,`scopest`,`scopest'`,
         `framel`, `status_running`,`status_running`, ‘t_scope_list’ ,‘t_scope_list_g’, ‘order’,
         ‘delta_g’,‘delta_b’,‘delta_t’, ‘delta_x’,‘f’,‘Prs_n’])) >> gvs[] >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘apply_table_f’, ‘ext_map’, ‘func_map’, ‘b_func_map’, ‘pars_map’, ‘tbl_map’])) >> gvs[] >>

   subgoal ‘frame_typ (t_scope_list_g,t_scope_list)
            (order,f,delta_g,delta_b,delta_x,delta_t) Prs_n  gscope scopest
            [stmt]’ >-
    (SIMP_TAC list_ss [frame_typ_cases] >> gvs[] >> REPEAT STRIP_TAC >>
     
     Q.EXISTS_TAC ‘tau_d_list’ >>
     Q.EXISTS_TAC ‘tau’ >>
     gvs[] >>  
     SIMP_TAC list_ss [stmtl_typ_cases] >>
     srw_tac [boolSimps.DNF_ss][] >>
     srw_tac [][type_ith_stmt_def] >>
     ‘i=0’ by fs[] >> srw_tac [][]
    ) >>

   gvs[] >>  
   fs[frame_typ_cases] >> gvs[] >>
   gvs[] >>
     
   qexistsl_tac [‘t_scope_list''’,‘tau_d_list’, ‘tau’] >>
   gvs[] >>
          
   (subgoal ‘∃ t_scope_res. t_scope_list'' = [t_scope_res]’ >-
     (Cases_on ‘t_scope_list''’ >> gvs[]))  >>
     
   gvs[] >>
   Cases_on ‘t_lookup_funn f delta_g delta_b delta_x’ >> gvs[] >>
   REPEAT STRIP_TAC >>
   
   ‘i=0 ∨ i=1’ by fs[] >> fs[] >>
   gvs[] >>
   IMP_RES_TAC stmtl_stmt_seq_typed_lemma  >> gvs[] >>
   SIMP_TAC list_ss [Once stmt_typ_cases] >> gvs[]                                      
   ,  
   STMT_STMT_SR_TAC ‘stmt_seq stmt stmt'’
  ]         
 ,

 (*****************************)
 (*   stmt_verify             *)
 (*****************************)

  IMP_RES_TAC stmtl_len_from_in_frame_theorem >>
  gvs[] >| [
    fs[Once stmt_red_cases] >>
    gvs[] 
    ,  
    STMT_STMT_SR_TAC ‘stmt_verify e e0’
   ]       
 ,

 (*****************************)
 (*   stmt_trans              *)
 (*****************************)

 IMP_RES_TAC stmtl_len_from_in_frame_theorem >>
 gvs[] >| [
 fs[Once stmt_red_cases] >>
    gvs[] 
    ,  
    STMT_STMT_SR_TAC ‘stmt_trans e’
  ]               
 ,

 (*****************************)
 (*   stmt_app                *)
 (*****************************)  

 IMP_RES_TAC stmtl_len_from_in_frame_theorem >>
 gvs[] >| [
   fs[Once stmt_red_cases] >>
   gvs[] 
   ,  
   STMT_STMT_SR_TAC ‘stmt_app s l’
 ]                                
,

(*****************************)
(*   stmt_ext                *)
(*****************************)

 IMP_RES_TAC stmtl_len_from_in_frame_theorem >>
 gvs[] >| [
   fs[Once stmt_red_cases] >>
   gvs[] 
   ,  
   STMT_STMT_SR_TAC ‘stmt_ext’
 ]
]
);



        


val sr_stmtl_def = Define `
 sr_stmtl (stmtl) (ty:'a itself) =
∀ stmtl' ascope ascope' gscope gscope' (scopest:scope list) scopest' framel status status' t_scope_list t_scope_list_g T_e (c:'a ctx) order delta_g delta_b delta_t delta_x f Prs_n  n apply_table_f ext_map func_map b_func_map pars_map tbl_map.
      
       type_scopes_list  (gscope)  (t_scope_list_g) ∧
       type_scopes_list  (scopest) (t_scope_list)   ∧
       star_not_in_sl (scopest) ∧
       parseError_in_gs t_scope_list_g [t_scope_list] ∧
       (c = ( apply_table_f , ext_map , func_map , b_func_map , pars_map , tbl_map ) ) ∧

                               
       (WT_c c order t_scope_list_g delta_g delta_b delta_x delta_t Prs_n ) ∧
       (T_e = (order, f, (delta_g, delta_b, delta_x, delta_t))) ∧   
       (frame_typ  ( t_scope_list_g  ,  t_scope_list ) T_e Prs_n  gscope scopest stmtl ) ∧
             
       (stmt_red c ( ascope ,  gscope  ,           [ (f, stmtl, scopest )] , status)
                   ( ascope',  gscope' , framel ++ [ (f, stmtl' , scopest')] , status')) ⇒
       (∃ t_scope_list' .
       res_frame_typ (order,f,(delta_g, delta_b, delta_x, delta_t)) Prs_n t_scope_list_g t_scope_list' gscope framel func_map b_func_map ) ∧
       (
       LENGTH stmtl ≤ LENGTH stmtl' ⇒
       ∃ t_scope_list''  .  LENGTH t_scope_list'' = (LENGTH stmtl' - LENGTH stmtl) ∧
                            frame_typ  ( t_scope_list_g  ,  t_scope_list''++t_scope_list ) T_e Prs_n  gscope' scopest' stmtl') ∧
       (
       LENGTH stmtl > LENGTH stmtl' ⇒
        n = (LENGTH stmtl - LENGTH stmtl') ⇒
        frame_typ  ( t_scope_list_g  ,  (DROP n t_scope_list) ) T_e Prs_n  gscope' scopest' stmtl'
       )                    
`;




Theorem empty_frame_not_typed:
∀ t_scope_list_g t_scope_list T_e Prs_n  scope scopest gscope.
  ~ frame_typ (t_scope_list_g,t_scope_list) T_e Prs_n  gscope scopest []
Proof  
   fs[frame_typ_cases, stmtl_typ_cases, type_ith_stmt_def]
QED



val clause_name_stmtl_red_exec_enter = prove (“
 ∀ ascope ascope' gscope gscope' status status' framel scopest scopest' f h h' t t'  c.

LENGTH t ≤ LENGTH t' ∧
stmt_red c (ascope,gscope,[(f,h::t,scopest)],status)
          (ascope',gscope',framel ⧺ [(f,h'::t',scopest')],status') ⇒
(∀ x . (clause_name x = clause_name "stmt_block_exec") ∧ t=t' ∨
       clause_name x = clause_name "stmt_block_enter" ∧ ~(t=t') ) ”,

REPEAT STRIP_TAC >>
gvs[Once stmt_red_cases] >>
gvs[clause_name_def]
);





Theorem frame_typ_head_of_stmtl:
∀ t_scope_list_g t_scope_list T_e  Prs_n  gscope scopest stmt stmtl.
   frame_typ (t_scope_list_g,t_scope_list) T_e  Prs_n  gscope scopest (stmt::stmtl) ⇒
   frame_typ (t_scope_list_g,t_scope_list) T_e  Prs_n  gscope scopest [stmt]
Proof          

 REPEAT STRIP_TAC >>                                       
fs[Once frame_typ_cases] >>

  Q.EXISTS_TAC ‘tau_d_list’ >>
  Q.EXISTS_TAC ‘tau’ >>
  gvs[] >>   

        
   fs[Once stmtl_typ_cases] >>
   fs[Once type_ith_stmt_def] >>
   srw_tac [boolSimps.DNF_ss][] >>

   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`0`])) >>
gvs[] >>

   ‘i=0’ by gvs[] >> fs[]
QED







val EL_2_lemma = prove (
“∀ l i h h' .
i>1 ⇒
EL (i) (h::h'::l) = (EL (i − 2) l) ”,

REPEAT STRIP_TAC >>
‘i>=2’ by gvs[] >>
fs[Once EL_compute] >> gvs[PRE_SUB1] >>
fs[Once EL_compute] >> gvs[PRE_SUB1]
);


val EL_3_lemma = prove (
“∀ l i h h' .
i>2 ⇒
EL (i − 1) (h::h'::l) = (EL (i − 3) l) ”,

REPEAT STRIP_TAC >>
‘i>=3’ by gvs[] >>
fs[Once EL_compute] >> gvs[PRE_SUB1] >>
fs[Once EL_compute] >> gvs[PRE_SUB1]
);

        
                                

val frame_type_seq_in_sr1 = prove (“
∀ t_scope_list_g  t_scope_list ts T_e Prs_n   gscope' scopest' gscope scopest s1 h h' t'  .                        
frame_typ (t_scope_list_g,t_scope_list) T_e  Prs_n  gscope' scopest' [s1] ∧
frame_typ (t_scope_list_g,t_scope_list) T_e  Prs_n  gscope  scopest (h::h'::t') ⇒
frame_typ (t_scope_list_g,t_scope_list) T_e  Prs_n  gscope' scopest' (s1::h'::t') ”,

REPEAT STRIP_TAC >>                                       
fs[Once frame_typ_cases] >>
qexistsl_tac [‘tau_d_list’,‘tau’] >>

fs[Once stmtl_typ_cases] >>
fs[Once type_ith_stmt_def] >>
srw_tac [boolSimps.DNF_ss][] >>

gvs[ADD1] >>

SIMP_TAC list_ss [Once EL_compute] >>       
Cases_on ‘i=0’ >> gvs[]   >|  [
 (* handles the s1 case *)
 LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`0`])) >>
 gvs[]
 ,
 
 SIMP_TAC list_ss [Once EL_compute] >>
 Cases_on ‘PRE i = 0’ >> gvs[] >| [

   (* handles s2 *)
   gvs[PRE_SUB1] >>
   ‘i=1’ by gvs[] >> fs[] >>           
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`1`])) >> gvs[]
   ,
   gvs[] >>       
   gvs[PRE_SUB1] >>  
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`i`])) >>
   gvs[] >>
   ‘i>1’ by gvs[] >> gvs[EL_2_lemma]
   ]
]

);



        

        
val frame_type_seq_in_sr2 = prove (“
∀ t_scope_list_g  t_scope_list ts T_e Prs_n   gscope' scopest' gscope scopest s1 s2 h h' t'  .                        
frame_typ (t_scope_list_g,ts::t_scope_list) T_e  Prs_n  gscope' scopest' [s1; s2] ∧
frame_typ (t_scope_list_g,t_scope_list)     T_e  Prs_n  gscope  scopest (h::h'::t') ⇒
frame_typ (t_scope_list_g,ts::t_scope_list) T_e  Prs_n  gscope' scopest' (s1::s2::h'::t')”,
        
REPEAT STRIP_TAC >>                                       
fs[Once frame_typ_cases] >>
qexistsl_tac [‘tau_d_list’,‘tau’] >>

fs[Once stmtl_typ_cases] >>
fs[Once type_ith_stmt_def] >>
srw_tac [boolSimps.DNF_ss][] >>
gvs[ADD1] >>

SIMP_TAC list_ss [Once EL_compute] >>       
Cases_on ‘i=0’ >> gvs[]   >|  [
 (* handles the s1 case *)
 LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`0`])) >>
 gvs[]
 ,
 
 SIMP_TAC list_ss [Once EL_compute] >>
 Cases_on ‘PRE i = 0’ >> gvs[] >| [
   (* handles s2 *)
   gvs[PRE_SUB1] >>
   ‘i=1’ by gvs[] >> fs[] >>           
   
   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`1`])) >>
   gvs[]
   ,
   
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`((PRE i))`])) >>
   gvs[] >>       
   gvs[PRE_SUB1] >>
   
     
   SIMP_TAC list_ss [Once EL_compute] >>
   Cases_on ‘PRE (PRE i) = 0’ >> gvs[] >| [
     gvs[PRE_SUB1] >>
     ‘i=2’ by gvs[] >> fs[] >>
     
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`1`])) >>
     gvs[]
     ,
     
     gvs[PRE_SUB1] >>                                      
     ‘i>2’ by gvs[] >> fs[] >>
     
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`PRE i`])) >>
     gvs[] >>
     
     gvs[PRE_SUB1] >> gvs[EL_3_lemma]
    ]
  ]                                   
]
);









val frame_type_block_exit_in_sr = prove (“
∀ t_scope_list_g  t_scope_list ts T_e Prs_n   gscope scopest stmt stmtl  .
  stmtl ≠ [] ∧
frame_typ (t_scope_list_g,t_scope_list) T_e Prs_n  gscope scopest (stmt::stmtl) ⇒
frame_typ (t_scope_list_g,DROP 1 t_scope_list) T_e  Prs_n  gscope (TL scopest) stmtl”,

REPEAT STRIP_TAC >>

REPEAT STRIP_TAC >>                                       
fs[Once frame_typ_cases] >>
qexistsl_tac [‘tau_d_list’,‘tau’] >>

gvs[args_t_same_def] >>
Cases_on ‘t_scope_list’ >> gvs[] >>
gvs[Once stmtl_typ_cases] >>
gvs[] >>

subgoal ‘LENGTH t > 0’ >-
  ( gvs[ADD1] >>
    Cases_on ‘stmtl’ >> gvs[] ) >>

‘t ≠ [] ’ by fs[NOT_NIL_EQ_LENGTH_NOT_0] >>
gvs[LAST_DEF, LAST_CONS_cond] >>
                                         
fs[Once stmtl_typ_cases] >>
fs[Once type_ith_stmt_def] >>
srw_tac [boolSimps.DNF_ss][] >| [
 Cases_on ‘scopest’ >>
 gvs[] >>         
 gvs[type_frame_tsl_def] >>
 gvs[type_scopes_list_def, similarl_def, star_not_in_sl_def]
    
 ,
 
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`i+1`])) >>
 gvs[ADD1] >>
 gvs[Once EL_compute] >> gvs[PRE_SUB1]
                            
]
);













(* here we know that also the frame we create and trying to type, the is empty*)
val SR_stmtl_newframe = prove (“
∀ stmtl stmtl' ascope ascope' gscope gscope' (scopest:scope list) scopest' framel status status' t_scope_list t_scope_list_g T_e (c:'a ctx) order delta_g delta_b delta_t delta_x f Prs_n apply_table_f ext_map func_map b_func_map pars_map tbl_map.
       type_scopes_list  (gscope)  (t_scope_list_g) ∧
       type_scopes_list  (scopest) (t_scope_list)   ∧
       star_not_in_sl (scopest) ∧
       (c = ( apply_table_f , ext_map , func_map , b_func_map , pars_map , tbl_map ) ) ∧        
       (WT_c c order t_scope_list_g delta_g delta_b delta_x delta_t Prs_n) ∧
       (T_e = (order, f, (delta_g, delta_b, delta_x, delta_t))) ∧   
       (frame_typ  ( t_scope_list_g  ,  t_scope_list ) T_e Prs_n  gscope scopest (stmtl) ) ∧
       (stmt_red c ( ascope ,  gscope  ,           [ (f, stmtl, scopest )] , status)
                   ( ascope',  gscope' , framel ++ [ (f, stmtl' , scopest')] , status')) ⇒
       (∃ t_scope_list'.
         res_frame_typ (order, f,(delta_g, delta_b, delta_x, delta_t)) Prs_n t_scope_list_g t_scope_list' gscope framel func_map b_func_map) ”,

STRIP_TAC >>
Cases_on ‘stmtl’ >| [

 fs[sr_stmtl_def] >>
 REPEAT STRIP_TAC >>
 gvs[empty_frame_not_typed]
 ,
 fs[sr_stmtl_def] >>
 REPEAT GEN_TAC >>
 STRIP_TAC >>
 Cases_on ‘t’ >> gvs[] >| [
          
   ASSUME_TAC SR_stmt_newframe >> 
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [
                ‘h’,  `stmtl'`,‘ascope’,‘ascope'’, ‘gscope’,‘gscope'’, ‘scopest’,‘scopest'’,‘framel’,‘status’,‘status'’,
                ‘t_scope_list’, ‘t_scope_list_g’, ‘(order,f,delta_g,delta_b,delta_x,delta_t)’,
                ‘(apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)’,‘order’, ‘delta_g’,
                ‘delta_b’, ‘delta_t’, ‘delta_x’,‘f’, ‘Prs_n’])) >> gvs[] >>                
   srw_tac [SatisfySimps.SATISFY_ss][]
   ,
   gvs[Once stmt_red_cases] >| [

     ASSUME_TAC SR_stmt_newframe >>      
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [
            ‘h’, `stmt_stack'`,‘ascope’,‘ascope'’, ‘gscope’,‘gscope'’, ‘scopest’,‘scopest'’,‘framel’,‘status’,‘status'’,
            ‘t_scope_list’,‘t_scope_list_g’, ‘(order,f,delta_g,delta_b,delta_x,delta_t)’,
            ‘(apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)’,
            ‘order’, ‘delta_g’, ‘delta_b’, ‘delta_t’, ‘delta_x’, ‘f’, ‘Prs_n’])) >> gvs[] >>

                                          
     IMP_RES_TAC frame_typ_head_of_stmtl >> gvs[] >>
     srw_tac [SatisfySimps.SATISFY_ss][] 
     ,
     gvs[Once res_frame_typ_def]
     ]
   ]                               
]
);
        





      
Theorem SR_stmtl_stmtl:
∀ ty stmtl . sr_stmtl stmtl ty
Proof
  
STRIP_TAC >>
Cases_on ‘stmtl’ >| [

 fs[sr_stmtl_def] >>
 REPEAT STRIP_TAC >>
 gvs[empty_frame_not_typed]
 ,

 fs[sr_stmtl_def] >>
 REPEAT GEN_TAC >>
 STRIP_TAC >>
 CONJ_TAC  >| [
   (* first show that the resulted frames are WT*)
   srw_tac [SatisfySimps.SATISFY_ss][SR_stmtl_newframe]              
   ,

   CONJ_TAC >| [
     (* show that the resulted block size is less or equal to initla blocks size then we can type the frame,
        show be directly shown from the stmt -> stmtl proof above *)
     STRIP_TAC >>
     Cases_on ‘t’ >> gvs[] >| [
              
     (* reduce [stmt] -> stmtl*)
     ASSUME_TAC SR_single_block >> 
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`ty`,‘h’])) >>
     fs[sr_stmt_def] >> gvs[] >>
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [
                      `stmtl'`,‘ascope’,‘ascope'’, ‘gscope’,‘gscope'’, ‘scopest’,‘scopest'’,‘framel’,‘status’,‘status'’,
                      ‘t_scope_list’,‘t_scope_list_g’,‘order’, ‘delta_g’, ‘delta_b’, ‘delta_t’, ‘delta_x’, ‘f’, ‘Prs_n’])) >>
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘apply_table_f’, ‘ext_map’, ‘func_map’, ‘b_func_map’, ‘pars_map’, ‘tbl_map’])) >> gvs[] >>

     gvs[] >>
     srw_tac [SatisfySimps.SATISFY_ss][]
     ,
     
     gvs[Once stmt_red_cases] >>
     gvs[ADD1] >>
     ‘1 ≤ LENGTH stmt_stack' ’ by gvs[] >>
     
     ASSUME_TAC SR_single_block >> 
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`ty`,‘h’])) >>
     fs[sr_stmt_def] >> gvs[] >>
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [
                   `stmt_stack'`,‘ascope’,‘ascope'’, ‘gscope’,‘gscope'’, ‘scopest’,‘scopest'’,‘framel’,‘status’,‘status'’,
                   ‘t_scope_list’,‘t_scope_list_g’,‘order’,
                   ‘delta_g’, ‘delta_b’, ‘delta_t’, ‘delta_x’, ‘f’, ‘Prs_n’])) >>
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘apply_table_f’, ‘ext_map’, ‘func_map’, ‘b_func_map’, ‘pars_map’, ‘tbl_map’])) >> gvs[] >>

     gvs[] >>
     
     IMP_RES_TAC frame_typ_head_of_stmtl >> gvs[] >>
     Q.EXISTS_TAC ‘t_scope_list''’  >>               
     gvs[] >>
     
     IMP_RES_TAC stmtl_len_from_in_frame_theorem >> gvs[] >| [
         (* Length of the resulted stack is 2 *)
       ‘∃ ts . t_scope_list'' = [ts] ’ by (Cases_on ‘t_scope_list''’ >> gvs[] ) >>
       ‘∃ s1 s2 . stmt_stack'  = [s1;s2] ’ by (Cases_on ‘stmt_stack'’ >> gvs[] >>
                                               Cases_on ‘t’ >> gvs[] ) >>
       fs[] >> IMP_RES_TAC frame_type_seq_in_sr2
       ,
       
       (* length of resulted stack is 1 *)
       ‘∃ s1 . stmt_stack'  = [s1] ’ by (Cases_on ‘stmt_stack'’ >> gvs[] ) >>        
       fs[] >> IMP_RES_TAC frame_type_seq_in_sr1
     ]
    ]
    ,

   (* case of exiting a block *)

   STRIP_TAC >> 
   fs[ADD1] >>
   gvs[Once stmt_red_cases] >| [
     (* case block exec removing a  frame *)

   ASSUME_TAC SR_single_block >> 
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`ty`,‘h’])) >>
   fs[sr_stmt_def] >> gvs[] >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [
             `stmt_stack'`,‘ascope’,‘ascope'’, ‘gscope’,‘gscope'’, ‘scopest’,‘scopest'’,‘framel’,‘status’,‘status'’,
             ‘t_scope_list’,‘t_scope_list_g’,‘order’,
             ‘delta_g’, ‘delta_b’, ‘delta_t’, ‘delta_x’, ‘f’, ‘Prs_n’])) >> gvs[] >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘apply_table_f’, ‘ext_map’, ‘func_map’, ‘b_func_map’, ‘pars_map’, ‘tbl_map’])) >> gvs[] >>


   IMP_RES_TAC frame_typ_head_of_stmtl >> gvs[] >>
   IMP_RES_TAC stmtl_len_from_in_frame_theorem >> gvs[] >>   
   fs[]
   ,
   IMP_RES_TAC frame_type_block_exit_in_sr >> gvs[] >>
   srw_tac [][]                       
  ]                               
 ]
]]
QED

      




(**********************************************************************)




val (WT_state_rules, WT_state_ind, WT_state_cases) = Hol_reln`
(* defn WT_state *)

( (* WT_state_state *) 
!  (funnl: funn list) (tsll : t_scope_list list) (scll: scope_list list) (stmtll: stmt_stack list)
(ctx:'a ctx) (ascope:'a) (g_scope_list:g_scope_list) (status:status) (Prs_n:Prs_n) (order:order) (t_scope_list_g:t_scope_list_g) (delta_g:delta_g) (delta_b:delta_b) (delta_x:delta_x) (delta_t:delta_t) apply_table_f ext_map func_map b_func_map pars_map tbl_map .

 ( LENGTH funnl = LENGTH tsll /\ LENGTH tsll = LENGTH scll /\ LENGTH tsll = LENGTH stmtll ) /\                                                                                                                                                                          
(WF_ft_order  funnl  delta_g delta_b delta_x order   /\

 type_state_tsll  scll tsll  /\ 

type_scopes_list  g_scope_list   t_scope_list_g  /\

parseError_in_gs  t_scope_list_g   tsll  /\

(ctx = ( apply_table_f , ext_map , func_map , b_func_map , pars_map , tbl_map ) ) ∧                  

WT_c ctx order t_scope_list_g delta_g delta_b delta_x delta_t  Prs_n /\

( ( type_frames  g_scope_list    (ZIP(funnl,ZIP(stmtll,scll)))    Prs_n   order   t_scope_list_g   tsll  delta_g   delta_b   delta_x   delta_t  func_map b_func_map) ))

 ==> 
( ( WT_state ctx  ( ascope ,  g_scope_list ,   (ZIP(funnl,ZIP(stmtll,scll)) ) ,  status )  Prs_n  order t_scope_list_g  ( tsll)   (  delta_g  ,  delta_b  ,  delta_x  ,  delta_t  )  )))

`;



val sr_state_def = Define `
 sr_state (framel) (ty:'a itself) =
∀ framel' (c:'a ctx) ascope ascope' gscope gscope'  status status' tslg  order delta_g delta_b delta_t delta_x Prs_n  tsll.
      
       (WT_state c ( ascope ,  gscope  , framel  , status) Prs_n  order tslg tsll (delta_g, delta_b, delta_x, delta_t)) ∧             
       (frames_red c ( ascope ,  gscope  , framel  , status)
                     ( ascope',  gscope' , framel' , status')) ⇒

 ∃  tsll' .    (WT_state c ( ascope' ,  gscope'  , framel'  , status') Prs_n  order tslg tsll' (delta_g, delta_b, delta_x, delta_t))                  
`;











        



val frame_to_multi_frame_transition1 = prove (“
∀ c ascope ascope' gscope gscope' funn stmtl scope_list frame_list status status'. 
stmt_red c (ascope , gscope , [(funn,stmtl,scope_list)], status)
           (ascope', gscope', frame_list               , status') ⇒
   ∃new_frame stmtl' scope_list'.  frame_list =  new_frame++[(funn,stmtl',scope_list')]  ”,             
REPEAT STRIP_TAC >>
gvs[Once stmt_red_cases] >> gvs[] 
);

        
val frame_to_multi_frame_transition2 = prove (“
∀ c ascope ascope' gscope gscope' funn stmtl scope_list frame_list status status'. 
stmt_red c (ascope, gscope,[(funn,stmtl,scope_list)],status)
           (ascope',gscope',frame_list,status') ⇒
   ∃new_frame stmtl' scope_list'.  frame_list = [(funn,stmtl',scope_list')] ∨
      frame_list =  new_frame++[(funn,stmtl',scope_list')] ”,             

STRIP_TAC >>
gvs[Once stmt_red_cases] >> gvs[] >>
srw_tac [SatisfySimps.SATISFY_ss][] >>
METIS_TAC []
);


val MAP_comp_quad_trio = prove ( 
“∀ l .
MAP (λ(a,b,c,d). (a,b,c)) l  =
     ZIP(MAP (λ(a,b,c,d). a) l,
    ZIP (MAP (λ(a,b,c,d). b) l,
         MAP (λ(a,b,c,d). c) l))”,
Induct >> gvs[] >> REPEAT STRIP_TAC >>
   PairCases_on ‘h’ >> gvs[]
);







(*TODO: take the proof from progress to here *)
val WT_state_HD_of_list = prove (“
∀  ascope gscope f stmtl locale status Prs_n order tslg tsll delta_g delta_b
       delta_x delta_t apply_table_f ext_map func_map b_func_map pars_map
       tbl_map t.
    
    WT_state  ( apply_table_f , ext_map , func_map , b_func_map , pars_map , tbl_map )
              (ascope,gscope,(f,stmtl,locale)::t,status) Prs_n  order tslg
              tsll (delta_g,delta_b,delta_x,delta_t) ⇒

       type_scopes_list  (gscope)  (tslg) ∧
       type_scopes_list  (locale) (HD tsll)   ∧
       star_not_in_sl (locale) ∧
  
             ∃ passed_tslg passed_gscope passed_delta_b passed_b_func_map passed_tbl_map passed_delta_t.
                                              t_scopes_to_pass f delta_g delta_b tslg = SOME passed_tslg ∧                                    
                                               scopes_to_pass f func_map b_func_map gscope = SOME passed_gscope ∧
                                                  map_to_pass f b_func_map = SOME passed_b_func_map ∧
                                                  t_map_to_pass f delta_b = SOME passed_delta_b   ∧
                                                  tbl_to_pass f b_func_map tbl_map = SOME passed_tbl_map ∧
                                                  t_tbl_to_pass f delta_b delta_t = SOME passed_delta_t ∧            
                                                             
WT_c ( apply_table_f , ext_map , func_map , passed_b_func_map , pars_map , passed_tbl_map ) order passed_tslg delta_g passed_delta_b delta_x passed_delta_t Prs_n   ∧
type_scopes_list  passed_gscope passed_tslg   ∧
parseError_in_gs passed_tslg [HD tsll] ∧
(frame_typ  ( passed_tslg ,  (HD tsll) ) (order, f, (delta_g, passed_delta_b, delta_x, passed_delta_t)) Prs_n  passed_gscope locale stmtl )”, cheat);








Theorem ZIP_tri_id1:
(∀l . l = ZIP (MAP (λx. FST x) l, ZIP (MAP (λx. FST (SND x)) l,MAP (λx. SND (SND x)) l)))
Proof          
Induct >>
gvs[] 
QED


Theorem ZIP_tri_id2:        
∀l.  l = ZIP (MAP (λ(f,stmt,sc). f) l, ZIP (MAP (λ(f,stmt,sc). stmt) l,MAP (λ(f,stmt,sc). sc) l))
Proof          
Induct >>
gvs[] >>
REPEAT STRIP_TAC >>
PairCases_on ‘h’ >> gvs[]
QED



Theorem ZIP_tri_sep_ind:
∀ l al bl cl a b c .
LENGTH al = LENGTH bl ∧ LENGTH bl = LENGTH cl ∧  
(a,b,c)::l =  (ZIP (al,ZIP (bl,cl))) ⇒
(a::MAP (λ(al_,bl_,cl_). al_) l) = al ∧
(b::MAP (λ(al_,bl_,cl_). bl_) l) = bl ∧
(c::MAP (λ(al_,bl_,cl_). cl_) l) = cl 
Proof
Induct_on ‘al’ >>
Induct_on ‘bl’ >>
Induct_on ‘cl’ >>
REPEAT STRIP_TAC >>
gvs[] >>
gvs[map_distrub]
QED



      

        
Theorem WT_state_frame_len:
∀  ascope gscope status Prs_n order tslg tsll delta_g delta_b delta_x
       delta_t c funn stmt_stack scope_list t .
WT_state c (ascope,gscope,(funn,stmt_stack,scope_list)::t,status) Prs_n order
           tslg tsll (delta_g,delta_b,delta_x,delta_t) ⇒
LENGTH ((funn,stmt_stack,scope_list)::t) = LENGTH tsll
Proof
REPEAT STRIP_TAC >>
gvs[Once WT_state_cases] >>

Cases_on ‘funnl’ >>
Cases_on ‘stmtll’ >>
Cases_on ‘scll’ >>
gvs[]
QED



Theorem type_state_tsll_normalization:                           
∀ scll tsll.
  LENGTH scll = LENGTH tsll ∧
  LENGTH scll > 0 ∧
type_state_tsll scll tsll ⇒
type_state_tsll [HD scll] [HD tsll] ∧
type_state_tsll (TL scll) (TL tsll)
Proof               
Cases_on ‘scll’ >>
Cases_on ‘tsll’ >>
REPEAT STRIP_TAC >>
gvs[type_state_tsll_def] >>
 REPEAT STRIP_TAC >| [                
 ‘i=0’ by gvs[] >> lfs[] >>
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`0`])) >>   
 gvs[] 
 ,
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`SUC i`])) >>   
 gvs[] >> lfs[]
]
QED





val WT_state_imp_tl_tsll = prove (“        
∀  ascope gscope status Prs_n order tslg tsll delta_g delta_b delta_x
       delta_t c funn stmt_stack scope_list t .
WT_state c (ascope,gscope,(funn,stmt_stack,scope_list)::t,status) Prs_n order tslg tsll (delta_g,delta_b,delta_x,delta_t) ⇒
type_state_tsll (MAP (λ(f,stmt,sc). sc) t) (TL tsll)”,

REPEAT STRIP_TAC >>
gvs[Once WT_state_cases] >>
subgoal ‘(MAP (λ(f,stmt,sc). sc) t) = TL scll’ >- cheat (*list manipulation simple *) >>
IMP_RES_TAC type_state_tsll_normalization >>
gvs[] >>
Cases_on ‘scll’ >>
Cases_on ‘tsll’ >>
gvs[]
);




         

val res_fr_typ_imp_typ_tsl = prove (“
∀ T_e Prs_n tslg tsl gscope locale f stmtl func_map b_func_map.
res_frame_typ T_e  Prs_n tslg tsl gscope [(f,stmtl,locale)] func_map b_func_map ⇒
type_frame_tsl locale tsl ”,

REPEAT STRIP_TAC >>
PairCases_on ‘T_e’ >>
gvs[res_frame_typ_def] >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘0’])) >>
gvs[frame_typ_cases]
);





val type_tsll_hd_l = prove (“        
∀ s1 scl ts1 tsl .
type_frame_tsl s1 ts1 ∧
type_state_tsll scl tsl ⇒
type_state_tsll (s1::scl) (ts1::tsl)”,

gvs[type_state_tsll_def] >>
REPEAT STRIP_TAC >>
SIMP_TAC list_ss [Once EL_compute] >> CASE_TAC >- gvs[EL_CONS] >>
gvs[ADD1, PRE_SUB1] >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [ ‘i-1’ ])) >>
gvs[] >>
gvs[EL_CONS, PRE_SUB1]
);


val type_tsll_hd_hd_l = prove (“        
∀ s1 s2 scl ts1 ts2 tsl .
type_frame_tsl s1 ts1 ∧
type_frame_tsl s2 ts2 ∧
type_state_tsll scl tsl ⇒
type_state_tsll (s1::s2::scl) (ts1::ts2::tsl)”,

gvs[type_state_tsll_def] >>
REPEAT STRIP_TAC >>
SIMP_TAC list_ss [Once EL_compute] >> CASE_TAC >- gvs[EL_CONS] >>
SIMP_TAC list_ss [Once EL_compute] >> CASE_TAC >- gvs[EL_CONS] >>
gvs[ADD1, PRE_SUB1] >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [ ‘i-2’ ])) >>
gvs[] >>
gvs[EL_CONS, PRE_SUB1]
);

 



val scopes_to_ret_is_wt = prove (“    
∀ funn delta_g delta_b func_map b_func_map tslg passed_gscope  gscope passed_tslg ret_gscope .
  dom_b_eq delta_b b_func_map ∧
  dom_g_eq delta_g func_map ∧
  dom_tmap_ei delta_g delta_b ∧
  LENGTH tslg = 2 ∧            
   t_scopes_to_pass funn delta_g delta_b tslg = SOME passed_tslg ∧
   type_scopes_list passed_gscope passed_tslg ∧
   type_scopes_list gscope tslg ∧
   SOME ret_gscope = scopes_to_retrieve funn func_map b_func_map gscope passed_gscope ==>
   type_scopes_list ret_gscope tslg”,

gvs[t_scopes_to_pass_def, scopes_to_retrieve_def] >>
REPEAT STRIP_TAC >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>

IMP_RES_TAC dom_eq_imp_NONE >> gvs[] >>
IMP_RES_TAC type_scopes_list_LENGTH >>
gvs[quantHeuristicsTheory.LIST_LENGTH_2] >>

simp_tac list_ss [Once type_scopes_list_normalize] >>
IMP_RES_TAC type_scopes_list_normalize >> gvs[]           
);



val block_exit_implic = prove (“
∀ ascope ascope' g_scope_list g_scope_list' funn stmtl stmtl' scope_list scope_list' status status' framel (c: 'a ctx).
                                                                   
stmt_red c (ascope, g_scope_list,  [(funn,stmtl,scope_list)],               status)
         (ascope' , g_scope_list' ,framel ⧺ [(funn,stmtl',scope_list')], status') ∧
LENGTH stmtl > LENGTH stmtl' ⇒         
(LENGTH stmtl − LENGTH stmtl' = 1 ∧ framel = [] ∧ g_scope_list =  g_scope_list' )”,

REPEAT STRIP_TAC >>
gvs[Once stmt_red_cases] >>
gvs[ADD1] >>
gvs[Once stmt_red_cases]
);




Theorem return_imp_same_g_base_case:
∀ stmt stmtl' c ascope ascope' gscope gscope' f  v framel locale locale'.
stmt_red c (ascope,gscope,[(f,[stmt],locale)],status_running)
           (ascope',gscope',[(f,stmtl',locale')],status_returnv v) ⇒
gscope = gscope'  
Proof
Induct >>
REPEAT GEN_TAC >>
STRIP_TAC >>
gvs[Once stmt_red_cases] >>
METIS_TAC []
QED                                                                              

     
Theorem return_imp_same_g:
∀ stmtl stmtl' c ascope ascope' gscope gscope' f  v framel locale locale'.
stmt_red c (ascope,gscope,[(f,stmtl,locale)],status_running)
           (ascope',gscope',[(f,stmtl',locale')],status_returnv v) ⇒
gscope = gscope' 
Proof
REPEAT STRIP_TAC >>
gvs[Once stmt_red_cases] >>
IMP_RES_TAC return_imp_same_g_base_case
QED  


Theorem create_frame_in_stmt_same_g:
∀stmt stmt' stmt_called (c:'a ctx) ascope ascope' gscope gscope' f locale locale' f_called stmt_stack copied_in_scope.
stmt_red c (ascope,gscope,[(f,[stmt],locale)],status_running)
           (ascope',gscope', [(f_called,[stmt_called],copied_in_scope); (f,stmt_stack ⧺ [stmt'],locale')],status_running) ⇒
     gscope = gscope' 
Proof
Induct >>
REPEAT GEN_TAC >>
STRIP_TAC >>
gvs[Once stmt_red_cases] >>
METIS_TAC []
QED



Theorem create_frame_in_stmt_same_g2:
  ∀stmt stmt_called (c:'a ctx) ascope ascope' gscope gscope' f locale locale'
       f_called copied_in_scope stmt_stack' status status'.
stmt_red c (ascope,gscope,[(f,[stmt],locale)],status)
           (ascope',gscope', [(f_called,[stmt_called],copied_in_scope); (f,stmt_stack',locale')],status') ⇒
     gscope = gscope' 
Proof
Induct >>
REPEAT GEN_TAC >>
STRIP_TAC >>
gvs[Once stmt_red_cases] >>
IMP_RES_TAC create_frame_in_stmt_same_g 
QED

        
Theorem create_frame_in_stmt_same_g3:
∀ stmtl stmtl' (c:'a ctx) f f_called stmt_called copied_in_scope ascope ascope' gscope gscope' scope_list scope_list' status status' .
stmt_red c (ascope, gscope,   [(f,stmtl,scope_list)],status)
           (ascope',gscope', [(f_called,[stmt_called],copied_in_scope); (f,stmtl',scope_list')],status') ⇒
 gscope = gscope'
Proof
REPEAT STRIP_TAC >>
gvs[Once stmt_red_cases] >>
IMP_RES_TAC create_frame_in_stmt_same_g >>
IMP_RES_TAC create_frame_in_stmt_same_g2
QED





val WF_ft_order_called_f = prove (“
∀ order f_called f fl delta_g delta_b delta_x.                                  
order (order_elem_f f_called) (order_elem_f f) ∧
WF_ft_order (f::fl) delta_g delta_b delta_x order ⇒
WF_ft_order (f_called::f::fl) delta_g delta_b delta_x order”,

gvs[WF_ft_order_cases] >>
gvs[ordered_list_def] >>
REPEAT STRIP_TAC >>
SIMP_TAC list_ss [Once EL_compute] >>
CASE_TAC >>
gvs[EL_CONS]
);       

(**************************)



  (*
                                 

                 

            
Theorem SR_state:
∀ ty framel . sr_state framel ty
Proof


STRIP_TAC >>
Cases_on ‘framel’ >-

(* case when frame is empty*)
 gvs[sr_state_def, Once frames_red_cases] >>
 

(* now we need to do cases on the transition of the frame comp1 and comp2 *)
gvs[sr_state_def] >>
REPEAT STRIP_TAC >>

gvs[Once frames_red_cases] >| [


 IMP_RES_TAC WT_state_HD_of_list >> gvs[] >>
 IMP_RES_TAC frame_to_multi_frame_transition1 >> gvs[] >>

             
 ASSUME_TAC SR_stmtl_stmtl >>
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`ty`,‘stmt_stack’])) >>
 gvs[sr_stmtl_def] >>     
 
 
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [
    `stmtl'`,‘ascope’,‘ascope'’, ‘g_scope_list'’,‘g_scope_list''’, ‘scope_list’,‘scope_list'’,
    ‘new_frame’,‘status’,‘status'’, ‘HD tsll’,‘passed_tslg’,
    ‘order’, ‘delta_g’, ‘passed_delta_b’, ‘passed_delta_t’, ‘delta_x’, ‘funn’,
    ‘Prs_n’, ‘1’, ‘apply_table_f’, ‘ext_map’, ‘func_map’, ‘b_func_map'’, ‘pars_map’, ‘passed_tbl_map’])) >> gvs[] >>
 gvs[] >>
 
 
 SIMP_TAC list_ss [WT_state_cases] >> gvs[] >>
 
 ‘WT_c (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)
  order tslg delta_g delta_b delta_x delta_t Prs_n’ by gvs[Once WT_state_cases] >> gvs[] >>
 
 
 (* When typing the frames in the state aftre making a statement reduction will depend on the length of the resulted statement stack
    there is one thing also we need to show when exsting a block, there will be no frame created *) 
 Cases_on ‘LENGTH stmt_stack ≤ LENGTH stmtl'’ >> gvs[]  >| [
   IMP_RES_TAC fr_len_from_a_stmtl_theorem >> gvs[] >| [
        
      (* case resulted frame length is 1 *)
     Q.EXISTS_TAC ‘[t_scope_list']++[t_scope_list'' ⧺ HD tsll ] ++ (TL tsll)’ >>
     Q.EXISTS_TAC ‘ f_called::funn::(MAP (\(f,stmt,sc).f ) t)’ >>
     Q.EXISTS_TAC ‘copied_in_scope::scope_list'::(MAP (\(f,stmt,sc).sc ) t)’ >>
     Q.EXISTS_TAC ‘[stmt_called]::stmtl'::(MAP (\(f,stmt,sc).stmt ) t)’ >>
     gvs[ADD1] >>

     CONJ_TAC >-
      ( gvs[ELIM_UNCURRY] >> gvs[ZIP_tri_id1]) >>

      
     (* now show that the lengths are coherent *)
      
     ‘LENGTH t + 1  = LENGTH tsll’ by (IMP_RES_TAC WT_state_frame_len >> gvs[ADD1] ) >>
     gvs[list_length1] >>


                       
     (* function being ordered: gotta prove this ffs going back to SR! TODO: add this  *)
     subgoal ‘WF_ft_order (f_called::funn::MAP (λ(f,stmt,sc). f) t) delta_g delta_b delta_x order’ >-
      (
        ‘order (order_elem_f f_called) (order_elem_f funn)’ by
           (gvs[res_frame_typ_def] >>
            FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘0’])) >> gvs[]) >>
            
        gvs[WT_state_cases] >>
        ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:funn``, ``:'b`` |-> ``:stmt list``, ``:'c`` |-> ``:scope_list``] ZIP_tri_sep_ind)  >>
        FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘t’,‘funnl’,‘stmtll’,‘scll’, ‘funn’,‘stmt_stack’,‘scope_list’])) >> gvs[] >>
            
        IMP_RES_TAC WF_ft_order_called_f >>  gvs[]
      ) >> gvs[] >>
     
           
     
     subgoal ‘type_state_tsll (copied_in_scope::scope_list'::MAP (λ(f,stmt,sc). sc) t)
              (t_scope_list'::(t_scope_list'' ⧺ HD tsll)::TL tsll) ’ >-
      (
      ‘type_frame_tsl copied_in_scope t_scope_list' ’ by (IMP_RES_TAC res_fr_typ_imp_typ_tsl >> gvs[] ) >>
      ‘type_frame_tsl scope_list' (t_scope_list'' ⧺ HD tsll) ’ by gvs[Once frame_typ_cases]  >>
      ‘type_state_tsll (MAP (λ(f,stmt,sc). sc) t) (TL tsll)’ by IMP_RES_TAC WT_state_imp_tl_tsll >>
      IMP_RES_TAC type_tsll_hd_hd_l
      ) >> gvs[] >>
     



                 
     (* prove that the retrived scope can stilll be typed with the original tslg *)
     subgoal ‘type_scopes_list gscope' tslg ’ >-
      (
     ‘type_scopes_list g_scope_list'' passed_tslg’ by gvs[Once frame_typ_cases] >>
     ‘dom_b_eq delta_b b_func_map ∧ dom_g_eq delta_g func_map ∧
      dom_tmap_ei delta_g delta_b ∧ LENGTH tslg = 2’ by gvs[WT_c_cases] >>
     IMP_RES_TAC scopes_to_ret_is_wt
      ) >> gvs[] >>




      
    (* TODO: needs to be added *)
     subgoal ‘parseError_in_gs tslg (t_scope_list'::(t_scope_list'' ⧺ HD tsll)::TL tsll) ’ >-
      (
      cheat
      ) >> gvs[] >>
                


                        
     gvs[GSYM ZIP_tri_id2] >>  (* the sub proofs above are done not using this info below*)
     ‘g_scope_list' = g_scope_list''’ by IMP_RES_TAC create_frame_in_stmt_same_g3
     rfs[]


              
              cheat
    
        
      ]
                  
     ,
     (* case resulted frame length is 0 *)
     Q.EXISTS_TAC ‘[t_scope_list'' ⧺ HD tsll ] ++ (TL tsll)’ >>
     Q.EXISTS_TAC ‘ funn::(MAP (\(f,stmt,sc).f ) t)’ >>
     Q.EXISTS_TAC ‘scope_list'::(MAP (\(f,stmt,sc).sc ) t)’ >>
     Q.EXISTS_TAC ‘stmtl'::(MAP (\(f,stmt,sc).stmt ) t)’ >>
     gvs[ADD1] >>
     CONJ_TAC >-
      ( gvs[ELIM_UNCURRY] >> gvs[ZIP_tri_id1]) >>
     
     
     (* now show that the lengths are coherent *)
     
     ‘LENGTH t + 1  = LENGTH tsll’ by (IMP_RES_TAC WT_state_frame_len >> gvs[ADD1] ) >>
     gvs[list_length1] >>
                       
     subgoal ‘WF_ft_order (funn::MAP (λ(f,stmt,sc). f) t) delta_g delta_b delta_x order’ >-
      (
      gvs[WT_state_cases] >>  
      ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:funn``, ``:'b`` |-> ``:stmt list``, ``:'c`` |-> ``:scope_list``] ZIP_tri_sep_ind)  >>
      FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘t’,‘funnl’,‘stmtll’,‘scll’, ‘funn’,‘stmt_stack’,‘scope_list’])) >> gvs[] >>
      gvs[ELIM_UNCURRY]
      ) >> gvs[] >>

      
     subgoal ‘type_state_tsll (scope_list'::MAP (λ(f,stmt,sc). sc) t)
              ((t_scope_list'' ⧺ HD tsll)::TL tsll) ’ >-
      (
      ‘type_frame_tsl scope_list' (t_scope_list'' ⧺ HD tsll) ’ by gvs[Once frame_typ_cases]  >>
      ‘type_state_tsll (MAP (λ(f,stmt,sc). sc) t) (TL tsll)’ by IMP_RES_TAC WT_state_imp_tl_tsll >>
      IMP_RES_TAC type_tsll_hd_l
      ) >> gvs[] >>
                       
     subgoal ‘type_scopes_list gscope' tslg ’ >-
      (
      ‘type_scopes_list g_scope_list'' passed_tslg’ by gvs[Once frame_typ_cases] >>
      ‘dom_b_eq delta_b b_func_map ∧ dom_g_eq delta_g func_map ∧
      dom_tmap_ei delta_g delta_b ∧ LENGTH tslg = 2’ by gvs[WT_c_cases] >>
      IMP_RES_TAC scopes_to_ret_is_wt
      ) >> gvs[] >>
     


     subgoal ‘parseError_in_gs tslg ((t_scope_list'' ⧺ HD tsll)::TL tsll)’ >-
      (
      cheat (* we need to ensure that when we enter a new block we can never find a pareError in the domain*)
      ) >> gvs[] >>

    

     gvs[GSYM ZIP_tri_id2] >>
     
     cheat
                
  ]

 ,
        
 (* case block exit LENGTH stmt_stack > LENGTH stmtl' *)
   
  ‘(LENGTH stmt_stack > LENGTH stmtl')’ by gvs[] >>
  IMP_RES_TAC block_exit_implic >> lfs[] >> gvs[] >>
  Q.EXISTS_TAC ‘[DROP 1 (HD tsll) ] ++ (TL tsll)’ >>
  Q.EXISTS_TAC ‘ funn::(MAP (\(f,stmt,sc).f ) t)’ >>
  Q.EXISTS_TAC ‘scope_list'::(MAP (\(f,stmt,sc).sc ) t)’ >>
  Q.EXISTS_TAC ‘stmtl'::(MAP (\(f,stmt,sc).stmt ) t)’ >>
  gvs[ADD1] >>
  CONJ_TAC >-
   ( gvs[ELIM_UNCURRY] >> gvs[ZIP_tri_id1]) >>
  
  
  (* now show that the lengths are coherent *)
  
  ‘LENGTH t + 1  = LENGTH tsll’ by (IMP_RES_TAC WT_state_frame_len >> gvs[ADD1] ) >>
  gvs[list_length1] >>
  
  subgoal ‘WF_ft_order (funn::MAP (λ(f,stmt,sc). f) t) delta_g delta_b delta_x order’ >-
      (
      gvs[WT_state_cases] >>  
      ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:funn``, ``:'b`` |-> ``:stmt list``, ``:'c`` |-> ``:scope_list``] ZIP_tri_sep_ind)  >>
      FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘t’,‘funnl’,‘stmtll’,‘scll’, ‘funn’,‘stmt_stack’,‘scope_list’])) >> gvs[] >>
      gvs[ELIM_UNCURRY]
      ) >> gvs[] >>
  
  subgoal ‘type_state_tsll (scope_list'::MAP (λ(f,stmt,sc). sc) t)
           (DROP 1 (HD tsll)::TL tsll)’ >-
   (
   ‘type_frame_tsl scope_list' (DROP 1 (HD tsll)) ’ by gvs[Once frame_typ_cases]  >>
   ‘type_state_tsll (MAP (λ(f,stmt,sc). sc) t) (TL tsll)’ by IMP_RES_TAC WT_state_imp_tl_tsll >>
      IMP_RES_TAC type_tsll_hd_l
   ) >> gvs[] >>
  

  subgoal ‘type_scopes_list gscope' tslg ’ >-
   (
   ‘type_scopes_list g_scope_list' passed_tslg’ by gvs[Once frame_typ_cases] >>
   ‘dom_b_eq delta_b b_func_map ∧ dom_g_eq delta_g func_map ∧
    dom_tmap_ei delta_g delta_b ∧ LENGTH tslg = 2’ by gvs[WT_c_cases] >>
   IMP_RES_TAC scopes_to_ret_is_wt
   ) >> gvs[] >>
  

  subgoal ‘parseError_in_gs tslg (DROP 1 (HD tsll)::TL tsll)’ >-
   (
   cheat
   ) >> gvs[] >>

      gvs[GSYM ZIP_tri_id2] >>
  cheat
  
 ]
 , 
 (* comp2 *)
 

  IMP_RES_TAC return_imp_same_g >> lfs[] >> gvs[] >>
  IMP_RES_TAC WT_state_HD_of_list >> gvs[] >>
  Q.EXISTS_TAC ‘TL tsll’ >>
  cheat


        
  ]

QED
        
*)

val _ = export_theory ();


