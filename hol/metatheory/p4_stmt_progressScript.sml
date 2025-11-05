open HolKernel boolLib liteLib simpLib Parse bossLib;
open arithmeticTheory stringTheory containerTheory pred_setTheory
     listTheory finite_mapTheory;

open p4Lib;
open blastLib bitstringLib;
open p4Theory;
open p4_auxTheory;
open p4_deterTheory;
open p4_e_subject_reductionTheory;
open p4_e_progressTheory;
open p4_stmt_subject_reductionTheory;
     
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



fun OPEN_V_TYP_TAC v_term =
(Q.PAT_X_ASSUM `v_typ v_term t bll` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once v_typ_cases] thm)))


               
fun OPEN_EXP_RED_TAC exp_term =
(Q.PAT_X_ASSUM `e_red c scope scopest ^exp_term exp2 fr` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once e_sem_cases] thm)))

fun OPEN_EXP_TYP_TAC exp_term =
(Q.PAT_X_ASSUM ` e_typ (t1,t2) t ^exp_term ta bll` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once e_typ_cases] thm)))

fun OPEN_STMT_TYP_TAC stmt_term =
(Q.PAT_X_ASSUM ` stmt_typ (t1,t2) q g ^stmt_term` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once stmt_typ_cases] thm)))

        
fun OPEN_STMT_RED_TAC stm_term =
(Q.PAT_X_ASSUM `stmt_red ct (ab, gsl,[(fun,[^stm_term],gam)],st) stat`
 (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once stmt_sem_cases] thm)))

val OPEN_ANY_STMT_RED_TAC =
(Q.PAT_X_ASSUM `stmt_red ct (ab, gsl,[(fun,[stm_term],gam)],st) stat`
 (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once stmt_sem_cases] thm)))
 
fun OPEN_FRAME_TYP_TAC frame_term =
(Q.PAT_X_ASSUM ` frame_typ (t1,t2) t a b h d ^frame_term` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once frame_typ_cases] thm)))
   
fun OPEN_LVAL_TYP_TAC lval_term =
(Q.PAT_X_ASSUM `lval_typ (g1,q1) t (^lval_term) (tp)` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once lval_typ_cases] thm)))



val _ = new_theory "p4_stmt_progress";

   
val prog_stmt_def = Define `
 prog_stmt (stmt) (ty:'a itself) =
∀ ascope gscope (scopest:scope list) status  t_scope_list t_scope_list_g T_e (c:'a ctx) order delta_g delta_b delta_t delta_x f Prs_n .
      
       type_scopes_list  (gscope)  (t_scope_list_g) ∧
       type_scopes_list  (scopest) (t_scope_list)   ∧
       star_not_in_sl (scopest) ∧


       
       (WT_c c order t_scope_list_g delta_g delta_b delta_x delta_t Prs_n) ∧
       (T_e = (order, f, (delta_g, delta_b, delta_x, delta_t))) ∧   
       (frame_typ  ( t_scope_list_g  ,  t_scope_list ) T_e Prs_n  gscope scopest [stmt] ) ∧
                   (stmt ≠ stmt_empty ∧ status = status_running ) ⇒
                                                                                                
       ∃ stmtl scopest' framel gscope' status' ascope'.
       (stmt_red c ( ascope ,  gscope  ,           [ (f, [stmt], scopest )] , status)
                   ( ascope',  gscope' , framel ++ [ (f, stmtl , scopest')] , status'))

`;


      



      
val vl_of_el_ev = prove (“                       
∀ vl .
is_consts vl ⇒
vl = MAP (λv_. e_v v_) (vl_of_el vl) ”,
Induct >> rw[] >> gvs[vl_of_el_def, is_consts_def] >>
Cases_on ‘h’ >> gvs[is_const_def, v_of_e_def]                         
);

        

val index_not_const_EL = prove ( “
∀ el x .
  x < LENGTH el ∧ index_not_const el = SOME x ⇒
  ¬is_const (EL x el)”,
Induct >>
rw[] >>
IMP_RES_TAC index_not_const_in_range >>
    
gvs[index_not_const_def] >>
Cases_on ‘INDEX_FIND 0 (λe. ¬is_const e) (h::el)’ >> gvs[] >>
PairCases_on ‘x'’ >> gvs[] >>                                           
IMP_RES_TAC INDEX_FIND_EQ_SOME_0 >> gvs[]
);



val oDROP_exists = prove (“
∀ sl i .
   LENGTH sl ≥ 3 ∧ i = LENGTH sl − 2 ⇒
   ∃l l'. SOME l = oDROP (i) sl ”,
Induct >>
Induct_on ‘i’ >>            

REPEAT STRIP_TAC >>
fs[oDROP_def] >>
gvs[ADD1] >>

Cases_on ‘LENGTH sl ≥ 3 ’ >> gvs[] >-
 (‘i=LENGTH sl -2’ by gvs[] >> METIS_TAC []) >>

‘i + 2 =LENGTH sl’ by gvs[] >>
Cases_on ‘i’ >> gvs[] >>
gvs[oDROP_def]
);


val oTAKE_exists = prove (“
∀ sl i .
   LENGTH sl ≥ 3 ∧ i = LENGTH sl − 2 ⇒
   ∃l l'. SOME l = oTAKE (i) sl ”,
Induct >>
Induct_on ‘i’ >>            

REPEAT STRIP_TAC >> 
fs[oTAKE_def] >> 
gvs[ADD1] >>

Cases_on ‘oTAKE i sl’ >> gvs[] >>     
Cases_on ‘LENGTH sl ≥ 3 ’ >> gvs[] >>
  
(‘i=LENGTH sl -2’ by gvs[] >> lfs[] ) >>

‘i + 2 =LENGTH sl’ by gvs[] >> Cases_on ‘i’ >> gvs[] >>
gvs[oTAKE_def]  >> fs[]
);




val separate_exists = prove (“
∀ sl.
 LENGTH sl ≥ 3 ⇒
 ∃ l l' . (SOME l , SOME l' ) = separate sl ”,

REPEAT STRIP_TAC  >>
fs[separate_def] >>
gvs[ADD1, oDROP_def, oTAKE_def ] >>
IMP_RES_TAC oDROP_exists >>
IMP_RES_TAC oTAKE_exists >>
gvs[] >> METIS_TAC []
);



        
val lval_typ_imp_e_typ = prove ( “      
∀ l tau gtsl tsl T_e .
  lval_typ (gtsl,tsl) T_e l (tau) ⇒
    ∃ e.  is_e_lval e ∧
      get_lval_of_e e = SOME l ∧
      e_typ (gtsl,tsl) T_e e tau T ”,

Induct >>                       
REPEAT GEN_TAC >> STRIP_TAC >| [
 Q.EXISTS_TAC ‘e_var v’ >>
 gvs[get_lval_of_e_def, is_e_lval_def] >>
 gvs[Once lval_typ_cases] 
 ,
 
 gvs[get_lval_of_e_def, is_e_lval_def] >>
 gvs[Once lval_typ_cases]
 ,
 
 OPEN_LVAL_TYP_TAC “(lval_field l s)”  >> gvs[] >>
 
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`(t_tau (tau_xtl struct_ty x_tau_list))`, ‘gtsl’,‘tsl’,‘T_e’])) >> gvs[] >>
 
 Q.EXISTS_TAC ‘e_acc e s’ >>
 gvs[get_lval_of_e_def, is_e_lval_def] >>
 SIMP_TAC list_ss [Once e_typ_cases] >> gvs[] >>
 Q.EXISTS_TAC ‘x_tau_list’ >>
 Q.EXISTS_TAC ‘struct_ty’  >>
 gvs[clause_name_def]     
 ,
 
 OPEN_LVAL_TYP_TAC “lval_slice l e0 e”  >> gvs[] >>
 
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`t_tau (tau_bit w)`, ‘gtsl’,‘tsl’,‘T_e’])) >> gvs[] >>
 Q.EXISTS_TAC ‘e_slice e  (e_v (v_bit bitv)) (e_v (v_bit bitv'))’ >>
 gvs[get_lval_of_e_def, is_e_lval_def] >>
 SIMP_TAC list_ss [Once e_typ_cases] >> gvs[clause_name_def] >>
 srw_tac [SatisfySimps.SATISFY_ss][]
 ,
 OPEN_LVAL_TYP_TAC “(lval_paren l)”  >> gvs[] 
  ]
);




val lookup_lval_empty = prove ( “        
∀ l .
lookup_lval [] l = NONE ”,
 Induct_on ‘l’ >>
 gvs[lookup_lval_def, lookup_v_def, lookup_map_def, topmost_map_def, find_topmost_map_def, INDEX_FIND_def]
);





Theorem lval_assign_exists:
∀ sl v v' v''.    
 lookup_lval sl (lval_varname v) = SOME v' ⇒
  ∃sl'. assign sl v'' (lval_varname v) = SOME sl'
Proof  
REPEAT STRIP_TAC >>
   gvs[assign_def] >>
    gvs[lookup_lval_def, lookup_v_def, lookup_map_def, topmost_map_def] >>                         
      REPEAT BasicProvers.FULL_CASE_TAC >> gvs[] >> 
   PairCases_on ‘x'’ >> Cases_on ‘ALOOKUP r v’ >>
 gvs[lookup_out_def, lookup_map_def, topmost_map_def, find_topmost_map_def]
QED
               

               
Theorem assignment_scope_exists:                                
∀  scopest gscope t_scope_list t_scope_list_g tau b l v T_e.
LENGTH scopest ≥ 1 ∧
LENGTH gscope = 2 ∧

star_not_in_sl scopest ∧ 
type_scopes_list gscope t_scope_list_g ∧
type_scopes_list scopest t_scope_list  ∧                
e_typ (t_scope_list_g,t_scope_list) T_e (e_v v) (t_tau tau) b ∧
lval_typ (t_scope_list_g,t_scope_list) T_e  l (t_tau tau) ⇒

 ∃scopest' gscope' scope_list'.
          SOME scope_list' = assign (scopest ⧺ gscope) v l ∧
          (SOME gscope',SOME scopest') = separate scope_list'
Proof
                                                 
Induct_on ‘l’ >> gvs[] >>
REPEAT STRIP_TAC >>
gvs[Once e_typ_cases]  >| [


 OPEN_LVAL_TYP_TAC “(lval_varname v)” >> gvs[] >>    
 IMP_RES_TAC lval_typ_imp_e_typ >>
 ASSUME_TAC e_lval_WT >>
 gvs[] >>
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`(e_var v)`, ‘t_tau (tau)’,‘t_scope_list_g’,‘gscope’,‘t_scope_list’, ‘scopest’, ‘T_e’])) >>
 gvs[] >>

 gvs[is_e_lval_def, get_lval_of_e_def] >>


 gvs[assign_def] >>
 gvs[lookup_lval_def, lookup_v_def, lookup_map_def, topmost_map_def] >>                         
 REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
 gvs[lookup_out_def, lookup_map_def, topmost_map_def, find_topmost_map_def] >>
 REPEAT BasicProvers.FULL_CASE_TAC >> gvs[] >> 
 

 gvs[AUPDATE_def] >>
 ‘LENGTH (LUPDATE (AFUPDKEY v (λold_v. (v',r')) r) q (scopest ⧺ gscope)) = LENGTH (scopest ⧺ gscope) ’ by gvs[LENGTH_LUPDATE] >>
 ‘LENGTH (scopest ⧺ gscope) >= 3 ’ by gvs[] >>
 ‘LENGTH (LUPDATE (AFUPDKEY v (λold_v. (v',r')) r) q (scopest ⧺ gscope)) >= 3 ’ by gvs[] >>
 drule separate_exists >> REPEAT STRIP_TAC >> srw_tac [SatisfySimps.SATISFY_ss][]
 ,

 (*lval null *)
 
 gvs[assign_def] >>
 ‘LENGTH (scopest ⧺ gscope) >= 3 ’ by gvs[] >>
 drule separate_exists >> REPEAT STRIP_TAC >> srw_tac [SatisfySimps.SATISFY_ss][]
                                                      
 ,

 (*lval feild *)


 OPEN_LVAL_TYP_TAC “(lval_field l s)” >> gvs[] >>
          
 IMP_RES_TAC lval_typ_imp_e_typ >>
 ASSUME_TAC e_lval_WT >> gvs[] >>
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`e`, ‘t_tau (tau_xtl struct_ty x_tau_list)’,‘t_scope_list_g’,‘gscope’,‘t_scope_list’, ‘scopest’, ‘T_e’])) >>
 gvs[] >>
 
 gvs[assign_def] >>
 
 Cases_on ‘v'’ >>  OPEN_V_TYP_TAC ‘anything’ >> gvs[] >>

 (Cases_on ‘INDEX_OF s (MAP FST (MAP (λ(x_,v_,tau_). (x_,v_)) x_v_tau_list))’ >>
  gvs[] >-
   ( IMP_RES_TAC correct_field_type_FIND >>
     gvs[ FIND_def, INDEX_OF_def] >>
     PairCases_on ‘z’ >> gvs[] >>
     gvs[] >>            
     ‘$= s = ((λ(xm). xm = s)) ’ by METIS_TAC[] >>
     
     (* PairCases_on ‘z’ >>  *)    
     gvs[] >>
     IMP_RES_TAC index_none_not_every >> 
     FULL_SIMP_TAC (std_ss) [combinTheory.o_DEF] >>
     fs[EVERY_EL] >>
     fs[INDEX_FIND_EQ_SOME_0] >>
     gvs[] >>
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`z0`])) >> gvs[] >>
     gvs[EL_MAP] 
   )) >| [
        
     (* struct: use IH *)
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘scopest’, ‘gscope’,‘t_scope_list’,‘t_scope_list_g’,
               ‘(tau_xtl struct_ty_struct (MAP (λ(x_,v_,tau_). (x_,tau_)) ( x_v_tau_list : (string # v # tau) list)))’, ‘F’,
               ‘v_struct (LUPDATE (s,v) x (MAP (λ(x_,v_,tau_). (x_,v_)) ( x_v_tau_list : (string # v # tau) list)))’, ‘T_e’])) >> gvs[] >>

    gvs[Once e_typ_cases] >>



    ASSUME_TAC e_lval_WT >> gvs[] >>
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘e’,
                        ‘(t_tau (tau_xtl struct_ty_struct (MAP (λ(x_,v_,tau_). (x_,tau_)) (x_v_tau_list : (string # v # tau) list))))’,
                        ‘t_scope_list_g’,‘gscope’,‘t_scope_list’, ‘scopest’, ‘T_e’])) >> gvs[] >>

    drule LUPDATE_header_struct_v_typed >> STRIP_TAC >>
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [ ‘(MAP (λ(x_,v_,tau_). (x_,v_)) (x_v_tau_list : (string # v # tau) list))’,
                                                 ‘v’, ‘struct_ty_struct’, ‘x’,‘F’])) >> gvs[] >>

    IMP_RES_TAC v_typ_always_lval >> 
    srw_tac [SatisfySimps.SATISFY_ss][]
    ,

    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`scopest`, ‘gscope’,‘t_scope_list’,‘t_scope_list_g’,
               ‘(tau_xtl struct_ty_header (MAP (λ(x_,v_,tau_). (x_,tau_)) ( x_v_tau_list : (string # v # tau) list)))’, ‘F’,
               ‘v_header b' (LUPDATE (s,v) x (MAP (λ(x_,v_,tau_). (x_,v_)) ( x_v_tau_list : (string # v # tau) list)))’, ‘T_e’])) >> gvs[] >>

   gvs[Once e_typ_cases] >>

    ASSUME_TAC e_lval_WT >> gvs[] >>
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`e`,
                                 ‘(t_tau (tau_xtl struct_ty_header (MAP (λ(x_,v_,tau_). (x_,tau_)) (x_v_tau_list : (string # v # tau) list))))’,
                                 ‘t_scope_list_g’,‘gscope’,‘t_scope_list’, ‘scopest’, ‘T_e’])) >> gvs[] >>

    drule LUPDATE_header_struct_v_typed >> STRIP_TAC >>

    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [ ‘(MAP (λ(x_,v_,tau_). (x_,v_)) (x_v_tau_list : (string # v # tau) list))’,
                                                   ‘v’, ‘struct_ty_header’, ‘x’,‘b'’])) >> gvs[] >>

    IMP_RES_TAC v_typ_always_lval >> 
    gvs[] >>
    srw_tac [SatisfySimps.SATISFY_ss][]
   ]
  ,
  (* slice *)
                     
  OPEN_LVAL_TYP_TAC “(lval_slice l e0 e)” >> gvs[] >>
                    
       
  IMP_RES_TAC lval_typ_imp_e_typ >>
  ASSUME_TAC e_lval_WT >> gvs[] >>
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`e`, ‘t_tau (tau_bit w)’,‘t_scope_list_g’,‘gscope’,‘t_scope_list’, ‘scopest’, ‘T_e’])) >> gvs[] >>
  

  gvs[Once e_typ_cases] >> 
  gvs[assign_def] >>
                  
  Cases_on ‘v'’ >> OPEN_V_TYP_TAC ‘anything’ >> gvs[] >>
  Cases_on ‘v’ >> OPEN_V_TYP_TAC ‘anything’ >> gvs[] >>

           
  REPEAT BasicProvers.FULL_CASE_TAC >> gvs[] >| [
    PairCases_on ‘p’ >>  PairCases_on ‘p'’ >>  PairCases_on ‘bitv’ >>  PairCases_on ‘bitv'’ >> gvs[] >>
    gvs[assign_to_slice_def]                                                                                              
    ,
    PairCases_on ‘p’ >>  PairCases_on ‘p'’ >>  PairCases_on ‘bitv’ >>  PairCases_on ‘bitv'’ >> gvs[bs_width_def] >>
    
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`scopest`, ‘gscope’,‘t_scope_list’,‘t_scope_list_g’, ‘(tau_bit p1)’, ‘F’,
                                                  ‘x’, ‘T_e’])) >> gvs[] >>

    gvs[assign_to_slice_def] >>
                
                    
    gvs[Once e_typ_cases, get_lval_of_e_def, is_e_lval_def] >>            
    fs[Once v_typ_cases] >> gvs[] >>
       
   ( gvs[Once v_typ_cases] >> fs[]) >>           
    gvs[bs_width_def] >>            
    gvs[vec_to_const_def] >>       
    srw_tac [SatisfySimps.SATISFY_ss][] >>
    gvs[vec_to_const_def, bs_width_def]                     
    ]
  ,

   (*lval paren *)     
    OPEN_LVAL_TYP_TAC “(lval_paren l)” >> gvs[]
 ]
QED


                



val frame_typ_into_stmt_typ_tac = gvs[Once frame_typ_cases] >>                        
gvs[Once stmtl_typ_cases] >>
gvs[type_ith_stmt_def] >>
gvs[] >>
gvs[Once stmt_typ_cases]
   
                                                  

Theorem PROG_stmt:
  ∀ ty stmt. prog_stmt stmt ty
Proof
        
STRIP_TAC >>
Induct >>
REPEAT STRIP_TAC >>          
SIMP_TAC list_ss [prog_stmt_def] >>      
REPEAT STRIP_TAC >| [

 (*****************************)
 (*   stmt_assign             *)
 (*****************************)

 SIMP_TAC list_ss [Once stmt_sem_cases] >> gvs[] >>
 Cases_on `is_const e` >| [
      
   gvs[is_const_val_exsist, clause_name_def, lemma_v_red_forall] >>
      
   gvs[Once frame_typ_cases] >>                        
   gvs[Once stmtl_typ_cases] >>
   gvs[type_ith_stmt_def] >>
   gvs[] >>
   fs[Once stmt_typ_cases] >> gvs[] >> 
   
   ‘LENGTH t_scope_list_g = 2’ by fs[WT_c_cases] >>         
   ‘LENGTH t_scope_list_g = LENGTH gscope’ by ( IMP_RES_TAC type_scopes_list_LENGTH >> gvs[] ) >>
   ‘LENGTH scopest >= 1’ by ( METIS_TAC[type_scopes_list_LENGTH])   >| [
     gvs[clause_name_def] >>
     srw_tac [SatisfySimps.SATISFY_ss][assignment_scope_exists]        
     ,
     gvs[assign_def] >>
     ‘LENGTH (scopest ⧺ gscope) >= 3 ’ by simp[] >>
     drule separate_exists >> REPEAT STRIP_TAC >> srw_tac [SatisfySimps.SATISFY_ss][]
      ]       

   ,
   (* e is not const *)
   gvs[is_const_val_exsist, clause_name_def, lemma_v_red_forall] >>
   
   gvs[Once frame_typ_cases] >>                        
   gvs[Once stmtl_typ_cases] >>
   gvs[type_ith_stmt_def] >>
   gvs[] >>
   gvs[Once stmt_typ_cases] >>


   ‘∀e. prog_exp e ty’ by ( ASSUME_TAC PROG_e >>
                            FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`ty`]))) >>
                            FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`e`])) >>           
   gvs[prog_exp_def] >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`gscope`, ‘scopest’, ‘t_scope_list’, ‘t_scope_list_g’,
                                                  ‘t_tau tau'’, ‘b’, ‘c’, ‘order’,‘delta_g’, ‘delta_b’, ‘delta_t’,
                                                  ‘delta_x’, ‘f’, ‘Prs_n’])) >>                  
   gvs[is_const_val_exsist] >>
   srw_tac [SatisfySimps.SATISFY_ss][]          
 ]         
 ,

 (*****************************)
 (*   stmt_cond               *)
 (*****************************)

 SIMP_TAC list_ss [Once stmt_sem_cases] >> gvs[] >>
 Cases_on `is_const e` >| [
             
   gvs[is_const_val_exsist, clause_name_def, lemma_v_red_forall] >>
   frame_typ_into_stmt_typ_tac >>           
   gvs[Once e_typ_cases, Once v_typ_cases] >>
   Cases_on ‘boolv’ >>         
   srw_tac [SatisfySimps.SATISFY_ss][]                                         
   ,
      (* e is not const *)
   gvs[is_const_val_exsist, clause_name_def, lemma_v_red_forall] >>
   frame_typ_into_stmt_typ_tac >>           
   
   ‘∀e. prog_exp e ty’ by ( ASSUME_TAC PROG_e >>
                            FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`ty`]))) >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`e`])) >>           
   gvs[prog_exp_def] >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`gscope`, ‘scopest’, ‘t_scope_list’, ‘t_scope_list_g’,
                                               ‘t_tau tau_bool’, ‘b’, ‘c’, ‘order’,‘delta_g’, ‘delta_b’, ‘delta_t’,
                                               ‘delta_x’, ‘f’, ‘Prs_n’])) >>                  
   gvs[is_const_val_exsist] >>
   srw_tac [SatisfySimps.SATISFY_ss][]          
           
 ]     
 ,
 
 (*****************************)
 (*   stmt_block              *)
 (*****************************)         
 SIMP_TAC list_ss [Once stmt_sem_cases] >> gvs[clause_name_def]
                                                
 ,

 (*****************************)
 (*   stmt_ret                *)
 (*****************************)
        
 SIMP_TAC list_ss [Once stmt_sem_cases] >> gvs[] >>
 Cases_on `is_const e` >| [
     
   gvs[is_const_val_exsist, clause_name_def, lemma_v_red_forall]
   ,
   (* e is not const *)
   gvs[is_const_val_exsist, clause_name_def, lemma_v_red_forall] >>
   frame_typ_into_stmt_typ_tac >>           
   
   ‘∀e. prog_exp e ty’ by ( ASSUME_TAC PROG_e >>
                            FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`ty`]))) >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`e`])) >>           
   gvs[prog_exp_def] >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`gscope`, ‘scopest’, ‘t_scope_list’, ‘t_scope_list_g’,
                                               ‘t_tau tau'’, ‘b’, ‘c’, ‘order’,‘delta_g’, ‘delta_b’, ‘delta_t’,
                                               ‘delta_x’, ‘f’, ‘Prs_n’])) >>                  
   gvs[is_const_val_exsist] >>
   srw_tac [SatisfySimps.SATISFY_ss][]                     
    ]     
 ,

 (*****************************)
 (*   stmt_seq                *)
 (*****************************)
         
 SIMP_TAC list_ss [Once stmt_sem_cases] >> gvs[] >>
 Cases_on ‘stmt = stmt_empty’ >> gvs[] >| [
            (* seq2 *) 
   gvs[Once stmt_sem_cases, clause_name_def] >>
   frame_typ_into_stmt_typ_tac >>           
   gvs[Once stmt_sem_cases, clause_name_def]
   ,
        
   srw_tac [boolSimps.DNF_ss][] >>
 
   Q.PAT_X_ASSUM `prog_stmt stmt ty` (STRIP_ASSUME_TAC o  SIMP_RULE (srw_ss()) [prog_stmt_def] ) >>
   
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [
	 `ascope`, `gscope`,`scopest`, ‘t_scope_list’ , ‘t_scope_list_g’,
         ‘c’,‘order’, ‘delta_g’,‘delta_b’,‘delta_t’, ‘delta_x’,‘f’,‘Prs_n’])) >> gvs[] >>
         
     (subgoal ‘frame_typ (t_scope_list_g,t_scope_list)
          (order,f,delta_g,delta_b,delta_x,delta_t) Prs_n  gscope scopest
          [stmt]’ >- (
         
      gvs[frame_typ_cases] >>                        
      gvs[stmtl_typ_cases] >>
      gvs[type_ith_stmt_def] >>
      gvs[] >>
      gvs[Once stmt_typ_cases] >>
      Q.EXISTS_TAC ‘tau_x_d_list’ >>
      Q.EXISTS_TAC ‘tau’ >>
      gvs[] >>             
      REPEAT STRIP_TAC >>
      ‘i=0’ by simp [] >> fs[]         
       )) >>


   gvs[] >>

   Cases_on ‘status' = status_running’ >| [
     (* seq1 *)
       
     DISJ1_TAC  >>     
     IMP_RES_TAC stmtl_len_from_in_frame_theorem >> gvs[]  >| [
       (subgoal ‘∃ s1 s2. stmtl = [s1]++[s2]’ >-
         (Cases_on ‘stmtl’ >> gvs[] >> Cases_on ‘t’ >> gvs[]   ))  >>
       srw_tac [SatisfySimps.SATISFY_ss][clause_name_def]          
       ,
       
       (subgoal ‘∃ s1. stmtl = []++[s1]’ >-
         (Cases_on ‘stmtl’ >> gvs[] ))  >>
       srw_tac [SatisfySimps.SATISFY_ss][clause_name_def] 
       ]                                                                   
     ,

     (* seq3 *)
     DISJ2_TAC  >>  
     gvs[Once stmt_sem_cases] >>
     IMP_RES_TAC stmtl_len_from_in_frame_theorem >> gvs[] >>
     SIMP_TAC list_ss  [Once stmt_sem_cases] >> gvs[] >>
     srw_tac [boolSimps.DNF_ss][] >>
     srw_tac [SatisfySimps.SATISFY_ss][clause_name_def]        
   ]                                        
 ]                                           
 ,

 
 (*****************************)
 (*   stmt_trans              *)
 (*****************************)                                       


 SIMP_TAC list_ss [Once stmt_sem_cases] >> gvs[] >>
 Cases_on `is_const e` >| [
   gvs[is_const_val_exsist, clause_name_def, lemma_v_red_forall] >>
   frame_typ_into_stmt_typ_tac >>           
   gvs[Once e_typ_cases, Once v_typ_cases]
      
   ,
   (* e is not const *)
   gvs[is_const_val_exsist, clause_name_def, lemma_v_red_forall] >>
   frame_typ_into_stmt_typ_tac >>           
   
   ‘∀e. prog_exp e ty’ by ( ASSUME_TAC PROG_e >>
                            FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`ty`]))) >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`e`])) >>           
   gvs[prog_exp_def] >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`gscope`, ‘scopest’, ‘t_scope_list’, ‘t_scope_list_g’,
                                               ‘t_string_names_a x_list’, ‘b’, ‘c’, ‘order’,‘delta_g’, ‘delta_b’, ‘delta_t’,
                                               ‘delta_x’, ‘f’, ‘Prs_n’])) >>                  
   gvs[is_const_val_exsist] >>
   srw_tac [SatisfySimps.SATISFY_ss][]
 ]
 ,

 (*****************************)
 (*   stmt_app                *)
 (*****************************)  

 SIMP_TAC list_ss [Once stmt_sem_cases] >> gvs[] >>
 srw_tac [boolSimps.DNF_ss][] >>
 Cases_on ‘index_not_const l = NONE’ >| [
   DISJ1_TAC >>
   IMP_RES_TAC index_not_const_NONE >>
   frame_typ_into_stmt_typ_tac >>           
   gvs[clause_name_def] >>
   
   PairCases_on ‘c’ >> gvs[] >>
   rename1 ‘(apply_table_f,c1,c2,c3,c4,tbl_map)’ >>
   
   subgoal ‘∃ y . ALOOKUP tbl_map s = SOME y’  >- ( 
     ‘dom_t_eq delta_t tbl_map’  by gvs[Once WT_c_cases] >>
     gvs[dom_t_eq_def, dom_eq_def, is_lookup_defined_def] >>
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`s`])) >>           
     gvs[]  ) >>
   
   PairCases_on ‘y’ >> gvs[] >>
   rename1 ‘(mk,default_action,default_action_args)’  >>         
   
   ‘f_in_apply_tbl tbl_map apply_table_f’ by gvs[Once WT_c_cases] >>
   fs[f_in_apply_tbl_def] >> 
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`s`, ‘mk’, ‘default_action’,
                             ‘default_action_args’,‘(MAP (λ(e_,tau_,b_). e_) (e_tau_b_list : (e # tau # bool) list))’ , ‘ascope’])) >>           
   gvs[] >>
   
   
   ‘table_map_typed tbl_map apply_table_f delta_g delta_b order’ by gvs[Once WT_c_cases] >>
   gvs[table_map_typed_def] >> 
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`s`, ‘mk’,‘default_action’,‘f'’,
                             ‘default_action_args’,‘MAP (λ(e_,tau_,b_). e_) (e_tau_b_list : (e # tau # bool) list)’,‘vl’,‘ascope’])) >>  gvs[] >>
   
   Q.EXISTS_TAC ‘ZIP (MAP (λ(e_,tau_,b_). e_) e_tau_b_list , mk)’ >>
   Q.EXISTS_TAC ‘vl_of_el vl’ >>
   Q.EXISTS_TAC ‘f'’ >>
   
   ‘LENGTH mk = LENGTH (MAP (λ(e_,tau_,b_). e_) e_tau_b_list)’ by simp[LENGTH_MAP] >>   
   srw_tac [][map_rw_doub, LENGTH_MAP, vl_of_el_ev]
   ,
   
   
   DISJ2_TAC >>
   Cases_on ‘index_not_const l’ >> gvs[] >>
   
   
   frame_typ_into_stmt_typ_tac >>           
   gvs[clause_name_def] >>
   
   IMP_RES_TAC index_not_const_in_range >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`x`])) >>           
   gvs[] >>
   
   
   
   ASSUME_TAC PROG_e >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`ty`])) >>
   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`(EL x (MAP (λ(e_,tau_,b_). e_) (e_tau_b_list:(e # tau # bool) list)))`])) >>
   fs[prog_exp_def] >>           
   
   
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`gscope`, ‘scopest’, ‘t_scope_list’, ‘t_scope_list_g’,
                                               ‘t_tau (EL x (MAP (λ(e_,tau_,b_). tau_) (e_tau_b_list : (e # tau # bool) list)))’,
                                               ‘EL x (MAP (λ(e_,tau_,b_). b_) (e_tau_b_list : (e # tau # bool) list))’, ‘c’,
                                               ‘order’,‘delta_g’, ‘delta_b’, ‘delta_t’,
                                               ‘delta_x’, ‘f’, ‘Prs_n’])) >>        
   IMP_RES_TAC index_not_const_EL >> gvs[] >>
   
   
   Q.EXISTS_TAC ‘framel’ >>
   Q.EXISTS_TAC ‘ZIP (MAP (λ(e_,tau_,b_). e_) e_tau_b_list  , LUPDATE e' x (MAP (λ(e_,tau_,b_). e_) e_tau_b_list) )’ >>
   Q.EXISTS_TAC ‘x’ >>
   Q.EXISTS_TAC ‘e'’ >>
   
   srw_tac [][map_rw_doub, LENGTH_MAP, vl_of_el_ev]  
   ]
 ,

 (*****************************)
 (*   stmt_ext                *)
 (*****************************)
        
 SIMP_TAC list_ss [Once stmt_sem_cases] >> gvs[] >>
 srw_tac [boolSimps.DNF_ss][clause_name_def] >>
 
 PairCases_on ‘c’ >> gvs[] >>
 rename1 ‘(c0,ext_map,c2,c3,c4,c5)’ >>
 frame_typ_into_stmt_typ_tac >>           
 gvs[clause_name_def] >>
 
 Cases_on ‘f’ >| [
     
   gvs[lookup_ext_fun_def] >>
   gvs[t_lookup_funn_def] >>
   
   Cases_on ‘ALOOKUP delta_b s’ >> gvs[] >>
   Cases_on ‘ALOOKUP delta_g s’ >> gvs[] >>
   gvs[ext_not_defined_def]
      
   ,
   (* fun inst *)
   gvs[lookup_ext_fun_def] >>
   gvs[t_lookup_funn_def] >>
   
   Cases_on ‘ALOOKUP delta_x s’ >> gvs[] >>   
   Cases_on ‘ALOOKUP ext_map s’ >> gvs[] >| [
       fs[WT_c_cases] >> gvs[dom_x_eq_def, dom_eq_def, is_lookup_defined_def] >>
       RES_TAC >> gvs[]
     ,
     PairCases_on ‘x'’ >> gvs[] >>
     REPEAT BasicProvers.FULL_CASE_TAC >> gvs[] >| [
         fs[WT_c_cases] >> gvs[dom_x_eq_def, dom_eq_def, is_lookup_defined_def] >>
         RES_TAC >> gvs[]
         ,
         Cases_on ‘q'’ >> gvs[] >>
         PairCases_on ‘x’ >> gvs[] >>
         fs[WT_c_cases, WTX_cases, extern_map_IoE_typed_def] >> gvs[] >>
         FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`q`,‘s’,‘r’,‘x'1’])) >> gvs[] >>
         FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`ascope`,‘gscope’,‘scopest’])) >> gvs[] >>
         srw_tac [SatisfySimps.SATISFY_ss][]
       ]
     ]
   ,
   (* fun ext *)  
   gvs[lookup_ext_fun_def] >>
   gvs[t_lookup_funn_def] >>
   
   Cases_on ‘ALOOKUP delta_x s’ >> gvs[] >>   
   Cases_on ‘ALOOKUP ext_map s’ >> gvs[] >| [
     fs[WT_c_cases] >> gvs[dom_x_eq_def, dom_eq_def, is_lookup_defined_def] >>
     RES_TAC >> gvs[]
     ,
     PairCases_on ‘x'’ >> gvs[] >>
     REPEAT BasicProvers.FULL_CASE_TAC >> gvs[] >| [
       Cases_on ‘ALOOKUP r s0 ’ >> gvs[] >>
       fs[WT_c_cases] >> gvs[dom_x_eq_def, dom_eq_def, is_lookup_defined_def] >>
       RES_TAC >> gvs[]
       ,
       
       Cases_on ‘ALOOKUP r' s0 ’ >> gvs[] >>
       PairCases_on ‘x’ >> gvs[] >>
       
       fs[WT_c_cases, WTX_cases, extern_MoE_typed_def] >> gvs[] >>
       FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘q’,‘s’,‘s0’,‘x'0’])) >> gvs[] >>
       FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`ascope`,‘gscope’,‘scopest’])) >> gvs[] >>
       srw_tac [SatisfySimps.SATISFY_ss][]
               
       ]
     ]
   ]
                 
]          
           
QED
        
        




   
val prog_stmtl_def = Define `
 prog_stmtl (stmtl) (ty:'a itself) =
∀ ascope gscope (scopest:scope list) status  t_scope_list t_scope_list_g T_e (c:'a ctx) order delta_g delta_b delta_t delta_x f Prs_n .
      
       type_scopes_list  (gscope)  (t_scope_list_g) ∧
       type_scopes_list  (scopest) (t_scope_list)   ∧
       star_not_in_sl (scopest) ∧

       
       (WT_c c order t_scope_list_g delta_g delta_b delta_x delta_t Prs_n) ∧
       (T_e = (order, f, (delta_g, delta_b, delta_x, delta_t))) ∧   
       (frame_typ  ( t_scope_list_g  ,  t_scope_list ) T_e Prs_n  gscope scopest stmtl ) ∧
                   (stmtl ≠ [stmt_empty] ∧ status = status_running ) ⇒
                                                                                                
       ∃ stmtl' scopest' framel gscope' status' ascope'.
       (stmt_red c ( ascope ,  gscope  ,           [ (f, stmtl, scopest )] , status)
                   ( ascope',  gscope' , framel ++ [ (f, stmtl' , scopest')] , status'))

`;

  




                                                    

Theorem PROG_stmtl:
  ∀ ty stmtl. prog_stmtl stmtl ty
Proof
     
STRIP_TAC >>
Cases_on ‘stmtl’ >-
 ( fs[prog_stmtl_def, Once stmt_sem_cases, empty_frame_not_typed] ) >>
 
fs[prog_stmtl_def] >>
REPEAT STRIP_TAC >>
Cases_on ‘h = stmt_empty’ >> gvs[] >| [

 (* if the statement is empty_stmt, then the tail is not empty, so the only thing can be done here is block exit *)
 gvs[Once stmt_sem_cases, clause_name_def]
 ,
 (* if the statement is not empty_stmt, then we need to check the length of t  *)      
 Cases_on ‘t’ >| [
     ASSUME_TAC PROG_stmt >> 
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`ty`,‘h’])) >>
     fs[prog_stmt_def] >> gvs[] >>
     
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`ascope`,‘gscope’,‘scopest’, ‘t_scope_list’, ‘t_scope_list_g’, ‘c’, ‘order’,‘delta_g’,
                                                 ‘delta_b’, ‘delta_t’, ‘delta_x’, ‘f’,‘Prs_n’])) >>
     srw_tac [SatisfySimps.SATISFY_ss][]
             
     ,
     (*now the case of block exec and seq *)        
     gvs[Once stmt_sem_cases, clause_name_def] >>
     IMP_RES_TAC frame_typ_head_of_stmtl  >>     
     ASSUME_TAC PROG_stmt >> 
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`ty`,‘h’])) >>
     fs[prog_stmt_def] >> gvs[] >>
     
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`ascope`,‘gscope’,‘scopest’, ‘t_scope_list’, ‘t_scope_list_g’, ‘c’, ‘order’,‘delta_g’,
                                                 ‘delta_b’, ‘delta_t’, ‘delta_x’, ‘f’,‘Prs_n’])) >> gvs[] >> PairCases_on ‘c’ >>
     srw_tac [SatisfySimps.SATISFY_ss][]
   ]
  ]
QED







val _ = export_theory ();




