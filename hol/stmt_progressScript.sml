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
open stmt_subject_reductionTheory;
     
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
(Q.PAT_X_ASSUM `e_red c scope scopest ^exp_term exp2 fr` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once e_red_cases] thm)))

fun OPEN_EXP_TYP_TAC exp_term =
(Q.PAT_X_ASSUM ` e_typ (t1,t2) t ^exp_term ta bll` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once e_typ_cases] thm)))

fun OPEN_STMT_TYP_TAC stmt_term =
(Q.PAT_X_ASSUM ` stmt_typ (t1,t2) q g ^stmt_term` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once stmt_typ_cases] thm)))

        
fun OPEN_STMT_RED_TAC stm_term =
(Q.PAT_X_ASSUM `stmt_red ct (ab, gsl,[(fun,[^stm_term],gam)],st) stat`
 (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once stmt_red_cases] thm)))

val OPEN_ANY_STMT_RED_TAC =
(Q.PAT_X_ASSUM `stmt_red ct (ab, gsl,[(fun,[stm_term],gam)],st) stat`
 (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once stmt_red_cases] thm)))
 
fun OPEN_FRAME_TYP_TAC frame_term =
(Q.PAT_X_ASSUM ` frame_typ (t1,t2) t a b h d ^frame_term` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once frame_typ_cases] thm)))
   
fun OPEN_LVAL_TYP_TAC lval_term =
(Q.PAT_X_ASSUM `lval_typ (g1,q1) t (^lval_term) (tp)` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once lval_typ_cases] thm)))



val _ = new_theory "stmt_progress";

   
val prog_stmt_def = Define `
 prog_stmt (stmt) (ty:'a itself) =
∀ ascope gscope (scopest:scope list) status  t_scope_list t_scope_list_g T_e (c:'a ctx) order delta_g delta_b delta_t delta_x f Prs_n .
      
       type_scopes_list  (gscope)  (t_scope_list_g) ∧
       type_scopes_list  (scopest) (t_scope_list)   ∧
       star_not_in_sl (scopest) ∧
       parseError_in_gs t_scope_list_g [t_scope_list] ∧


       
       (WT_c c order t_scope_list_g delta_g delta_b delta_x delta_t Prs_n) ∧
       (T_e = (order, f, (delta_g, delta_b, delta_x, delta_t))) ∧   
       (frame_typ  ( t_scope_list_g  ,  t_scope_list ) T_e Prs_n  gscope scopest [stmt] ) ∧
                   (stmt ≠ stmt_empty ∧ status = status_running ) ⇒
                                                                                                
       ∃ stmtl scopest' framel gscope' status' ascope'.
       (stmt_red c ( ascope ,  gscope  ,           [ (f, [stmt], scopest )] , status)
                   ( ascope',  gscope' , framel ++ [ (f, stmtl , scopest')] , status'))

`;


      

val frame_typ_into_stmt_typ_tac = gvs[Once frame_typ_cases] >>                        
                    gvs[Once stmtl_typ_cases] >>
                    gvs[type_ith_stmt_def] >>
                    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`0`])) >>
                    gvs[] >>
                    gvs[Once stmt_typ_cases]

      
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
gvs[oDROP_def] >> 
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
gvs[oTAKE_def] >> 
gvs[ADD1] >>

Cases_on ‘oTAKE i sl’ >> gvs[] >>
        
Cases_on ‘LENGTH sl ≥ 3 ’ >> gvs[] >-
 
(‘i=LENGTH sl -2’ by gvs[] >> lfs[] ) >>

‘i + 2 =LENGTH sl’ by gvs[] >> Cases_on ‘i’ >> gvs[] >>
gvs[oTAKE_def]  
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





val lval_assign_exists = prove ( “
∀ sl v v' v''.    
 lookup_lval sl (lval_varname v) = SOME v' ⇒
  ∃sl'. assign sl v'' (lval_varname v) = SOME sl' ”,
REPEAT STRIP_TAC >>
   gvs[assign_def] >>
    gvs[lookup_lval_def, lookup_v_def, lookup_map_def, topmost_map_def] >>                         
      REPEAT BasicProvers.FULL_CASE_TAC >> gvs[] >> 
   PairCases_on ‘x'’ >> Cases_on ‘ALOOKUP r v’ >>
 gvs[lookup_out_def, lookup_map_def, topmost_map_def, find_topmost_map_def]
);
               




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
 
 Cases_on ‘v'’ >> gvs[Once v_typ_cases] >>
 
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
  
  gvs[assign_def] >>
  
  Cases_on ‘v'’ >> gvs[Once v_typ_cases] >>
  Cases_on ‘v’ >> gvs[Once v_typ_cases] >>
  REPEAT BasicProvers.FULL_CASE_TAC >> gvs[] >| [
    PairCases_on ‘p’ >>  PairCases_on ‘p'’ >>  PairCases_on ‘bitv’ >>  PairCases_on ‘bitv'’ >> gvs[] >>
    gvs[assign_to_slice_def]                                                                                              
    ,
    PairCases_on ‘p’ >>  PairCases_on ‘p'’ >>  PairCases_on ‘bitv’ >>  PairCases_on ‘bitv'’ >> gvs[bs_width_def] >>
    
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`scopest`, ‘gscope’,‘t_scope_list’,‘t_scope_list_g’, ‘(tau_bit p1)’, ‘F’,
                                                  ‘x’, ‘T_e’])) >> gvs[] >>
      
    gvs[Once e_typ_cases] >>            
    gvs[vec_to_const_def] >>
                       
    IMP_RES_TAC bit_slice_typed >>
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`p1`])) >>           
    REPEAT ( gvs[Once v_typ_cases] >>            
             gvs[bs_width_def] >>            
             gvs[vec_to_const_def] >>       
             srw_tac [SatisfySimps.SATISFY_ss][])                        
    ]
  ,

   (*lval paren *)     
  gvs[Once lval_typ_cases]
 ]
QED


                


                                                  

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

 SIMP_TAC list_ss [Once stmt_red_cases] >> gvs[] >>
 Cases_on `is_const e` >| [
      
   gvs[is_const_val_exsist, clause_name_def, lemma_v_red_forall] >>
      
   gvs[Once frame_typ_cases] >>                        
   gvs[Once stmtl_typ_cases] >>
   gvs[type_ith_stmt_def] >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`0`])) >>
   gvs[] >>
   gvs[Once stmt_typ_cases] >>
   
   ‘LENGTH t_scope_list_g = 2’ by fs[WT_c_cases] >>         
   ‘LENGTH t_scope_list_g = LENGTH gscope’ by ( IMP_RES_TAC type_scopes_list_LENGTH >> gvs[] ) >>
   ‘LENGTH scopest >= 1’ by ( IMP_RES_TAC type_scopes_list_LENGTH >> gvs[] )   >| [
     gvs[clause_name_def] >>
     srw_tac [SatisfySimps.SATISFY_ss][assignment_scope_exists]        
     ,
     gvs[assign_def] >>
     ‘LENGTH (scopest ⧺ gscope) >= 3 ’ by gvs[] >>
     drule separate_exists >> REPEAT STRIP_TAC >> srw_tac [SatisfySimps.SATISFY_ss][]
      ]       

   ,
   (* e is not const *)
   gvs[is_const_val_exsist, clause_name_def, lemma_v_red_forall] >>
   
   gvs[Once frame_typ_cases] >>                        
   gvs[Once stmtl_typ_cases] >>
   gvs[type_ith_stmt_def] >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`0`])) >>
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

 SIMP_TAC list_ss [Once stmt_red_cases] >> gvs[] >>
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
 SIMP_TAC list_ss [Once stmt_red_cases] >> gvs[clause_name_def]
                                                
 ,

 (*****************************)
 (*   stmt_ret                *)
 (*****************************)
        
 SIMP_TAC list_ss [Once stmt_red_cases] >> gvs[] >>
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
         
 SIMP_TAC list_ss [Once stmt_red_cases] >> gvs[] >>
 Cases_on ‘stmt = stmt_empty’ >> gvs[] >| [
            (* seq2 *) 
   gvs[Once stmt_red_cases, clause_name_def] >>
   frame_typ_into_stmt_typ_tac >>           
   gvs[Once stmt_red_cases, clause_name_def]
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
      FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`0`])) >>
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
     gvs[Once stmt_red_cases] >>
     IMP_RES_TAC stmtl_len_from_in_frame_theorem >> gvs[] >>
     SIMP_TAC list_ss  [Once stmt_red_cases] >> gvs[] >>
     srw_tac [boolSimps.DNF_ss][] >>
     srw_tac [SatisfySimps.SATISFY_ss][clause_name_def]        
   ]                                        
 ]                                           
 ,

 (*****************************)
 (*   stmt_verify             *)
 (*****************************)

 SIMP_TAC list_ss [Once stmt_red_cases] >> gvs[] >>
 Cases_on `is_const e` >| [
   Cases_on `is_const e0` >| [
     (* verify T/F  err  *)
     gvs[is_const_val_exsist, clause_name_def, lemma_v_red_forall] >>
     frame_typ_into_stmt_typ_tac >>           
     gvs[Once e_typ_cases, Once v_typ_cases] >>
     Cases_on ‘boolv’ >>         
     srw_tac [SatisfySimps.SATISFY_ss][] >>        
     gvs[Once e_typ_cases, Once v_typ_cases, clause_name_def]                         
     ,
     (* verify T/F  e *)
     gvs[is_const_val_exsist, clause_name_def, lemma_v_red_forall] >>
     frame_typ_into_stmt_typ_tac >>           
     gvs[Once e_typ_cases, Once v_typ_cases] >>
     

     ‘∀e0. prog_exp e0 ty’ by ( ASSUME_TAC PROG_e >>
                                FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`ty`]))) >>
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`e0`])) >>           
     gvs[prog_exp_def] >>
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`gscope`, ‘scopest’, ‘t_scope_list’, ‘t_scope_list_g’,
                                                 ‘t_tau tau_err’, ‘b'’, ‘c’, ‘order’,‘delta_g’, ‘delta_b’, ‘delta_t’,
                                                 ‘delta_x’, ‘f’, ‘Prs_n’])) >>                  
     gvs[is_const_val_exsist] >>
     srw_tac [SatisfySimps.SATISFY_ss][]          
   ]
   ,
   (* verify e e' *)
   
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
 (*   stmt_trans              *)
 (*****************************)                                       


 SIMP_TAC list_ss [Once stmt_red_cases] >> gvs[] >>
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

 SIMP_TAC list_ss [Once stmt_red_cases] >> gvs[] >>
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
        
 SIMP_TAC list_ss [Once stmt_red_cases] >> gvs[] >>
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
         FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`ascope`,‘gscope’,‘scopest’, ‘lol’])) >> gvs[] >>
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
       FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`ascope`,‘gscope’,‘scopest’, ‘lol’])) >> gvs[] >>
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
       parseError_in_gs t_scope_list_g [t_scope_list] ∧

       
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
 ( fs[prog_stmtl_def, Once stmt_red_cases, empty_frame_not_typed] ) >>
 
fs[prog_stmtl_def] >>
REPEAT STRIP_TAC >>
Cases_on ‘h = stmt_empty’ >> gvs[] >| [

 (* if the statement is empty_stmt, then the tail is not empty, so the only thing can be done here is block exit *)
 gvs[Once stmt_red_cases, clause_name_def]
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
     gvs[Once stmt_red_cases, clause_name_def] >>
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


   

(* ========================================================================== *)
(*                                                                            *)
(*         Progress of the state definitions, lemmas and thms                 *)
(*                                                                            *)
(* ========================================================================== *)




        
val prog_state_def = Define `
 prog_state (framel) (ty:'a itself) =
∀ (c:'a ctx) ascope  gscope   status  tslg tsll order delta_g delta_b delta_t delta_x Prs_n .
      
  (WT_state c ( ascope ,  gscope  , framel  , status) Prs_n  order tslg tsll (delta_g, delta_b, delta_x, delta_t))
      ∧ framel ≠ []  ∧ status = status_running ∧
     (∀ (f:funn) (local_scope: scope list) (t:frame_list) . framel ≠ ((f,[stmt_empty],local_scope)::t))
  ⇒

     ∃ status' ascope' gscope' framel'.
       (frames_red c ( ascope ,  gscope  , framel  , status)
                     ( ascope',  gscope' , framel' , status'))                   
`;




val list_len_3 = prove ( “
  ∀ l a b c . a::b::c = l ⇒ LENGTH l > 1 ”,
  Cases >> REPEAT STRIP_TAC >> gvs[ADD1]);


val MAP_ZIP_tri_normalization = prove ( 
“∀ al bl cl a b c t.
 LENGTH al = LENGTH bl ∧ LENGTH bl = LENGTH cl ∧ 
(a,b,c)::t = MAP (λ(a_,b_,c_). (a_,b_,c_)) (ZIP (al,ZIP (bl,cl))) ⇒
 HD al = a ∧ HD bl = b ∧ HD cl = c ∧
 t = TL (MAP (λ(a_,b_,c_). (a_,b_,c_)) (ZIP (al,ZIP (bl,cl)))) ∧
 LENGTH al > 0
”,

Cases_on ‘al’ >>
Cases_on ‘bl’ >>
Cases_on ‘cl’ >>
gvs[] 
);
                                  


val type_state_tsll_normalization = prove (                            
“∀ scll tsll.
  LENGTH scll = LENGTH tsll ∧
  LENGTH scll > 0 ∧
type_state_tsll scll tsll ⇒
type_state_tsll [HD scll] [HD tsll] ∧
type_state_tsll (TL scll) (TL tsll)”,
               
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
);




val t_map_to_pass_delta_b_cases = prove (
“∀ delta_b passed_delta_b f .
t_map_to_pass f delta_b = SOME passed_delta_b ⇒
(passed_delta_b = [] ∨ passed_delta_b= delta_b)”,
REPEAT STRIP_TAC >>
gvs[t_map_to_pass_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) 
);

        

val t_lookup_funn_not_blk_lemma = prove (
“ ∀ delta_g delta_b delta_x f txdl tau .
SOME (txdl,tau) = t_lookup_funn f delta_g [] delta_x ⇒
dom_tmap_ei delta_g delta_b ⇒
SOME (txdl,tau) = t_lookup_funn f delta_g delta_b delta_x
”,

REPEAT STRIP_TAC >>
fs[dom_tmap_ei_def] >>
rfs[dom_empty_intersection_def] >>

gvs[t_lookup_funn_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`s`])) >> gvs[]
);




        
val ext_not_def_in_mpty_delta_b = prove (“
∀ f delta_g delta_b delta_x txdl t.
   typying_domains_ei delta_g delta_b delta_x ∧
   t_lookup_funn f delta_g [] delta_x = SOME (txdl,t) ∧
   ext_is_defined delta_x f ∧
   ext_not_defined delta_g [] f ⇒
   ext_not_defined delta_g delta_b f”,

REPEAT STRIP_TAC >>
Cases_on ‘f’ >> gvs[] >>
gvs[typying_domains_ei_def, t_lookup_funn_def, ext_is_defined_def,  ext_not_defined_def] >>
gvs[dom_empty_intersection_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 
REPEAT (FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘s’])) >> gvs[])
);

    

val delta_b_maps_empty_lemma = prove (“
∀ f delta_b b_func_map.
 dom_b_eq delta_b b_func_map ∧  
 t_map_to_pass f delta_b = SOME [] ⇒
  map_to_pass f b_func_map = SOME []  ” ,                    

gvs[t_map_to_pass_def, map_to_pass_def ] >>

REPEAT STRIP_TAC >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[dom_b_eq_def, dom_eq_def, is_lookup_defined_def]) >> 
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘s’])) >> gvs[]
);




        
val  delta_b_maps_lemma  = prove (“
∀ f delta_b b_func_map.
 LENGTH delta_b = LENGTH b_func_map ∧
 dom_b_eq delta_b b_func_map ∧            
 t_map_to_pass f delta_b = SOME delta_b ⇒
  map_to_pass f b_func_map = SOME b_func_map   ”,

REPEAT STRIP_TAC >>
gvs[t_map_to_pass_def, map_to_pass_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
REPEAT STRIP_TAC >>

gvs[dom_b_eq_def,dom_eq_def, is_lookup_defined_def ] >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘s’])) >> gvs[] >>
Cases_on ‘b_func_map’ >> gvs[]
);


val  delta_t_maps_lemma  = prove (“
∀ f delta_b delta_t b_func_map tbl_map.
 LENGTH delta_t = LENGTH tbl_map ∧
  dom_b_eq delta_b b_func_map ∧                  
  t_tbl_to_pass f delta_b delta_t  = SOME delta_t ⇒
  tbl_to_pass f b_func_map tbl_map = SOME tbl_map   ”,

REPEAT STRIP_TAC >>
gvs[t_tbl_to_pass_def, tbl_to_pass_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
REPEAT STRIP_TAC >>

gvs[dom_b_eq_def,dom_eq_def, is_lookup_defined_def ] >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘s’])) >> gvs[]
);
                                                
              





val find_stars_in_g_same = prove (“        
∀ e1 e2 x y r .
find_star_in_globals [e1; e2] (varn_star (funn_name x)) = SOME r ∧
(∀y'. ALOOKUP e1 (varn_star (funn_name x)) ≠ SOME y') ∧                                                               
ALOOKUP e2 (varn_star (funn_name x)) = SOME y ⇒
find_star_in_globals [[]; e2] (varn_star (funn_name x)) = SOME r ” ,

REPEAT STRIP_TAC >>
gvs[find_star_in_globals_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >-

(IMP_RES_TAC lookup_map_none_lemma1 >> gvs[]) >>

gvs[lookup_map_def, topmost_map_def, find_topmost_map_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
       
gvs[INDEX_FIND_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[])
);


     

(* because this is the base frame, we know that there exsist typing global scope,
that is an extension of the current one (because it is scopes to pass ) *)
        
val WT_state_imp_frame_typ_single = prove ( 
  “ ∀  ascope gscope f stmtl locale status Prs_n order tslg tsll delta_g delta_b
       delta_x delta_t apply_table_f ext_map func_map b_func_map pars_map
       tbl_map.
    
    WT_state  ( apply_table_f , ext_map , func_map , b_func_map , pars_map , tbl_map )
              (ascope,gscope,[(f,stmtl,locale)],status) Prs_n  order tslg
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
(frame_typ  ( passed_tslg ,  (HD tsll) ) (order, f, (delta_g, passed_delta_b, delta_x, passed_delta_t)) Prs_n  passed_gscope locale stmtl ) ”,


REPEAT GEN_TAC >>
STRIP_TAC >>     
gvs[Once WT_state_cases] >>


subgoal ‘locale = HD scll ∧ f = HD funnl ∧ stmtl = HD stmtll’ >-  (
    ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:funn`` , ``:'b`` |-> ``:stmt list`` , ``:γ`` |-> ``:(varn#v#lval option)list list`` ] ZIP_HD_tri_1)  >> 
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`funnl`, ‘stmtll’, ‘scll’, ‘f’, ‘stmtl’, ‘locale’]))  >>  gvs[] ) >>
   
fs[] >> gvs[] >>
         
gvs[type_state_tsll_def] >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`0`])) >> gvs[] >>
subgoal ‘0 < LENGTH scll’ >- (Cases_on ‘scll’ >> gvs[]  ) >> gvs[] >>
gvs[type_frame_tsl_def] >>

                       
gvs[type_frames_def, type_frame_tsl_def] >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`0`])) >> gvs[] >>

                     
Cases_on ‘tsll’ >> gvs[] >>
gvs[map_distrub] >>

         
IMP_RES_TAC parseError_in_gs_normalization >> gvs[] >>

‘ ∃ g_scope_passed .  scopes_to_pass (HD funnl) func_map b_func_map gscope = SOME g_scope_passed
                       ∧  type_scopes_list g_scope_passed passed_tslg’ by (gvs[Once WT_c_cases] >> IMP_RES_TAC typed_imp_scopes_to_pass_lemma >> gvs[]) >>
Cases_on ‘scopes_to_pass (HD funnl) func_map b_func_map gscope’ >> gvs[] >>

         
gvs[frame_typ_cases] >>
IMP_RES_TAC WT_c_empty_db >> gvs[] >> 
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘tau_x_d_list’, ‘tau’])) >> gvs[] >>

IMP_RES_TAC parseError_in_gs_normalization >>
IMP_RES_TAC t_scopes_passed_parseError           
);








        
val WT_state_imp_t_funn_lookup_HD = prove ( “
∀ f apply_table_f ext_map func_map b_func_map pars_map tbl_map ascope gscope stmtl locale t status Prs_n order tslg
        delta_g delta_b delta_x delta_t tsll.
        
   WT_state (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)
          (ascope,gscope,(f,stmtl,locale)::t,status)
          Prs_n order tslg tsll (delta_g,delta_b,delta_x,delta_t) ⇒
   ∃  txdl t .
        t_lookup_funn f delta_g delta_b delta_x = SOME (txdl,t) ”,


REPEAT STRIP_TAC >>
gvs[WT_state_cases, type_frames_def] >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`0`])) >> gvs[] >>
 subgoal ‘0 < LENGTH scll’ >- (Cases_on ‘scll’ >> gvs[]  ) >> gvs[] >>
   Cases_on ‘ (ZIP (funnl,ZIP (stmtll,scll)))’ >> gvs[] >> 
 gvs[frame_typ_cases, Once stmtl_typ_cases] >>

 IMP_RES_TAC t_map_to_pass_delta_b_cases >> gvs[] >| [
 gvs[t_lookup_funn_def] >>
      REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) 
 ,
 ‘dom_b_eq delta_b b_func_map’ by gvs[Once WT_c_cases] >>
 ‘LENGTH delta_b = LENGTH b_func_map’ by gvs[Once WT_c_cases] >>     
          
  IMP_RES_TAC delta_b_maps_lemma >> gvs[] >>
  gvs[t_lookup_funn_def] >>
  REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[])                                                                
 ]
);





val ret_status_framel_empty_lemma = prove (
“∀ c ascope ascope' gscope gscope' f stmt stmt_stack v framel locale locale'.
stmt_red c (ascope,gscope,[(f,[stmt],locale)],status_running)
           (ascope',gscope',framel ⧺ [(f,stmt_stack,locale')], status_returnv v) ⇒
framel = []”,
REPEAT STRIP_TAC >>
gvs[Once stmt_red_cases]
);



        
val ret_status_framel_empty = prove (
“∀ c ascope ascope' gscope gscope' f stmtl stmtl' v framel locale locale'.
stmt_red c (ascope,gscope,[(f,stmtl,locale)],status_running)
           (ascope',gscope',framel ⧺ [(f,stmtl',locale')],status_returnv v) ⇒
   framel = []”,
REPEAT STRIP_TAC >>
gvs[Once stmt_red_cases] >>
IMP_RES_TAC ret_status_framel_empty_lemma
);



Theorem passed_b_same_lookup_sig_body:
∀ b_func_map delta_b passed_b_func_map passed_delta_b func_map ext_map f.
map_to_pass f b_func_map = SOME passed_b_func_map ∧
t_map_to_pass f delta_b = SOME passed_delta_b ⇒
(lookup_funn_sig_body f func_map b_func_map ext_map = lookup_funn_sig_body f func_map passed_b_func_map ext_map)
Proof
REPEAT STRIP_TAC >>                      
gvs[lookup_funn_sig_body_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
gvs[t_map_to_pass_def, map_to_pass_def]
QED


     
  


val assign_star_length_2 = prove (“
∀ gscope v f sl.                                  
LENGTH gscope = 2 ∧
assign gscope v (lval_varname (varn_star f)) = SOME sl ⇒
LENGTH sl = 2 ”,

REPEAT STRIP_TAC >>
gvs[assign_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[])
);



val retrieved_scopes_exsist = prove (“
∀ sl  f func_map b_func_map ext_map stmt xdl gscope.               
LENGTH sl = 2 ∧
lookup_funn_sig_body f func_map b_func_map ext_map = SOME (stmt,xdl) ⇒
∃ retrieved_g_scope . SOME retrieved_g_scope = scopes_to_retrieve f func_map b_func_map gscope sl ∧
                      LENGTH retrieved_g_scope = 2 ”,
REPEAT STRIP_TAC >>
gvs[lookup_funn_sig_body_def, scopes_to_retrieve_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) 
);


   
Theorem lval_of_star_in_gscope:
∀ v locale gscope f .
star_not_in_sl locale ∧
SOME v = lookup_vexp2 locale gscope (varn_star f) ⇒
∃ v' . lookup_lval gscope (lval_varname (varn_star f)) = SOME v'
Proof
REPEAT STRIP_TAC >> IMP_RES_TAC lookup_map_in_gsl_lemma >>
gvs[lookup_vexp2_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘q’, ‘r’, ‘gscope’, ‘f’])) >>
gvs[] >>
gvs[lookup_lval_def, lookup_v_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[])
QED



          
               



(* note that pre local means the (previous frame's scope ++ global scopes ) *)
(* probably we need to add that lval and v are the same type? *)
val co_wf_arg_def = Define ‘
co_wf_arg d x (ts_curr_local: t_scope list) passed_tslg pre_ts T_e =                         
(is_d_out d ⇒ ∃ t lval.  lookup_map ts_curr_local (varn_name x) = SOME (t, SOME lval) ∧
                            lval_typ (passed_tslg,pre_ts) T_e lval (t_tau t) ) ’;



val co_wf_arg_list_def = Define ‘
co_wf_arg_list dl xl (ts_curr_local: t_scope list) passed_tslg pre_ts T_e =                         
∀ i . 0 <= i ∧ i < LENGTH xl ∧ LENGTH xl = LENGTH dl ⇒ 
      co_wf_arg (EL i dl) (EL i xl) ts_curr_local passed_tslg pre_ts T_e ’;



      
val co_wf_arg_list_normalization = prove (“
∀ xdl d x ts_current passed_tslg pre_ts T_e.
co_wf_arg_list (d::MAP (λ(x_,d_). d_) xdl) (x::MAP (λ(x_,d_). x_) xdl) ts_current passed_tslg pre_ts T_e ⇒
co_wf_arg_list (MAP (λ(x_,d_). d_) xdl) (MAP (λ(x_,d_). x_) xdl) ts_current passed_tslg pre_ts T_e∧
co_wf_arg d x ts_current passed_tslg pre_ts T_e  ” ,            

REPEAT STRIP_TAC >>                  
gvs[co_wf_arg_list_def]>>
REPEAT STRIP_TAC >| [
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘SUC i’])) >>
 lfs[]      
 ,
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘0’])) >>
 lfs[]
]
);







val t_lookup_passed_map = prove (“
∀ f delta_b delta_g delta_x passed_delta_b tau txdl.
t_map_to_pass f delta_b = SOME passed_delta_b ∧
t_lookup_funn f delta_g passed_delta_b delta_x =  SOME (txdl,tau) ⇒
t_lookup_funn f delta_g        delta_b delta_x =  SOME (txdl,tau) ”,

REPEAT STRIP_TAC >>        
gvs[t_map_to_pass_def, t_lookup_funn_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[])
);






val scopes_to_pass_length = prove (“
∀ f func_map b_func_map scl.        
LENGTH scl = 2 ⇒
∃ scl'. SOME scl' = scopes_to_pass f func_map b_func_map scl ∧
LENGTH scl' = 2”,

gvs[scopes_to_pass_def] >>
REPEAT STRIP_TAC >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[])
);



(* from stmt sr *)        
Theorem ret_status_stmt_len_lemma:
∀ c ascope ascope' gscope gscope' f stmt_stack stmt_stack' v framel locale locale'.
stmt_red c (ascope,gscope,[(f,stmt_stack,locale)],status_running)
           (ascope',gscope,[(f,stmt_stack',locale')], status_returnv v) ⇒
LENGTH stmt_stack = LENGTH stmt_stack'
Proof
cheat
QED















                                                         

Theorem PROG_framel:
  ∀ ty framel. prog_state framel ty
Proof
  
STRIP_TAC >>
gvs[prog_state_def] >> REPEAT STRIP_TAC >>

(* we know that the framel is not empty *)
Cases_on ‘framel’ >> gvs[] >>

PairCases_on ‘c’ >>
rename1 ‘( apply_table_f , ext_map , func_map , b_func_map , pars_map , tbl_map )’ >>         
PairCases_on ‘h’ >>
rename1 ‘(f,stmtl,locale)::t’ >>

(* We know that the head of the frames is well typed and holds the following features *)
IMP_RES_TAC WT_state_HD_of_list >>


(* use progress  stmtl to show that the head indeed makes a step *)

ASSUME_TAC PROG_stmtl >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`ty`,‘stmtl’])) >>
gvs[prog_stmtl_def] >>

FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`ascope`,‘passed_gscope’,‘locale’, ‘HD tsll’, ‘passed_tslg’, ‘(apply_table_f,ext_map,func_map,passed_b_func_map,pars_map,passed_tbl_map)’, ‘order’,‘delta_g’, ‘passed_delta_b’, ‘passed_delta_t’, ‘delta_x’, ‘f’,‘Prs_n’])) >> gvs[] >>


(* now the difference between comp1 and comp2 is the status after the transition being return or not*)
                  
SIMP_TAC list_ss [Once frames_red_cases] >>
srw_tac [boolSimps.DNF_ss][] >>
  gvs[Once frame_typ_cases, type_frame_tsl_def] >>       

Cases_on ‘notret status'’ >| [

         (* if the status is not return, comp1 holds *)
  DISJ1_TAC >>

  Q.EXISTS_TAC ‘status'’ >>
  srw_tac [][clause_name_def] >>
  Q.EXISTS_TAC ‘ascope'’ >>

  CONV_TAC $ RESORT_EXISTS_CONV rev >>              
  Q.EXISTS_TAC ‘gscope'’ >>
  Q.EXISTS_TAC ‘framel ⧺ [(f,stmtl',scopest')]’ >>
  srw_tac [][] >>


  gvs[scopes_to_retrieve_def] >>
  Cases_on ‘f’ >> gvs[] >>
  REPEAT BasicProvers.FULL_CASE_TAC >> gvs[]
  ,                                                      
    (* if the status is return, then we need to check the length of t*)
  subgoal ‘∃ v . status' = status_returnv v’ >-
   (Cases_on ‘status'’ >>  gvs[notret_def] ) >> lfs[] >>

   (* now depending on the length of the frame list tail we should have two cases*)
  Cases_on ‘t’ >> gvs[] >- (
    (* case1 when t is empty, it means we are at the bottom of the stack returning, and this applies comp1 not comp2*)
    Q.EXISTS_TAC ‘status_returnv v’ >>
    srw_tac [][clause_name_def] >>
    Q.EXISTS_TAC ‘ascope'’ >>
    
    CONV_TAC $ RESORT_EXISTS_CONV rev >>              
    
    Q.EXISTS_TAC ‘gscope'’ >>
    Q.EXISTS_TAC ‘framel ⧺ [(f,stmtl',scopest')]’ >>
    srw_tac [][] >>
    

    gvs[scopes_to_retrieve_def] >>
    Cases_on ‘f’ >> gvs[] >>
    REPEAT BasicProvers.FULL_CASE_TAC >> gvs[]
    ) >>
  
  (* case2 when t is not empty it means that we have to prove all neccesary conditions to make sure that we have a step*)
     
  PairCases_on ‘h’ >> gvs[clause_name_def] >>
  DISJ2_TAC >>
  
  Q.EXISTS_TAC ‘ascope'’ >>
  CONV_TAC $ RESORT_EXISTS_CONV $ Listsort.sort Term.compare >>
  Q.EXISTS_TAC ‘gscope'’ >>

  (* we know that the function is defined and its body and sig can be found via *)             
  subgoal ‘∃ stmt xdl . SOME (stmt,xdl) =
                        lookup_funn_sig_body f func_map b_func_map ext_map ∧
                ALL_DISTINCT (MAP FST xdl) ’ >- (
    
    gvs[frame_typ_cases] >>  
    IMP_RES_TAC WT_state_imp_t_funn_lookup_HD >>
    
    ‘WT_c (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)
     order tslg delta_g delta_b delta_x delta_t Prs_n’ by gvs[WT_state_cases] >>           
    drule  tfunn_imp_sig_body_lookup >> REPEAT STRIP_TAC >>
    METIS_TAC []   
    ) >>

    
  CONV_TAC $ RESORT_EXISTS_CONV rev >>              
  Q.EXISTS_TAC ‘xdl’ >>
  Q.EXISTS_TAC ‘v’ >>
  Q.EXISTS_TAC ‘stmtl'’ >>
  Q.EXISTS_TAC ‘stmt’ >>


               
  (* the frame list being produced by such transition is indeed empty  *)             
  IMP_RES_TAC ret_status_framel_empty >> gvs[] >>            
  
  (* now show that indeed varn star is in the gscope'' and that because we have to show that there will be an assign to that val*)      
 (* ‘type_scopes_list gscope' tslg'’ by
    (  gvs[WT_c_cases] >>
       IMP_RES_TAC typed_imp_scopes_to_pass_lemma  ) >>
  *)
  ASSUME_TAC Fg_star_lemma1 >>
  LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
                                    [‘passed_tslg’,‘f’, ‘func_map’, ‘delta_g’, ‘passed_delta_b’, ‘delta_x’, ‘order’, ‘passed_b_func_map’,
                                     ‘passed_gscope’,‘ext_map’,‘stmt’,‘xdl’,‘apply_table_f’,‘pars_map’,‘passed_tbl_map’,‘passed_delta_t’, ‘Prs_n’])) >> gvs[] >>
                                     
  IMP_RES_TAC passed_b_same_lookup_sig_body >> 
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘func_map’, ‘ext_map’])) >> gvs[] >>


   ‘∃ v''. SOME v'' = lookup_vexp2 locale passed_gscope (varn_star f) ’ by (IMP_RES_TAC star_tau_exists_in_scl_tscl >> srw_tac [SatisfySimps.SATISFY_ss][] )>>

  (* the initial global scope and final global scope are eq in the statement reduction *)             
  IMP_RES_TAC return_imp_same_g >> lfs[] >>
    gvs[] >>
              
  ‘∃ v'. lookup_lval gscope' (lval_varname (varn_star f)) = SOME v'’ by (IMP_RES_TAC lval_of_star_in_gscope >> srw_tac [SatisfySimps.SATISFY_ss][])>>
     
  IMP_RES_TAC lval_assign_exists >>          
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘v’])) >> gvs[] >>
  CONV_TAC $ SWAP_EXISTS_CONV >>
  Q.EXISTS_TAC ‘scopest'’ >> gvs[] >>

 (* now we show that scopes to retrieve exsists & it's length is 2 *)
 subgoal ‘LENGTH gscope' = 2 ’ >- ( IMP_RES_TAC type_scopes_list_LENGTH >> gvs[WT_c_cases] ) >>
    
  IMP_RES_TAC assign_star_length_2 >>
 ‘lookup_funn_sig_body f func_map b_func_map ext_map = SOME (stmt,xdl) ’ by METIS_TAC [] >>
              
  ASSUME_TAC retrieved_scopes_exsist >>
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘sl'’,‘f’,‘func_map’,‘b_func_map’, ‘ext_map’, ‘stmt’, ‘xdl’, ‘gscope’])) >>
  gvs[] >>
  CONV_TAC $ RESORT_EXISTS_CONV rev >>
  Q.EXISTS_TAC ‘retrieved_g_scope’ >> gvs[] >>

  IMP_RES_TAC frame_typ_local_LENGTH  >>



 Cases_on ‘t_lookup_funn f delta_g passed_delta_b delta_x’ >> gvs[] >>

  subgoal ‘
  MAP (λ(t,x,d). d) tau_x_d_list = (MAP (λ(x,d). d) xdl) ∧
  MAP (λ(t,x,d). x) tau_x_d_list = (MAP (λ(x,d). x) xdl)’ >-  (
    IMP_RES_TAC tfunn_imp_sig_body_lookup >>
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘tau_x_d_list’,‘tau’,‘f’])) >>
    gvs[] >>
   Cases_on ‘lookup_funn_sig_body f func_map passed_b_func_map ext_map’ >> gvs[] >>
   gvs[ELIM_UNCURRY, GSYM lambda_FST, GSYM lambda_SND]
   )>> gvs[] >>



  IMP_RES_TAC t_lookup_passed_map >> gvs[] >>

  ‘∃ g_scope_list'⁵' . SOME g_scope_list'⁵' =
                       scopes_to_pass h0 func_map b_func_map retrieved_g_scope  ∧ LENGTH g_scope_list'⁵' = 2 ’ by (
      IMP_RES_TAC scopes_to_pass_length >> gvs[] 
    ) >>
   Q.EXISTS_TAC ‘g_scope_list'⁵'’ >> gvs[] >>






 (* show that scopest' has the same type as locale original *)
  (* we need the SR for stmtl here *)

  subgoal ‘type_frame_tsl scopest' (HD tsll)  ∧ stmtl' ≠ [] ∧
           LENGTH (HD tsll) >= 1   ’ >- (
  IMP_RES_TAC ret_status_stmt_len_lemma >>
   ASSUME_TAC SR_stmtl_stmtl >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`ty`,‘stmtl’])) >>
   gvs[sr_stmtl_def, frame_typ_cases] >> 
   
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [
    `stmtl'`,‘ascope’,‘ascope'’, ‘gscope'’,‘gscope'’, ‘locale’,‘scopest'’,
    ‘[]’,‘status_running’,‘status_returnv v’, ‘HD tsll’,‘passed_tslg’,
    ‘order’, ‘delta_g’, ‘passed_delta_b’, ‘passed_delta_t’, ‘delta_x’, ‘f’,
    ‘Prs_n’, ‘0’, ‘apply_table_f’, ‘ext_map’, ‘func_map’, ‘passed_b_func_map’, ‘pars_map’, ‘passed_tbl_map’])) >> gvs[] >>
  gvs[clause_name_def, type_frame_tsl_def] >>
  gvs[Once stmtl_typ_cases] >> Cases_on ‘stmtl'’ >> gvs[]             
  ) >>


 





   

              
   (*********************************)
   
  subgoal ‘LENGTH scopest' >= 1’ >- ( cheat) >>
  subgoal ‘LENGTH h2 > 0’ >- ( cheat ) >>





          
  Cases_on ‘copyout (MAP (λ(x_,d_). x_) xdl) (MAP (λ(x_,d_). d_) xdl)
            g_scope_list'⁵' h2 scopest'’ >| [



      gvs[WT_state_cases] >>     
      ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:funn``, ``:'b`` |-> ``:stmt list``, ``:'c`` |-> ``:scope_list``] ZIP_tri_sep_ind)  >>
      FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘(h0,h1,h2)::t'’,‘funnl’,‘stmtll’,‘scll’, ‘f’,‘stmtl’,‘locale’])) >> gvs[] >>
      gvs[EL_CONS, PRE_SUB1] >>
      gvs[GSYM ZIP_tri_id2] >>

  (* that the t_scopes between caller and callee *)
    gvs[t_scopes_consistent_list_def] >>
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘0’])) >>
    gvs[] >> 

   Cases_on ‘tsll’ >> gvs[] >>
   Cases_on ‘t’ >> gvs[] >>


          
            
  ‘~(copyout (MAP (λ(x_,d_). x_) xdl) (MAP (λ(x_,d_). d_) xdl)
          g_scope_list'⁵' h2 scopest' =
     NONE)’ by cheat >> gvs[]

     gvs[copyout_def]


                                

       ,
       PairCases_on ‘x’ >> gvs[] >>
SIMP_TAC list_ss [scopes_to_retrieve_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[])

    ]



     

  ]
                                
QED







val assign_re_LENGTH = prove (“
∀ ss v lval res_ss n.
LENGTH ss > n ∧
assign ss v lval = SOME res_ss ⇒
LENGTH res_ss > n”,

Induct_on ‘lval’ >>              
REPEAT STRIP_TAC >>
gvs[assign_def, find_topmost_map_def]>>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
METIS_TAC [] 
);



          
          
val FOLDL_co_not_empty= prove (“
∀ xdl ss curr_sc .
LENGTH ss > 0   ⇒
   FOLDL
     (λss_temp_opt (x,d).
          if is_d_none_in d then ss_temp_opt
          else
            case ss_temp_opt of
              NONE => NONE
            | SOME ss_temp =>
              case lookup_map [LAST curr_sc] (varn_name x) of
                NONE => NONE
              | SOME (v5,NONE) => NONE
              | SOME (v5,SOME str) => assign ss_temp v5 str)
     (SOME (ss))
     (xdl) ≠ SOME []”,

Induct >> gvs[] >>
REPEAT STRIP_TAC >>
PairCases_on ‘h’ >> gvs[]>> 
Cases_on ‘is_d_none_in h1’ >> gvs[] >>
Cases_on ‘lookup_map [LAST curr_sc] (varn_name h0)’ >> gvs[] >>
IMP_RES_TAC co_none >>
PairCases_on ‘x’ >> gvs[]>>        
Cases_on ‘x1’ >> gvs[] >- IMP_RES_TAC co_none >>
Cases_on ‘assign ss x0 x’ >- IMP_RES_TAC co_none >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘x'’,‘curr_sc’])) >>
gvs[] >> IMP_RES_TAC assign_re_LENGTH
);


         



                              

val update_res_frame_not_empty = prove (“
∀ ss curr_sc xl dl .
LENGTH ss > 0  ⇒
~ (update_return_frame (xl) (dl) (ss) [LAST curr_sc] = SOME [])”,
   
gvs[update_return_frame_def] >>
REPEAT STRIP_TAC >>
METIS_TAC [FOLDL_co_not_empty]
);




val dir_rel_1 = prove (“
∀ d .
¬is_d_none_in d ⇔ is_d_out d ”,

Cases_on ‘d’ >>
gvs[is_d_none_in_def, is_d_out_def]
);




val LAST_TL = prove (“                                       
∀l .
LENGTH l > 1 ⇒                                        
LAST l = LAST (TL l) ”,

Induct >>
REPEAT STRIP_TAC >>
gvs[ADD1]>>
Cases_on ‘l’ >> gvs[]
);





val out_consis_inp_LENGTH = prove (“
∀ l1 l2 .
out_lval_consistent l1 l2 ⇒
LENGTH l1 = LENGTH l2”,

Induct_on ‘l1’ >>
Induct_on ‘l2’ >>
gvs[out_lval_consistent_def] >>
REPEAT STRIP_TAC >>
gvs[LIST_REL_LENGTH]
);
                        
val out_consis_normalization = prove (“
∀ l1 l2 h h'.                        
out_lval_consistent (h::l1) (h'::l2) ⇒ 
out_lval_consistent (l1) (l2) ∧
(h ≠ NONE ⇔ is_d_out h')”,

gvs[out_lval_consistent_def] >>
REPEAT STRIP_TAC >>
gvs[]
);
                    





val type_scopes_list_LAST = prove (“
∀ scl tsl .
LENGTH scl > 0 ∧
type_scopes_list scl tsl ⇒
type_scopes_list [LAST scl] [LAST tsl]”,
cheat
);



val type_scopes_list_single_LENGTH = prove (“
∀ l1 l2 .
type_scopes_list [l1] [l2] ⇒
LENGTH l1 = LENGTH l2”,

gvs[type_scopes_list_def, similarl_def] >>
Induct_on ‘l1’ >>
Induct_on ‘l2’ >>
gvs[similar_def]
);

                      






Theorem v_types_ev:
∀ v t tslg ts T_e .
v_typ v (t_tau t) F ⇒ e_typ (tslg,ts) T_e (e_v v) (t_tau t) F
Proof
  cheat
QED





Theorem separate_abstract:
∀ l a b .
 LENGTH l > 1 ∧ 
(SOME b,SOME a) = separate l ⇒
l = a++b
Proof
cheat
QED  


     

Theorem separate_result_LENGTH:
 ∀ scopest gscope scope_list.
  (SOME gscope,SOME scopest) = separate scope_list ⇒
  LENGTH scope_list = LENGTH gscope + LENGTH scopest
Proof  

cheat
QED

Theorem map_snd_EQ:
!l . MAP (λx. SND x) l = MAP SND l
Proof
cheat
QED




Theorem lookup_map_single_LAST_ALOOKUP:
∀ l varn tup.
LENGTH l > 0 ∧  
lookup_map [LAST l] varn = SOME tup ⇒
ALOOKUP    (LAST l) varn = SOME tup
Proof
cheat                                         
QED



        

val co_wf_imp_update_frame_exists = prove (“
∀xdl pre_local pre_gscope_passed LASTcurr_local pre_passed_tslg pre_tsl LASTcurr_local_ts T_e.

LENGTH pre_local ≥ 1 ∧
LENGTH pre_gscope_passed = 2 ∧
     
     type_scopes_list pre_gscope_passed pre_passed_tslg ∧
     type_scopes_list pre_local pre_tsl ∧
      star_not_in_sl pre_local ∧                 
     type_scopes_list [LASTcurr_local] [LASTcurr_local_ts] ∧
                      
     
     co_wf_arg_list (MAP (λ(x,d). d) xdl) (MAP (λ(x,d). x) xdl) [LASTcurr_local_ts] pre_passed_tslg pre_tsl T_e ⇒
     ∃x. update_return_frame (MAP (λ(x,d). x) xdl) (MAP (λ(x,d). d) xdl) (pre_local ⧺ pre_gscope_passed) [LASTcurr_local] = SOME x” ,

gvs[update_return_frame_def] >>
Induct >>
REPEAT STRIP_TAC >>
gvs[] >>

PairCases_on ‘h’ >>
gvs[]>>
IMP_RES_TAC co_wf_arg_list_normalization  >> gvs[] >>
       
Cases_on ‘is_d_none_in h1’ >> gvs[] >| [

      (* use IH directly *)                                           
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘pre_local’, ‘pre_gscope_passed’, ‘LASTcurr_local’, ‘pre_passed_tslg’,
                                                 ‘pre_tsl’, ‘LASTcurr_local_ts’, ‘T_e’])) >> gvs[] 
    ,              

    gvs[co_wf_arg_def] >>
            

                       
    subgoal ‘is_d_out h1’ >- ( Cases_on ‘h1’ >> gvs[is_d_out_def, is_d_none_in_def]) >> gvs[] >>
    (* prove that indeed when we look into teh scope we will find a value and an lval and it is typed*)        
    subgoal ‘ ∃ v . lookup_map [LASTcurr_local] (varn_name h0) = SOME (v,SOME lval) ∧ v_typ v (t_tau t) F’ >- (
      ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:(v#lval option)``, ``:'b`` |-> ``:(tau#lval option)``] R_implies_lookup_map_scopesl)  >>
      gvs[type_scopes_list_def] >>           
      FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘(λ(v,lop1) (t,lop2). v_typ v (t_tau t) F ∧ lop1 = lop2)’,
                                                  ‘(t,SOME lval)’, ‘(varn_name h0)’, ‘v’, ‘[LASTcurr_local_ts]’, ‘[LASTcurr_local]’])) >>
      gvs[] >> Cases_on ‘lookup_map [LASTcurr_local] (varn_name h0)’ >> gvs[] >>
      PairCases_on ‘t'’ >> gvs[]
      ) >> gvs[] >> 
              

     (* now we know that typying a value, is teh same as ttyping an expression value with respect to ANY typing scopes and T_e *)

    IMP_RES_TAC v_types_ev >>
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘pre_passed_tslg’, ‘pre_tsl’, ‘T_e’])) >>

    (* since the lval is typed, and also the value is typed, then there exsists a scope such that  assign lval = v *)              
    ASSUME_TAC assignment_scope_exists >>  
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘pre_local’,‘pre_gscope_passed’,‘pre_tsl’,‘pre_passed_tslg’,‘t’,‘F’,‘lval’,‘v’,‘T_e’])) >>
    gvs[] >>                

    (* we know that the assignment yeilds a WT scopes, this is needed for the IH *)      
    ASSUME_TAC assign_e_is_wt>>
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘lval’, ‘pre_local’, ‘pre_tsl’,  ‘pre_gscope_passed’, ‘pre_passed_tslg’, ‘T_e’, ‘scopest'’, ‘gscope'’,
                                                ‘t’, ‘F’ ,‘scope_list'’ ,‘v’])) >>
    gvs[] >>
    IMP_RES_TAC type_scopes_list_LENGTH >> gvs[] >>

    (* now use the IH with the resulted scope of assignment *)            
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘scopest'’, ‘gscope'’, ‘LASTcurr_local’, ‘pre_passed_tslg’, ‘pre_tsl’, ‘LASTcurr_local_ts’, ‘T_e’])) >>
    gvs[] >>
    
    Cases_on ‘assign (pre_local ⧺ pre_gscope_passed) v lval’ >> gvs[] >>

    subgoal ‘scopest' ++ gscope'= scope_list'’ >- (
      IMP_RES_TAC separate_abstract >> gvs[] >>
      subgoal ‘LENGTH scope_list' > 1 ’ >-(            
        ASSUME_TAC assign_re_LENGTH >>
        IMP_RES_TAC type_scopes_list_LENGTH >> gvs[] >>
        FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘pre_local ⧺ pre_gscope_passed’, ‘v’, ‘lval’, ‘scope_list'’, ‘1’])) >>
        gvs[]
        ) >> gvs[]
      ) >> gvs[] >>
    
    IMP_RES_TAC type_scopes_list_LENGTH >> gvs[]
]
);






val out_lval_consis_imp_lval = prove (“
∀  i dl lol.
i < LENGTH dl ∧
is_d_out (EL i dl) ∧
out_lval_consistent lol dl ⇒
∃ lop . EL i lol = SOME lop”,

Induct >>
REPEAT STRIP_TAC >>                                
IMP_RES_TAC out_consis_inp_LENGTH >>  gvs[] >>                             
gvs[out_lval_consistent_def] >>
Cases_on ‘dl’ >>
Cases_on ‘lol’ >> gvs[] >-
 (Cases_on ‘h'’ >> gvs[]) >> 
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘t’, ‘t'’])) >>
gvs[]
); 



                                                 

val EL_exists_tri = prove (“
∀ i l b c .                 
i < LENGTH l ∧            
EL i (MAP (λ(a,b,c). c) (l)) = c ⇒
∃ b a. EL i (MAP (λ(a,b,c). b) (l)) =  b ∧
      EL i (MAP (λ(a,b,c). a) (l)) =  a ”,
Induct >>
Cases_on ‘l’ >> REPEAT STRIP_TAC >>
gvs[]
);


val mk_varn_EL = prove (“
∀ i l1 l2.
i < LENGTH l1 ∧  
mk_varn l1 = l2 ⇒
varn_name (EL i l1) = EL i l2
”,
Induct >> 
REPEAT STRIP_TAC >>
gvs[] >| [
Cases_on ‘l1’ >> gvs[] >>
gvs[mk_varn_def]
 ,
Cases_on ‘l1’ >> gvs[EL_CONS] >> gvs[PRE_SUB1] >>
gvs[mk_varn_lemma2]
]        
);


val EL_FST_P = prove (  “
∀ i l .
  i < LENGTH l ⇒
  EL i (MAP FST l) = FST (EL i l)”,
REPEAT STRIP_TAC >>
METIS_TAC[P_on_any_EL]
);


val ALOOKUP_LIST_index = prove (“        
∀ l i bc.
i < LENGTH l ∧
ALL_DISTINCT (MAP (λ(a,b,c). a) l) ∧
ALOOKUP l (EL i (MAP (λ(a,b,c). a) l)) = SOME bc ⇒
 FST bc = EL i (MAP (λ(a,b,c). b) l) ∧ SND bc = EL i (MAP (λ(a,b,c). c) l)”,

REPEAT STRIP_TAC >>
PairCases_on ‘bc’ >> gvs[] >>
IMP_RES_TAC ALOOKUP_ALL_DISTINCT_EL >>
                                                 
gvs[ELIM_UNCURRY,map_fst_EQ] >>
‘EL i (MAP FST l) = FST (EL i l)’ by  gvs[EL_FST_P] >>
gvs[] >>
Cases_on ‘EL i l’ >> gvs[]>>

gvs[EL_pair_list] >>
gvs[MAP_MAP_o] >>
METIS_TAC[ELIM_UNCURRY,map_snd_EQ, map_fst_EQ]
);                                           



val ALOOKUP_LIST_index2 = prove (“        
∀ l i b c.
i < LENGTH l ∧
ALL_DISTINCT (MAP (λ(a,b,c). a) l) ∧
ALOOKUP l (EL i (MAP (λ(a,b,c). a) l)) = SOME (b,c) ⇒
 b = EL i (MAP (λ(a,b,c). b) l) ∧ c = EL i (MAP (λ(a,b,c). c) l)”,
                                           
REPEAT STRIP_TAC >>
IMP_RES_TAC ALOOKUP_LIST_index >>
gvs[]
);





     
val lookup_map_index_distinct = prove (“ 
∀ i (l:(varn#'a#'b) list) a b c.
  i < LENGTH l ∧
ALL_DISTINCT (MAP (λ(a,b,c). a) l) ∧
EL i (MAP (λ(a,b,c). a) l) = a ∧
EL i (MAP (λ(a,b,c). b) l) = b ∧
EL i (MAP (λ(a,b,c). c) l) = c ⇒
lookup_map [l] a = SOME (b,c)”,

gvs[lookup_map_def, topmost_map_def, find_topmost_map_def] >>
REPEAT STRIP_TAC >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >| [
  gvs[INDEX_FIND_def] >>
  gvs[ALOOKUP_NONE] >>
  gvs[ELIM_UNCURRY, GSYM lambda_FST, EL_MEM]
  ,
 IMP_RES_TAC INDEX_FIND_EQ_SOME_0 >> gvs[]
, 

‘q = 0’ by ( IMP_RES_TAC INDEX_FIND_EQ_SOME_0 >> gvs[]) >>
 lfs[] >> gvs[] >>
PairCases_on ‘x’ >> gvs[] >>
gvs[INDEX_FIND_def] >>
IMP_RES_TAC ALOOKUP_LIST_index2 >> gvs[]
  ] 
);





        
        
(* TODO: remove many of the unneeded assumptions and also make a better version where t_funn_call and also txdl not there *)
val consistent_imp_wf_arg = prove (“
∀ curr_local pre_local curr_local_ts pre_tsl  T_e pre_gscope_passed pre_passed_tslg
  f delta_g passed_delta_b delta_x txdl xdl tau.

      type_frame_tsl curr_local curr_local_ts
   ∧  LENGTH curr_local > 0 
                                         
    ∧  MAP (λ(t,x,d). d) txdl = MAP (λ(x,d). d) xdl
    ∧  MAP (λ(t,x,d). x) txdl = MAP (λ(x,d). x) xdl
    ∧  ALL_DISTINCT (MAP FST xdl)
                                                 
    ∧  sig_tscope_consistent f delta_g passed_delta_b delta_x curr_local_ts
    ∧  t_lookup_funn f delta_g passed_delta_b delta_x = SOME (txdl,tau)
  ∧  t_scopes_consistent (T_e) pre_tsl pre_passed_tslg curr_local_ts ⇒
     co_wf_arg_list (MAP (λ(x,d). d) xdl) (MAP (λ(x,d). x) xdl)
          [LAST curr_local_ts] pre_passed_tslg pre_tsl T_e”,

    REPEAT STRIP_TAC >>
    gvs[t_scopes_consistent_def] >>
   gvs[sig_tscope_consistent_def, extract_elem_tri_def] >>

   gvs[co_wf_arg_list_def] >>
   REPEAT STRIP_TAC >>

   gvs[co_wf_arg_def] >>
   REPEAT STRIP_TAC >>

(*************)
IMP_RES_TAC out_consis_inp_LENGTH >>
IMP_RES_TAC out_lval_consis_imp_lval >> gvs[] >>
‘∃t varn.
          EL i (MAP (λ(a,b,c). b) (LAST curr_local_ts)) = t ∧
          EL i (MAP (λ(a,b,c). a) (LAST curr_local_ts)) = varn’ by (IMP_RES_TAC EL_exists_tri >> gvs[]) >>


Q.EXISTS_TAC ‘t’ >>
Q.EXISTS_TAC ‘lop’ >>
gvs[] >>

subgoal ‘varn_name (EL i (MAP (λ(x,d). x) xdl)) = EL i (MAP (λ(a,b,c). a) (LAST curr_local_ts))’ >-
 (  gvs[mk_varn_EL] )  >> gvs[] >>



subgoal ‘ALL_DISTINCT (MAP (λ(a,b,c). a) (LAST curr_local_ts))’ >- (
   IMP_RES_TAC mk_varn_lemma3 >>
   gvs[ELIM_UNCURRY,map_fst_EQ]
  ) >>

                
      
subgoal ‘lookup_map [LAST curr_local_ts]
          (varn_name (EL i (MAP (λ(x,d). x) xdl))) =
        SOME (EL i (MAP (λ(a,b,c). b) (LAST curr_local_ts)),SOME lop)’ >- 
 (
     IMP_RES_TAC lookup_map_index_distinct >> gvs[]
 ) >>  gvs[] >>

      IMP_RES_TAC lookup_map_single_LAST_ALOOKUP >>
      gvs[type_frame_tsl_def] >>
 IMP_RES_TAC type_scopes_list_LENGTH >> gvs[] >>
      METIS_TAC []
);



   


val copyout_not_none = prove (“

∀ curr_local pre_local curr_local_ts pre_tsl  T_e pre_gscope_passed pre_passed_tslg
  f delta_g passed_delta_b delta_x txdl xdl tau.
      LENGTH curr_local_ts ≥ 1
   ∧  LENGTH pre_local ≥ 1                  
   ∧  LENGTH pre_gscope_passed = 2
   ∧  type_frame_tsl curr_local curr_local_ts
   ∧  type_frame_tsl pre_local   pre_tsl
   ∧  type_scopes_list pre_gscope_passed pre_passed_tslg

    ∧  MAP (λ(t,x,d). d) txdl = MAP (λ(x,d). d) xdl
    ∧  MAP (λ(t,x,d). x) txdl = MAP (λ(x,d). x) xdl
    ∧  ALL_DISTINCT (MAP FST xdl)
                                                 
    ∧  sig_tscope_consistent f delta_g passed_delta_b delta_x curr_local_ts
    ∧  t_lookup_funn f delta_g passed_delta_b delta_x = SOME (txdl,tau)
  ∧  t_scopes_consistent (T_e) pre_tsl pre_passed_tslg curr_local_ts

==>     copyout (MAP (λ(x_,d_). x_) xdl) (MAP (λ(x_,d_). d_) xdl)
          pre_gscope_passed pre_local curr_local ≠
        NONE”,


REPEAT STRIP_TAC >>
      gvs[copyout_def] >>
      Cases_on ‘update_return_frame (MAP (λ(x_,d_). x_) xdl)
             (MAP (λ(x_,d_). d_) xdl) (pre_local ⧺ pre_gscope_passed)
             [LAST curr_local]’ >> gvs[]  >| [
          ASSUME_TAC consistent_imp_wf_arg >>

          FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘curr_local’, ‘pre_local’ ,‘curr_local_ts’ , ‘pre_tsl’ ,‘T_e’ ,
                                                      ‘pre_gscope_passed’ , ‘pre_passed_tslg’ , ‘f’ , ‘delta_g’ , ‘passed_delta_b’ ,
                                                      ‘delta_x’ ,‘txdl’, ‘xdl’ ,‘tau’])) >>
          gvs[type_frame_tsl_def] >>
          IMP_RES_TAC type_scopes_list_LENGTH  >>
          gvs[] >>
                   
          ASSUME_TAC co_wf_imp_update_frame_exists >>
         IMP_RES_TAC type_scopes_list_LAST  >>          
        FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘xdl’ , ‘pre_local’ , ‘pre_gscope_passed’ , ‘LAST curr_local’ , ‘pre_passed_tslg’
                                                    , ‘pre_tsl’, ‘LAST curr_local_ts’, ‘T_e’])) >>                                         
        gvs[] 
       ,
       Cases_on ‘LENGTH x’ >> gvs[] >>
       ASSUME_TAC update_res_frame_not_empty >>
       FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘pre_local ⧺ pre_gscope_passed’, ‘curr_local’,
                                                   ‘(MAP (λ(x_,d_). x_) (xdl : (string # d) list))’,
                                                   ‘(MAP (λ(x_,d_). d_) (xdl : (string # d) list))’])) >>
       gvs[]

  ]

);




        








                                                                        

                    


                        
                        


                
val _ = export_theory ();




