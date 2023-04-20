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
      Q.EXISTS_TAC ‘tau_d_list’ >>
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



        
val parseError_in_gs_normalization = prove (           
“∀ tslg  t h .
parseError_in_gs tslg (h::t) ⇒
parseError_in_gs tslg [h] ∧
parseError_in_gs tslg t”,

REPEAT GEN_TAC >> STRIP_TAC >>                      
gvs[parseError_in_gs_def] >> rw[] >| [
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`i`])) >> gvs[] >>
  ‘i=0’ by gvs[] >> lfs[] 
 ,
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`SUC i`])) >> gvs[]
  ]                    
);


   



     
Theorem scopes_to_pass_imp_typed_lemma:
∀ gscope tslg funn func_map b_func_map delta_g delta_b g_scope_passed.
  dom_b_eq delta_b b_func_map ∧
  dom_g_eq delta_g func_map ∧
  dom_tmap_ei delta_g delta_b ∧
  LENGTH tslg = 2 ∧            
  type_scopes_list gscope tslg ∧                                                                                                    
  scopes_to_pass funn func_map b_func_map gscope = SOME g_scope_passed ⇒
  ∃ tslg_passed .
                t_scopes_to_pass funn delta_g delta_b tslg = SOME tslg_passed ∧
                type_scopes_list g_scope_passed tslg_passed                                                
Proof
gvs[scopes_to_pass_def, t_scopes_to_pass_def] >>
REPEAT STRIP_TAC >>

Cases_on ‘funn’ >> gvs[] >>

REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
gvs[dom_g_eq_def, dom_eq_def, is_lookup_defined_def] >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘s’])) >>
gvs[] >>              

simp_tac list_ss [Once type_scopes_list_normalize] >>
srw_tac [][type_scopes_list_EL] >>
simp_tac list_ss [type_scopes_list_def, similarl_def, similar_def] >>

gvs[dom_b_eq_def, dom_eq_def, is_lookup_defined_def] >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘s’])) >>
gvs[]
QED

 (* same proof as  to scopes_to_pass_imp_typed_lemma, TODO: refactor *)    
val typed_imp_scopes_to_pass_lemma = prove (
“∀ gscope tslg funn func_map b_func_map delta_g delta_b tslg_passed .
  dom_b_eq delta_b b_func_map ∧
  dom_g_eq delta_g func_map ∧
  dom_tmap_ei delta_g delta_b ∧
  LENGTH tslg = 2 ∧            
  type_scopes_list gscope tslg ∧
  t_scopes_to_pass funn delta_g delta_b tslg = SOME tslg_passed ⇒
∃ g_scope_passed . scopes_to_pass funn func_map b_func_map gscope = SOME g_scope_passed ∧
                   type_scopes_list g_scope_passed tslg_passed  ”,
cheat

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
“ ∀ delta_g delta_b delta_x f tdl tau .
SOME (tdl,tau) = t_lookup_funn f delta_g [] delta_x ⇒
dom_tmap_ei delta_g delta_b ⇒
SOME (tdl,tau) = t_lookup_funn f delta_g delta_b delta_x
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
∀ f delta_g delta_b delta_x tdl t.
   typying_domains_ei delta_g delta_b delta_x ∧
   t_lookup_funn f delta_g [] delta_x = SOME (tdl,t) ∧
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


     

          




val t_scopes_lookup_empty_ctx_lemma = prove (“
∀ delta_g delta_b e1 e2 s t_scope_list_g q r.
ALOOKUP delta_g s = SOME (q,r) ∧
dom_tmap_ei delta_g delta_b ∧
t_scopes_to_pass (funn_name s) delta_g delta_b [e1; e2] = SOME t_scope_list_g ⇒
t_scopes_to_pass (funn_name s) delta_g []      [[]; e2] = SOME t_scope_list_g”,

REPEAT STRIP_TAC >>
gvs[t_scopes_to_pass_def] >>
gvs[dom_tmap_ei_def, dom_empty_intersection_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>    
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘s’])) >> gvs[] 
);
            

val find_star_of_globals_ctx_lemma = prove ( “
∀ delta_g delta_b func_map b_func_map e1 e2 q r x.
dom_map_ei func_map b_func_map ∧            
dom_tmap_ei delta_g delta_b ∧
dom_g_eq delta_g func_map ∧
dom_b_eq delta_b b_func_map ∧
Fb_star_defined b_func_map [e1; e2] ∧
Fg_star_defined func_map [e1; e2] ∧
ALOOKUP delta_g x = SOME (q,r) ∧
find_star_in_globals [e1; e2] (varn_star (funn_name x)) = SOME r ⇒
find_star_in_globals [[]; e2] (varn_star (funn_name x)) = SOME r”,

REPEAT STRIP_TAC >>
gvs[find_star_in_globals_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>    

                              
 fs[dom_tmap_ei_def, dom_map_ei_def ,dom_empty_intersection_def] >>
 fs[dom_g_eq_def, dom_b_eq_def, dom_eq_def, is_lookup_defined_def] >>
 fs[Fg_star_defined_def, Fb_star_defined_def, is_lookup_defined_def] >>
 NTAC 6 (LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘x’])) >> gvs[]  ) >| [
 IMP_RES_TAC lookup_map_none_lemma1 >> gvs[]
 ,
 fs[lookup_map_def, topmost_map_def, find_topmost_map_def] >>
 REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
 gvs[INDEX_FIND_def] >>
 REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) 
]
);



(******************************************)



        

val find_star_of_inst_ctx_lemma = prove ( “
∀ ext_map r x e1 e2 sig.
  X_star_not_defined [e1; e2] ∧                                        
  ALOOKUP ext_map x = SOME sig ∧ 
  X_star_defined ext_map [e1; e2] ∧              
  find_star_in_globals [e1; e2] (varn_star (funn_inst x)) = SOME r ⇒
  find_star_in_globals [[]; e2] (varn_star (funn_inst x)) = SOME r ”,
                                                                
REPEAT STRIP_TAC >>
gvs[find_star_in_globals_def, X_star_not_defined_def, X_star_defined_def, is_lookup_defined_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>

REPEAT (LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘funn_inst x’, ‘x’])) >> gvs[]) >>
IMP_RES_TAC lookup_map_none_lemma1 >> gvs[]    
);       



val find_star_of_ext_ctx_lemma = prove ( “
∀ ext_map r x x' e1 e2 sig.
  X_star_not_defined [e1; e2] ∧                                        
  ALOOKUP ext_map x  = SOME sig ∧ 
  X_star_defined ext_map [e1; e2] ∧              
  find_star_in_globals [e1; e2] (varn_star (funn_ext x x')) = SOME r ⇒
  find_star_in_globals [[]; e2] (varn_star (funn_ext x x')) = SOME r ”,
                                                                
REPEAT STRIP_TAC >>
gvs[find_star_in_globals_def, X_star_not_defined_def, X_star_defined_def, is_lookup_defined_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>

REPEAT (LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘funn_ext x x'’, ‘x’])) >> gvs[]) >>
IMP_RES_TAC lookup_map_none_lemma1 >> gvs[]    
);       









val WTFg_empty_empty_db = prove ( “
∀ func_map b_func_map order g1 g2 delta_g delta_b delta_x Prs_n.
  dom_tmap_ei delta_g delta_b ∧ dom_map_ei func_map b_func_map ∧
  dom_g_eq delta_g func_map ∧  dom_b_eq delta_b b_func_map ∧
  Fb_star_defined b_func_map [g1; g2] ∧
  Fg_star_defined func_map [g1; g2] ∧                
WTFg func_map order [g1; g2] delta_g delta_b delta_x Prs_n⇒
WTFg func_map order [[]; g2] delta_g [] delta_x Prs_n”,

gvs[WTFg_cases, func_map_typed_def] >>
REPEAT STRIP_TAC >>

FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘stmt’, ‘xdl’, ‘x’])) >> gvs[] >>
Q.EXISTS_TAC ‘tau’ >> gvs[] >>
Q.EXISTS_TAC ‘tdl’ >> gvs[] >>
Q.EXISTS_TAC ‘t_scope_list_g'’ >>
gvs[] >>
gvs[t_lookup_funn_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
IMP_RES_TAC t_scopes_lookup_empty_ctx_lemma >> gvs[] >>
IMP_RES_TAC find_star_of_globals_ctx_lemma >> gvs[]
);




        
val WTFX_empty_empty_db = prove ( “
∀ func_map (ext_map: 'a ext_map ) order g1 g2 delta_g delta_b delta_x .
  X_star_not_defined [g1; g2] ∧
  X_star_defined ext_map [g1; g2] ∧
WTX ext_map order [g1; g2] delta_g delta_b delta_x ⇒
WTX ext_map order [[]; g2] delta_g [] delta_x ” ,
                                  
REPEAT STRIP_TAC >>
gvs[WTX_cases] >>
CONJ_TAC >| [
                                      
 gvs[extern_map_IoE_typed_def] >>
 REPEAT STRIP_TAC >>
        
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘xdl’, ‘x’, ‘IoE’, ‘MoE’])) >> gvs[] >>
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘a’, ‘g_scope_list’, ‘local_scopes’])) >> gvs[] >>
 qexistsl_tac [‘tdl’, ‘tau’ ,‘a'’, ‘scope_list'’,‘v’, ‘t_scope_list_g'’] >> gvs[] >>
              
 gvs[t_scopes_to_pass_def] >>
 REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
 
 
 gvs[t_lookup_funn_def] >>
 REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 
 IMP_RES_TAC find_star_of_inst_ctx_lemma
 ,
 gvs[extern_MoE_typed_def] >>
 REPEAT STRIP_TAC >>
        
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘xdl’, ‘x’,‘x'’ ,‘IoEsig’, ‘MoE’, ‘MoE_map’])) >> gvs[] >>
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘a’, ‘g_scope_list’, ‘local_scopes’])) >> gvs[] >>
 qexistsl_tac [‘tdl’,‘tau’,‘a'’, ‘scope_list'’,‘v’, ‘t_scope_list_g'’] >> gvs[] >>
              
 gvs[t_scopes_to_pass_def] >>
 REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[])  >>

 gvs[t_lookup_funn_def] >>
 REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 
 IMP_RES_TAC find_star_of_ext_ctx_lemma        
]
);
  


         
  
                           

            
val WT_c_empty_db = prove (
“∀ f delta_b delta_g delta_x delta_t passed_delta_b passed_delta_t
       apply_table_f (ext_map: 'a ext_map) func_map b_func_map tbl_map pars_map order tau
       tdl gscope g_scope_passed tslg passed_tslg  Prs_n.          

t_lookup_funn f delta_g passed_delta_b delta_x = SOME (tdl, tau)∧
t_tbl_to_pass f delta_b delta_t = SOME passed_delta_t ∧
t_map_to_pass f delta_b = SOME passed_delta_b ∧
t_scopes_to_pass f delta_g delta_b tslg = SOME passed_tslg ∧
scopes_to_pass f func_map b_func_map gscope = SOME g_scope_passed ∧

WT_c (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)
          order tslg delta_g delta_b delta_x delta_t Prs_n ⇒
∃passed_b_func_map passed_tbl_map.
          map_to_pass f b_func_map = SOME passed_b_func_map ∧
          tbl_to_pass f b_func_map tbl_map = SOME passed_tbl_map ∧
          WT_c
            (apply_table_f,ext_map,func_map,passed_b_func_map,pars_map,
             passed_tbl_map) order passed_tslg delta_g passed_delta_b delta_x
            passed_delta_t Prs_n”,

 REPEAT STRIP_TAC >>

 gvs[t_tbl_to_pass_def, t_map_to_pass_def] >>
 REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[])  >>
 
 gvs[tbl_to_pass_def, map_to_pass_def] >>
 REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>

 gvs[scopes_to_pass_def, t_scopes_to_pass_def] >>
 REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
 
 gvs[t_lookup_funn_def] >>
 REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
 
 TRY (  gvs[WT_c_cases] >>                                 
        IMP_RES_TAC dom_eq_imp_NONE >> gvs[]
     ) >>
 
 
 
 ‘dom_map_ei func_map [] ∧ dom_tmap_ei delta_g [] ∧
  typying_domains_ei delta_g [] delta_x ∧ dom_b_eq [] [] ∧
  dom_t_eq [] [] ∧ WTFb [] order [[]; EL 1 tslg] delta_g [] delta_x [] Prs_n ’ by
   (gvs [dom_map_ei_def, dom_tmap_ei_def, typying_domains_ei_def] >>
    gvs [dom_empty_intersection_def] >> gvs[] >>
    gvs [dom_b_eq_def, dom_t_eq_def, dom_eq_def, is_lookup_defined_def] >>
    SIMP_TAC list_ss [WTFb_cases, func_map_blk_typed_def, clause_name_def] >> gvs[]) >> gvs[] >>
 
 
 
 ‘table_map_typed [] apply_table_f delta_g [] order ∧
  f_in_apply_tbl [] apply_table_f’ by ( gvs [f_in_apply_tbl_def] >>
                                        gvs[table_map_typed_def] >>
                                        gvs[]) >> gvs[] >>
 
 ‘ Fg_star_defined func_map [[]; EL 1 tslg] ∧
   Fb_star_defined [] [[]; EL 1 tslg]  ’ by  
   (gvs [Fb_star_defined_def, is_lookup_defined_def] >> gvs[] >>
    gvs [Fg_star_defined_def, is_lookup_defined_def] >> gvs[]) >> gvs[] >>
 
 
 (subgoal ‘X_star_defined ext_map [[]; EL 1 tslg]’ >- (
   fs[quantHeuristicsTheory.LIST_LENGTH_2] >> gvs[] >>
   gvs[X_star_defined_def, is_lookup_defined_def] >> REPEAT STRIP_TAC >> gvs[]
   ) >> gvs[]
 ) >>
   
 fs[quantHeuristicsTheory.LIST_LENGTH_2] >> gvs[] >>

 (subgoal ‘X_star_not_defined [[]; e2]’ >- (
   gvs[X_star_not_defined_def] >> REPEAT STRIP_TAC >> gvs[]
   )                                          
 ) >> gvs[] >> rw[] >>

  IMP_RES_TAC WTFg_empty_empty_db >>                     
  IMP_RES_TAC WTFX_empty_empty_db
);



val t_scopes_passed_parseError = prove (“
∀ tslg tscl passed_tslg f delta_b delta_g.
t_scopes_to_pass f delta_g delta_b tslg = SOME passed_tslg ∧
parseError_in_gs tslg tscl ⇒
parseError_in_gs passed_tslg tscl ”,               

REPEAT STRIP_TAC >>
gvs[t_scopes_to_pass_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
gvs[parseError_in_gs_def]
)








                              


       

(* because this is the base frame, we know that there exsist typing global scope,
that is an extension of the current one (because it is scopes to pass lol ) *)
        
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
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘tau_d_list’, ‘tau’])) >> gvs[] >>

IMP_RES_TAC parseError_in_gs_normalization >>
IMP_RES_TAC t_scopes_passed_parseError           
);





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
(frame_typ  ( passed_tslg ,  (HD tsll) ) (order, f, (delta_g, passed_delta_b, delta_x, passed_delta_t)) Prs_n  passed_gscope locale stmtl )”,


REPEAT GEN_TAC >>
STRIP_TAC >>
gvs[WT_state_cases] >>

gvs[type_state_tsll_def] >>

FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`0`])) >> gvs[] >>
 subgoal ‘0 < LENGTH scll’ >- (Cases_on ‘scll’ >> gvs[] ) >> gvs[] >>

subgoal ‘locale = HD scll ∧ f = HD funnl ∧ stmtl = HD stmtll’ >-  (Cases_on ‘scll’ >> gvs[] >>
                                                                   Cases_on ‘stmtll’ >> gvs[] >>
                                                                   Cases_on ‘funnl’ >> gvs[] ) >>
lfs[] >> gvs[] >>                                                                   
gvs[type_frame_tsl_def] >>

gvs[type_frames_def, type_frame_tsl_def] >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`0`])) >> gvs[] >>
gvs[map_distrub] >>


‘ ∃ g_scope_passed .  scopes_to_pass (HD funnl) func_map b_func_map gscope = SOME g_scope_passed
                       ∧  type_scopes_list g_scope_passed passed_tslg’ by (gvs[Once WT_c_cases] >> IMP_RES_TAC typed_imp_scopes_to_pass_lemma >> gvs[]) >>
Cases_on ‘scopes_to_pass (HD funnl) func_map b_func_map gscope’ >> gvs[] >>

gvs[frame_typ_cases] >>
IMP_RES_TAC WT_c_empty_db >> gvs[] >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘tau_d_list’, ‘tau’])) >> gvs[] >>  


IMP_RES_TAC parseError_in_gs_normalization >>
IMP_RES_TAC t_scopes_passed_parseError >>
Cases_on ‘tsll’ >> gvs[] >> IMP_RES_TAC parseError_in_gs_normalization          
);





        
val WT_state_imp_t_funn_lookup_HD = prove ( “
∀ f apply_table_f ext_map func_map b_func_map pars_map tbl_map ascope gscope stmtl locale t status Prs_n order tslg
        delta_g delta_b delta_x delta_t tsll.
        
   WT_state (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)
          (ascope,gscope,(f,stmtl,locale)::t,status)
          Prs_n order tslg tsll (delta_g,delta_b,delta_x,delta_t) ⇒
   ∃  tdl t .
        t_lookup_funn f delta_g delta_b delta_x = SOME (tdl,t) ”,


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


val frame_typ_local_LENGTH = prove (“
∀ tslg tsl c Prs_n gscope locale stmtl .
frame_typ (tslg,tsl) c Prs_n gscope locale stmtl ⇒
 LENGTH locale > 0 ∧ stmtl ≠ []”,

REPEAT STRIP_TAC >>
gvs[frame_typ_cases, stmtl_typ_cases, type_ith_stmt_def, type_frame_tsl_def] >>
IMP_RES_TAC type_scopes_list_LENGTH >>
Cases_on ‘stmtl’ >> gvs[]
);
               



               
(* in psi:

psi : x -> (tau , lval)
unlike what we have with bool


1. We know that for every x of the frame_typ Psi(x) = type of Gamma(x)
2. extend deltas to return also the name of the parameter
3. 
       

*)
               



(* note that pre local means the (previous frame's scope ++ global scopes ) *)
(* probably we need to add that lval and v are the same type? *)
val co_wf_arg_def = Define ‘
co_wf_arg d x (curr_local: scope list) pre_local =                         
(is_d_out d ⇒ ∃ v lval v' .  lookup_map curr_local (varn_name x) = SOME (v, SOME lval) ∧
                              lookup_lval pre_local lval = SOME v') ’;



val co_wf_arg_list_def = Define ‘
co_wf_arg_list dl xl (curr_local: scope list) pre_local =                         
∀ i . 0 <= i ∧ i < LENGTH xl ∧ LENGTH xl = LENGTH dl ⇒ 
      co_wf_arg (EL i dl) (EL i xl) curr_local pre_local ’;



      
val co_wf_arg_list_normalization = prove (“
∀ xdl d x scopest copy_to_ss .
co_wf_arg_list (d::MAP (λ(x_,d_). d_) xdl) (x::MAP (λ(x_,d_). x_) xdl) scopest copy_to_ss ⇒
co_wf_arg_list (MAP (λ(x_,d_). d_) xdl) (MAP (λ(x_,d_). x_) xdl) scopest copy_to_ss ∧
co_wf_arg_list [d] [x] scopest copy_to_ss  ” ,            

REPEAT STRIP_TAC >>                  
gvs[co_wf_arg_list_def]>>
REPEAT STRIP_TAC >| [
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘SUC i’])) >>
 lfs[]      
 ,
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘0’])) >>
 ‘i=0’ by simp [] >>
 lfs[]
]
);






      (********************)








(*







        


∀ lval s x x' v scopest.
lookup_map scopest (varn_name x) = SOME (v,SOME (lval_field lval s)) ==>
∃ v'. lookup_map scopest (varn_name x') = SOME (v',SOME lval)

REPEAT STRIP_TAC >>
gvs[lookup_map_def] >>
gvs[topmost_map_def, find_topmost_map_def]





      






           
      
   ∀ lval v x d copy_to_ss scopest.
     
  LENGTH copy_to_ss > 1 ∧
  is_d_out d ∧
  lookup_map scopest (varn_name x) = SOME (v,SOME lval) ∧
  co_wf_arg d x scopest copy_to_ss ⇒
  ∃ scope_h_co . assign copy_to_ss v lval = SOME scope_h_co ∧
                 LENGTH scope_h_co > 1

Induct >>                             
REPEAT STRIP_TAC >>
gvs[co_wf_arg_def]  >| [
    
 gvs[assign_def] >>
 REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
 gvs[lookup_lval_def] >>
 gvs[lookup_v_def, lookup_out_def]>>
 REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
 gvs[lookup_map_def, topmost_map_def] >>
 REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[])
 ,
 gvs[assign_def]
 ,
 gvs[] >>       
 SIMP_TAC list_ss [assign_def] >>
  Cases_on ‘lookup_lval copy_to_ss lval ’ >> gvs[] >-
  (IMP_RES_TAC lookup_lval_exsists >> gvs[]) >>
  Cases_on ‘x'’ >> gvs[]
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘0’])) >>



                        
          
]




                                 







                                 
        
∀ xdl copy_to_ss scopest.
co_wf_arg_list (MAP (λ(x_,d_). d_) xdl) (MAP (λ(x_,d_). x_) xdl) scopest copy_to_ss  ∧
LENGTH copy_to_ss > 1 ⇒
~ (FOLDL (λss_temp_opt (x,d).
               if is_d_none_in d then ss_temp_opt
               else
                 case ss_temp_opt of
                   NONE => NONE
                 | SOME ss_temp =>
                   case lookup_map scopest (varn_name x) of
                     NONE => NONE
                   | SOME (v5,NONE) => NONE
                   | SOME (v5,SOME str) => assign ss_temp v5 str)
          (SOME copy_to_ss)
          (ZIP (MAP (λ(x_,d_). x_) xdl,MAP (λ(x_,d_). d_) xdl)) = NONE)



Induct_on `xdl` >>
fs[] >>
REPEAT STRIP_TAC >>
PairCases_on `h` >>
gvs[] >>

Cases_on ‘is_d_none_in h1’ >> gvs[] >| [

  ‘co_wf_arg_list (MAP (λ(x_,d_). d_) xdl)
   (MAP (λ(x_,d_). x_) xdl) scopest copy_to_ss’ by (IMP_RES_TAC co_wf_arg_list_normalization ) >>
  RES_TAC 
  ,
 
  Cases_on ‘lookup_map scopest (varn_name h0)’ >> gvs[] >| [
         
    ‘co_wf_arg_list [h1] [h0] scopest copy_to_ss’ by (IMP_RES_TAC co_wf_arg_list_normalization ) >>
    gvs[co_wf_arg_list_def] >>
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘0’])) >>
    gvs[co_wf_arg_def] >>                       
    Cases_on ‘h1’ >> gvs[is_d_out_def, is_d_none_in_def]
    ,
    PairCases_on ‘x’ >> gvs[] >>
    Cases_on ‘x1’ >> gvs[] >| [
             
       ‘co_wf_arg_list [h1] [h0] scopest copy_to_ss’ by (IMP_RES_TAC co_wf_arg_list_normalization ) >>
       gvs[co_wf_arg_list_def] >>
       FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘0’])) >>
       gvs[co_wf_arg_def] >>                       
       Cases_on ‘h1’ >> gvs[is_d_out_def, is_d_none_in_def]                        
       ,
       gvs[] >>
       ‘assign copy_to_ss x0 x = SOME scope_h_co ’ by cheat >>
       ‘LENGTH scope_h_co > 1 ’ by cheat >>
       
       ‘co_wf_arg_list (MAP (λ(x_,d_). d_) xdl)
        (MAP (λ(x_,d_). x_) xdl) scopest copy_to_ss’ by cheat >>
       
       
       FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`scope_h_co`,‘scopest’])) >>              
       gvs[]
      ]
    ]
  ]                                                          




                                                           
∀ copy_to_ss scopest xdl .
LENGTH copy_to_ss > 1 ⇒
~ (update_return_frame (MAP (λ(x_,d_). x_) xdl) (MAP (λ(x_,d_). d_) xdl) copy_to_ss scopest = NONE)
  
REPEAT STRIP_TAC >>
gvs[update_return_frame_def]






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
                        lookup_funn_sig_body f func_map b_func_map ext_map’ >- (
    
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
               
                
  gvs[copyout_def] >>
  Cases_on ‘update_return_frame (MAP (λ(x_,d_). x_) xdl)
              (MAP (λ(x_,d_). d_) xdl) (h2 ⧺ retrieved_g_scope) scopest'’ >> gvs[] >>   
  
  cheat >> Cases_on ‘LENGTH x’ >> gvs[] >> cheat
                

  ]
                                
QED

*)

                
val _ = export_theory ();




