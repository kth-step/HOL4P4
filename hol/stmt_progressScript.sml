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


       
       (WT_c c order t_scope_list_g delta_g delta_b delta_x delta_t ) ∧
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
Induct >> rw[] >> gvs[vl_of_el_def, is_consts_def]>>
Cases_on ‘h’ >> gvs[is_const_def, v_of_e_def]                         
);

        

val index_not_const_EL = prove (
“∀ el x .
  x < LENGTH el ∧
index_not_const el = SOME x ⇒
¬is_const (EL x el)”,

Induct >>
rw[] >>
IMP_RES_TAC index_not_const_in_range >>
    
gvs[index_not_const_def] >>
Cases_on ‘INDEX_FIND 0 (λe. ¬is_const e) (h::el)’ >> gvs[]>>
PairCases_on ‘x'’ >> gvs[] >>                                           
IMP_RES_TAC INDEX_FIND_EQ_SOME_0 >> gvs[]
);





val oDROP_exists = prove (
“∀ sl i .
   LENGTH sl ≥ 3 ∧
   i = LENGTH sl − 2 ⇒
   ∃l l'. SOME l = oDROP (i) sl”,
Induct >>
Induct_on ‘i’ >>            

REPEAT STRIP_TAC >> 
gvs[oDROP_def] >> 
gvs[ADD1] >>

        
Cases_on ‘LENGTH sl ≥ 3 ’ >> gvs[] >-
 
(‘i=LENGTH sl -2’ by gvs[]
 >> METIS_TAC []) >>

‘i + 2 =LENGTH sl’ by gvs[] >>
Cases_on ‘i’ >> gvs[] >>
gvs[oDROP_def]  
);


val oTAKE_exists = prove (
“∀ sl i .
   LENGTH sl ≥ 3 ∧
   i = LENGTH sl − 2 ⇒
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




val separate_exists = prove (
“∀ sl.
LENGTH sl ≥ 3 ⇒
∃ l l' . (SOME l , SOME l' ) = separate sl ”,

REPEAT STRIP_TAC  >>
fs[separate_def] >>
gvs[ADD1, oDROP_def, oTAKE_def ] >>
IMP_RES_TAC oDROP_exists >>
IMP_RES_TAC oTAKE_exists >>
gvs[] >> METIS_TAC []
);

          





val lval_typ_imp_e_typ = prove ( 
    “      
∀ l tau gtsl tsl T_e .
  lval_typ (gtsl,tsl) T_e l (tau) ⇒
    ∃ e.  is_e_lval e ∧
      get_lval_of_e e = SOME l ∧
      e_typ (gtsl,tsl) T_e e tau T”,


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
     Q.EXISTS_TAC ‘e_slice e  (e_v (v_bit bitv)) (e_v (v_bit bitv'))’ >>                              gvs[get_lval_of_e_def, is_e_lval_def] >>
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









val lval_assign_exists = prove (
“∀ sl v v' v''.    
lookup_lval sl (lval_varname v) = SOME v' ⇒
∃sl'. assign sl v'' (lval_varname v) = SOME sl'”,

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
     ASSUME_TAC e_lval_WT >> gvs[] >>
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`(e_var v)`, ‘t_tau (tau)’,‘t_scope_list_g’,‘gscope’,‘t_scope_list’, ‘scopest’, ‘T_e’])) >> gvs[] >>

                 
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
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`e`, ‘t_tau (tau_xtl struct_ty x_tau_list)’,‘t_scope_list_g’,‘gscope’,‘t_scope_list’, ‘scopest’, ‘T_e’])) >> gvs[] >>

   gvs[assign_def] >>
              
  Cases_on ‘v'’ >> gvs[Once v_typ_cases] >>
     
    (Cases_on ‘INDEX_OF s (MAP FST (MAP (λ(x_,v_,tau_). (x_,v_)) x_v_tau_list))’ >>
    gvs[] >-
     (

     IMP_RES_TAC correct_field_type_FIND >>
     gvs[ FIND_def, INDEX_OF_def]  >>
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


    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`scopest`, ‘gscope’,‘t_scope_list’,‘t_scope_list_g’,
               ‘(tau_xtl struct_ty_struct (MAP (λ(x_,v_,tau_). (x_,tau_)) ( x_v_tau_list : (string # v # tau) list)))’, ‘F’,
               ‘v_struct (LUPDATE (s,v) x (MAP (λ(x_,v_,tau_). (x_,v_)) ( x_v_tau_list : (string # v # tau) list)))’, ‘T_e’])) >> gvs[] >>

   gvs[Once e_typ_cases] >>



  ASSUME_TAC e_lval_WT >> gvs[] >>
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`e`, ‘(t_tau
             (tau_xtl struct_ty_struct
                (MAP (λ(x_,v_,tau_). (x_,tau_)) (x_v_tau_list : (string # v # tau) list))))’,‘t_scope_list_g’,‘gscope’,‘t_scope_list’, ‘scopest’, ‘T_e’])) >> gvs[] >>



   drule LUPDATE_header_struct_v_typed >> STRIP_TAC >>

    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [
                                          ‘(MAP (λ(x_,v_,tau_). (x_,v_)) (x_v_tau_list : (string # v # tau) list))’,
                                          ‘v’, ‘struct_ty_struct’, ‘x’,‘F’])) >> gvs[] >>

  IMP_RES_TAC v_typ_always_lval >> 

srw_tac [SatisfySimps.SATISFY_ss][]

    ,

    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`scopest`, ‘gscope’,‘t_scope_list’,‘t_scope_list_g’,
               ‘(tau_xtl struct_ty_header (MAP (λ(x_,v_,tau_). (x_,tau_)) ( x_v_tau_list : (string # v # tau) list)))’, ‘F’,
               ‘v_header b' (LUPDATE (s,v) x (MAP (λ(x_,v_,tau_). (x_,v_)) ( x_v_tau_list : (string # v # tau) list)))’, ‘T_e’])) >> gvs[] >>

   gvs[Once e_typ_cases] >>



  ASSUME_TAC e_lval_WT >> gvs[] >>
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`e`, ‘(t_tau
             (tau_xtl struct_ty_header
                (MAP (λ(x_,v_,tau_). (x_,tau_)) (x_v_tau_list : (string # v # tau) list))))’,‘t_scope_list_g’,‘gscope’,‘t_scope_list’, ‘scopest’, ‘T_e’])) >> gvs[] >>



   drule LUPDATE_header_struct_v_typed >> STRIP_TAC >>

    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [
                                          ‘(MAP (λ(x_,v_,tau_). (x_,v_)) (x_v_tau_list : (string # v # tau) list))’,
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

         FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`scopest`, ‘gscope’,‘t_scope_list’,‘t_scope_list_g’,
               ‘(tau_bit p1)’, ‘F’,
               ‘x’, ‘T_e’])) >> gvs[] >>

              gvs[Once e_typ_cases] >>            
              gvs[vec_to_const_def] >>
                       
                IMP_RES_TAC bit_slice_typed >>
                FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`p1`])) >>           
                 REPEAT (           gvs[Once v_typ_cases] >>            
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
                                                  ‘delta_x’, ‘f’])) >>                  
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
                                                  ‘delta_x’, ‘f’])) >>                  
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
                                                  ‘delta_x’, ‘f’])) >>                  
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
      srw_tac [SatisfySimps.SATISFY_ss][]  >>        
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
                                                  ‘delta_x’, ‘f’])) >>                  
      gvs[is_const_val_exsist] >>
      srw_tac [SatisfySimps.SATISFY_ss][]          
        ] ,


         (* verify e e' *)
                
    gvs[is_const_val_exsist, clause_name_def, lemma_v_red_forall] >>
      frame_typ_into_stmt_typ_tac >>           

    ‘∀e. prog_exp e ty’ by ( ASSUME_TAC PROG_e >>
                                FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`ty`]))) >>
      FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`e`])) >>           
      gvs[prog_exp_def] >>
      FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`gscope`, ‘scopest’, ‘t_scope_list’, ‘t_scope_list_g’,
                                                  ‘t_tau tau_bool’, ‘b’, ‘c’, ‘order’,‘delta_g’, ‘delta_b’, ‘delta_t’,
                                                  ‘delta_x’, ‘f’])) >>                  
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
                                                  ‘delta_x’, ‘f’])) >>                  
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
      
    PairCases_on ‘y’ >> gvs[]>>
      rename1 ‘(mk,default_action,default_action_args)’  >>         

    ‘f_in_apply_tbl tbl_map apply_table_f’ by gvs[Once WT_c_cases] >>
     fs[f_in_apply_tbl_def] >> 
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`s`, ‘mk’, ‘default_action’,‘default_action_args’,‘(MAP (λ(e_,tau_,b_). e_) (e_tau_b_list : (e # tau # bool) list))’ , ‘ascope’])) >>           
     gvs[] >>
             
                             
      ‘table_map_typed tbl_map apply_table_f delta_g delta_b order’ by gvs[Once WT_c_cases] >>
    gvs[table_map_typed_def] >> 
          FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`s`, ‘mk’,‘default_action’,‘f'’,‘default_action_args’,‘MAP (λ(e_,tau_,b_). e_) (e_tau_b_list : (e # tau # bool) list)’,‘vl’,‘ascope’])) >>  gvs[] >>

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
                                                  ‘delta_x’, ‘f’])) >>        
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

        fs[WT_c_cases] >> gvs[dom_x_eq_def, dom_eq_def, is_lookup_defined_def] >>                                    RES_TAC >> gvs[]

        ,
        PairCases_on ‘x'’ >> gvs[] >>
        REPEAT BasicProvers.FULL_CASE_TAC >> gvs[] >| [
          fs[WT_c_cases] >> gvs[dom_x_eq_def, dom_eq_def, is_lookup_defined_def] >>                                    RES_TAC >> gvs[]
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

              fs[WT_c_cases] >> gvs[dom_x_eq_def, dom_eq_def, is_lookup_defined_def] >>                                    RES_TAC >> gvs[]
              ,
                
       PairCases_on ‘x'’ >> gvs[] >>
       REPEAT BasicProvers.FULL_CASE_TAC >> gvs[] >| [
             
              Cases_on ‘ALOOKUP r s0 ’ >> gvs[] >>
              fs[WT_c_cases] >> gvs[dom_x_eq_def, dom_eq_def, is_lookup_defined_def] >>                                    RES_TAC >> gvs[]
              ,
                
              Cases_on ‘ALOOKUP r' s0 ’ >> gvs[]>>
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

       
       (WT_c c order t_scope_list_g delta_g delta_b delta_x delta_t ) ∧
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
      
        FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`ascope`,‘gscope’,‘scopest’, ‘t_scope_list’, ‘t_scope_list_g’, ‘c’, ‘order’,‘delta_g’, ‘delta_b’, ‘delta_t’, ‘delta_x’, ‘f’,‘Prs_n’])) >>
         srw_tac [SatisfySimps.SATISFY_ss][]

         ,
        (*now the case of block exec and seq *)        
      gvs[Once stmt_red_cases, clause_name_def] >>
      IMP_RES_TAC frame_typ_head_of_stmtl  >>     
                ASSUME_TAC PROG_stmt >> 
        FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`ty`,‘h’])) >>
         fs[prog_stmt_def] >> gvs[] >>
      
        FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`ascope`,‘gscope’,‘scopest’, ‘t_scope_list’, ‘t_scope_list_g’, ‘c’, ‘order’,‘delta_g’, ‘delta_b’, ‘delta_t’, ‘delta_x’, ‘f’,‘Prs_n’])) >> gvs[] >> PairCases_on ‘c’ >>
         srw_tac [SatisfySimps.SATISFY_ss][]
                                        
        ]
  ]
QED


   

(* ========================================================================== *)
(*                                                                            *)
(*         Progress of the state definitions, lemmas and thms                 *)
(*                                                                            *)
(* ========================================================================== *)












   
        
(* new definition for WT_state *)
(* new definition for WT_state *)
(* new definition for WT_state *)
(* new definition for WT_state *)
(* new definition for WT_state *)

val (WT_state_rules, WT_state_ind, WT_state_cases) = Hol_reln`
(* defn WT_state *)

( (* WT_state_state *) 
!  (funnl: funn list) (tsll : t_scope_list list) (scll: scope_list list) (stmtll: stmt_stack list)
(ctx:'a ctx) (ascope:'a) (g_scope_list:g_scope_list) (status:status) (Prs_n:Prs_n) (order:order) (t_scope_list_g:t_scope_list_g) (delta_g:delta_g) (delta_b:delta_b) (delta_x:delta_x) (delta_t:delta_t) .

 ( LENGTH funnl = LENGTH tsll /\ LENGTH tsll = LENGTH scll /\ LENGTH tsll = LENGTH stmtll ) /\                                                                                                                                                                          
(WF_ft_order  funnl  delta_g delta_b delta_x order   /\

type_state_tsll  scll tsll  /\

type_scopes_list  g_scope_list   t_scope_list_g  /\

parseError_in_gs  t_scope_list_g   tsll  /\

WT_c ctx order t_scope_list_g delta_g delta_b delta_x delta_t   /\

( ( type_frames  g_scope_list    (ZIP(funnl,ZIP(stmtll,scll)))    Prs_n      order   t_scope_list_g   tsll  delta_g   delta_b   delta_x   delta_t  ) ))

 ==> 
( ( WT_state ctx  ( ascope ,  g_scope_list ,   ((MAP (\(funn,stmt_stack,scope_list). (funn,stmt_stack,scope_list)) (ZIP(funnl,ZIP(stmtll,scll)))   )) ,  status )  Prs_n  order t_scope_list_g  ( tsll)   (  delta_g  ,  delta_b  ,  delta_x  ,  delta_t  )  )))

`;


        
val prog_state_def = Define `
 prog_state (framel) (ty:'a itself) =
∀ (c:'a ctx) ascope  gscope   status  tslg tsll order delta_g delta_b delta_t delta_x Prs_n .
      
  (WT_state c ( ascope ,  gscope  , framel  , status) Prs_n  order tslg tsll (delta_g, delta_b, delta_x, delta_t)) ∧

     ((∀ f local_scope . framel ≠ [(f,[stmt_empty],local_scope)] ∧ framel ≠ [] ) ∧ status = status_running )
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
gvs[parseError_in_gs_def]  >> rw[] >| [
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`i`])) >> gvs[] >>
  ‘i=0’ by gvs[] >> lfs[] 
 ,
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`SUC i`])) >> gvs[]
  ]                    
);


   



     


 (* same proof as  to scopes_to_pass_imp_typed_lemma, TODO: refactor *)    
val typed_imp_scopes_to_pass_lemma = prove (
“∀ gscope tslg funn func_map b_func_map delta_g delta_b tslg_passed .
  dom_b_eq delta_b b_func_map ∧
  dom_g_eq delta_g func_map ∧
  dom_tmap_ei delta_g delta_b ∧
  LENGTH tslg = 2 ∧            
  type_scopes_list gscope tslg ∧
  typing_scopes_to_pass funn delta_g delta_b tslg = SOME tslg_passed ⇒
∃ g_scope_passed . scopes_to_pass funn func_map b_func_map gscope = SOME g_scope_passed ∧
                   type_scopes_list g_scope_passed tslg_passed  ”,
cheat

  );


val t_map_to_pass_delta_t_cases = prove (
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





val e_in_pty_delta_b_def = Define `
   e_in_pty_delta_b (e:e) (ty:'a itself)  =
   (! f tau b order t_scope_list_g t_scope_local delta_g delta_b delta_x delta_t .
dom_tmap_ei delta_g delta_b /\
e_typ (t_scope_list_g,t_scope_local)
          (order,f,delta_g,[],delta_x,delta_t) e tau b
==>
e_typ (t_scope_list_g,t_scope_local)
          (order,f,delta_g,delta_b,delta_x,delta_t) e tau b )
`;



val el_in_pty_delta_b_def = Define `
   el_in_pty_delta_b (el:e list) (ty:'a itself)  =
    ! e . MEM e el ==> e_in_pty_delta_b (e:e) (ty:'a itself)
`;


val stel_in_pty_delta_b_def = Define `
   stel_in_pty_delta_b (stel: (string#e) list ) (ty:'a itself)  =
    ! e . MEM e (SND (UNZIP stel)) ==> e_in_pty_delta_b (e:e) (ty:'a itself)
`;



val stetup_in_pty_delta_b_def = Define `
   stetup_in_pty_delta_b (stetup: (string#e)) (ty:'a itself)  =
      e_in_pty_delta_b (SND stetup) ty
`;




        

val stetup_in_pty_delta_b_tac = TRY( OPEN_EXP_TYP_TAC ``e``) >>
                 SIMP_TAC list_ss [Once e_typ_cases] >>
                 gvs[clause_name_def, Once e_typ_cases] >>
                 RES_TAC >>
		 IMP_RES_TAC t_lookup_funn_not_blk_lemma >>
                 srw_tac [SatisfySimps.SATISFY_ss][] >>
		 METIS_TAC[]


               

val exp_in_pty_delta_b = prove (  ``
 ! (ty:'a itself) . (
(! e  . e_in_pty_delta_b (e) ty) /\
(! el . el_in_pty_delta_b (el) ty) /\
(! stel . stel_in_pty_delta_b (stel) ty) /\
(! stetup . stetup_in_pty_delta_b (stetup) ty))
``,

STRIP_TAC >>
Induct >>
fs[e_in_pty_delta_b_def] >>
REPEAT STRIP_TAC >~ [‘e_typ _ _ (e_call f el ) tau b’] >- 

  (* resolves the : f call*)

   (OPEN_EXP_TYP_TAC ``(e_call f l)`` >>
   SIMP_TAC list_ss [Once e_typ_cases] >>
   gvs[] >>
   RES_TAC >>
   Q.EXISTS_TAC `e_tau_d_b_list` >>
   gvs[] >>

     REPEAT STRIP_TAC >>
     fs[el_in_pty_delta_b_def] >>
    

     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
     [`EL i (MAP (λ(e_,tau_,d_,b_). e_) (e_tau_d_b_list: (e # tau # d # bool) list))`])) >>
   fs[MEM_EL] >> gvs[] >>
               
 RES_TAC >> gvs[] >>
    fs[e_in_pty_delta_b_def] >>
    IMP_RES_TAC t_lookup_funn_not_blk_lemma >> gvs[]


   ) >~  [‘e_typ _ _ (e_struct stel ) tau b’ ] >- 
 (
 (* resolves the : struct, header*)

 fs[e_in_pty_delta_b_def, stel_in_pty_delta_b_def] >>
 OPEN_EXP_TYP_TAC ``(e_struct stel)``>>
                              
 SIMP_TAC list_ss [Once e_typ_cases] >>
 gvs[] >>
 RES_TAC >>
 Q.EXISTS_TAC `f_e_tau_b_list` >>
 gvs[] >>

 REPEAT STRIP_TAC >>
 RES_TAC >>

 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`EL i (MAP (λ(f_,e_,tau_,b_). e_) (f_e_tau_b_list: (string # e # tau # bool) list))`])) >>
 fs[MEM_EL] >>

  subgoal `! l i . EL i (MAP (λx. FST (SND x)) l) =
                   EL i (SND (UNZIP (MAP (λx. (FST x,FST (SND x))) l)))` >-
   (Induct >>
    FULL_SIMP_TAC list_ss [MAP_MAP_o, FST,SND] >>
    REPEAT STRIP_TAC >>
    PairCases_on `h` >>
    Cases_on `i'` >>
    fs[] ) >>

 RES_TAC >>
 SRW_TAC [] [] >>
 gvs[ELIM_UNCURRY, UNZIP_rw]
 ) >~  [‘e_typ (t_scope_list_g,t_scope_local)
          (order,f,delta_g,delta_b,delta_x,delta_t) (e_header b stel) tau b'’ ] >- 
 (
 (* resolves the : struct, header*)

 fs[e_in_pty_delta_b_def, stel_in_pty_delta_b_def] >>
 OPEN_EXP_TYP_TAC ``(e_header b stel)`` >>
                
 SIMP_TAC list_ss [Once e_typ_cases] >>
 gvs[] >>
 RES_TAC >>
 Q.EXISTS_TAC `f_e_tau_b_list` >>
 gvs[] >>

 REPEAT STRIP_TAC >>
 RES_TAC >>

 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`EL i (MAP (λ(f_,e_,tau_,b_). e_) (f_e_tau_b_list: (string # e # tau # bool) list))`])) >>
 fs[MEM_EL] >>

  subgoal `! l i . EL i (MAP (λx. FST (SND x)) l) =
                   EL i (SND (UNZIP (MAP (λx. (FST x,FST (SND x))) l)))` >-
   (Induct >>
    FULL_SIMP_TAC list_ss [MAP_MAP_o, FST,SND] >>
    REPEAT STRIP_TAC >>
    PairCases_on `h` >>
    Cases_on `i'` >>
    fs[] ) >>

 RES_TAC >>
 SRW_TAC [] [] >>
 gvs[ELIM_UNCURRY, UNZIP_rw]
 ) >>  cheat (* done with the proof, just refactor  the bottom part*)


(*

                                  [

 (* resolves the : v, var, e_list, acc e s, unop, binop, concat, slice, select*)
 fs[stel_in_pty_delta_b_def, el_in_pty_delta_b_def, e_in_pty_delta_b_def, stetup_in_pty_delta_b_def] >>
 REPEAT STRIP_TAC >>
 gvs[] 
 (* resolves the : inductive cases on the properties *)
 ,


stetup_in_pty_delta_b_tac
]

                               )
*)

);




val lval_typ_in_pty_delta_b_lemma = prove (“
! lval tau f order t_scope_list_g t_scope_list_g s delta_g delta_b
 delta_x delta_t Prs_n order t_scope_local ty.
      dom_tmap_ei delta_g delta_b ∧       
lval_typ (t_scope_list_g,t_scope_local)
         (order,f,delta_g,[],delta_x,delta_t) lval (t_tau tau) ⇒
(lval_typ (t_scope_list_g,t_scope_local)
            (order,f,delta_g,delta_b,delta_x,delta_t) lval
            (t_tau tau))   ”,
             
Induct_on ‘lval’>>
REPEAT STRIP_TAC >>

       
gvs[Once lval_typ_cases] >>
TRY(gvs[Once e_typ_cases]) >>
SIMP_TAC list_ss [Once lval_typ_cases] >>
TRY(SIMP_TAC list_ss [Once e_typ_cases]) >>
gvs[] >| [

        IMP_RES_TAC t_lookup_funn_not_blk_lemma >> gvs[] >>
                                            
    Cases_on ‘t_lookup_funn funn' delta_g delta_b delta_x’ >> gvs[]

     ,
      
    gvs[] >>         
    RES_TAC >>        
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`delta_x`,‘delta_t’])) >>
    srw_tac [SatisfySimps.SATISFY_ss][]  
    ,

    gvs[] >>         
    RES_TAC >>        
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`delta_x`,‘delta_t’])) >>
    srw_tac [SatisfySimps.SATISFY_ss][]  
    ]
);



fun OPEN_ANY_STMT_TYP_TAC stmt_term =
(Q.PAT_X_ASSUM `stmt_typ (t_scope_list_g,t_scope_local)
          (order,f,delta_g,[],delta_x,delta_t) Prs_n stmt_term` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once stmt_typ_cases] thm)))







val ext_not_def_in_mpty_delta_b = prove ( 
  “ ∀ f delta_g delta_b delta_x tdl t.
   typying_domains_ei delta_g delta_b delta_x ∧
t_lookup_funn f delta_g [] delta_x = SOME (tdl,t) ∧
ext_is_defined delta_x f ∧
ext_not_defined delta_g [] f ⇒
ext_not_defined delta_g delta_b f”,

REPEAT STRIP_TAC >>
Cases_on ‘f’ >> gvs[] >>
gvs[typying_domains_ei_def, t_lookup_funn_def, ext_is_defined_def,  ext_not_defined_def]>>
gvs[dom_empty_intersection_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 
REPEAT (FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘s’])) >> gvs[])
);







                                                     


val delta_b_maps_empty_lemma = prove ( 
“∀ f delta_b b_func_map.
dom_b_eq delta_b b_func_map ∧  
t_map_to_pass f delta_b = SOME [] ⇒
 map_to_pass f b_func_map = SOME []  ” ,                    

gvs[t_map_to_pass_def, map_to_pass_def ] >>

REPEAT STRIP_TAC >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[dom_b_eq_def, dom_eq_def, is_lookup_defined_def]) >> 
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘s’])) >> gvs[]
);







        
 val  delta_b_maps_lemma  = prove (     
“∀ f delta_b b_func_map.
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


                                                
              

val type_scopes_list_single_detr = prove (
“∀ h h' h''.
type_scopes_list [h''] [h] ∧
type_scopes_list [h''] [h'] ⇒
h = h'”,

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

);




        
val type_scopes_list_detr = prove (

(* move to stmt sr after v_typ_deter *)
“∀ sl tscl tscl' .
type_scopes_list sl tscl ∧
type_scopes_list sl tscl' ==>
tscl = tscl'”,
     
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
);




(*
   


val WT_c_imp_empty_delta_b = prove (
“
∀  apply_table_f ext_map func_map b_func_map pars_map tbl_map f  delta_g delta_b delta_x delta_t  order t_scope_list_g'
                 tau_d_list tau gscope g_scope_passed .
                 
scopes_to_pass f func_map b_func_map gscope = SOME g_scope_passed ∧
typing_scopes_to_pass f delta_g delta_b t_scope_list_g' = SOME t_scope_list_g' ∧            
SOME (tau_d_list,tau) = t_lookup_funn f delta_g [] delta_x ∧
(LENGTH delta_t = LENGTH tbl_map) ∧ MEM f  ∧

WT_c (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map) order t_scope_list_g' delta_g delta_b delta_x delta_t  ⇒
WT_c (apply_table_f,ext_map,func_map, []       ,pars_map,tbl_map) order t_scope_list_g' delta_g []      delta_x delta_t ”,

REPEAT STRIP_TAC >>
gvs[WT_c_cases]>>

(* to resolve the following 
‘dom_map_ei func_map [] ∧ dom_tmap_ei delta_g [] ∧
        typying_domains_ei delta_g [] delta_x ∧ dom_b_eq [] [] ∧
        WTFb [] order t_scope_list_g' delta_g [] delta_x  *)     
gvs[dom_map_ei_def, dom_tmap_ei_def, typying_domains_ei_def]>>
gvs[dom_empty_intersection_def] >> gvs[] >>
gvs[dom_b_eq_def, dom_eq_def, is_lookup_defined_def] >>
SIMP_TAC list_ss [WTFb_cases, func_map_blk_typed_def, clause_name_def] >> gvs[] >>
gvs[] >>

rw[] >| [

Cases_on ‘f’ >> 

         
     ( gvs[Fb_star_defined_def, is_lookup_defined_def] >>
     gvs[typing_scopes_to_pass_def]  >>
     REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 
     gvs[t_lookup_funn_def] >-

     ( ‘HD t_scope_list_g' = []’ by (Cases_on ‘t_scope_list_g'’ >> gvs[]) >>
     gvs[] ) >>
        REPEAT ( LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`s`])) >> gvs[]))

      ,
Cases_on ‘f’ >>
        
    gvs[table_map_typed_def] >> REPEAT STRIP_TAC >>
    LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`s'`])) >> gvs[] >>
    REPEAT (FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`f`, ‘el’, ‘vl’,‘ascope’]))) >> gvs[] >>
    Q.EXISTS_TAC ‘tdl’ >> gvs[] >> cheat (* TODO: PROBLEM HERE with tables, either fix the def of tbl_map_typed or something else *)

                                         
      ,

Cases_on ‘f’ >>
        
     (gvs[f_ordered_with_any_reserved_def] >>
     REPEAT STRIP_TAC >>
     ‘∀delta_b.
          dom_tmap_ei delta_g delta_b ⇒
          SOME (tdl,tau') = t_lookup_funn f delta_g delta_b delta_x’ by IMP_RES_TAC t_lookup_funn_not_blk_lemma >>
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘delta_b’])) >> gvs[dom_tmap_ei_def, dom_empty_intersection_def] >>
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘f’, ‘tau'’,‘tdl’])) >> gvs[])
      ,
Cases_on ‘f’ >>
      
     ( gvs[f_not_reserved_then_ordered_def] >> 
      REPEAT STRIP_TAC >>

     ‘∀delta_b.
          dom_tmap_ei delta_g delta_b ⇒
          SOME (tdl,tau') = t_lookup_funn f delta_g delta_b delta_x’ by IMP_RES_TAC t_lookup_funn_not_blk_lemma >>
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘delta_b’])) >> gvs[dom_tmap_ei_def, dom_empty_intersection_def] >>
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘f’, ‘tau'’,‘tdl’])) >> gvs[]  )  

    ]


);

        

              
              

(* because this is the base frame, we know that there exsist typing global scope,
that is an extension of the current one (because it is scopes to pass lol ) *)
        
val WT_state_imp_frame_typ_single = prove ( 
  “ ∀  ascope gscope f stmtl locale status Prs_n  order tslg tsll delta_g delta_b delta_x delta_t
       apply_table_f  ext_map  func_map  b_func_map  pars_map tbl_map passed_tbl_map.
    
    WT_state  ( apply_table_f , ext_map , func_map , b_func_map , pars_map , tbl_map )
             (ascope,gscope,[(f,stmtl,locale)],status) Prs_n  order tslg
          tsll (delta_g,delta_b,delta_x,delta_t) ⇒

 




          
       type_scopes_list  (gscope)  (tslg) ∧
       type_scopes_list  (locale) (HD tsll)   ∧
       star_not_in_sl (locale) ∧
       parseError_in_gs tslg [HD tsll] ∧
  
             (delta_t ≠ [] ⇒ MEM f ) ∧
             ∃ tslg' gscope' passed_delta_b passed_b_func_map.
                                              typing_scopes_to_pass f delta_g delta_b tslg = SOME tslg' ∧                                    
                                               scopes_to_pass f func_map b_func_map gscope = SOME gscope' ∧
                                                  map_to_pass f b_func_map = SOME passed_b_func_map ∧
                                                t_map_to_pass f delta_b = SOME passed_delta_b   ∧
                                                             
WT_c ( apply_table_f , ext_map , func_map , passed_b_func_map , pars_map , tbl_map ) order tslg' delta_g passed_delta_b delta_x delta_t   ∧
type_scopes_list  (gscope') (tslg')   ∧                         
(frame_typ  ( tslg' ,  (HD tsll) ) (order, f, (delta_g, passed_delta_b, delta_x, delta_t)) Prs_n  gscope' locale stmtl ) ”,


 REPEAT GEN_TAC >>
  STRIP_TAC >>     
 gvs[Once WT_state_cases] >>
 PairCases_on ‘x0’ >> gvs[] >>
 gvs[type_state_tsll_def] >>
                          
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`0`])) >> gvs[] >>
 gvs[type_frame_tsl_def] >>
 subgoal ‘0 < LENGTH scll’ >- (Cases_on ‘scll’ >> gvs[]  ) >> gvs[] >>
         
 subgoal ‘locale = HD scll ’ >-  (
   ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:funn`` , ``:'b`` |-> ``:stmt list`` , ``:γ`` |-> ``:(varn#v#lval option)list list`` ] ZIP_HD_tri_1)  >> 
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`funnl`, ‘stmtll’, ‘scll’]))  >>  gvs[] ) >>
   
 gvs[type_frames_def, type_frame_tsl_def] >>
 Cases_on ‘tsll’ >> gvs[] >>
 IMP_RES_TAC parseError_in_gs_normalization   >> gvs[]  >>
             
   ‘ ∃ g_scope_passed' .  scopes_to_pass f func_map b_func_map gscope = SOME g_scope_passed'
                          ∧  type_scopes_list g_scope_passed' t_scope_list_g'’ by (gvs[Once WT_c_cases] >> IMP_RES_TAC typed_imp_scopes_to_pass_lemma >> gvs[]) >>

   srw_tac [SatisfySimps.SATISFY_ss][] >>

   gvs[frame_typ_cases] >>
 srw_tac [SatisfySimps.SATISFY_ss][] >>

  IMP_RES_TAC type_scopes_list_detr >> rfs[] >> gvs[] >>
         
 IMP_RES_TAC t_map_to_pass_delta_t_cases >> gvs[] >>
 srw_tac [SatisfySimps.SATISFY_ss][] >| [

  Q.EXISTS_TAC ‘[]’ >>
 ‘dom_b_eq delta_b b_func_map’ by gvs[Once WT_c_cases] >>
  IMP_RES_TAC delta_t_maps_empty_lemma >> gvs[] >>

 ‘LENGTH delta_b = LENGTH b_func_map’ by gvs[WT_c_cases]

              
  IMP_RES_TAC table_deltat_maps_lemma cheat


  Cases_on ‘MEM f ’ >> gvs[]










                                      
               
  ]

                                                        
  ,

  Q.EXISTS_TAC ‘b_func_map’ >> gvs[] >>
     gvs[WT_c_cases] >>
  IMP_RES_TAC delta_t_maps_lemma 
]

);












WT_state c (ascope,gscope,h::t,status_running) Prs_n  order tslg
          tsll (delta_g,delta_b,delta_x,delta_t) ⇒

WT_state c (ascope,gscope,[h],status_running) Prs_n  order tslg
          [HD tsll] (delta_g,delta_b,delta_x,delta_t)


REPEAT STRIP_TAC >>
gvs[WT_state_cases] >>
srw_tac [boolSimps.DNF_ss][] >>

PairCases_on ‘h’ >> gvs[] >>
Q.EXISTS_TAC ‘[h0]’ >>
Q.EXISTS_TAC ‘[h2]’ >>
Q.EXISTS_TAC ‘[h1]’ >>
Q.EXISTS_TAC ‘(h0,h1,h2)’ >>
gvs[] >>

gvs[type_frames_def] >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘0’])) >>
Cases_on ‘0 = LENGTH scll − 1’ >> gvs[] >| [

         
 subgoal ‘LENGTH scll = 1 ∨ LENGTH scll = 0 ’ >-  (fs[quantHeuristicsTheory.LIST_LENGTH_1] >> Cases_on ‘scll’ >> gvs[] >>
                     Cases_on ‘t'’ >> gvs[]) >> gvs[] >>                                                             
 

 fs[quantHeuristicsTheory.LIST_LENGTH_1] >> gvs[]
 ,
 ‘LENGTH scll > 1’ by gvs[] >>

 Cases_on ‘(ZIP (funnl,ZIP (stmtll,scll)))’ >> gvs[] >>
 PairCases_on ‘h’ >> gvs[] >> rw[] >| [
   gvs[ordered_list_def]
   ,
   gvs[type_state_tsll_def] >>
   REPEAT STRIP_TAC >>
   ‘i=0’ by gvs[] >> lfs[] >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘i’]))  >>  gvs[]  >>
   gvs[] >>
   ‘ (HD scll) = h2 ’ by cheat >>
   gvs[] 

   ,
   gvs[parseError_in_gs_def] >>    
    REPEAT STRIP_TAC >>
   ‘i=0’ by gvs[] >> lfs[] >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘i’]))  >>  gvs[]
   ,
   gvs[WT_c_cases] >> gvs[] >> cheat
   ,
        
         
   ]



gvs[frame_typ_cases]
  gvs[base_frame_is_in__def]
  Q.EXISTS_TAC ‘tau_d_list’ >>
  Q.EXISTS_TAC ‘tau’ >>
  gvs[]


        
  ]
          






WT_state c
          (ascope,gscope,[(funn,stmt_stack,scope_list)],status_running) Prs_n
           order tslg tsll (delta_g,delta_b,delta_x,delta_t) ∧
stmt_stack ≠ [stmt_empty] ⇒
        ∃status' ascope' gscope' framel'.
          frames_red c
            (ascope,gscope,[(funn,stmt_stack,scope_list)],status_running)
            (ascope',gscope',framel',status')

REPEAT STRIP_TAC >>
PairCases_on ‘c’ >>
IMP_RES_TAC WT_state_imp_frame_typ_single >>

gvs[Once frames_red_cases]                    


gvs[map_to_pass_def]
Cases_on ‘funn’ >> gvs[]

Cases_on ‘ALOOKUP c3 s ’ >> gvs[] >>


ASSUME_TAC PROG_stmtl >>
            
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`ty`,‘stmtl’])) >>
gvs[prog_stmtl_def] >>

FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘ascope’, ‘gscope'’, ‘scopest’, ‘tsl’ , ‘tslg'’, ‘ (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)’, ‘order’,‘delta_g’,  ‘delta_b’, ‘delta_t’, ‘delta_x’, ‘f’, ‘Prs_n’ ])) >>

gvs[]








                        











                        


                
        

Theorem PROG_framel:
  ∀ ty framel. prog_state framel ty
Proof
  


STRIP_TAC >>
gvs[prog_state_def] >> REPEAT STRIP_TAC >>

(* we know that the framel is not empty *)
Cases_on ‘framel’ >> gvs[] >>


IMP_RES_TAC WT_state_imp_frame_typ_single






                                
QED


*)



                
val _ = export_theory ();







