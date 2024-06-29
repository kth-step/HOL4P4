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
open p4_stmt_progressTheory;
     
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





fun OPEN_LVAL_TYP_TAC lval_term =
(Q.PAT_X_ASSUM `lval_typ (g1,q1) t (^lval_term) (tp)` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once lval_typ_cases] thm)))



val _ = new_theory "p4_frames_subject_reduction";


val t_scopes_consistent_list_def = Define ‘
 t_scopes_consistent_list funnl tsll t_scope_list_g (delta_g, delta_b, delta_x, delta_t) order =     
 (∀ i . i+1 < LENGTH funnl ⇒
        ∃ passed_delta_b passed_delta_t passed_tslg.
         t_passed_elem  (EL (i+1)  funnl) delta_g delta_b delta_t t_scope_list_g = (SOME passed_delta_b,  SOME passed_delta_t , SOME passed_tslg) ∧         
          t_scopes_consistent (order,  (EL (i+1) funnl), (delta_g, passed_delta_b, delta_x, passed_delta_t))  (EL (i+1) tsll) passed_tslg (EL i tsll) )
’;  

         







        
val (WT_state_rules, WT_state_ind, WT_state_cases) = Hol_reln`
(* defn WT_state *)

( (* WT_state_state *) 
!  (funnl: funn list) (tsll : t_scope_list list) (scll: scope_list list) (stmtll: stmt_stack list)
(ctx:'a ctx) (ascope:'a) (g_scope_list:g_scope_list) (status:status) (Prs_n:Prs_n) (order:order) (t_scope_list_g:t_scope_list_g) (delta_g:delta_g) (delta_b:delta_b) (delta_x:delta_x) (delta_t:delta_t) apply_table_f ext_map func_map b_func_map pars_map tbl_map .

 ( LENGTH funnl = LENGTH tsll /\ LENGTH tsll = LENGTH scll /\ LENGTH tsll = LENGTH stmtll ) /\                                                                                                                                                                          
 (WF_ft_order  funnl  delta_g delta_b delta_x order   /\

               
 t_scopes_consistent_list funnl tsll t_scope_list_g (delta_g, delta_b, delta_x, delta_t) order   /\

               
type_state_tsll  scll tsll  /\ 

type_scopes_list  g_scope_list   t_scope_list_g  /\

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




     
Theorem scopes_to_pass_imp_typed_lemma:
∀ gscope tslg funn func_map b_func_map delta_g delta_b g_scope_passed.
  dom_b_eq delta_b b_func_map ∧
  dom_g_eq delta_g func_map ∧
  dom_tmap_ei delta_g delta_b ∧
  LENGTH tslg = 2 ∧            
  type_scopes_list gscope tslg ⇒                                                                                                   
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


        
Theorem typed_imp_scopes_to_pass_lemma:
∀ gscope tslg funn func_map b_func_map delta_g delta_b tslg_passed .
  dom_b_eq delta_b b_func_map ∧
  dom_g_eq delta_g func_map ∧
  dom_tmap_ei delta_g delta_b ∧
  LENGTH tslg = 2 ∧            
  type_scopes_list gscope tslg ∧
  t_scopes_to_pass funn delta_g delta_b tslg = SOME tslg_passed ⇒
∃ g_scope_passed . scopes_to_pass funn func_map b_func_map gscope = SOME g_scope_passed ∧
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


       

Theorem find_star_of_globals_ctx_lemma:
∀ delta_g delta_b func_map b_func_map e1 e2 q r x.
dom_map_ei func_map b_func_map ∧            
dom_tmap_ei delta_g delta_b ∧
dom_g_eq delta_g func_map ∧
dom_b_eq delta_b b_func_map ∧
Fb_star_defined b_func_map [e1; e2] ∧
Fg_star_defined func_map [e1; e2] ∧
ALOOKUP delta_g x = SOME (q,r) ∧
find_star_in_globals [e1; e2] (varn_star (funn_name x)) = SOME r ⇒
find_star_in_globals [[]; e2] (varn_star (funn_name x)) = SOME r
Proof
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
QED



        
Theorem find_star_of_inst_ctx_lemma:
∀ ext_map r x e1 e2 sig.
  X_star_not_defined [e1; e2] ∧                                        
  ALOOKUP ext_map x = SOME sig ∧ 
  X_star_defined ext_map [e1; e2] ∧              
  find_star_in_globals [e1; e2] (varn_star (funn_inst x)) = SOME r ⇒
  find_star_in_globals [[]; e2] (varn_star (funn_inst x)) = SOME r
Proof                                                                
REPEAT STRIP_TAC >>
gvs[find_star_in_globals_def, X_star_not_defined_def, X_star_defined_def, is_lookup_defined_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>

REPEAT (LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘funn_inst x’, ‘x’])) >> gvs[]) >>
IMP_RES_TAC lookup_map_none_lemma1 >> gvs[] >>

gvs[lookup_map_def, topmost_map_def, find_topmost_map_def, INDEX_FIND_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[])            
QED



   


Theorem find_star_of_ext_ctx_lemma:
∀ ext_map r x x' e1 e2 sig.
  X_star_not_defined [e1; e2] ∧                                        
  ALOOKUP ext_map x  = SOME sig ∧ 
  X_star_defined ext_map [e1; e2] ∧              
  find_star_in_globals [e1; e2] (varn_star (funn_ext x x')) = SOME r ⇒
  find_star_in_globals [[]; e2] (varn_star (funn_ext x x')) = SOME r 
Proof                                                                
REPEAT STRIP_TAC >>
gvs[find_star_in_globals_def, X_star_not_defined_def, X_star_defined_def, is_lookup_defined_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>

REPEAT (LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘funn_ext x x'’, ‘x’])) >> gvs[]) >>
IMP_RES_TAC lookup_map_none_lemma1 >> gvs[] >>

gvs[lookup_map_def, topmost_map_def, find_topmost_map_def, INDEX_FIND_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[])   
QED      



        
                                        
Theorem WTFg_empty_empty_db:
∀ func_map b_func_map order g1 g2 delta_g delta_b delta_x Prs_n.
  dom_tmap_ei delta_g delta_b ∧ dom_map_ei func_map b_func_map ∧
  dom_g_eq delta_g func_map ∧  dom_b_eq delta_b b_func_map ∧
  Fb_star_defined b_func_map [g1; g2] ∧
  Fg_star_defined func_map [g1; g2] ∧                
WTFg func_map order [g1; g2] delta_g delta_b delta_x Prs_n⇒
WTFg func_map order [[]; g2] delta_g [] delta_x Prs_n
Proof
gvs[WTFg_cases, func_map_typed_def] >>
REPEAT STRIP_TAC >>

FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘stmt’, ‘xdl’, ‘x’, ‘lol’])) >> gvs[] >>
Q.EXISTS_TAC ‘tau’ >> gvs[] >>
Q.EXISTS_TAC ‘txdl’ >> gvs[] >>
Q.EXISTS_TAC ‘t_scope_list_g'’ >>
gvs[] >>
gvs[t_lookup_funn_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
IMP_RES_TAC t_scopes_lookup_empty_ctx_lemma >> gvs[] >>
IMP_RES_TAC find_star_of_globals_ctx_lemma >> gvs[]
QED




        
Theorem WTFX_empty_empty_db:
∀ func_map (ext_map: 'a ext_map ) order g1 g2 delta_g delta_b delta_x .
  X_star_not_defined [g1; g2] ∧
  X_star_defined ext_map [g1; g2] ∧
WTX ext_map order [g1; g2] delta_g delta_b delta_x ⇒
WTX ext_map order [[]; g2] delta_g [] delta_x
Proof                                  
REPEAT STRIP_TAC >>
gvs[WTX_cases] >>
CONJ_TAC >| [
                                      
 gvs[extern_map_IoE_typed_def] >>
 REPEAT STRIP_TAC >>
        
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘xdl’, ‘x’, ‘IoE’, ‘MoE’])) >> gvs[] >>
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘a’, ‘g_scope_list’, ‘local_scopes’])) >> gvs[] >>

 qexistsl_tac [‘txdl’, ‘tau’ ,‘a'’, ‘scope_list'’,‘status’, ‘t_scope_list_g'’] >> gvs[] >>
              
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
 qexistsl_tac [‘txdl’,‘tau’,‘a'’, ‘scope_list'’,‘status’, ‘t_scope_list_g'’] >> gvs[] >>
              
 gvs[t_scopes_to_pass_def] >>
 REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[])  >>

 gvs[t_lookup_funn_def] >>
 REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 
 IMP_RES_TAC find_star_of_ext_ctx_lemma        
]
QED


        
            
Theorem WT_c_empty_db:
∀ f delta_b delta_g delta_x delta_t passed_delta_b passed_delta_t
       apply_table_f (ext_map: 'a ext_map) func_map b_func_map tbl_map pars_map order tau
       txdl gscope g_scope_passed tslg passed_tslg  Prs_n.          

t_lookup_funn f delta_g passed_delta_b delta_x = SOME (txdl, tau)∧
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
            passed_delta_t Prs_n
Proof
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
   fs[] >> gvs[] >>
   gvs[X_star_defined_def, is_lookup_defined_def] >> REPEAT STRIP_TAC >> gvs[]
   ) >> gvs[]
 ) >>
   
 fs[] >> gvs[] >>

 (subgoal ‘X_star_not_defined [[]; EL 1 tslg]’ >- (
   gvs[X_star_not_defined_def] >> REPEAT STRIP_TAC >> gvs[] >>
   gvs[is_lookup_defined_def]
   )                                          
 ) >> gvs[] >> rw[] >>


 Cases_on ‘tslg’ >> gvs[] >>
 Cases_on ‘t’ >> gvs[] >>
 
 IMP_RES_TAC WTFg_empty_empty_db >>
 IMP_RES_TAC WTFX_empty_empty_db >>
 fs[]
            
QED







        
Theorem WT_state_HD_of_list:
∀  ascope gscope f stmtl locale status Prs_n order tslg tsll delta_g delta_b
       delta_x delta_t apply_table_f ext_map func_map b_func_map pars_map
       tbl_map t.
    
    WT_state  ( apply_table_f , ext_map , func_map , b_func_map , pars_map , tbl_map )
              (ascope,gscope,(f,stmtl,locale)::t,status) Prs_n  order tslg
              tsll (delta_g,delta_b,delta_x,delta_t) ⇒

             ∃ passed_tslg passed_gscope passed_delta_b passed_b_func_map passed_tbl_map passed_delta_t.
                                              t_scopes_to_pass f delta_g delta_b tslg = SOME passed_tslg ∧                                    
                                               scopes_to_pass f func_map b_func_map gscope = SOME passed_gscope ∧
                                                  map_to_pass f b_func_map = SOME passed_b_func_map ∧
                                                  t_map_to_pass f delta_b = SOME passed_delta_b   ∧
                                                  tbl_to_pass f b_func_map tbl_map = SOME passed_tbl_map ∧
                                                  t_tbl_to_pass f delta_b delta_t = SOME passed_delta_t ∧            
                                                             
WT_c ( apply_table_f , ext_map , func_map , passed_b_func_map , pars_map , passed_tbl_map ) order passed_tslg delta_g passed_delta_b delta_x passed_delta_t Prs_n   ∧
type_scopes_list  passed_gscope passed_tslg   ∧
(frame_typ  ( passed_tslg ,  (HD tsll) ) (order, f, (delta_g, passed_delta_b, delta_x, passed_delta_t)) Prs_n  passed_gscope locale stmtl )
Proof

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
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘tau_x_d_list’, ‘tau’])) >> gvs[] >>  

Cases_on ‘tsll’ >> gvs[] 
QED








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
subgoal ‘(MAP (λ(f,stmt,sc). sc) t) = TL scll’ >-
 (ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:funn``, ``:'b`` |-> ``:stmt list``, ``:'c`` |-> ``:scope_list``] ZIP_tri_sep_ind)  >>
      FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘t’,‘funnl’,‘stmtll’,‘scll’, ‘funn’,‘stmt_stack’,‘scope_list’])) >> gvs[] >>
      gvs[ELIM_UNCURRY]
 ) >>
IMP_RES_TAC type_state_tsll_normalization >>
gvs[] >>
Cases_on ‘scll’ >>
Cases_on ‘tsll’ >>
gvs[]
);




         

val res_fr_typ_imp_typ_tsl = prove (“
∀ T_e Prs_n tslg tsl gscope locale f stmtl func_map b_func_map tsl_fr.
res_frame_typ T_e  Prs_n tslg tsl gscope [(f,stmtl,locale)] func_map b_func_map tsl_fr ⇒
type_frame_tsl locale tsl ”,

REPEAT STRIP_TAC >>
PairCases_on ‘T_e’ >>
gvs[res_frame_typ_def] >>
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



val EL_PRE = prove (“     
∀i l t h. i > 0 ⇒
   EL i (h::t) = EL (i-1) (t)”,

Induct >>
gvs[Once EL_compute]
);




Theorem LIST_LENGTH_2_simp:
 ∀ l .  LENGTH l = 2 ⇔ ∃ a b . l = [a;b]
Proof        
 Induct >> gvs[] >>
 Cases_on ‘l’ >> gvs[]
QED

             
        
Theorem scopes_to_ret_is_wt:  
∀ funn delta_g delta_b func_map b_func_map tslg passed_gscope  gscope passed_tslg ret_gscope .
  dom_b_eq delta_b b_func_map ∧
  dom_g_eq delta_g func_map ∧
  dom_tmap_ei delta_g delta_b ∧
  LENGTH tslg = 2 ∧            
   t_scopes_to_pass funn delta_g delta_b tslg = SOME passed_tslg ∧
   type_scopes_list passed_gscope passed_tslg ∧
   type_scopes_list gscope tslg ∧
   SOME ret_gscope = scopes_to_retrieve funn func_map b_func_map gscope passed_gscope ==>
   type_scopes_list ret_gscope tslg
Proof   

gvs[t_scopes_to_pass_def, scopes_to_retrieve_def] >>
REPEAT STRIP_TAC >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>

IMP_RES_TAC dom_eq_imp_NONE >> gvs[] >>
IMP_RES_TAC type_scopes_list_LENGTH >>
gvs[LIST_LENGTH_2_simp] >>

simp_tac list_ss [Once type_scopes_list_normalize] >>
IMP_RES_TAC type_scopes_list_normalize >> gvs[]           
QED



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



fun OPEN_ANY_STMT_RED_TAC a =
(Q.PAT_X_ASSUM `stmt_red ct (ab, gsl,[(f,[stm_term],gam)],st) stat`
 (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once stmt_red_cases] thm)))

 
Theorem return_imp_same_g_base_case:
∀ stmt stmtl' c ascope ascope' gscope gscope' f  v framel locale locale'.
stmt_red c (ascope,gscope,[(f,[stmt],locale)],status_running)
           (ascope',gscope',[(f,stmtl',locale')],status_returnv v) ⇒
gscope = gscope'  
Proof
Induct >>
REPEAT GEN_TAC >>
STRIP_TAC >>
OPEN_ANY_STMT_RED_TAC “anystmt” >>
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
OPEN_ANY_STMT_RED_TAC “anystmt” >>
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
OPEN_ANY_STMT_RED_TAC “anystmt” >>
IMP_RES_TAC create_frame_in_stmt_same_g >> gvs[] >> METIS_TAC[]
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

         

         
val t_map_to_pass_twice = prove (“
∀ f f_called delta_b passed_delta_b passed_delta_b' delta_g delta_x txdl txdl' tau tau'.
SOME (txdl',tau') = t_lookup_funn f delta_g passed_delta_b delta_x ∧
SOME (txdl,tau) = t_lookup_funn f_called delta_g passed_delta_b' delta_x ∧                
typying_domains_ei delta_g delta_b delta_x ∧         
typying_domains_ei delta_g passed_delta_b delta_x ∧
t_map_to_pass f               delta_b = SOME passed_delta_b ∧
t_map_to_pass f_called passed_delta_b = SOME passed_delta_b' ⇒
t_map_to_pass f_called        delta_b = SOME passed_delta_b' ”,

REPEAT GEN_TAC >> STRIP_TAC >>

gvs[t_map_to_pass_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 
  
gvs[t_lookup_funn_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 

gvs[typying_domains_ei_def, dom_empty_intersection_def] >>
REPEAT (FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘s’])) >> fs[])
);

        

val t_tbl_to_pass_twice = prove (“
∀ f f_called delta_b passed_delta_b passed_delta_b' delta_t passed_delta_t passed_delta_t' delta_g delta_x txdl txdl' tau tau'.                                 
SOME (txdl',tau') = t_lookup_funn f       delta_g passed_delta_b  delta_x ∧
SOME (txdl ,tau) = t_lookup_funn f_called delta_g passed_delta_b' delta_x ∧
typying_domains_ei delta_g delta_b delta_x ∧         
typying_domains_ei delta_g passed_delta_b delta_x ∧
t_map_to_pass f               delta_b = SOME passed_delta_b ∧
t_map_to_pass f_called passed_delta_b = SOME passed_delta_b' ∧
t_tbl_to_pass f                delta_b       delta_t = SOME passed_delta_t ∧
t_tbl_to_pass f_called passed_delta_b passed_delta_t = SOME passed_delta_t' ⇒
t_tbl_to_pass f_called        delta_b        delta_t = SOME passed_delta_t'   ”,

REPEAT GEN_TAC >> STRIP_TAC >>
         
gvs[t_map_to_pass_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 

       
gvs[t_lookup_funn_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 
       
gvs[t_tbl_to_pass_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 

gvs[typying_domains_ei_def, dom_empty_intersection_def] >>
REPEAT (FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘s’])) >> fs[]) >>
gvs[]
);

        
val t_scopes_to_pass_twice = prove (“
∀ f f_called delta_b passed_delta_b passed_delta_b' delta_g delta_x txdl txdl' tau tau' tslg passed_tslg passed_tslg'.                                    
SOME (txdl',tau') = t_lookup_funn f        delta_g passed_delta_b  delta_x ∧
SOME (txdl,tau)  =  t_lookup_funn f_called delta_g passed_delta_b' delta_x ∧
typying_domains_ei delta_g        delta_b delta_x ∧         
typying_domains_ei delta_g passed_delta_b delta_x ∧
t_map_to_pass f               delta_b = SOME passed_delta_b ∧
t_map_to_pass f_called passed_delta_b = SOME passed_delta_b' ∧             
t_scopes_to_pass f        delta_g        delta_b        tslg = SOME passed_tslg ∧
t_scopes_to_pass f_called delta_g passed_delta_b passed_tslg = SOME passed_tslg' 
⇒       
t_scopes_to_pass f_called delta_g        delta_b        tslg = SOME passed_tslg' ”,

REPEAT GEN_TAC >> STRIP_TAC >>
gvs[LIST_LENGTH_2_simp] >>
   
gvs[t_map_to_pass_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 
      
gvs[t_lookup_funn_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 
       
gvs[t_scopes_to_pass_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 

gvs[typying_domains_ei_def, dom_empty_intersection_def] >>
REPEAT (FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘s’])) >> fs[]) >>
gvs[]
);


        
val scopes_to_pass_twice = prove (“
∀ f f_called delta_b passed_delta_b passed_delta_b' delta_g delta_x txdl txdl' tau tau' func_map b_func_map b_func_map'
gscope gscope' passed_gscope g_scope_list' .                              
SOME (txdl', tau')  = t_lookup_funn f        delta_g passed_delta_b  delta_x ∧
SOME (txdl , tau )  = t_lookup_funn f_called delta_g passed_delta_b' delta_x ∧
SOME gscope'  = scopes_to_retrieve f func_map b_func_map gscope g_scope_list' ∧
typying_domains_ei delta_g        delta_b delta_x ∧         
typying_domains_ei delta_g passed_delta_b delta_x ∧
dom_b_eq        delta_b b_func_map  ∧
dom_b_eq passed_delta_b b_func_map' ∧
dom_g_eq delta_g          func_map  ∧
dom_map_ei func_map b_func_map' ∧
dom_map_ei func_map b_func_map  ∧                     
map_to_pass   f b_func_map = SOME b_func_map' ∧      
t_map_to_pass f               delta_b = SOME passed_delta_b ∧
t_map_to_pass f_called passed_delta_b = SOME passed_delta_b' ∧
scopes_to_pass f        func_map b_func_map           gscope = SOME g_scope_list' ∧
scopes_to_pass f_called func_map b_func_map'   g_scope_list' = SOME passed_gscope  ⇒       
scopes_to_pass f_called func_map b_func_map          gscope' = SOME passed_gscope”,
                                 
REPEAT GEN_TAC >> STRIP_TAC >>
IMP_RES_TAC type_scopes_list_LENGTH >>
gvs[LIST_LENGTH_2_simp] >>
   
gvs[map_to_pass_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 

gvs[t_map_to_pass_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 
       
gvs[t_lookup_funn_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 


gvs[typying_domains_ei_def, dom_empty_intersection_def] >>
REPEAT (FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘s’])) >> fs[]) >>
gvs[] >>

gvs[scopes_to_pass_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 

IMP_RES_TAC dom_eq_imp_NONE >> gvs[] >>

gvs[t_scopes_to_pass_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 

            
gvs[scopes_to_retrieve_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 

gvs[dom_b_eq_def, dom_g_eq_def, dom_eq_def, is_lookup_defined_def] >>
REPEAT (FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘s'’])) >> fs[]) >>
gvs[] >>

gvs[dom_map_ei_def, dom_empty_intersection_def ] >>
REPEAT (FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘s'’])) >> fs[]) >>
gvs[] 
);



val retrived_scopes_can_be_passed = prove (“
∀ f txdl tau delta_g delta_b passed_delta_b func_map b_func_map delta_x gscope gscope' g_scope_list'.                                           
SOME (txdl,tau) = t_lookup_funn f delta_g passed_delta_b delta_x ∧
t_map_to_pass f delta_b = SOME passed_delta_b ∧
scopes_to_pass f func_map b_func_map gscope = SOME g_scope_list' ∧ 
SOME gscope' = scopes_to_retrieve f func_map b_func_map gscope g_scope_list' ⇒
scopes_to_pass f func_map b_func_map gscope' = SOME g_scope_list' ”,

REPEAT GEN_TAC >> STRIP_TAC >>

gvs[t_map_to_pass_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 
       
gvs[t_lookup_funn_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 

gvs[typying_domains_ei_def, dom_empty_intersection_def] >>
REPEAT (FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘s’])) >> fs[]) >>
gvs[] >>

gvs[scopes_to_pass_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 
IMP_RES_TAC dom_eq_imp_NONE >> gvs[] >>

gvs[t_scopes_to_pass_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 
            
gvs[scopes_to_retrieve_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 

gvs[dom_b_eq_def, dom_g_eq_def, dom_eq_def, is_lookup_defined_def] >>
REPEAT (FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘s'’])) >> fs[]) >>
gvs[] >>

gvs[dom_map_ei_def, dom_empty_intersection_def ] >>
REPEAT (FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘s'’])) >> fs[]) >>
gvs[]
);



val  to_pass_same_as_retr = prove (“
∀ f delta_g delta_b passed_delta_b delta_x func_map b_func_map tau txdl gscope gscope' passed_gscope.                                   
dom_g_eq delta_g func_map ∧
dom_b_eq delta_b b_func_map ∧
typying_domains_ei delta_g        delta_b delta_x ∧         
typying_domains_ei delta_g passed_delta_b delta_x ∧
t_map_to_pass f delta_b = SOME passed_delta_b ∧
LENGTH gscope = 2 ∧
  SOME (txdl,tau) = t_lookup_funn f delta_g passed_delta_b delta_x ∧
  scopes_to_pass f func_map b_func_map gscope = SOME passed_gscope ∧
  scopes_to_retrieve f func_map b_func_map gscope passed_gscope = SOME gscope' ⇒
   gscope = gscope' ”  ,  

REPEAT GEN_TAC >> STRIP_TAC >>
gvs[LIST_LENGTH_2_simp] >>

       
gvs[t_map_to_pass_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 
       
gvs[t_lookup_funn_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 

gvs[scopes_to_pass_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 
IMP_RES_TAC dom_eq_imp_NONE >> gvs[] >>
       
gvs[scopes_to_retrieve_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 

       
gvs[typying_domains_ei_def, dom_empty_intersection_def] >>
REPEAT (FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘s’])) >> fs[]) >>
gvs[] >>
gvs[t_scopes_to_pass_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 
     
gvs[dom_b_eq_def, dom_g_eq_def, dom_eq_def, is_lookup_defined_def] >>
REPEAT (FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘s’])) >> fs[]) >>
gvs[] 
);




                




val frame_typ_different_globals = prove (“
∀ gscope gscope' tslg tscl T_e Prs_n scl stmtl.
type_scopes_list gscope' tslg ∧
frame_typ (tslg,tscl) T_e Prs_n gscope scl stmtl ⇒
frame_typ (tslg,tscl) T_e Prs_n gscope' scl stmtl ”,

REPEAT STRIP_TAC >>
gvs[frame_typ_cases] >>
qexistsl_tac [‘tau_x_d_list’,‘tau’] >>
gvs[]
);

        
val frame_typ_different_globals_local = prove (“
∀ gscope gscope' tslg tscl T_e Prs_n scl scl' stmtl.
type_scopes_list gscope' tslg ∧
type_frame_tsl scl' tscl ∧
frame_typ (tslg,tscl) T_e Prs_n gscope scl stmtl ⇒
frame_typ (tslg,tscl) T_e Prs_n gscope' scl' stmtl ”,

REPEAT STRIP_TAC >>
gvs[frame_typ_cases] >>
qexistsl_tac [‘tau_x_d_list’,‘tau’] >>
gvs[type_frame_tsl_def]
);
        

val WT_state_of_largest_possible_frame = prove (“

∀ apply_table_f ext_map func_map b_func_map pars_map tbl_map passed_b_func_map passed_tbl_map
ascope gscope f stmt_stack scope_list t status Prs_n order tslg tsll delta_g delta_b delta_x delta_t
passed_gscope passed_tslg passed passed_b_func_map passed_delta_b passed_tbl_map passed_delta_t
f_called stmt_called copied_in_scope t_scope_list' t_scope_list'' gscope' scope_list' stmtl' scope_list'.
                        
WT_state  (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)
          (ascope,gscope,(f,stmt_stack,scope_list)::t,status) Prs_n order
          tslg tsll (delta_g,delta_b,delta_x,delta_t) ∧

  scopes_to_pass f func_map b_func_map gscope = SOME passed_gscope ∧
t_scopes_to_pass f delta_g delta_b tslg = SOME passed_tslg ∧
  map_to_pass f b_func_map = SOME passed_b_func_map ∧
t_map_to_pass f delta_b = SOME passed_delta_b ∧
  tbl_to_pass f b_func_map tbl_map = SOME passed_tbl_map ∧
t_tbl_to_pass f delta_b delta_t = SOME passed_delta_t ∧

SOME gscope' = scopes_to_retrieve f func_map b_func_map gscope passed_gscope ∧
type_scopes_list gscope' tslg ∧
frame_typ (passed_tslg,t_scope_list'' ⧺ HD tsll)
          (order,f,delta_g,passed_delta_b,delta_x,passed_delta_t) Prs_n
          passed_gscope scope_list' stmtl' ∧
                     
res_frame_typ (order,f,delta_g,passed_delta_b,delta_x,passed_delta_t) Prs_n 
          passed_tslg t_scope_list' passed_gscope [(f_called,[stmt_called],copied_in_scope)] func_map passed_b_func_map (HD tsll)∧


WT_c (apply_table_f,ext_map,func_map,b_func_map       ,pars_map       ,tbl_map) order        tslg delta_g        delta_b delta_x        delta_t Prs_n ∧
WT_c (apply_table_f,ext_map,func_map,passed_b_func_map,pars_map,passed_tbl_map) order passed_tslg delta_g passed_delta_b delta_x passed_delta_t Prs_n ⇒

type_frames gscope' ((f_called,[stmt_called],copied_in_scope):: (f,stmtl',scope_list')::t) Prs_n order tslg (t_scope_list'::(t_scope_list'' ⧺ HD tsll)::TL tsll) delta_g delta_b delta_x delta_t func_map b_func_map”,



REPEAT STRIP_TAC >>
gvs[type_frames_def] >>
REPEAT STRIP_TAC >>
gvs[Once EL_compute] >>
CASE_TAC >| [
    
  (* first we need to show that the newly created frame is well typed with all the passes that are happening *)  
  gvs[EL_CONS] >>
  gvs[res_frame_typ_def] >>
  gvs[] >>
  gvs[t_passed_elem_def] >>
  
  Q.EXISTS_TAC ‘passed_tslg'’ >>
  Q.EXISTS_TAC ‘passed_delta_b'’ >>
  Q.EXISTS_TAC ‘passed_delta_t'’ >>
  Q.EXISTS_TAC ‘passed_gscope'’ >>
  gvs[] >>

  ‘∃ txdl tau. SOME (txdl,tau) =
          t_lookup_funn f_called delta_g passed_delta_b' delta_x’ by (gvs[frame_typ_cases] >>  srw_tac [SatisfySimps.SATISFY_ss][] ) >>

        
  gvs[WT_state_cases, type_frames_def] >>
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`0`])) >>
  Cases_on ‘ (ZIP (funnl,ZIP (stmtll,scll)))’ >> gvs[] >>
  subgoal ‘0 < LENGTH scll’ >- (Cases_on ‘scll’ >> gvs[]  ) >> gvs[] >>

  ‘∃ txdl tau. SOME (txdl,tau) =
          t_lookup_funn f delta_g passed_delta_b delta_x’ by (gvs[frame_typ_cases] >>  srw_tac [SatisfySimps.SATISFY_ss][] ) >>
  gvs[WT_c_cases] >> 
  rw[] >| [
       
   drule t_scopes_to_pass_twice >> gvs[] >> STRIP_TAC >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘f_called’])) >>
   RES_TAC
   ,                                            
   drule t_map_to_pass_twice >> gvs[] >> STRIP_TAC >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘f_called’])) >>
   RES_TAC
   ,
   drule t_tbl_to_pass_twice >> gvs[] >> STRIP_TAC >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘f_called’])) >>
   RES_TAC
   ,
   
   drule scopes_to_pass_twice >> gvs[] >> STRIP_TAC >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘f_called’, ‘delta_b’, ‘passed_delta_b'’, ‘txdl’, ‘tau’, ‘func_map’, ‘b_func_map’])) >>
   gvs[] >>
   RES_TAC
   ]
  ,

 


  gvs[Once EL_compute] >> CASE_TAC >> gvs[EL_CONS] >| [
    (* now we should show that the caller is also well typed, and this is from the frame being typed *)
    ‘i>0’ by gvs[] >>
    Q.EXISTS_TAC ‘passed_gscope’ >>
    gvs[] >>
    
    ‘∃ txdl tau. SOME (txdl,tau) =
                t_lookup_funn f delta_g passed_delta_b delta_x’ by (gvs[frame_typ_cases] >>  srw_tac [SatisfySimps.SATISFY_ss][] ) >>
    IMP_RES_TAC retrived_scopes_can_be_passed
      ,
      

   gvs[PRE_SUB1, EL_CONS, ADD1] >>
    
    gvs[WT_state_cases] >> 
    gvs[type_frames_def] >>
    gvs[map_distrub] >>
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘i-1’])) >>
    
    
    subgoal ‘i -1 < LENGTH scll’ >- (
      Cases_on ‘tsll’ >>
      Cases_on ‘scll’ >>
      Cases_on ‘funnl’ >>
      Cases_on ‘stmtll’ >>
      REPEAT STRIP_TAC >>
      gvs[]  ) >> gvs[] >>
    
      Q.EXISTS_TAC ‘passed_tslg'’ >>       
      Q.EXISTS_TAC ‘passed_delta_b'’ >>                                    
      Q.EXISTS_TAC ‘passed_delta_t'’  >>  
    
    ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:funn``, ``:'b`` |-> ``:stmt list``, ``:'c`` |-> ``:scope_list``] ZIP_tri_sep_ind)  >>
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘t’,‘funnl’,‘stmtll’,‘scll’, ‘f’,‘stmt_stack’,‘scope_list’])) >> gvs[] >>
    gvs[EL_CONS, PRE_SUB1] >> 
    
    Cases_on ‘tsll’ >> gvs[EL_CONS, PRE_SUB1] >>


             
    subgoal ‘∃passed_gscope'. scopes_to_pass (EL (i − 2) (MAP (λ(f,stml,scl). f) t)) func_map b_func_map gscope' = SOME passed_gscope' ∧
                             type_scopes_list  passed_gscope' passed_tslg'’ >- (
      gvs[WT_c_cases] >>
      ASSUME_TAC typed_imp_scopes_to_pass_lemma >>
      FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘gscope'’,‘tslg’ ,
                     ‘(EL (i − 2) (MAP (λ(al_,bl_,cl_). al_) (t : (funn # stmt list # (varn # v # lval option) list list) list)))’,
                                         ‘func_map’,‘b_func_map’,‘delta_g’, ‘delta_b’,‘passed_tslg'’])) >> gvs[]
                 ) >>

      
    Q.EXISTS_TAC ‘passed_gscope''’  >> gvs[] >>
    IMP_RES_TAC frame_typ_different_globals >> gvs[]              
                            
    ]
   ]
);








val to_retr_same_as_pass = prove ( “
∀ delta_b delta_g func_map b_func_map gscope gscope' g_scope_list' g_scope_list'' tslg passed_tslg f .                                   
dom_b_eq delta_b b_func_map ∧
dom_g_eq delta_g func_map ∧

t_scopes_to_pass f delta_g delta_b tslg = SOME passed_tslg ∧
type_scopes_list g_scope_list' passed_tslg ∧
type_scopes_list g_scope_list'' passed_tslg ∧

scopes_to_retrieve f func_map b_func_map gscope g_scope_list'' = SOME gscope' ⇒
scopes_to_pass f func_map b_func_map gscope' = SOME g_scope_list'' ” ,
                                           
REPEAT GEN_TAC >> STRIP_TAC >>
IMP_RES_TAC type_scopes_list_LENGTH >>
gvs[] >>
gvs[LIST_LENGTH_2_simp] >>

gvs[t_map_to_pass_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 
       
gvs[scopes_to_pass_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 
IMP_RES_TAC dom_eq_imp_NONE >> gvs[] >>

gvs[t_scopes_to_pass_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 

gvs[scopes_to_retrieve_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 

gvs[dom_b_eq_def, dom_g_eq_def, dom_eq_def, is_lookup_defined_def] >>
REPEAT (FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘s’])) >> fs[]) >>
gvs[] >>

gvs[LIST_LENGTH_2_simp] >>                                   
IMP_RES_TAC type_scopes_list_normalize2 >> gvs[] >>
gvs[type_scopes_list_def, similarl_def, similar_def] >> gvs[]
);












  
        

val WT_state_of_frame_and_tl = prove ( “
∀ apply_table_f ext_map func_map b_func_map pars_map tbl_map ascope gscope
       f stmt_stack scope_list t status Prs_n order tslg tsll delta_g delta_b
       delta_x delta_t passed_tslg passed_b_func_map passed_delta_b
       passed_tbl_map passed_delta_t t_scope_list'' gscope' stmtl'
       scope_list' g_scope_list' g_scope_list''.
  
WT_state (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)
          (ascope,gscope,(f,stmt_stack,scope_list)::t,status) Prs_n order
          tslg tsll (delta_g,delta_b,delta_x,delta_t) ∧

t_scopes_to_pass f delta_g delta_b tslg = SOME passed_tslg ∧
scopes_to_pass f func_map b_func_map gscope = SOME g_scope_list' ∧
map_to_pass f b_func_map = SOME passed_b_func_map ∧
t_map_to_pass f delta_b = SOME passed_delta_b ∧
tbl_to_pass f b_func_map tbl_map = SOME passed_tbl_map ∧
t_tbl_to_pass f delta_b delta_t = SOME passed_delta_t ∧

type_scopes_list gscope' tslg ∧
scopes_to_retrieve f func_map b_func_map gscope g_scope_list'' = SOME gscope' ∧
frame_typ (passed_tslg,t_scope_list'' ⧺ HD tsll)
          (order,f,delta_g,passed_delta_b,delta_x,passed_delta_t) Prs_n
          g_scope_list'' scope_list' stmtl' ∧

 WT_c  (apply_table_f,ext_map,func_map,passed_b_func_map,pars_map,passed_tbl_map) order passed_tslg delta_g passed_delta_b delta_x passed_delta_t Prs_n ∧
 WT_c  (apply_table_f,ext_map,func_map,       b_func_map,pars_map,       tbl_map) order        tslg delta_g        delta_b delta_x        delta_t Prs_n ⇒

type_frames gscope' ((f,stmtl',scope_list')::t) Prs_n order tslg
          ((t_scope_list'' ⧺ HD tsll)::TL tsll) delta_g delta_b delta_x
          delta_t func_map b_func_map ”,


REPEAT STRIP_TAC >>
gvs[type_frames_def] >>
REPEAT STRIP_TAC >>
gvs[Once EL_compute] >>
CASE_TAC >| [

    gvs[EL_CONS] >>
    Q.EXISTS_TAC ‘g_scope_list''’ >>
    gvs[] >>

    ‘∃ txdl tau. SOME (txdl,tau) =
                t_lookup_funn f delta_g passed_delta_b delta_x’ by (gvs[frame_typ_cases] >>  srw_tac [SatisfySimps.SATISFY_ss][] ) >>
    gvs[WT_c_cases] >>            
    ‘type_scopes_list g_scope_list'' passed_tslg’ by (gvs[frame_typ_cases] ) >>
    IMP_RES_TAC to_retr_same_as_pass                 
    ,
    
    gvs[PRE_SUB1, EL_CONS, ADD1] >>
    
    gvs[WT_state_cases] >> 
    gvs[type_frames_def] >>
    gvs[map_distrub] >>
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘i’])) >>
    
    
    subgoal ‘i < LENGTH scll’ >- (
      Cases_on ‘tsll’ >>
      Cases_on ‘scll’ >>
      Cases_on ‘funnl’ >>
      Cases_on ‘stmtll’ >>
      REPEAT STRIP_TAC >>
      gvs[]  ) >> gvs[] >>
    
    Q.EXISTS_TAC ‘passed_tslg'’ >>       
    Q.EXISTS_TAC ‘passed_delta_b'’ >>                                    
    Q.EXISTS_TAC ‘passed_delta_t'’  >>  
    
    ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:funn``, ``:'b`` |-> ``:stmt list``, ``:'c`` |-> ``:scope_list``] ZIP_tri_sep_ind)  >>
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘t’,‘funnl’,‘stmtll’,‘scll’, ‘f’,‘stmt_stack’,‘scope_list’])) >> gvs[] >>
    gvs[EL_CONS, PRE_SUB1] >> 
    
    Cases_on ‘tsll’ >> gvs[EL_CONS, PRE_SUB1] >>


             
    subgoal ‘∃passed_gscope'. scopes_to_pass (EL (i − 1) (MAP (λ(f,stml,scl). f) t)) func_map
                                             b_func_map gscope' = SOME passed_gscope' ∧
                             type_scopes_list  passed_gscope' passed_tslg'’ >- (
      gvs[WT_c_cases] >>
      ASSUME_TAC typed_imp_scopes_to_pass_lemma >>
      FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘gscope'’,‘tslg’ ,
                     ‘(EL (i − 1) (MAP (λ(al_,bl_,cl_). al_) (t : (funn # stmt list # (varn # v # lval option) list list) list)))’,
                                         ‘func_map’,‘b_func_map’,‘delta_g’, ‘delta_b’,‘passed_tslg'’])) >> gvs[]
                 ) >>

      
    Q.EXISTS_TAC ‘passed_gscope'’  >> gvs[] >>
    IMP_RES_TAC frame_typ_different_globals >> gvs[]   
  ]
);






val WT_state_of_blk_exit_and_tl = prove (“        
∀ f apply_table_f ext_map func_map b_func_map pars_map tbl_map ascope gscope
       stmt_stack scope_list t status Prs_n order tslg tsll delta_g delta_b
       delta_x delta_t passed_b_func_map passed_tslg passed_delta_b passed_tbl_map
       passed_delta_t gscope' stmtl' scope_list' g_scope_list' .

WT_state (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)
          (ascope,gscope,(f,stmt_stack,scope_list)::t,status) Prs_n order
          tslg tsll (delta_g,delta_b,delta_x,delta_t) ∧

type_scopes_list gscope' tslg ∧
t_scopes_to_pass f delta_g delta_b tslg = SOME passed_tslg ∧
scopes_to_pass f func_map b_func_map gscope = SOME g_scope_list' ∧
map_to_pass f b_func_map = SOME passed_b_func_map /\
t_map_to_pass f delta_b = SOME passed_delta_b ∧
tbl_to_pass f b_func_map tbl_map = SOME passed_tbl_map ∧
t_tbl_to_pass f delta_b delta_t = SOME passed_delta_t ∧

SOME gscope' = scopes_to_retrieve f func_map b_func_map gscope g_scope_list' ∧
                         
frame_typ (passed_tslg,DROP 1 (HD tsll))
          (order,f,delta_g,passed_delta_b,delta_x,passed_delta_t) Prs_n
          g_scope_list' scope_list' stmtl' ∧

WT_c (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)
          order tslg delta_g delta_b delta_x delta_t Prs_n ∧

WT_c (apply_table_f,ext_map,func_map,passed_b_func_map,pars_map,passed_tbl_map)
          order passed_tslg delta_g passed_delta_b delta_x passed_delta_t
          Prs_n  ⇒
        
type_frames gscope' ((f,stmtl',scope_list')::t) Prs_n order tslg
          (DROP 1 (HD tsll)::TL tsll) delta_g delta_b delta_x delta_t
          func_map b_func_map ”,
                                                
REPEAT STRIP_TAC >>
gvs[type_frames_def] >>
REPEAT STRIP_TAC >>
gvs[Once EL_compute] >>
CASE_TAC >| [

    gvs[EL_CONS] >>
    ‘type_scopes_list gscope tslg’ by (gvs[WT_state_cases]) >>
                
      
    subgoal ‘∃passed_gscope'. scopes_to_pass f func_map b_func_map gscope' = SOME passed_gscope' ∧
                             type_scopes_list  passed_gscope' passed_tslg’ >- (
      gvs[WT_c_cases] >>
      ASSUME_TAC typed_imp_scopes_to_pass_lemma >>
      FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘gscope'’,‘tslg’ ,
                     ‘f’, ‘func_map’,‘b_func_map’,‘delta_g’, ‘delta_b’,‘passed_tslg’])) >> gvs[]
                 ) >>

      
    Q.EXISTS_TAC ‘passed_gscope'’  >> gvs[] >>
    IMP_RES_TAC frame_typ_different_globals >> gvs[]         
    ,
    
    gvs[PRE_SUB1, EL_CONS, ADD1] >>
    
    gvs[WT_state_cases] >> 
    gvs[type_frames_def] >>
    gvs[map_distrub] >>
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘i’])) >>
    
    
    subgoal ‘i < LENGTH scll’ >- (
      Cases_on ‘tsll’ >>
      Cases_on ‘scll’ >>
      Cases_on ‘funnl’ >>
      Cases_on ‘stmtll’ >>
      REPEAT STRIP_TAC >>
      gvs[]  ) >> gvs[] >>
    
    Q.EXISTS_TAC ‘passed_tslg'’ >>       
    Q.EXISTS_TAC ‘passed_delta_b'’ >>                                    
    Q.EXISTS_TAC ‘passed_delta_t'’  >>  
    
    ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:funn``, ``:'b`` |-> ``:stmt list``, ``:'c`` |-> ``:scope_list``] ZIP_tri_sep_ind)  >>
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘t’,‘funnl’,‘stmtll’,‘scll’, ‘f’,‘stmt_stack’,‘scope_list’])) >> gvs[] >>
    gvs[EL_CONS, PRE_SUB1] >> 
    Cases_on ‘tsll’ >> gvs[EL_CONS, PRE_SUB1] >>
             
    subgoal ‘∃passed_gscope'. scopes_to_pass (EL (i − 1) (MAP (λ(f,stml,scl). f) t)) func_map
                                             b_func_map gscope' = SOME passed_gscope' ∧
                             type_scopes_list  passed_gscope' passed_tslg'’ >- (
      gvs[WT_c_cases] >>
      ASSUME_TAC typed_imp_scopes_to_pass_lemma >>
      FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘gscope'’,‘tslg’ ,
                     ‘(EL (i − 1) (MAP (λ(al_,bl_,cl_). al_) (t : (funn # stmt list # (varn # v # lval option) list list) list)))’,
                                         ‘func_map’,‘b_func_map’,‘delta_g’, ‘delta_b’,‘passed_tslg'’])) >> gvs[]
                 ) >>

      
    Q.EXISTS_TAC ‘passed_gscope'’  >> gvs[] >>
    IMP_RES_TAC frame_typ_different_globals >> gvs[]   
  ]

);




val WT_state_of_copyout = prove ( “
∀ funn funn' frame_list h stmt_stack' scope_list'' apply_table_f ext_map func_map b_func_map pars_map tbl_map gscope
       stmt_stack scope_list t Prs_n order tslg delta_g delta_b delta_x b_func_map'
       delta_t passed_tslg passed_delta_b passed_tbl_map passed_delta_t
       gscope' scope_list'.
       
     WT_c
       (apply_table_f,ext_map,func_map,b_func_map',pars_map,passed_tbl_map)
       order passed_tslg delta_g passed_delta_b delta_x passed_delta_t Prs_n ∧
     WT_c (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map) order
          tslg delta_g delta_b delta_x delta_t Prs_n ∧
          
     type_frame_tsl scope_list'' (HD t) ∧ type_scopes_list gscope tslg ∧
     type_scopes_list gscope' tslg ∧
                      
     type_frames gscope
       ((funn,stmt_stack,scope_list)::(funn',stmt_stack',scope_list')::
            frame_list) Prs_n order tslg (h::t) delta_g delta_b delta_x
       delta_t func_map b_func_map ⇒
       
     type_frames gscope' ((funn',stmt_stack',scope_list'')::frame_list)
       Prs_n order tslg t delta_g delta_b delta_x delta_t func_map b_func_map   ”,


          
REPEAT STRIP_TAC >>
gvs[type_frames_def] >>
REPEAT STRIP_TAC >>
Cases_on ‘i=0’ >> gvs[] >| [

    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘1’])) >>
    gvs[] >>
   
    subgoal ‘∃passed_gscope'.
               scopes_to_pass funn' func_map b_func_map gscope' =
               SOME passed_gscope' ∧ type_scopes_list passed_gscope' passed_tslg' ’ >- (
    gvs[WT_c_cases] >>
    ASSUME_TAC typed_imp_scopes_to_pass_lemma >>
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘gscope'’,‘tslg’ , ‘funn'’, ‘func_map’,‘b_func_map’,
                                                ‘delta_g’, ‘delta_b’,‘passed_tslg'’])) >> gvs[]
    ) >>

      
    gvs[] >>
    IMP_RES_TAC frame_typ_different_globals_local   
                
    ,
    
    gvs[PRE_SUB1, EL_CONS, ADD1] >>
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘i+1’])) >>
    gvs[EL_CONS] >> 
    gvs[PRE_SUB1] >> 
    gvs[EL_PRE] >>       
       
       
       subgoal ‘∃passed_gscope'.
               scopes_to_pass (EL (i − 1) (MAP (λ(f,stml,scl). f) frame_list))
                         func_map b_func_map gscope' = SOME passed_gscope' ∧
          type_scopes_list  passed_gscope' passed_tslg'’ >- (
      gvs[WT_c_cases] >>
      ASSUME_TAC typed_imp_scopes_to_pass_lemma >>
      FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘gscope'’,‘tslg’ ,
                                                  ‘(EL (i − 1) (MAP (λ(al_,bl_,cl_). al_) (frame_list : frame_list)))’,
                     ‘func_map’,‘b_func_map’,‘delta_g’, ‘delta_b’,‘passed_tslg'’])) >> gvs[]
      ) >>
    
    gvs[] >>
    drule frame_typ_different_globals   >> REPEAT STRIP_TAC >> 
    METIS_TAC []
]
);












        
(*

val parseError_doub_lemma = prove (“
∀ tscl tsll tslg tslg'.        
parseError_in_gs tslg  [tscl ⧺ HD tsll]  ∧
parseError_in_gs tslg' tsll ⇒
parseError_in_gs tslg' ((tscl ⧺ HD tsll)::TL tsll)”,

gvs[parseError_in_gs_def] >>
REPEAT STRIP_TAC >>
gvs[ADD1] >>

SIMP_TAC list_ss [Once EL_compute] >> CASE_TAC >> gvs[] >| [
  LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘0’])) >>
  gvs[]
  ,
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘(i)’])) >>
  Cases_on ‘tsll’ >> gvs[] >>                                               
  gvs[EL_CONS] >>
  gvs[PRE_SUB1, ADD1]
 ]
);

                           
val parseError_tri_lemma = prove (“
∀ tscl tscl' tsll tslg tslg' tslg''.        
parseError_in_gs tslg   [tscl]  ∧
parseError_in_gs tslg'  [tscl' ⧺ HD tsll]  ∧
parseError_in_gs tslg'' tsll ⇒
parseError_in_gs tslg'' (tscl::(tscl' ⧺ HD tsll)::TL tsll)”,

gvs[parseError_in_gs_def] >>
REPEAT STRIP_TAC >>
gvs[ADD1] >>

SIMP_TAC list_ss [Once EL_compute] >> CASE_TAC >> gvs[] >| [
  LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘0’])) >>
  gvs[]
  ,
  SIMP_TAC list_ss [Once EL_compute] >> CASE_TAC >> gvs[] >| [
    REPEAT (LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘0’])) >> gvs[])
    ,
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘(PRE i)’])) >>
    Cases_on ‘tsll’ >> gvs[] >>                                               
    gvs[EL_CONS] >>
    gvs[PRE_SUB1, ADD1]
    ]
]
);




val parseError_DROP_lemma = prove (“
∀ tsll passed_tslg tslg .
LENGTH tsll > 0 ∧
parseError_in_gs passed_tslg [DROP 1 (HD tsll)] ∧
parseError_in_gs tslg tsll ⇒
parseError_in_gs tslg (DROP 1 (HD tsll)::TL tsll)”,

REPEAT STRIP_TAC >>                      
gvs[parseError_in_gs_def] >>
REPEAT STRIP_TAC >>
SIMP_TAC list_ss [Once EL_compute] >> CASE_TAC >> gvs[] >| [
  LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘0’])) >>
  gvs[] >>
gvs[DROP_1] 
  ,
  gvs[PRE_SUB1] >>      
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘i’])) >>
  gvs[] >>
  Cases_on ‘tsll’ >> gvs[] >>
  gvs[EL_CONS, PRE_SUB1]
]
 );       

*)


val WF_ft_order_imp_HD = prove (“
∀ f f' fl delta_g delta_b delta_x order.
WF_ft_order (f::f'::fl) delta_g delta_b delta_x order ⇒
WF_ft_order (   f'::fl) delta_g delta_b delta_x order ”,


gvs[WF_ft_order_cases] >>
gvs[ordered_list_def] >>

REPEAT STRIP_TAC >>
gvs[ADD1, PRE_SUB1] >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘i+1’])) >>
gvs[EL_CONS, PRE_SUB1]
); 







val ret_status_typed_def = Define ‘
  ret_status_typed status (order, f, (delta_g, delta_b, delta_x, delta_t)) =
  ∀ v tau txdl . status = status_returnv v /\
        SOME (txdl,tau) = t_lookup_funn f delta_g delta_b delta_x ⇒
               v_typ v (t_tau (tau))  F
                       ’;



val t_lookup_funn_not_x = prove ( ``
! delta_g delta_b delta_x f txdl tau .
SOME (txdl,tau) = t_lookup_funn f delta_g delta_b [] /\
dom_tmap_ei delta_g delta_b ==>
SOME (txdl,tau) = t_lookup_funn f delta_g delta_b delta_x``,

REPEAT STRIP_TAC >>
fs[t_lookup_funn_def] >>

REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>

fs[dom_tmap_ei_def] >>
rfs[dom_empty_intersection_def] >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`s`])) >> gvs[]
);


        
     
 fun OPEN_FRAME_TYP_TAC frame_term =
(Q.PAT_X_ASSUM ` frame_typ (t1,t2) a b h d ^frame_term` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [Once frame_typ_cases] thm)))       

               
fun EXP_IS_WT_IN_FRAME_TAC frm = OPEN_FRAME_TYP_TAC frm >>
                               fs[stmtl_typ_cases, type_ith_stmt_def] >>
                               gvs[] >>
                               rfs[Once stmt_typ_cases]


         
val stmt_case_ret_stat_typed = prove (“
∀gscope scopest t_scope_list t_scope_list_g order delta_g delta_b delta_t
       delta_x f Prs_n c v tau txdl.
     WT_c c order t_scope_list_g delta_g delta_b delta_x delta_t Prs_n ∧
     frame_typ (t_scope_list_g,t_scope_list)
       (order,f,delta_g,delta_b,delta_x,delta_t) Prs_n gscope scopest
       [stmt_ret (e_v v)] ∧
     SOME (txdl,tau) = t_lookup_funn f delta_g delta_b delta_x ⇒
     v_typ v (t_tau tau) F ”,

 REPEAT STRIP_TAC >>

 EXP_IS_WT_IN_FRAME_TAC “[stmt_ret (e_v v)]” >>
 Cases_on ‘t_lookup_funn f delta_g delta_b delta_x’ >> gvs[] >>
 ‘dom_tmap_ei delta_g delta_b’ by gvs[WT_c_cases] >>
 
 IMP_RES_TAC t_lookup_funn_not_x >>
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘delta_x’])) >> gvs[] >>
 gvs[Once e_typ_cases] >>
 Cases_on ‘t_lookup_funn f delta_g delta_b []’ >> gvs[] >>         
 IMP_RES_TAC v_typ_always_lval >> gvs[]
 );                                    
                       

                   
val stmt_case_ext_stat_typed = prove (“
∀ascope ascope' gscope scopest scopest' t_scope_list t_scope_list_g order
       delta_g delta_b delta_t delta_x f Prs_n v tau txdl apply_table_f
       ext_map func_map b_func_map pars_map tbl_map ext_fun.
     WT_c (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map) order
       t_scope_list_g delta_g delta_b delta_x delta_t Prs_n ∧
     frame_typ (t_scope_list_g,t_scope_list)
       (order,f,delta_g,delta_b,delta_x,delta_t) Prs_n gscope scopest
       [stmt_ext] ∧
     SOME (ascope',scopest', status_returnv v) = ext_fun (ascope,gscope,scopest) ∧
     SOME ext_fun = lookup_ext_fun f ext_map ∧
     SOME (txdl,tau) = t_lookup_funn f delta_g delta_b delta_x ⇒
     v_typ v (t_tau tau) F    ”,

 REPEAT STRIP_TAC >>            
 EXP_IS_WT_IN_FRAME_TAC “[stmt_ext]” >>
    Cases_on ‘t_lookup_funn f delta_g delta_b delta_x’ >> gvs[] >>
    gvs[WT_c_cases] >> fs[Once WTX_cases] >>
    Cases_on ‘f’ >> gvs[lookup_ext_fun_def] >| [
        REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
        gvs[extern_map_IoE_typed_def] >>
        FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘q’, ‘s’, ‘ext_fun’, ‘r’])) >> gvs[] >>
        FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘ascope’, ‘gscope’, ‘scopest’])) >> gvs[] >>
        Cases_on ‘ext_fun (ascope,gscope,scopest)’ >> gvs[] >>
        gvs[t_lookup_funn_def]
        ,                                                 

        REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
        gvs[extern_MoE_typed_def] >>
        FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘q'’, ‘s’, ‘s0’, ‘q’, ‘r’, ‘ext_fun’])) >> gvs[] >>
        FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘ascope’, ‘gscope’, ‘scopest’])) >> gvs[] >>
        Cases_on ‘ext_fun (ascope,gscope,scopest)’ >> gvs[] >>
        gvs[t_lookup_funn_def]
  ]
);



                       
val status_ret_in_stmt_typed_verbose = prove (“
∀stmt stmtl ascope ascope' gscope gscope' scopest scopest' framel status
       t_scope_list t_scope_list_g order delta_g delta_b delta_t delta_x f
       Prs_n c v tau
       txdl.
     WT_c c order  t_scope_list_g delta_g delta_b delta_x delta_t Prs_n ∧
     frame_typ (t_scope_list_g,t_scope_list)
       (order,f,delta_g,delta_b,delta_x,delta_t) Prs_n gscope scopest [stmt] ∧
     stmt_red c
       (ascope,gscope,            [(f,[stmt],scopest)],status)
       (ascope',gscope',framel ⧺ [(f,stmtl,scopest')],status_returnv v) ∧
     SOME (txdl,tau) = t_lookup_funn f delta_g delta_b delta_x ⇒
     v_typ v (t_tau tau) F”,

Induct >>
REPEAT STRIP_TAC >>
OPEN_ANY_STMT_RED_TAC “anystmt” >> gvs[] >| [
    (* return statement *)
    IMP_RES_TAC stmt_case_ret_stat_typed
    ,
    (* seq statement *)     
    subgoal ‘frame_typ (t_scope_list_g,t_scope_list)
             (order,f,delta_g,delta_b,delta_x,delta_t) Prs_n  gscope scopest
             [stmt]’ >-
     (EXP_IS_WT_IN_FRAME_TAC “[stmt_seq stmt stmt']” >>
      SIMP_TAC list_ss [frame_typ_cases] >> gvs[] >> REPEAT STRIP_TAC >>
      
      Q.EXISTS_TAC ‘tau_x_d_list’ >>
      Q.EXISTS_TAC ‘tau’ >>
      Cases_on ‘ t_lookup_funn f delta_g delta_b delta_x’ >> gvs[] >>
      SIMP_TAC list_ss [stmtl_typ_cases] >>
      srw_tac [boolSimps.DNF_ss][] >>
      srw_tac [][type_ith_stmt_def] >>
      ‘i=0’ by fs[] >> srw_tac [][]
     ) >>
    
    LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘[stmt1']’, ‘ascope’, ‘ascope'’, ‘gscope’, ‘gscope'’, ‘scopest’, ‘scopest'’, ‘[]’, ‘status_running’,
                                               ‘t_scope_list’, ‘t_scope_list_g’, ‘order’, ‘delta_g’, ‘delta_b’, ‘delta_t’, ‘delta_x’, ‘f’, ‘Prs_n’,
                                               ‘c’,‘ v’,‘tau’, ‘txdl’])) >> gvs[]                                                                            
    ,
    (* ext statement *)  
    IMP_RES_TAC stmt_case_ext_stat_typed        
  ]
);


      
Theorem status_ret_in_stmt_typed:
∀stmt stmtl ascope ascope' gscope gscope' scopest scopest' framel status
       status' t_scope_list t_scope_list_g order delta_g delta_b delta_t
       delta_x f Prs_n c.
     WT_c c order t_scope_list_g delta_g delta_b delta_x delta_t Prs_n ∧
     frame_typ (t_scope_list_g,t_scope_list)
       (order,f,delta_g,delta_b,delta_x,delta_t) Prs_n gscope scopest [stmt] ∧
     stmt_red c
       (ascope,gscope,[(f,[stmt],scopest)],status)
       (ascope',gscope',framel ⧺ [(f,stmtl,scopest')],status') ⇒
     ret_status_typed status' (order,f,delta_g,delta_b,delta_x,delta_t)
Proof
gvs[ret_status_typed_def] >>
REPEAT STRIP_TAC >>
gvs[] >>
IMP_RES_TAC status_ret_in_stmt_typed_verbose
QED



Theorem status_ret_in_stmtl_typed_verbose:

∀stmtl stmtl' ascope ascope' gscope gscope' scopest scopest' framel
        t_scope_list t_scope_list_g order delta_g delta_b delta_t
       delta_x f Prs_n c tau txdl v.
WT_c c order t_scope_list_g delta_g delta_b delta_x delta_t Prs_n ∧
frame_typ (t_scope_list_g,t_scope_list)
          (order,f,delta_g,delta_b,delta_x,delta_t) Prs_n gscope scopest
          stmtl ∧
stmt_red c (ascope,gscope,[(f,stmtl,scopest)],status_running)
          (ascope',gscope',framel ⧺ [(f,stmtl',scopest')],status_returnv v) ∧
SOME (txdl,tau) = t_lookup_funn f delta_g delta_b delta_x ⇒
        v_typ v (t_tau tau) F 
Proof        
Induct >>
REPEAT STRIP_TAC >>
fs[Once stmt_red_cases] >| [

   ASSUME_TAC status_ret_in_stmt_typed_verbose >>

  LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘stmt1’,‘[stmt1']’, ‘ascope’, ‘ascope'’, ‘gscope’, ‘gscope'’, ‘scopest’, ‘scopest'’, ‘[]’, ‘status_running’,
                                                 ‘t_scope_list’, ‘t_scope_list_g’, ‘order’, ‘delta_g’, ‘delta_b’, ‘delta_t’, ‘delta_x’, ‘f’, ‘Prs_n’,
                                                 ‘c’,‘ v’,‘tau’, ‘txdl’])) >> gvs[] >>


   
   
   subgoal ‘frame_typ (t_scope_list_g,t_scope_list)
            (order,f,delta_g,delta_b,delta_x,delta_t) Prs_n  gscope scopest
            [stmt1]’ >-
    (EXP_IS_WT_IN_FRAME_TAC “[stmt_seq stmt stmt']” >>
     SIMP_TAC list_ss [frame_typ_cases] >> gvs[] >> REPEAT STRIP_TAC >>
              
     Q.EXISTS_TAC ‘tau_x_d_list’ >>
     Q.EXISTS_TAC ‘tau’ >>
     Cases_on ‘ t_lookup_funn f delta_g delta_b delta_x’ >> gvs[] >>
     SIMP_TAC list_ss [stmtl_typ_cases] >>
     srw_tac [boolSimps.DNF_ss][] >>
     srw_tac [][type_ith_stmt_def] >>
     ‘i=0’ by fs[] >> srw_tac [][]
    ) >> gvs[]

    
  ,

   ASSUME_TAC status_ret_in_stmt_typed_verbose >>
  LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘h’,‘stmt_stack'’, ‘ascope’, ‘ascope'’, ‘gscope’, ‘gscope'’, ‘scopest’, ‘scopest'’, ‘framel’, ‘status_running’,
                                                 ‘t_scope_list’, ‘t_scope_list_g’, ‘order’, ‘delta_g’, ‘delta_b’, ‘delta_t’, ‘delta_x’, ‘f’, ‘Prs_n’,
                                                 ‘(apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)’,‘ v’,‘tau’, ‘txdl’])) >> gvs[] >>
   
   subgoal ‘frame_typ (t_scope_list_g,t_scope_list)
            (order,f,delta_g,delta_b,delta_x,delta_t) Prs_n  gscope scopest
            [h]’ >-
    (
    
    fs[Once frame_typ_cases] >>
    fs[Once stmtl_typ_cases] >>
    fs[Once type_ith_stmt_def] >>
    
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`0`])) >>
    gvs[] >>
              
     Q.EXISTS_TAC ‘tau_x_d_list’ >>
     Q.EXISTS_TAC ‘tau’ >>
    Cases_on ‘ t_lookup_funn f delta_g delta_b delta_x’ >> gvs[] >>
     REPEAT STRIP_TAC >>        
     ‘i=0’ by fs[] >> srw_tac [][]
    ) >> gvs[]
  ,
  IMP_RES_TAC stmt_case_ret_stat_typed >> METIS_TAC[]         
  ,                                     
  IMP_RES_TAC stmt_case_ext_stat_typed >> METIS_TAC[]                                               
  ]
QED




val status_ret_in_stmtl_typed = prove (“
∀stmtl stmtl' ascope ascope' gscope gscope' scopest scopest' framel 
       status' t_scope_list t_scope_list_g order delta_g delta_b delta_t
       delta_x f Prs_n c.
     WT_c c order t_scope_list_g delta_g delta_b delta_x delta_t Prs_n ∧
     frame_typ (t_scope_list_g,t_scope_list)
       (order,f,delta_g,delta_b,delta_x,delta_t) Prs_n gscope scopest stmtl ∧
     stmt_red c
       (ascope,gscope,[(f,stmtl,scopest)],status_running)
       (ascope',gscope',framel ⧺ [(f,stmtl',scopest')],status') ⇒
     ret_status_typed status' (order,f,delta_g,delta_b,delta_x,delta_t) ”,
                                                                     
gvs[ret_status_typed_def] >>
REPEAT STRIP_TAC >>
gvs[] >>
IMP_RES_TAC status_ret_in_stmtl_typed_verbose                                                    
);





val t_lookup_passed_b_lemma  =  prove (“
 ∀ f delta_b delta_g delta_x passed_delta_b tau tau' txdl txdl' . 
t_map_to_pass f delta_b = SOME passed_delta_b ∧
t_lookup_funn f delta_g passed_delta_b delta_x = SOME (txdl ,tau ) ∧
t_lookup_funn f delta_g delta_b delta_x        = SOME (txdl',tau') ⇒
(txdl = txdl' ∧ tau = tau') ”,
REPEAT STRIP_TAC >>    
Cases_on ‘f’ >>
gvs[t_map_to_pass_def, t_lookup_funn_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) 
 );                     



val lookup_funn_sig_body_passed_lemma = prove (“
∀ f  func_map b_func_map b_func_map' ext_map stmt xdl.
map_to_pass f b_func_map = SOME b_func_map' ∧
SOME (stmt,xdl) = lookup_funn_sig_body f func_map b_func_map ext_map ⇒
SOME (stmt,xdl) = lookup_funn_sig_body f func_map b_func_map' ext_map ”,
REPEAT STRIP_TAC >>    
Cases_on ‘f’ >>
gvs[map_to_pass_def, lookup_funn_sig_body_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) 
);

        



Theorem assign_in_global_typed_output:
∀ tslg gscl gscl' f tau v.
type_scopes_list gscl tslg ∧
v_typ v (t_tau tau) F ∧                
SOME tau = find_star_in_globals tslg (varn_star f) ∧
SOME gscl' = assign gscl v (lval_varname (varn_star f)) ⇒
type_scopes_list gscl' tslg
Proof

REPEAT STRIP_TAC >>
gvs[find_star_in_globals_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
              
gvs[assign_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
gvs[lookup_out_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>

ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:(v#lval option)``,
                       ``:'b`` |-> ``:(tau#lval option)``] R_lookup_map_scopesl)  >>

LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL  [`(λ(v,lop1) (t,lop2). v_typ v (t_tau t) F ∧ lop1 = lop2)`, `(x)`, `(varn_star f)`, `(q',r')`,
                                             `tslg`, `gscl`])) >>
gvs[] >>
‘similarl (λ(v,lop1) (t,lop2). v_typ v (t_tau t) F ∧ lop1 = lop2) gscl tslg’ by  gvs[type_scopes_list_def, similarl_def]  >>
gvs[] >>

REPEAT STRIP_TAC >>
fs[AUPDATE_def] >>
CASE_TAC >> gvs[]  >| [
 IMP_RES_TAC find_topmost_map_not_none
 ,    
 ASSUME_TAC  AFUPDKEY_in_scopelist_typed >>
 PairCases_on ‘x’ >>
 PairCases_on ‘x'’ >>            
 gvs[] >>
 LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`tslg`, `v`, `q'`, `x0`,
                                             `r'`, `(varn_star f)`, ‘gscl’, ‘q’, ‘r’, ‘r'’])) >> gvs[] >>

 IMP_RES_TAC find_general_lemma >>
 LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘(x'0,x'1)’, ‘r’])) >> gvs[]
      
]
QED




val ret_status_stmt_len_single_lemma = prove (
“∀ c ascope ascope' gscope gscope' f stmt stmt_stack v framel locale locale'.
stmt_red c (ascope,gscope,[(f,[stmt],locale)],status_running)
           (ascope',gscope,[(f,stmt_stack,locale')], status_returnv v) ⇒
LENGTH stmt_stack = 1 ”,
REPEAT STRIP_TAC >>
gvs[Once stmt_red_cases]
);

        
Theorem ret_status_stmt_len_lemma:
∀ c ascope ascope' gscope gscope' f stmt_stack stmt_stack' v framel locale locale'.
stmt_red c (ascope,gscope,[(f,stmt_stack,locale)],status_running)
           (ascope',gscope,[(f,stmt_stack',locale')], status_returnv v) ⇒
LENGTH stmt_stack = LENGTH stmt_stack'
Proof
REPEAT STRIP_TAC >>
gvs[Once stmt_red_cases] >>
gvs[ADD1] >>
IMP_RES_TAC ret_status_stmt_len_single_lemma
QED
        
   









                                      

val lval_typ_any_order_f = prove (
“∀ order order' funn funn'  delta l tau  tslg tsl h.
lval_typ (tslg,tsl) ( order , funn   , delta ) l (t_tau tau) ⇒
lval_typ (tslg,tsl) ( order' , funn' , delta ) l (t_tau tau) ”,

Induct_on ‘l’ >> gvs[] >>
REPEAT STRIP_TAC >>
SIMP_TAC list_ss [Once lval_typ_cases] >| [
  OPEN_LVAL_TYP_TAC “(lval_varname v)” >>
  gvs[Once e_typ_cases] >>
  gvs[Once e_typ_cases] >>
  srw_tac [SatisfySimps.SATISFY_ss][] 
  ,         
  OPEN_LVAL_TYP_TAC “lval_null” >> gvs[]
  ,

  OPEN_LVAL_TYP_TAC “lval_field l s” >> gvs[] >>
  METIS_TAC []
  ,
  OPEN_LVAL_TYP_TAC “(lval_slice l e0 e)” >> gvs[] >>
  METIS_TAC []
  ,
  OPEN_LVAL_TYP_TAC “(lval_paren l)” >> gvs[] >>
  METIS_TAC []     
  ]
);















val local_sc_same_stmt1 = prove (“
∀c ascope ascope' gscope funn stmt stmt_stack' scope_list scope_list' status
       status' copied_in_scope stmt_called f_called.
     stmt_red c (ascope,gscope,[(funn,[stmt],scope_list)],status)
       (ascope',gscope,
        [(f_called,[stmt_called],copied_in_scope); (funn,stmt_stack',scope_list')],status') ⇒
     scope_list' = scope_list   ”,

Induct_on ‘stmt’ >>
REPEAT STRIP_TAC >>
OPEN_ANY_STMT_RED_TAC “anystmt” >>
gvs[] >>
METIS_TAC []
);


val local_sc_same_stmt2 = prove (“
∀c ascope ascope' gscope funn stmt stmt' scope_list scope_list' status
       status' copied_in_scope stmt_called f_called stmt_stack .
stmt_red c (ascope,gscope,[(funn,[stmt],scope_list)],status_running)
           (ascope',gscope, [(f_called,[stmt_called],copied_in_scope); (funn,stmt_stack ⧺ [stmt'],scope_list')],status_running) ⇒
scope_list' = scope_list  ”,

Induct_on ‘stmt’ >>
REPEAT STRIP_TAC >>
OPEN_ANY_STMT_RED_TAC “anystmt” >>
gvs[] >>
METIS_TAC []
);

        
val local_sc_same_stmtl = prove (“               
∀ c ascope ascope' gscope funn stmtl stmtl' scope_list scope_list' status status'
copied_in_scope stmt_called f_called. 
stmt_red  c
          (ascope,gscope,[(funn,stmtl,scope_list)],status)
          (ascope',gscope,
           [(f_called,[stmt_called],copied_in_scope); (funn,stmtl',scope_list')],status') ⇒
scope_list' = scope_list  ”,

REPEAT STRIP_TAC >>
gvs[Once stmt_red_cases] >>
gvs[] >>
IMP_RES_TAC local_sc_same_stmt2>>
IMP_RES_TAC local_sc_same_stmt1
);






val frame_typ_tsll_lemma = prove (“
∀ tslg tsll tsll' T_e Prs_n gscope scl stmtl' stmt_stack.
frame_typ (tslg,tsll' ++ tsll) T_e  Prs_n gscope scl stmtl' ∧
frame_typ (tslg,         tsll) T_e  Prs_n gscope scl stmt_stack ⇒
tsll' = []”,

REPEAT STRIP_TAC >>
gvs[frame_typ_cases, type_frame_tsl_def] >>
IMP_RES_TAC type_scopes_list_detr >>
gvs[]
);
        


        
Theorem frame_typ_local_LENGTH:
∀ tslg tsl T_e Prs_n gscope locale stmtl .
frame_typ (tslg,tsl) T_e Prs_n gscope locale stmtl ⇒
 LENGTH locale > 0 ∧ stmtl ≠ [] ∧ LENGTH tsl = LENGTH locale
Proof
REPEAT STRIP_TAC >>
gvs[frame_typ_cases, stmtl_typ_cases, type_ith_stmt_def, type_frame_tsl_def] >>
IMP_RES_TAC type_scopes_list_LENGTH >>
Cases_on ‘stmtl’ >> gvs[]
QED





        
val tsc_consistency_ci = prove (“           
∀ delta_g delta_b delta_t delta_x passed_delta_b passed_delta_t passed_delta_b' passed_delta_t'
  tsll funn funnl f_called tslg passed_tslg passed_tslg' ci_tscl order .
LENGTH tsll = LENGTH (funn::funnl) ∧ 
LENGTH (HD tsll) > 0 ∧
            
t_scopes_consistent_list (funn::funnl) tsll tslg
                         (delta_g,delta_b,delta_x,delta_t) order ∧

t_scopes_to_pass funn delta_g delta_b tslg = SOME passed_tslg ∧
t_map_to_pass funn delta_b = SOME passed_delta_b ∧
t_tbl_to_pass funn delta_b delta_t = SOME passed_delta_t ∧
              
t_scopes_consistent (order,funn,delta_g,passed_delta_b,delta_x,passed_delta_t)
                    (HD tsll) passed_tslg ci_tscl ∧

t_passed_elem f_called delta_g passed_delta_b passed_delta_t
          passed_tslg = (SOME passed_delta_b',SOME passed_delta_t',SOME passed_tslg') ⇒
              
t_scopes_consistent_list (f_called::funn::funnl)
          (ci_tscl::HD tsll::TL tsll) tslg
          (delta_g,delta_b,delta_x,delta_t) order ”,

REPEAT STRIP_TAC >>
SIMP_TAC list_ss [t_scopes_consistent_list_def] >>
REPEAT STRIP_TAC >> gvs[] >>
Cases_on ‘i=0’ >> gvs[] >| [   
    gvs[t_passed_elem_def] 
    ,
    gvs[t_scopes_consistent_list_def] >>
    gvs[ADD1, PRE_SUB1] >>                                  
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘i-1’])) >>
    gvs[EL_CONS, PRE_SUB1] >>
    Cases_on ‘tsll’  >> gvs[] >>

             
    ‘i>0’ by gvs[] >>
    gvs[EL_PRE]
  ]
);




        
val tsc_consistency_blk = prove (“
∀ funnl tsll f tslg deltas order tscl_block.     
LENGTH (f::funnl) = LENGTH tsll ∧
LENGTH (HD tsll) > 0 ∧
t_scopes_consistent_list (f::funnl) tsll                              tslg deltas order ⇒
t_scopes_consistent_list (f::funnl) ((tscl_block ⧺ HD tsll)::TL tsll) tslg deltas order ”,

REPEAT STRIP_TAC >>
PairCases_on ‘deltas’ >>
gvs [t_scopes_consistent_list_def] >>
REPEAT STRIP_TAC >> gvs[] >>
Cases_on ‘i=0’ >> gvs[] >| [
      
    gvs[t_passed_elem_def]  >>
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘0’])) >> gvs[] >>
    gvs[t_scopes_consistent_def] >>
    
    gvs[t_scopes_consistent_def] >>
    REPEAT STRIP_TAC >>                             
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘x’, ‘t’, ‘lop’])) >> gvs[] >>
    Cases_on ‘tsll’ >> gvs[] >>
    Cases_on ‘h’ >> gvs[] >>
    gvs[LAST_APPEND_CONS]
       
    ,
    gvs[ADD1, PRE_SUB1] >>                                  
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘i’])) >>
    gvs[EL_CONS, PRE_SUB1] >>
    gvs[t_scopes_consistent_def] >>
    gvs[t_passed_elem_def] >>


    REPEAT STRIP_TAC >>
      FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘x’, ‘t’, ‘lop’])) >> gvs[] >>
    Cases_on ‘tsll’ >> gvs[] >>
    gvs[EL_PRE]     
  ]
);




val DROP_LAST1 = prove (
“∀ h .
LENGTH h > 1 ⇒
LAST (DROP 1 h) = (LAST h)”,

Induct >> REPEAT STRIP_TAC >>
gvs[] >>
Cases_on ‘h’ >> gvs[]
);
 





val tsc_consistency_blk_exit = prove ( “       
∀ funnl tsll f tslg delta_g delta_b delta_x delta_t order tscl_block.          
LENGTH (f::funnl) = LENGTH tsll ∧       
LENGTH (HD tsll) > 1 ∧
t_scopes_consistent_list (f::funnl) tsll tslg (delta_g,delta_b,delta_x,delta_t) order ⇒     
t_scopes_consistent_list (f::funnl) (DROP 1 (HD tsll)::TL tsll) tslg (delta_g,delta_b,delta_x,delta_t) order
”,
REPEAT STRIP_TAC >>
gvs [t_scopes_consistent_list_def] >>
REPEAT STRIP_TAC >> gvs[] >>
Cases_on ‘i=0’ >> gvs[] >| [
      
    gvs[t_passed_elem_def]  >>
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘0’])) >> gvs[] >>
    gvs[t_scopes_consistent_def] >>
    
    gvs[t_scopes_consistent_def] >>
    REPEAT STRIP_TAC >>                             
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘x’, ‘t’, ‘lop’])) >> gvs[] >>
    Cases_on ‘tsll’ >> gvs[] >>
    IMP_RES_TAC DROP_LAST1 >>
    gvs[] 
    ,
    gvs[ADD1, PRE_SUB1] >>                                  
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘i’])) >>
    gvs[EL_CONS, PRE_SUB1] >>
    gvs[t_scopes_consistent_def] >>
    gvs[t_passed_elem_def] >>


    REPEAT STRIP_TAC >>
      FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘x’, ‘t’, ‘lop’])) >> gvs[] >>
    Cases_on ‘tsll’ >> gvs[] >>
    gvs[EL_PRE]     
  ]
);



        
val tsc_consistency_comp2 = prove ( “
∀ funnl tsll f f' tslg delta_g delta_b delta_x delta_t order h t.          
t_scopes_consistent_list (f::f'::funnl) (h::t) tslg (delta_g,delta_b,delta_x,delta_t) order ⇒
t_scopes_consistent_list (   f'::funnl)     t  tslg (delta_g,delta_b,delta_x,delta_t) order          ”  ,                                           

REPEAT STRIP_TAC >>
gvs [t_scopes_consistent_list_def] >>
REPEAT STRIP_TAC >> gvs[] >>
gvs[ADD1, PRE_SUB1] >>                                  
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘i+1’])) >>
gvs[EL_CONS, PRE_SUB1] >>
gvs[t_scopes_consistent_def] >>
gvs[t_passed_elem_def] 
);

                               







val lookup_sig_map_lemma = prove (“
∀   f func_map b_func_map ext_map b_func_map' stmt stmt' xdl xdl'.                                
map_to_pass f b_func_map = SOME b_func_map' ∧
SOME (stmt',xdl') = lookup_funn_sig_body f func_map b_func_map' ext_map ∧
SOME (stmt,xdl) = lookup_funn_sig_body f func_map b_func_map ext_map ⇒
xdl' = xdl ∧ stmt = stmt' ”,

REPEAT STRIP_TAC >>
gvs[map_to_pass_def] >>
gvs[lookup_funn_sig_body_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) 
); 













val oDROP_gscope_only = prove (“
∀ gscope scl n .        
LENGTH gscope = 2 ∧
LENGTH gscope + LENGTH scl = n  ⇒       
oDROP (n − 2) (scl ⧺ gscope) = SOME gscope”,

REPEAT STRIP_TAC >>
gvs[oDROP_def]>>
METIS_TAC [oDROP_LENGTH_lemma1]
);
                                        



val oTAKE_scl_only = prove ( “
∀ scl tscl n gscope. 
LENGTH scl + 2 =  n ∧
type_frame_tsl scl tscl ⇒
type_state_tsll [THE (oTAKE ( n − 2) (scl ⧺ gscope))] [tscl]”,


REPEAT STRIP_TAC >>
gvs[type_state_tsll_def] >>
REPEAT STRIP_TAC  >> lfs[] >>
gvs[type_frame_tsl_def] >>  IMP_RES_TAC  type_scopes_list_LENGTH >> gvs[]>>
Cases_on ‘(oTAKE (LENGTH tscl) (scl ⧺ gscope))’ >> gvs[] >>
METIS_TAC[oTAKE_is_not_empty,  oTAKE_LENGTH_lemma1]
);




        



val t_sig_tsc_abstraction = prove (“
∀ f delta_g delta_b delta_x txdl tau scl.
t_lookup_funn f delta_g delta_b delta_x = SOME (txdl,tau) ∧    
sig_tscope_consistent f delta_g delta_b delta_x scl ⇒

∀ tl xl dl varnl tl' lol .  
(
extract_elem_tri txdl       = (tl,xl,dl) ∧
extract_elem_tri (LAST scl) = (varnl,tl',lol) ⇒
mk_varn xl = varnl ∧ tl = tl' ∧ out_lval_consistent lol dl
)” ,


REPEAT STRIP_TAC >>
gvs[sig_tscope_consistent_def]
);







Theorem co_none:
∀ xdl scope_list'' x.
       ~ (FOLDL
          (λss_temp_opt (x,d).
               if is_d_none_in d then ss_temp_opt
               else
                 case ss_temp_opt of
                   NONE => NONE
                 | SOME ss_temp =>
                   case lookup_map [LAST scope_list''] (varn_name x) of
                     NONE => NONE
                   | SOME (v5,NONE) => NONE
                   | SOME (v5,SOME str) => assign ss_temp v5 str) NONE
          (xdl) =
        SOME x)
Proof        
Induct_on `xdl` >>
fs[] >>
REPEAT GEN_TAC >>
PairCases_on `h` >> gvs[]
QED
                



val oTAKE_oDROP_l = prove ( “
∀ l i a b .
LENGTH l > 1 ∧
LENGTH l − 2 = i ∧
SOME a = oTAKE (i) l ∧
SOME b = oDROP (i) l ⇒
l = a ⧺ b ”,

reverse (
  Induct >>            
  Induct_on ‘i’ ) >- (

  REPEAT STRIP_TAC >>
  gvs[oDROP_def, oTAKE_def] >>

         
Cases_on ‘oTAKE i l’ >> gvs[] >>        
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘x’, ‘b’])) >> gvs[] >>
            
‘i = LENGTH l − 2’ by gvs[] >>

subgoal  ‘SOME x = oTAKE (LENGTH l − 2) l’ >- METIS_TAC [] >>
  gvs[] >>
  
ASSUME_TAC oDROP_lemma >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘l’, ‘LENGTH l − 1’, ‘h’  ])) >> gvs[] >>
           
   
gvs[ADD1] >>

ASSUME_TAC oDROP_lemma >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘l’, ‘LENGTH l − 1’, ‘h’  ])) >> gvs[] ) >>

gvs[oTAKE_def] >> 
REPEAT STRIP_TAC >> gvs[] >>
gvs[ADD1] >>

gvs[oDROP_def]
);


               



Theorem separate_abstract:
∀ l a b .
 LENGTH l > 1 ∧ 
(SOME b,SOME a) = separate l ⇒
l = a++b
Proof
REPEAT STRIP_TAC >>
gvs[separate_def, ADD1, oDROP_def, oTAKE_def] >>
gvs[oTAKE_oDROP_l]
QED        








Theorem type_scopes_list_LAST:
∀ scl tsc .
LENGTH  scl > 0 ∧ 
type_scopes_list scl tsc ⇒
type_scopes_list [LAST scl] [LAST tsc]
Proof
gvs[type_scopes_list_def] >>
gvs[similarl_def, similar_def] >>
Induct_on ‘scl’ >>
Induct_on ‘tsc’ >>
REPEAT STRIP_TAC >> gvs[LAST_DEF] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
Cases_on ‘scl’ >> gvs[]
QED


val star_not_in_sl_LAST = prove (“
∀ scl.
LENGTH  scl > 0 ∧   
star_not_in_sl scl ⇒
star_not_in_sl [LAST scl]”,

Induct >-                     
gvs[] >>

gvs[star_not_in_sl_def, LAST, star_not_in_s_def, ALOOKUP_def] >>
REPEAT STRIP_TAC >>
RES_TAC >>
Cases_on ‘scl’ >> gvs[]
);


          
val type_frame_tsl_LAST = prove (“
∀ scl tsc .
LENGTH  scl > 0 ∧ 
type_frame_tsl scl tsc ⇒
type_frame_tsl [LAST scl] [LAST tsc]”,

gvs[type_frame_tsl_def,star_not_in_sl_LAST, type_scopes_list_LAST]
);





val lookup_map_LAST_typed = prove (“
∀ scl tsc varn v lval.
LENGTH scl > 0 ∧
type_frame_tsl scl tsc ∧
lookup_map [LAST scl] (varn) = SOME (v,SOME lval) ⇒
∃t. lookup_map [LAST tsc] (varn) = SOME (t,SOME lval) ∧
    v_typ v (t_tau t) F ”,


REPEAT STRIP_TAC >>
IMP_RES_TAC type_frame_tsl_LAST >>
gvs[type_frame_tsl_def, type_scopes_list_def] >>
 IMP_RES_TAC R_implies_lookup_map_scopesl >>
 LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`varn`, `(v,SOME lval)`])) >>
 gvs[] >> PairCases_on ‘v'’ >> gvs[] >>
 Q.EXISTS_TAC ‘v'0’ >> gvs[]
);




val lookup_map_single_LENGTH = prove (“
∀ l varn tup.
lookup_map [l] varn = SOME tup ⇒
LENGTH l > 0   ”,

gvs[lookup_map_def, topmost_map_def, find_topmost_map_def] >>
Induct >> REPEAT STRIP_TAC >> gvs[] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
gvs[INDEX_FIND_EQ_SOME_0] >>
‘q=0’ by simp [] >> lfs[] 
);




        
         

Theorem lookup_map_single_LAST_ALOOKUP:
∀ l varn tup.
LENGTH l > 0 ∧  
lookup_map [LAST l] varn = SOME tup ⇒
ALOOKUP    (LAST l) varn = SOME tup
Proof

Induct >>      
gvs[lookup_map_def, topmost_map_def, find_topmost_map_def] >>
Induct >> REPEAT STRIP_TAC >> gvs[] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[LAST]) >>
gvs[INDEX_FIND_EQ_SOME_0] >>                         
‘q=0’ by simp [] >> lfs[]                                         
QED



val oDROP_LENGTH = prove ( “   
∀ l i a.       
SOME a = oDROP i l ⇒
LENGTH a = LENGTH l - i”,

Induct >>
Induct_on ‘i’ >>
gvs[oDROP_def]
);



val oTAKE_LENGTH = prove ( “   
∀ l i a.       
SOME a = oTAKE i l ⇒
LENGTH a = i”,

Induct >>
Induct_on ‘i’ >>
gvs[oTAKE_def] >>
REPEAT STRIP_TAC >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[])
);

        

Theorem separate_result_LENGTH:
 ∀ scopest gscope scope_list.
  (SOME gscope,SOME scopest) = separate scope_list ⇒
  LENGTH scope_list = LENGTH gscope + LENGTH scopest
Proof  

gvs[separate_def] >>
REPEAT STRIP_TAC >>

IMP_RES_TAC oTAKE_LENGTH >>
IMP_RES_TAC oDROP_LENGTH  >>
gvs[]
QED
  






Theorem copyout_assign_exists:
∀ curr_local pre_local h h' T_e x v lval tslg gscope .
      
LENGTH curr_local > 0 ∧
LENGTH pre_local ≥ 1 ∧
LENGTH gscope = 2 ∧

type_frame_tsl pre_local h ∧
type_frame_tsl curr_local h' ∧
type_scopes_list gscope tslg ∧
          
(∀x t' lop.
          ALOOKUP (LAST h') x = SOME (t',SOME lop) ⇒
          lval_typ (tslg,h) T_e  lop (t_tau t')) ∧

lookup_map [LAST curr_local] (varn_name x) = SOME (v,SOME lval)  ⇒

∃ assigned_sc scopest_sep gscope_sep.
                 assign (pre_local ⧺ gscope) v lval = SOME (assigned_sc) ∧
                 (SOME gscope_sep,SOME scopest_sep) = separate (assigned_sc) ∧
                  assigned_sc =   scopest_sep ++ gscope_sep ∧
                  type_scopes_list scopest_sep h ∧
                  type_scopes_list gscope_sep tslg ∧
                  star_not_in_sl scopest_sep ∧
                  LENGTH assigned_sc =  LENGTH pre_local + LENGTH gscope              
Proof
REPEAT STRIP_TAC >>
gvs[] >>

‘∃ t . lookup_map [LAST h'] (varn_name x) = SOME (t,SOME lval) ∧ v_typ v (t_tau t) F ’ by (IMP_RES_TAC lookup_map_LAST_typed >> gvs[] ) >>    
subgoal ‘ALOOKUP (LAST h') (varn_name x) = SOME (t,SOME lval)’ >- (IMP_RES_TAC lookup_map_single_LAST_ALOOKUP >>
                                                                   gvs[type_frame_tsl_def] >>
                                                                   IMP_RES_TAC type_scopes_list_LENGTH >> gvs[]  ) >>
RES_TAC >>
IMP_RES_TAC v_types_ev >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘tslg’, ‘h’, ‘T_e’])) >>

            
ASSUME_TAC assignment_scope_exists >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘pre_local’,‘gscope’,‘h’,‘tslg’,‘t’,‘F’,‘lval’,‘v’,‘T_e’])) >>
gvs[] >>

gvs[type_frame_tsl_def] >>
ASSUME_TAC assign_e_is_wt>>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘lval’, ‘pre_local’, ‘h’,  ‘gscope’, ‘tslg’, ‘T_e’, ‘scopest'’, ‘gscope'’,
                                            ‘t’, ‘F’ ,‘scope_list'’ ,‘v’])) >>
gvs[] >>

‘LENGTH tslg = 2’ by (IMP_RES_TAC type_scopes_list_LENGTH >> gvs[]) >>
gvs[] >>

qexistsl_tac [‘scopest'’,‘gscope'’] >>
gvs[] >>


subgoal ‘LENGTH scope_list' > 1’ >- (
  IMP_RES_TAC separate_result_LENGTH >>    
  IMP_RES_TAC type_scopes_list_LENGTH >> gvs[]
  ) >>

      
‘scopest' ++ gscope'= scope_list'’ by (IMP_RES_TAC separate_abstract >> gvs[]) >>
 gvs[] >>                       
IMP_RES_TAC type_scopes_list_LENGTH >> gvs[]
QED



                             
                
 
   
val co_FOLDL_typed = prove (“
∀ xdl h h' T_e tslg n x curr_local pre_local gscope.
  LENGTH tslg = 2 ∧
   LENGTH curr_local > 0 ∧ LENGTH pre_local ≥ 1 ∧      
  type_frame_tsl curr_local h ∧
  type_frame_tsl pre_local h' ∧
  type_scopes_list gscope tslg ∧
     t_scopes_consistent T_e h' tslg h ∧
     FOLDL
       (λss_temp_opt (x,d).
            if is_d_none_in d then ss_temp_opt
            else
              case ss_temp_opt of
                NONE => NONE
              | SOME ss_temp =>
                case lookup_map [LAST curr_local] (varn_name x) of
                  NONE => NONE
                | SOME (v5,NONE) => NONE
                | SOME (v5,SOME str) => assign ss_temp v5 str)
       (SOME (pre_local ⧺ gscope)) (xdl) =
     SOME x ∧ LENGTH x = SUC n ⇒
     type_scopes_list (THE (oDROP (SUC n − 2) x)) tslg ∧
     type_state_tsll [THE (oTAKE (SUC n − 2) x)] [h']”,

                                 
Induct >> REPEAT GEN_TAC >>
STRIP_TAC >- (
  gvs[] >>
  IMP_RES_TAC type_scopes_list_LENGTH >> gvs[] >>
  gvs[oDROP_gscope_only, oTAKE_scl_only ]) >>

PairCases_on ‘h’ >> gvs[] >>

(* Cases_on the direction *)
Cases_on ‘is_d_none_in h1’ >> gvs[] >| [
  (* use the IH directly here *)
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘h'’, ‘h''’, ‘T_e’, ‘tslg’, ‘n’, ‘x’, ‘curr_local’, ‘pre_local’, ‘gscope’ ])) >>
  gvs[]
  ,
  gvs[] >>    
  Cases_on ‘lookup_map [LAST curr_local] (varn_name h0)’ >> gvs[] >| [
    (* show that it is impossible that the arg is out, inout *)
    IMP_RES_TAC  co_none
    ,
    gvs[t_scopes_consistent_def] >>
    PairCases_on ‘x'’ >> gvs[] >>
    Cases_on ‘x'1’ >> gvs[] >| [
      IMP_RES_TAC co_none
      ,
              
      subgoal ‘∃ assigned_sc scopest_sep gscope_sep.
                 assign (pre_local ⧺ gscope) x'0 x' = SOME (assigned_sc) ∧
                 (SOME gscope_sep,SOME scopest_sep) = separate (assigned_sc) ∧
                 assigned_sc =   scopest_sep ++ gscope_sep ∧
                 type_scopes_list scopest_sep h'' ∧
                 type_scopes_list gscope_sep tslg ∧
                 star_not_in_sl scopest_sep ∧
                 LENGTH assigned_sc =  LENGTH pre_local + LENGTH gscope ’ >-(
        ASSUME_TAC copyout_assign_exists >> 
        FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘curr_local’, ‘pre_local’, ‘h''’,‘h'’, ‘T_e’, ‘h0’,‘x'0’, ‘x'’, ‘tslg’, ‘gscope’])) >>
        gvs[] >> IMP_RES_TAC type_scopes_list_LENGTH >> gvs[] >> METIS_TAC []
        ) >>
      
      FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [ ‘h'’, ‘h''’, ‘T_e’, ‘tslg’, ‘n’,‘x’, ‘curr_local’, ‘scopest_sep’, ‘gscope_sep’])) >>
      gvs[] >>
      RES_TAC >>
      
      
      fs[type_frame_tsl_def] >> gvs[] >>
      IMP_RES_TAC type_scopes_list_LENGTH >> gvs[]       
      ]       
    ]    
  ]
);                                       




val t_scopes_to_pass_len = prove (“
∀ f delta_g delta_b tslg passed_tslg .
LENGTH tslg = 2 ∧
t_scopes_to_pass f delta_g delta_b tslg = SOME passed_tslg ⇒
LENGTH passed_tslg = 2”,

gvs[t_scopes_to_pass_def] >>
REPEAT STRIP_TAC >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[])
);
                                         

                                         

(* copy out is well typed
   passed_tslg here means the previous functions passed global scope *)
val co_is_welltyped = prove (“
∀ curr_local pre_local passed_gscope passed_tslg h t xdl co_local co_global T_e .         
LENGTH curr_local > 0 ∧
LENGTH pre_local ≥ 1 ∧
LENGTH passed_tslg = 2 ∧

type_scopes_list passed_gscope passed_tslg ∧
type_frame_tsl curr_local h ∧
type_frame_tsl pre_local (HD t) ∧

t_scopes_consistent T_e (HD t) passed_tslg h ∧
          
SOME (co_global,co_local) = copyout (MAP (λ(x_,d_). x_) xdl) (MAP (λ(x_,d_). d_) xdl) passed_gscope pre_local curr_local
                ⇒
        type_state_tsll [co_local] [HD t] ∧
        type_scopes_list co_global passed_tslg ”,

REPEAT GEN_TAC >> STRIP_TAC >>                              
gvs[copyout_def] >>
Cases_on ‘ update_return_frame (MAP (λ(x_,d_). x_) xdl)
            (MAP (λ(x_,d_). d_) xdl) (pre_local ⧺ passed_gscope)
            [LAST curr_local]’ >> gvs[] >>
Cases_on ‘LENGTH x’ >> gvs[] >>

gvs[update_return_frame_def] >>
        
ASSUME_TAC co_FOLDL_typed >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘(ZIP (MAP (λ(x_,d_). x_) xdl,MAP (λ(x_,d_). d_) xdl))’, ‘h’, ‘HD t’, ‘T_e’, ‘passed_tslg’,
                                           ‘n’,‘x’, ‘curr_local’, ‘pre_local’, ‘passed_gscope’ ])) >>
gvs[]
);




        


(******************)


Theorem co_typed_verbose_final:
   ∀gscope funn pre_funn init_scope_list pre_local stmt_stack stmt_stack'
       frame_list Prs_n order tslg delta_g delta_b delta_x delta_t func_map
       b_func_map passed_delta_b passed_delta_t co_scope co_gscope h t
       passed_tslg tslg_passed pre_passed_gscope g_scope_list' curr_local
       stmt_stack'' xdl.
     LENGTH passed_tslg = 2 ∧ LENGTH tslg = 2 ∧
     type_frames gscope
       ((funn,stmt_stack,init_scope_list)::(pre_funn,stmt_stack',pre_local)::
            frame_list) Prs_n order tslg (h::t) delta_g delta_b delta_x
       delta_t func_map b_func_map ∧
     t_scopes_consistent_list
       (funn::pre_funn::MAP (λ(al_,bl_,cl_). al_) frame_list) (h::t) tslg
       (delta_g,delta_b,delta_x,delta_t) order ∧
     frame_typ (passed_tslg,h)
       (order,funn,delta_g,passed_delta_b,delta_x,passed_delta_t) Prs_n
       g_scope_list' curr_local stmt_stack'' ∧
     type_state_tsll
       (init_scope_list::pre_local::MAP (λ(al_,bl_,cl_). cl_) frame_list)
       (h::t) ∧
     SOME (co_gscope,co_scope) =
     copyout (MAP (λ(x_,d_). x_) xdl) (MAP (λ(x_,d_). d_) xdl)
       pre_passed_gscope pre_local curr_local ∧
     type_scopes_list pre_passed_gscope tslg_passed ∧
     t_scopes_to_pass pre_funn delta_g delta_b tslg = SOME tslg_passed ⇒
     type_scopes_list co_gscope tslg_passed ∧
     type_state_tsll [co_scope] [HD t]
Proof


REPEAT GEN_TAC >>                                   
STRIP_TAC >>

(* get lengths info *)                         
IMP_RES_TAC frame_typ_local_LENGTH >>
 
‘LENGTH pre_local >= 1 ’ by ( gvs[type_frames_def] >>
                              FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘1’])) >>  gvs[] >>
                              IMP_RES_TAC frame_typ_local_LENGTH >> gvs[]
                                ) >>

    
(* get sig_tscope_consistent between funn and pre_funn  *)                       
gvs[frame_typ_cases] >>
Cases_on ‘t_lookup_funn funn delta_g passed_delta_b delta_x’ >>   gvs[] >>

gvs[t_scopes_consistent_list_def] >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘0’])) >>  gvs[] >>
gvs[t_passed_elem_def] >>
            

(* prove that scope_list' is typed with HD t *)              
gvs[type_frames_def] >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘1’])) >>  gvs[] >>
gvs[t_passed_elem_def] >>
gvs[frame_typ_cases] >>
      
subgoal ‘LENGTH passed_tslg' = 2 ’ >- ( IMP_RES_TAC t_scopes_to_pass_len >> gvs[]) >>


ASSUME_TAC co_is_welltyped >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘curr_local’,‘pre_local’,‘pre_passed_gscope’,‘passed_tslg'’,‘h’,‘t’,‘xdl’, ‘co_scope’,‘co_gscope’,
                                               ‘(order,pre_funn,delta_g,passed_delta_b',delta_x,passed_delta_t')’])) >>
gvs[]
QED















   


                               
            
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
      ‘type_frame_tsl scope_list' (t_scope_list'' ⧺ HD tsll) ’ by fs[Once frame_typ_cases]  >>
      ‘type_state_tsll (MAP (λ(f,stmt,sc). sc) t) (TL tsll)’ by IMP_RES_TAC WT_state_imp_tl_tsll >>
      IMP_RES_TAC type_tsll_hd_hd_l
      ) >> gvs[] >>
     



                 
     (* prove that the retrived scope can stilll be typed with the original tslg *)
     subgoal ‘type_scopes_list gscope' tslg ’ >-
      (
     ‘type_scopes_list gscope tslg’ by (gvs[WT_state_cases] )   >> 
     ‘type_scopes_list g_scope_list'' passed_tslg’ by fs[Once frame_typ_cases] >>
     ‘dom_b_eq delta_b b_func_map ∧ dom_g_eq delta_g func_map ∧
      dom_tmap_ei delta_g delta_b ∧ LENGTH tslg = 2’ by gvs[WT_c_cases] >>
     IMP_RES_TAC scopes_to_ret_is_wt
      ) >> gvs[] >>



                        
     gvs[GSYM ZIP_tri_id2] >>
              (* the sub proofs above are done not using this info below*)
     ‘g_scope_list' = g_scope_list''’ by IMP_RES_TAC create_frame_in_stmt_same_g3 >>
     rfs[] >> gvs[] >>           

     CONJ_TAC >| [
              
       (* i need to know that the locals of the initial frame are unchanged, otherwise we can not prove the consistency*) 
       ‘scope_list' = scope_list ’ by ( IMP_RES_TAC local_sc_same_stmtl >> gvs[] ) >>
       gvs[] >>
       (* we need to show that evern after the transition there will be no t_scope_list'', it should be empty *)
       ‘t_scope_list'' = [] ’ by IMP_RES_TAC frame_typ_tsll_lemma >> gvs[] >>
       
       ‘LENGTH (HD tsll) > 0 ’ by (IMP_RES_TAC frame_typ_local_LENGTH >>gvs[]) >>  
       
       gvs[Once WT_state_cases] >>
       gvs[Once res_frame_typ_def] >>
       gvs[] >>
       
       ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:funn``, ``:'b`` |-> ``:stmt list``, ``:'c`` |-> ``:scope_list``] ZIP_tri_sep_ind)  >>
       FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘t’,‘funnl’,‘stmtll’,‘scll’, ‘funn’,‘stmt_stack’,‘scope_list’])) >> gvs[] >>
       
       IMP_RES_TAC tsc_consistency_ci >> gvs[ADD1]
       ,        
       IMP_RES_TAC WT_state_of_largest_possible_frame        
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
      ‘type_frame_tsl scope_list' (t_scope_list'' ⧺ HD tsll) ’ by fs[Once frame_typ_cases]  >>
      ‘type_state_tsll (MAP (λ(f,stmt,sc). sc) t) (TL tsll)’ by IMP_RES_TAC WT_state_imp_tl_tsll >>
      IMP_RES_TAC type_tsll_hd_l
      ) >> gvs[] >>
                       
     subgoal ‘type_scopes_list gscope' tslg ’ >-
      (
      ‘type_scopes_list gscope tslg’ by (gvs[WT_state_cases] )   >> 
      ‘type_scopes_list g_scope_list'' passed_tslg’ by fs[Once frame_typ_cases] >>
      ‘dom_b_eq delta_b b_func_map ∧ dom_g_eq delta_g func_map ∧
      dom_tmap_ei delta_g delta_b ∧ LENGTH tslg = 2’ by gvs[WT_c_cases] >>
      IMP_RES_TAC scopes_to_ret_is_wt
      ) >> gvs[] >>
    

    
     (* to show that all the frames are well typed *)
     gvs[GSYM ZIP_tri_id2] >>
     drule WT_state_of_frame_and_tl >>
     STRIP_TAC >> 
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘passed_tslg’,  ‘b_func_map'’, ‘passed_delta_b’,
                                                 ‘passed_tbl_map’,‘passed_delta_t’, ‘t_scope_list''’, ‘gscope'’, ‘stmtl'’, ‘scope_list'’,
                                                 ‘g_scope_list'’, ‘g_scope_list''’])) >>
     gvs[] >>


     (* the typing lists consistencies*)

    ‘LENGTH (HD tsll) > 0 ’ by (IMP_RES_TAC frame_typ_local_LENGTH >>gvs[]) >>  
     gvs[Once WT_state_cases] >>

     ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:funn``, ``:'b`` |-> ``:stmt list``, ``:'c`` |-> ``:scope_list``] ZIP_tri_sep_ind)  >>
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘t’,‘funnl’,‘stmtll’,‘scll’, ‘funn’,‘stmt_stack’,‘scope_list’])) >> gvs[] >>
     gvs[GSYM ZIP_tri_id2] >>

     ASSUME_TAC tsc_consistency_blk >> 
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘MAP (λ(f,stmt,sc). f) (t:frame_list)’,  ‘tsll’, ‘funn’,
                                                 ‘tslg’,‘(delta_g,delta_b,delta_x,delta_t)’, ‘order’, ‘t_scope_list''’])) >>
     gvs[ADD1]
                
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
  ‘type_scopes_list gscope tslg’ by (gvs[WT_state_cases] )   >> 
  ‘type_frame_tsl scope_list' (DROP 1 (HD tsll)) ’ by fs[Once frame_typ_cases]  >>
  ‘type_state_tsll (MAP (λ(f,stmt,sc). sc) t) (TL tsll)’ by IMP_RES_TAC WT_state_imp_tl_tsll >>
  IMP_RES_TAC type_tsll_hd_l
  ) >> gvs[] >>
  

  subgoal ‘type_scopes_list gscope' tslg ’ >-
  (
  ‘type_scopes_list gscope tslg’ by (fs[WT_state_cases] )   >> 
   ‘type_scopes_list g_scope_list' passed_tslg’ by fs[Once frame_typ_cases] >>
   ‘dom_b_eq delta_b b_func_map ∧ dom_g_eq delta_g func_map ∧
    dom_tmap_ei delta_g delta_b ∧ LENGTH tslg = 2’ by gvs[WT_c_cases] >>
   IMP_RES_TAC scopes_to_ret_is_wt
   ) >> gvs[] >>
  
 
 gvs[GSYM ZIP_tri_id2] >>


 CONJ_TAC >| [
      ‘LENGTH (DROP 1 (HD tsll)) > 0 ’ by (IMP_RES_TAC frame_typ_local_LENGTH >>gvs[]) >>  
      gvs[Once WT_state_cases] >>
      
      ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:funn``, ``:'b`` |-> ``:stmt list``, ``:'c`` |-> ``:scope_list``] ZIP_tri_sep_ind)  >>
      FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘t’,‘funnl’,‘stmtll’,‘scll’, ‘funn’,‘stmt_stack’,‘scope_list’])) >> gvs[] >>
      gvs[GSYM ZIP_tri_id2] >>
      
      IMP_RES_TAC  tsc_consistency_blk_exit>>
      gvs[ADD1]
      ,        
      drule WT_state_of_blk_exit_and_tl >>
      REPEAT STRIP_TAC >>
      RES_TAC        
    ]                
 ]

 
,


        
 (* comp2 *)
 

 subgoal  ‘LENGTH (TL tsll) = LENGTH frame_list + 1’ >- (
   IMP_RES_TAC WT_state_frame_len >> 
   gvs[ADD1] >>
   Cases_on ‘tsll’ >>
   gvs[]
   ) >> gvs[] >>
 
  Q.EXISTS_TAC ‘TL tsll’ >>
  SIMP_TAC list_ss [WT_state_cases] >> gvs[] >>


  IMP_RES_TAC return_imp_same_g >> lfs[] >> gvs[] >>
  IMP_RES_TAC WT_state_HD_of_list >> gvs[] >>

 
  Q.EXISTS_TAC ‘ funn'::(MAP (\(f,stmt,sc).f ) frame_list)’ >>
  Q.EXISTS_TAC ‘scope_list'³'::(MAP (\(f,stmt,sc).sc ) frame_list)’ >>
  Q.EXISTS_TAC ‘stmt_stack'::(MAP (\(f,stmt,sc).stmt ) frame_list)’ >>
  gvs[ADD1] >>
  CONJ_TAC >-
   ( gvs[ELIM_UNCURRY] >> gvs[ZIP_tri_id1]) >>



 gvs[WT_state_cases] >>

    ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:funn``, ``:'b`` |-> ``:stmt list``, ``:'c`` |-> ``:scope_list``] ZIP_tri_sep_ind)  >>
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘(funn',stmt_stack',scope_list')::frame_list’,‘funnl’,‘stmtll’,‘scll’, ‘funn’,‘stmt_stack’,‘scope_list’])) >> gvs[] >>
    gvs[EL_CONS, PRE_SUB1] >> 
    Cases_on ‘tsll’ >> gvs[EL_CONS, PRE_SUB1] >>

              
         
 ‘WF_ft_order (funn'::MAP (λ(f,stmt,sc). f) frame_list) delta_g delta_b delta_x order’ by (
    IMP_RES_TAC WF_ft_order_imp_HD
   )>> gvs[] >>
  

   
   (* return status is well typed with respect to the return type *)
   subgoal ‘∃ tau tau_x_d_list . SOME (tau_x_d_list,tau) = t_lookup_funn funn delta_g passed_delta_b delta_x ∧
            v_typ v (t_tau tau) F ’ >- (
 
     ASSUME_TAC status_ret_in_stmtl_typed >>
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘stmt_stack’, ‘stmt_stack''’, ‘ascope’, ‘ascope'’, ‘g_scope_list'’, ‘g_scope_list'’,
                                                        ‘scope_list’, ‘scope_list''’, ‘[]’, ‘status_returnv v’, ‘h’, ‘passed_tslg’, ‘order’,
                                                        ‘delta_g’, ‘passed_delta_b’, ‘passed_delta_t’, ‘delta_x’, ‘funn’, ‘Prs_n’,
                                                        ‘(apply_table_f,ext_map,func_map,b_func_map',pars_map,passed_tbl_map)’])) >>
    gvs[ret_status_typed_def] >>                 
    gvs[frame_typ_cases] >>
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘tau’, ‘tau_x_d_list’])) >> gvs[] >>
    srw_tac [SatisfySimps.SATISFY_ss][]
   ) >>



  
  subgoal ‘SOME tau = find_star_in_globals tslg (varn_star funn)’ >- (
  IMP_RES_TAC Fg_star_lemma1 >>
  Cases_on ‘find_star_in_globals tslg (varn_star funn)’ >> gvs[] >>
  Cases_on ‘t_lookup_funn funn delta_g delta_b delta_x’ >> gvs[] >>
  Cases_on ‘t_lookup_funn funn delta_g delta_b delta_x’ >> gvs[] >>
  ASSUME_TAC t_lookup_passed_b_lemma >>
        
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘funn’, ‘delta_b’, ‘delta_g’,‘delta_x’, ‘passed_delta_b’, ‘tau’,‘tau'’,
                                              ‘tau_x_d_list’, ‘txdl’  ])) >>
  gvs[]
   ) >>


  subgoal ‘SOME tau = find_star_in_globals passed_tslg (varn_star funn)’ >- (
   IMP_RES_TAC lookup_funn_sig_body_passed_lemma >>
   IMP_RES_TAC Fg_star_lemma2 >>
   Cases_on ‘find_star_in_globals passed_tslg (varn_star funn)’ >> gvs[]
   ) >>


  subgoal ‘type_scopes_list  g_scope_list'³'  passed_tslg  ’ >- (
   IMP_RES_TAC assign_in_global_typed_output
   ) >>






  ‘LENGTH stmt_stack = LENGTH stmt_stack''’ by IMP_RES_TAC ret_status_stmt_len_lemma >>
             
  ASSUME_TAC SR_stmtl_stmtl >>
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`ty`,‘stmt_stack’])) >>
  gvs[sr_stmtl_def] >>     
 
 
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [
    `stmt_stack''`,‘ascope’,‘ascope'’, ‘g_scope_list'’,‘g_scope_list'’, ‘scope_list’,‘scope_list''’,
    ‘[]’,‘status_running’,‘status_returnv v’, ‘h’,‘passed_tslg’,
    ‘order’, ‘delta_g’, ‘passed_delta_b’, ‘passed_delta_t’, ‘delta_x’, ‘funn’,
    ‘Prs_n’, ‘0’, ‘apply_table_f’, ‘ext_map’, ‘func_map’, ‘b_func_map'’, ‘pars_map’, ‘passed_tbl_map’])) >> gvs[] >>
   gvs[] >>
 
 
  SIMP_TAC list_ss [WT_state_cases] >> gvs[] >>
  gvs[GSYM ZIP_tri_id2] >>

  ‘t_scopes_consistent_list
          (funn'::MAP (λ(al_,bl_,cl_). al_) frame_list) t tslg
          (delta_g,delta_b,delta_x,delta_t) order’ by (IMP_RES_TAC tsc_consistency_comp2 >> gvs[]) >> gvs[] >>


  (*simplify teh proof layout a bit? *)
   gvs[res_frame_typ_def] >>






  (* first we need to show that xdl and txdl that being copied out are the same *)
  subgoal ‘
  MAP (λ(t,x,d). d) tau_x_d_list = (MAP (λ(x,d). d) x_d_list) ∧
  MAP (λ(t,x,d). x) tau_x_d_list = (MAP (λ(x,d). x) x_d_list)’ >-  (
   IMP_RES_TAC tfunn_imp_sig_body_lookup >> RES_TAC >>
   Cases_on ‘lookup_funn_sig_body funn func_map b_func_map' ext_map’ >> gvs[] >>
   Cases_on ‘t_lookup_funn funn delta_g passed_delta_b delta_x’ >> gvs[] >>         
   IMP_RES_TAC  lookup_sig_map_lemma >> gvs[ELIM_UNCURRY, GSYM lambda_FST, GSYM lambda_SND]
   )>> gvs[] >>



(******************)



 (* first show that the first retrived scope is well typed with the original tslg *)

subgoal ‘ type_scopes_list  g_scope_list'⁴' tslg ’ >- (
     ‘dom_b_eq delta_b b_func_map ∧ dom_g_eq delta_g func_map ∧
      dom_tmap_ei delta_g delta_b ∧ LENGTH tslg = 2’ by gvs[WT_c_cases] >>
     IMP_RES_TAC scopes_to_ret_is_wt
   ) >>



 (* now show that when we pass the previous subgoal's scope, it has a type and we can find in in t_scope*)

subgoal ‘ ∃tslg_passed.
          t_scopes_to_pass funn' delta_g delta_b tslg = SOME tslg_passed ∧
          type_scopes_list g_scope_list'⁵' tslg_passed ’ >- (
   ‘dom_b_eq delta_b b_func_map ∧ dom_g_eq delta_g func_map ∧
    dom_tmap_ei delta_g delta_b ∧ LENGTH tslg = 2’ by gvs[WT_c_cases] >>
   ASSUME_TAC scopes_to_pass_imp_typed_lemma >>
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘g_scope_list'⁴'’, ‘tslg’, ‘funn'’,‘func_map’,‘b_func_map’, ‘delta_g’,‘delta_b’,‘g_scope_list'⁵'’])) >>
   gvs[]               
) >>



        
subgoal ‘type_scopes_list  g_scope_list'⁶' tslg_passed ∧
         type_state_tsll  [scope_list'³'] [(HD t)] ’ >- (

‘LENGTH tslg = 2 ∧ LENGTH passed_tslg = 2 ’ by  (gvs[WT_c_cases] >>
                                                 IMP_RES_TAC t_scopes_to_pass_len >> gvs[] ) >>
METIS_TAC[co_typed_verbose_final]) >>          



   
  subgoal ‘type_scopes_list gscope' tslg’ >-
      (
    ‘dom_b_eq delta_b b_func_map ∧ dom_g_eq delta_g func_map ∧
      dom_tmap_ei delta_g delta_b ∧ LENGTH tslg = 2’ by gvs[WT_c_cases] >>
     IMP_RES_TAC scopes_to_ret_is_wt     
      ) >> gvs[] >>


 ‘type_frame_tsl scope_list'³' (HD t) ’ by (gvs[type_state_tsll_def] >> 
                                            FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘0’])) >> gvs[]) >> 

      
 subgoal ‘type_state_tsll (scope_list'³'::MAP (λ(f,stmt,sc). sc) frame_list) t’ >-
 (

 ‘t≠[]’ by (Cases_on ‘t’ >> gvs[] ) >>     
 ‘type_frame_tsl scope_list'³' (HD t) ’ by (gvs[type_state_tsll_def] >> 
                                            FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘0’])) >> gvs[]) >> 
 ‘type_state_tsll (MAP (λ(f,stmt,sc). sc) frame_list) (TL t)’ by (REPEAT (IMP_RES_TAC type_state_tsll_normalization >> gvs[]) ) >>
 IMP_RES_TAC type_tsll_hd_l  >> Cases_on ‘t’ >> gvs[]

  ) >> gvs[] >>


  
 gvs[GSYM ZIP_tri_id2] >>

drule WT_state_of_copyout >> gvs[] >> REPEAT STRIP_TAC >> RES_TAC

 ]

QED
        





val _ = export_theory ();

