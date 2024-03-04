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
open p4_frames_subject_reductionTheory;
open p4_frames_progressTheory     


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



val _ = new_theory "p4_arch_sr_prog";





Theorem type_state_tsll_empty_lemma:
type_state_tsll [[[]]] [[[]]]
Proof
gvs[type_state_tsll_def] >>
Induct >> gvs[] >>                     
REPEAT STRIP_TAC >>    
gvs[type_state_tsll_def, type_frame_tsl_def, type_scopes_list_def,
    similarl_def, similar_def, LIST_REL_def, star_not_in_sl_def, star_not_in_s_def]
QED



 
                                
Theorem lookup_pb_in_db:                     
  ∀delta_g delta_b func_map b_func_map f sxdl ext_map delta_x order
       t_scope_list_g pars_map tbl_map apply_table_f delta_t Prs_n.
SOME sxdl = lookup_block_sig_body f b_func_map ∧
WT_c (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)
     order t_scope_list_g delta_g delta_b delta_x delta_t Prs_n  ⇒
(
(ALOOKUP func_map f = NONE /\
 ALOOKUP delta_g f = NONE /\        
ALOOKUP b_func_map f = SOME sxdl /\
 (?sig . ALOOKUP delta_b f = SOME sig) 
))
Proof
REPEAT GEN_TAC >> STRIP_TAC >>
gvs[Once WT_c_cases] >>
gvs[lookup_block_sig_body_def] >>
gvs[dom_b_eq_def, dom_g_eq_def, dom_eq_def, is_lookup_defined_def] >>
gvs[typying_domains_ei_def, dom_empty_intersection_def] >>
gvs[dom_tmap_ei_def, dom_map_ei_def, dom_empty_intersection_def] >>

                     
REPEAT (
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘f’])) >>      
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >> gvs[]
) >>

METIS_TAC []
QED


(*

∀ f delta_g delta_b delta_x .
sig_tscope_consistent (funn_name f) delta_g delta_b delta_x [[]]

REPEAT STRIP_TAC >>
gvs[sig_tscope_consistent_def] >>
REPEAT STRIP_TAC >>
gvs[extract_elem_tri_def] >>
gvs[mk_varn_def]

                                 




type_scopes_list g_scope_list' t_scope_list_g ∧
WT_c (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)
     order t_scope_list_g delta_g delta_b delta_x delta_t Prs_n ∧        
SOME (stmt,xdl) = lookup_block_sig_body f b_func_map ⇒     
type_frames g_scope_list' [(funn_name f,[stmt],[[]])] Prs_n order
          t_scope_list_g [[[]]] delta_g delta_b delta_x delta_t func_map b_func_map

REPEAT STRIP_TAC >>
IMP_RES_TAC lookup_pb_in_db >>

          
gvs[type_frames_def] >>
Induct >> gvs[] >>
gvs[Once frame_typ_cases, clause_name_def] >>
gvs[Once stmtl_typ_cases] >>
gvs[type_ith_stmt_def] >>


gvs[t_scopes_to_pass_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>

gvs[scopes_to_pass_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>

gvs[t_map_to_pass_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>

gvs[t_tbl_to_pass_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>

gvs[t_lookup_funn_def, clause_name_def] >> PairCases_on ‘sig’ >> gvs[]>>

gvs[star_not_in_sl_def, star_not_in_s_def] >>

SIMP_TAC list_ss [type_frame_tsl_def, type_scopes_list_def,
    similarl_def, similar_def, LIST_REL_def, star_not_in_sl_def, star_not_in_s_def] >>

gvs[args_t_same_def]

*)

















        
       

(* ================================================= *)
(*              well typed Envirounment              *)
(* ================================================= *)

val (WT_E_rules, WT_E_ind, WT_E_cases) = Hol_reln`
(
∀ ab_list copyin_pbl copyout_pbl ffblock_map input_f output_f pblock_map (apply_table_f:'a apply_table_f)
          (ext_map:'a ext_map) (func_map:func_map) (b_func_map:b_func_map) (pars_map:pars_map) (tbl_map:tbl_map)
          (order:order) (t_scope_list_g:t_scope_list_g) (deltas:delta) (Prs_n:Prs_n) i . 
       
  (      ∀ f el .
        EL i ab_list = arch_block_pbl f el ⇒
               ALOOKUP  pblock_map   f  = SOME  (pblock_regular pbl_type b_func_map t_scope pars_map tbl_map)
               ∧   
               (deltas = ( delta_g , delta_b , delta_x , delta_t ) ∧ 
                deltas_order delta_g delta_b delta_x order ∧
                WT_c (apply_table_f, ext_map, func_map, b_func_map, pars_map, tbl_map) order t_scope_list_g delta_g delta_b delta_x delta_t Prs_n
      )
   )  ∧




  (*            
  (EL i ab_list = arch_block_inp ∨
   EL i ab_list = arch_block_out ∨
   ∃ x .EL i ab_list = arch_block_ffbl x ∨
   ∃ x el .EL i ab_list = arch_block_pbl x el) ∧
   *)
    
   (*arch-in*)
  ((∀ in_out_list1 ascope . EL i ab_list = arch_block_inp ⇒
       SOME (in_out_list1', ascope') = input_f (in_out_list1,ascope)
  ) ∧


  (*arch-out*)
  (∀ in_out_list2 ascope . EL i ab_list = arch_block_out ⇒
       SOME (in_out_list2', ascope') = output_f (in_out_list2,ascope)
  ) ∧


 (*arch-ffb*)   
  (∀ x ascope. EL i ab_list = arch_block_ffbl x ⇒
   (ALOOKUP  ffblock_map   x  = SOME  (ffblock_ff ff) ∧
    SOME  ascope'  =  ff ascope
   )
  ) ∧
  
  
  (*arch-init*)
  (∀ x el ascope g_scope_list. EL i ab_list = arch_block_pbl x el ⇒   (*TODO: g_scope_list*)
     (ALOOKUP pblock_map x = SOME (pblock_regular pbl_type b_func_map t_scope pars_map tbl_map) ∧
      SOME (stmt,xdl) = lookup_block_sig_body x b_func_map ∧
      LENGTH el = LENGTH xdl ∧     
      SOME scope' = copyin_pbl  ( MAP FST xdl, MAP SND xdl, el, ascope) ∧
      scope''  = declare_list_in_scope (t_scope,scope') ∧
      g_scope_list' = LASTN 1 g_scope_list ∧
      g_scope_list'' =  [scope''] ++ g_scope_list') ∧
     SOME  g_scope_list''' = initialise_var_stars func_map b_func_map ext_map g_scope_list'' 
  ))



      
 ⇒
 WT_E order t_scope_list_g deltas Prs_n
      i (ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map )  
)
`;





        
(* ================================================= *)
(*               typing rules for arch               *)
(* ================================================= *)

val (WT_arch_rules, WT_arch_ind, WT_arch_cases) = Hol_reln`                         

(* NON empty arch frame *)
( 
∀  (ab_list:ab_list) (pblock_map:pblock_map) (ffblock_map:'a ffblock_map) (input_f:'a input_f) (output_f:'a output_f)
   (copyin_pbl:'a copyin_pbl) (copyout_pbl:'a copyout_pbl) (apply_table_f:'a apply_table_f) (ext_map:'a ext_map)
   (func_map:func_map) (i:i) (in_out_list1:in_out_list) (in_out_list2:in_out_list) (ascope:'a)
   (g_scope_list:g_scope_list) (Prs_n:Prs_n) (order:order) (t_scope_list_g:t_scope_list_g) (deltas:delta).


  type_scopes_list g_scope_list t_scope_list_g ∧ 
  EL i ab_list = arch_block_pbl f el ∧ (* this should always be in a pbl and has a mapping*)
  (ALOOKUP  pblock_map   f  = SOME  (pblock_regular pbl_type b_func_map t_scope pars_map tbl_map)) ∧        
  ( WT_state (apply_table_f, ext_map, func_map, b_func_map, pars_map, tbl_map) (ascope, g_scope_list, framel, status) Prs_n order t_scope_list_g  tsll deltas) ∧



  (   (*related to A-ret *)  
  (state_fin status framel ⇒
   SOME (stmt,xdl) = lookup_block_sig_body f b_func_map ∧
   status' = set_fin_status pbl_type status ∧
   LENGTH el = LENGTH xdl ∧
   SOME ascope' = copyout_pbl (g_scope_list,ascope,MAP SND xdl,MAP FST xdl,status'))
  ∧   (*related to A-trans *)  
  (∀x'. status = status_trans x' ∧ x' ≠ "accept" ∧ x' ≠ "reject" ⇒
               ALOOKUP pars_map x' = SOME stmt' ∧ pbl_type = pbl_type_parser)
  ∨
  status = status_running)
  
  
        
  
    
 ⇒
  (WT_arch
   Prs_n  order t_scope_list_g  tsll  deltas (* Γ ψll ψG *)
   ( ab_list , pblock_map , ffblock_map , input_f , output_f , copyin_pbl , copyout_pbl , apply_table_f , ext_map , func_map ) (*E*)
  ((i , in_out_list1 , in_out_list2 ,  ascope ) , g_scope_list , arch_frame_list_regular framel  , status) (*arch state*)
  
 )
)



        
∧


(* empty arch frame *)
        
( 
∀  (ab_list:ab_list) (pblock_map:pblock_map) (ffblock_map:'a ffblock_map) (input_f:'a input_f) (output_f:'a output_f)
   (copyin_pbl:'a copyin_pbl) (copyout_pbl:'a copyout_pbl) (apply_table_f:'a apply_table_f) (ext_map:'a ext_map)
   (func_map:func_map) (i:i) (in_out_list1:in_out_list) (in_out_list2:in_out_list) (ascope:'a)
   (g_scope_list:g_scope_list) (Prs_n:Prs_n) (order:order) (t_scope_list_g:t_scope_list_g) (deltas:delta).


  (*the status must be running*)
  status = status_running ∧
  type_scopes_list g_scope_list t_scope_list_g
                  
 ⇒
  (WT_arch
   Prs_n  order t_scope_list_g  tsll  deltas (* Γ ψll ψG *)
   ( ab_list , pblock_map , ffblock_map , input_f , output_f , copyin_pbl , copyout_pbl , apply_table_f , ext_map , func_map ) (*E*)
   ((i , in_out_list1 , in_out_list2 ,  ascope ) , g_scope_list , arch_frame_list_empty  , status) (*arch state*)
  )
        
)
  
`;





















        
(* ================================================= *)
(*           Subject reduction for arch              *)
(* ================================================= *)


val sr_arch_def = Define `
 sr_arch (framel) (ty:'a itself) =
∀  (ab_list:ab_list) (pblock_map:pblock_map) (ffblock_map:'a ffblock_map) (input_f:'a input_f) (output_f:'a output_f) (copyin_pbl:'a copyin_pbl) (copyout_pbl:'a copyout_pbl) (apply_table_f:'a apply_table_f) (ext_map:'a ext_map) (func_map:func_map) (i:i) (i':i) (in_out_list1:in_out_list) (in_out_list1':in_out_list) (in_out_list2:in_out_list) (in_out_list2':in_out_list) (ascope:'a) (ascope':'a) (g_scope_list:g_scope_list) (g_scope_list':g_scope_list) (Prs_n:Prs_n) (order:order) (t_scope_list_g:t_scope_list_g) (deltas:delta) framel'  status status' tsll.
  
   
   (* should remove  wt E from here because each arch frame has a different b_func_map and table map??*)

  (∀ i'' . WT_E order t_scope_list_g deltas Prs_n
       i'' (ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map )) ∧
  
  (WT_arch
   Prs_n  order t_scope_list_g  tsll  deltas (* Γ ψll ψG *)
   ( ab_list , pblock_map , ffblock_map , input_f , output_f , copyin_pbl , copyout_pbl , apply_table_f , ext_map , func_map ) (*E*)
   ((i , in_out_list1 , in_out_list2 ,  ascope ) , g_scope_list , framel  , status) (*arch state*)
  ) ∧
  
  (arch_red ( ab_list ,  pblock_map ,  ffblock_map ,  input_f ,  output_f ,  copyin_pbl ,  copyout_pbl ,  apply_table_f ,  ext_map ,  func_map )
   ((i  , in_out_list1  , in_out_list2  ,  ascope )  , g_scope_list  , framel  , status)
   ((i' , in_out_list1' , in_out_list2' ,  ascope' ) , g_scope_list' , framel' , status')    
  )

  ⇒
  
∃  tsll' t_scope_list_g.
  (WT_arch
   Prs_n  order t_scope_list_g  tsll'  deltas (* Γ ψll ψG *)
   ( ab_list , pblock_map , ffblock_map , input_f , output_f , copyin_pbl , copyout_pbl , apply_table_f , ext_map , func_map ) (*E*)
   ((i' , in_out_list1' , in_out_list2' ,  ascope' ) , g_scope_list' , framel'  , status') (*arch state*)
  )                  
`;





     

                                  

Theorem SR_arch:
∀ ty framel . sr_arch framel ty
Proof
  
REPEAT STRIP_TAC >>
gvs[sr_arch_def] >>
REPEAT STRIP_TAC >>
(* first we look into the 7 possible reductions of the arch *)
gvs[Once arch_red_cases] >| [
    (*arch in *)
    gvs[Once WT_arch_cases] >>
             
    SIMP_TAC list_ss [Once WT_arch_cases] >>
    Cases_on ‘EL (i+1) ab_list’ >> gvs[] >>
    
    srw_tac [boolSimps.DNF_ss][] >>
    Q.EXISTS_TAC ‘t_scope_list_g’  >> gvs[]      
    ,
    (* arch_init *)
    gvs[Once WT_arch_cases] >>
    SIMP_TAC list_ss [Once WT_arch_cases] >>
    Cases_on ‘EL i ab_list’ >> gvs[] >>
    
    qexistsl_tac [‘[[[]]]’] >>

    gvs[]

    (******************)    


             
                 
    cheat
    ,
    (* arch_ffbl*)
    gvs[Once WT_arch_cases] >>
    SIMP_TAC list_ss [Once WT_arch_cases] >>
    Cases_on ‘EL (i+1) ab_list’ >> gvs[] >>
    Q.EXISTS_TAC ‘t_scope_list_g’  >> gvs[]  
    ,
    (*arch_out *)
    gvs[Once WT_arch_cases] >>
    SIMP_TAC list_ss [Once WT_arch_cases] >>
    Cases_on ‘HD ab_list’ >> gvs[] >>
    Q.EXISTS_TAC ‘t_scope_list_g’  >> gvs[]  
                                                      
    ,
        
    (*arch-trans*)
    gvs[Once WT_arch_cases] >>
    gvs[state_fin_def] >>
    SIMP_TAC list_ss [Once WT_arch_cases] >>
    Cases_on ‘EL i ab_list’ >> gvs[] >>
    gvs[state_fin_def]>>
    Q.EXISTS_TAC ‘[[[]]]’ >>
    Q.EXISTS_TAC ‘t_scope_list_g’  >> gvs[] >>
                 
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘i’])) >>                           
    SIMP_TAC list_ss [WT_state_cases] >>
    qexistsl_tac [‘[funn_name x']’,‘[[[]]]’,‘[[stmt']]’] >>
    gvs[type_state_tsll_empty_lemma] >>

    PairCases_on ‘deltas’ >> gvs[] >>
    rename1 ‘(delta_g,delta_b,delta_x,delta_t) ’ >>

            
    subgoal ‘WF_ft_order [funn_name x'] delta_g delta_b delta_x order’ >-
     (
     gvs[WF_ft_order_cases, clause_name_def] >>
     REPEAT STRIP_TAC >>
     gvs[ordered_list_def] >>
     gvs[WT_E_cases] >>   
     gvs[WT_c_cases, WF_o_def] 
     ) >> gvs[] >>

    gvs[t_scopes_consistent_list_def] >>

    
    gvs[WT_E_cases] >>   
    gvs[type_frames_def] >>
    REPEAT STRIP_TAC >>
    ‘i'=0’ by gvs[] >> fs[] >>
    LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘i'’])) >>                           
    gvs[] >>
       
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘g_scope_list’])) >>                           
    gvs[]

           
                        
    cheat
    ,
    (*arch-exec*)
    gvs[Once WT_arch_cases] >>
    SIMP_TAC list_ss [Once WT_arch_cases] >>
    srw_tac [boolSimps.DNF_ss][]  >> 

    gvs[state_fin_def, state_fin_def]>>
    Cases_on ‘status'’ >> gvs[] >| [
        DISJ2_TAC >>

        PairCases_on ‘deltas’ >> gvs[] >>

                  
        ASSUME_TAC SR_state >>
        FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘ty’,‘frame_list’])) >>                           
        gvs[sr_state_def] >>
        FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘frame_list'’,
                                                    ‘(apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)’,
                                                    ‘ascope’, ‘ascope'’,
                                                    ‘g_scope_list’, ‘g_scope_list'’,
                                                    ‘status_running’, ‘status_running’,
                                                ‘t_scope_list_g’, 
                                                ‘order’,
                                                ‘deltas0’, ‘deltas1’,
                                                ‘deltas3’, ‘deltas2’,
                                                ‘Prs_n’, ‘tsll ’  
                                                   ])) >>
        gvs[] >>




        gvs[] >> Q.EXISTS_TAC ‘tsll'’ >> Q.EXISTS_TAC ‘t_scope_list_g’ >> gvs[WT_state_cases]
        ,



        FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘i’])) >>                                  
        gvs[WT_E_cases] >>
        FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘ascope'’,‘g_scope_list'’])) >>                                  
        gvs[]
                
        cheat
        ,
            srw_tac [boolSimps.DNF_ss][]        
        cheat
      ]
    ,

    SIMP_TAC list_ss [Once WT_arch_cases] >>
             srw_tac [boolSimps.DNF_ss][]        
          cheat                                      

    
  ] 
        
QED























(* ================================================= *)
(*          progress not stuck for arch              *)
(* ================================================= *)





val prog_arch_def = Define `
 prog_arch (framel) (ty:'a itself) =
∀  (ab_list:ab_list) (pblock_map:pblock_map) (ffblock_map:'a ffblock_map) (input_f:'a input_f) (output_f:'a output_f) (copyin_pbl:'a copyin_pbl) (copyout_pbl:'a copyout_pbl) (apply_table_f:'a apply_table_f) (ext_map:'a ext_map) (func_map:func_map) (i:i) (i':i) (in_out_list1:in_out_list) (in_out_list2:in_out_list) (ascope:'a) (g_scope_list:g_scope_list) (Prs_n:Prs_n) (order:order) (t_scope_list_g:t_scope_list_g) (deltas:delta)  status tsll.

  WT_E order t_scope_list_g deltas Prs_n
       i (ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map ) ∧

  (WT_arch
   Prs_n  order t_scope_list_g  tsll  deltas (* Γ ψll ψG *)
   ( ab_list , pblock_map , ffblock_map , input_f , output_f , copyin_pbl , copyout_pbl , apply_table_f , ext_map , func_map ) (*E*)
   ((i , in_out_list1 , in_out_list2 ,  ascope ) , g_scope_list , framel  , status) (*arch state*)
  )     
        
   ⇒            
  
   ∃ i' in_out_list1' in_out_list2' ascope' g_scope_list' framel' status'.
   (arch_red ( ab_list ,  pblock_map ,  ffblock_map ,  input_f ,  output_f ,  copyin_pbl ,  copyout_pbl ,  apply_table_f ,  ext_map ,  func_map )
    ((i  , in_out_list1  , in_out_list2  ,  ascope )  , g_scope_list  , framel  , status)
    ((i' , in_out_list1' , in_out_list2' ,  ascope' ) , g_scope_list' , framel' , status')    
   )                 
`;






Theorem prog_arch:
∀ ty framel . prog_arch framel ty
Proof


REPEAT STRIP_TAC >>
gvs[prog_arch_def] >>
REPEAT STRIP_TAC >>
Cases_on ‘framel’ >> gvs[] >| [
    (*empty arch frame list *)
           
SIMP_TAC list_ss [Once arch_red_cases] >>  
gvs[] >>
Cases_on ‘EL i ab_list’ >> gvs[] >| [  
      
      (* arch input *)
      rfs[WT_arch_cases, clause_name_def] >>
      gvs[WT_E_cases] >>
      METIS_TAC[]               
      ,
      
      (* arch init *)  
      gvs[WT_arch_cases, clause_name_def] >>
      gvs[WT_E_cases] >>
      FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘ascope’, ‘g_scope_list’])) >>

                      
      Q.EXISTS_TAC ‘g_scope_list'³'’ >>
      Q.EXISTS_TAC ‘ZIP(l,ZIP(MAP FST xdl,MAP SND xdl))’ >>
      Q.EXISTS_TAC ‘stmt’ >>
      Q.EXISTS_TAC ‘scope'’ >>
      gvs[] >>
      gvs[map_distrub, LENGTH_MAP] >>
      gvs[map_rw1] >>
      gvs[map_distrub, LENGTH_MAP] >>      
      gvs[ZIP_MAP_FST_SND]

      ,
        
      (*arch ffbl *)
      gvs[WT_arch_cases, clause_name_def] >>
      gvs[WT_E_cases] >>
      METIS_TAC[]

      ,

      (* arch out *)
      gvs[WT_arch_cases, clause_name_def] >>
      gvs[WT_E_cases] >>
      METIS_TAC[]
    ]
,

        
(*regular block *)

Cases_on ‘status = status_running’ >> gvs[] >| [
          
  SIMP_TAC list_ss [Once arch_red_cases] >>
  gvs[] >>
  srw_tac [boolSimps.DNF_ss][] >>
  gvs[WT_arch_cases, clause_name_def] >>
  DISJ1_TAC >>
  gvs[WT_arch_cases, clause_name_def, WT_E_cases] >>
  ASSUME_TAC PROG_framel >> 
  
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘ty’,‘l’])) >>
  gvs[prog_state_def]>>
  gvs[Once WT_arch_cases] >>
  
  

  FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [ ‘(apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)’,
                                               ‘ascope’, ‘g_scope_list’, ‘t_scope_list_g’,
                                               ‘tsll’,‘order’,‘delta_g’,‘delta_b’, ‘delta_t’, ‘delta_x’, ‘Prs_n’
                                             ])) >>
  
  
  
  ‘l ≠ [] ∧ (∀f local_scope t. l ≠ (f,[stmt_empty],local_scope)::t)’ by cheat >> (*This must be added to the arch semantics in the A-exec rule*)
  gvs[] >>
  
  qexistsl_tac [‘ascope'’,‘gscope'’,‘status'’,‘framel'’] >>
  gvs[]
   
  ,
  
  
  SIMP_TAC list_ss [Once arch_red_cases] >>
  gvs[] >>
  srw_tac [boolSimps.DNF_ss][] >>
  gvs[WT_arch_cases] >>
  
  Cases_on ‘state_fin status l’ >> gvs[] >| [
   DISJ2_TAC >>
   Q.EXISTS_TAC ‘ascope'’ >>
   Q.EXISTS_TAC ‘ZIP(el,ZIP(MAP FST xdl,MAP SND xdl))’ >>
   Q.EXISTS_TAC ‘stmt’ >>
   gvs[] >>
   gvs[map_distrub, LENGTH_MAP] >>
   gvs[map_rw1] >>
   gvs[map_distrub, LENGTH_MAP] >>      
   gvs[ZIP_MAP_FST_SND] >>
   gvs[clause_name_def]   
   ,
   Cases_on ‘status’ >> gvs[state_fin_def, clause_name_def]     
  ]]]
QED



val _ = export_theory ();

