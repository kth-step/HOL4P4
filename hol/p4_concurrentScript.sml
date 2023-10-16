open HolKernel boolLib liteLib simpLib Parse bossLib;
open arithmeticTheory stringTheory containerTheory pred_setTheory
     listTheory finite_mapTheory;

open p4Lib;
open blastLib bitstringLib;
open p4Theory p4_auxTheory ottTheory;
open bitstringTheory;
open wordsTheory;
open optionTheory;
open sumTheory;
open stringTheory;
open ottTheory;
open pairTheory;
open rich_listTheory;

open p4_exec_semTheory p4_exec_sem_arch_soundnessTheory;

val _ = new_theory "p4_concurrent";



Definition trace_path_def:
trace_path R (n:num) init fin = NRC R (n:num) init fin
End



(* The Compositionality of Trace Paths Theorem *)        
Theorem paths_compose:
 ∀ init mid fin R m n.
  trace_path R n init mid ∧
  trace_path R m mid fin ⇒
  trace_path R (m+n) init fin                       
Proof
gvs[trace_path_def] >>
REPEAT STRIP_TAC >>
IMP_RES_TAC NRC_ADD_I >>
gvs[]
QED     


      
Theorem arch_paths_compose:
∀ init mid fin actx m n.
  trace_path ( \i f. arch_red actx i f) n init mid ∧
  trace_path ( \i f. arch_red actx i f) m mid fin ⇒
  trace_path ( \i f. arch_red actx i f) (m+n) init fin           
Proof

REPEAT STRIP_TAC >>     
ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:('a aenv # g_scope_list # arch_frame_list # status)``] paths_compose)  >>
RES_TAC
QED

        
Theorem conc_paths_compose:
∀ init mid fin actx m n.
  trace_path ( \i f. conc_red actx i f) n init mid ∧
  trace_path ( \i f. conc_red actx i f) m mid fin ⇒
  trace_path ( \i f. conc_red actx i f) (m+n) init fin           
Proof

REPEAT STRIP_TAC >>     
ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:((in_out_list # in_out_list # 'a) # ((num # g_scope_list # arch_frame_list # status) # (num # g_scope_list # arch_frame_list # status)))``] paths_compose)  >>
RES_TAC
QED

     


Theorem arch_path_implies_conc_thread1:
 ∀ n actx i io1 io2 a gsl framel status i' io1' io2' a' gsl' framel' status' thread2.
  trace_path ( \i f. arch_red actx i f) n ((i,io1,io2,a),gsl,framel,status) ((i',io1',io2',a'),gsl',framel',status') ⇒
  trace_path ( \i f. conc_red actx i f) n ((io1 ,io2 ,a ), ((i ,gsl ,framel ,status ) , thread2))
                                          ((io1',io2',a'), ((i',gsl',framel',status') , thread2))
Proof
Induct_on ‘n’ >>
gvs[trace_path_def] >>
REPEAT STRIP_TAC >> 
gvs[NRC] >>
PairCases_on ‘f’ >>
Q.EXISTS_TAC ‘((f1,f2,f3),((f0,f4,f5,f6),thread2))’ >>
CONJ_TAC >| [
 SIMP_TAC list_ss [Once conc_red_cases]>>
 DISJ1_TAC>>             
 PairCases_on ‘thread2’ >>
 PairCases_on ‘actx’ >>
 srw_tac [] [clause_name_def],

 RES_TAC >>    
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘thread2’]))
]    
QED

Theorem arch_path_implies_conc_thread2:
 ∀ n actx i io1 io2 a gsl framel status i' io1' io2' a' gsl' framel' status' thread1.
  trace_path ( \i f. arch_red actx i f) n ((i,io1,io2,a),gsl,framel,status) ((i',io1',io2',a'),gsl',framel',status') ⇒
  trace_path ( \i f. conc_red actx i f) n ((io1 ,io2 ,a ), (thread1, (i ,gsl ,framel ,status)))
                                          ((io1',io2',a'), (thread1, (i',gsl',framel',status')))
Proof
Induct_on ‘n’ >>
gvs[trace_path_def] >>
REPEAT STRIP_TAC >> 
gvs[NRC] >>
PairCases_on ‘f’ >>
Q.EXISTS_TAC ‘((f1,f2,f3),(thread1, (f0,f4,f5,f6)))’ >>
CONJ_TAC >| [
 SIMP_TAC list_ss [Once conc_red_cases]>>
 DISJ2_TAC>>             
 PairCases_on ‘thread1’ >>
 PairCases_on ‘actx’ >>
 srw_tac [] [clause_name_def],

 RES_TAC >>    
 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘thread1’]))
]    
QED

Theorem arch_exec_trace_1:
!actx s s'.
 arch_multi_exec actx s 1 = SOME s' ==>
 trace_path ( \s s'. arch_red actx s s') 1 s s'
Proof
rpt strip_tac >>
fs[arch_multi_exec_1, trace_path_def] >>
PairCases_on ‘s’ >>
ASSUME_TAC (ISPECL [“s5:arch_frame_list”, “alpha_dummy:'a itself”] arch_exec_sound_red) >>
fs [arch_exec_sound]
QED

Theorem arch_exec_trace_n:
!actx n s s'.
 arch_multi_exec actx s n = SOME s' ==>
 trace_path ( \s s'. arch_red actx s s') n s s'
Proof
Induct_on ‘n’ >| [
 rpt strip_tac >>
 PairCases_on ‘s’ >>
 fs[arch_multi_exec_def, trace_path_def],

 rpt strip_tac >>
 subgoal ‘?s''. arch_multi_exec actx s n = SOME s'' /\
                arch_multi_exec actx s'' 1 = SOME s'’ >- (
  cheat
 ) >>
 metis_tac [arch_exec_trace_1, arch_paths_compose, arithmeticTheory.SUC_ONE_ADD]
]
QED



val _ = export_theory ();
