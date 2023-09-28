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

val _ = new_theory "p4_concurrent";



val trace_path_def = Define `
trace_path R (n:num) init fin = NRC R (n:num) init fin
`;



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

     


Theorem arch_path_imples_conc:
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
    srw_tac [][clause_name_def]
    ,
    RES_TAC >>    
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘thread2’]))
  ] 
       
QED
     

       


val _ = export_theory ();
