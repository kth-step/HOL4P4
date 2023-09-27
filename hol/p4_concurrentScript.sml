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

     


       


val _ = export_theory ();
