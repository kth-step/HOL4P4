open HolKernel boolLib liteLib simpLib Parse bossLib;
open arithmeticTheory stringTheory containerTheory pred_setTheory
     listTheory finite_mapTheory;

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
open alistTheory;
open set_relationTheory;
open pred_setTheory;
open pred_setLib;


    
open p4_auxTheory;
     
open bdd_genTheory;     

val _ = new_theory "bdd_aux";




Theorem MEM_INDEX_OF:           
  ∀ l x .
    MEM x l ⇒
    ∃ i . INDEX_OF x l = SOME i
Proof                                
  Induct >>                                
  rpt strip_tac >>
  gvs[INDEX_OF_def,  INDEX_FIND_def] >>
  Cases_on ‘x=h’ >> gvs[] >>
  res_tac >>
  PairCases_on ‘z’ >>
  imp_res_tac P_implies_next >>
  gvs[]
QED



Theorem lookup_edges_in_domain:
  ∀ edges n n1 n2.        
    ALOOKUP edges n = SOME (n1,n2) ⇒
    (MEM n (dom_range_edges edges) ∧
     MEM n1 (dom_range_edges edges) ∧
     MEM n2 (dom_range_edges edges))
Proof
  Induct >>
  gvs[dom_range_edges_def] >>
  rpt strip_tac >>
  PairCases_on ‘h’ >>
  gvs[AllCaseEqs()] >>
  res_tac >>
  gvs[]
QED




Theorem non_term_leaf_updt_concat:    
  ∀ x l1 l2.
  non_term_leaf_updt (l1++l2) x = non_term_leaf_updt l1 x ++ non_term_leaf_updt l2 x
Proof    
  fs[non_term_leaf_updt_def]
QED



Theorem non_term_leaf_updt_cons:        
  ∀ l h x . non_term_leaf_updt (h::l) x = non_term_leaf_updt [h] x ++ non_term_leaf_updt l x
Proof
  fs[non_term_leaf_updt_def]
QED




Theorem non_term_leaf_updt_rec:
  ∀ l x x'.                                                                                
    non_term_leaf_updt ( non_term_leaf_updt l x ) x' =  non_term_leaf_updt l x 
Proof
  Induct >>
  rpt strip_tac >-
   gvs[non_term_leaf_updt_def] >>
  
  PairCases_on ‘h’ >> gvs[non_term_leaf_updt_def] >>
               
  Cases_on ‘h1’ >> gvs[] >>
  Cases_on ‘p’ >> gvs[] >>
  Cases_on ‘q’ >> gvs[]
QED




Theorem lookup_labels_in_updt:
  ∀ labels n x p h.
    ALOOKUP labels n = SOME (non_termn (SOME x,p)) ⇒
    ALOOKUP (non_term_leaf_updt labels h) n = SOME (non_termn (SOME x,p))
Proof
  Induct >>
  rpt strip_tac >>
  simp[non_term_leaf_updt_def] >>
  PairCases_on ‘h’ >> gvs[ALOOKUP_def] >>
  gvs[AllCaseEqs()] >>
  Cases_on ‘h1’ >> gvs[] >>
  last_x_assum (strip_assume_tac o (Q.SPECL [‘n’, ‘x’, ‘p’, ‘h'’])) >>
  gvs[non_term_leaf_updt_def] >>
  Cases_on ‘p'’ >> gvs[] >>
  Cases_on ‘q’ >> gvs[]
QED



Theorem lookup_labels_in_updt_none:
  ∀ labels n x p h.
    ALOOKUP labels n = SOME (non_termn (NONE,p)) ⇒
    ALOOKUP (non_term_leaf_updt labels h) n = SOME (non_termn (SOME h,p))
Proof
  Induct >>
  rpt strip_tac >>
  gvs[ALOOKUP_def] >>
  
  gvs[Once non_term_leaf_updt_cons] >>
  rgs[ALOOKUP_APPEND]>>
  gvs[AllCaseEqs()] >>
  
  PairCases_on ‘h’ >> 
  gvs[AllCaseEqs()] >>
  simp[non_term_leaf_updt_def] >>
  
  
  Cases_on ‘h1’ >> gvs[] >>
  Cases_on ‘p'’ >> gvs[] >>
  Cases_on ‘q’ >> gvs[]
QED
    


Theorem lookup_labels_in_updt_term:
  ∀ labels n p h.
    ALOOKUP labels n = SOME (termn p) ⇒
    ALOOKUP (non_term_leaf_updt labels h) n = SOME (termn p)
Proof
  Induct >>
  rpt strip_tac >>
  gvs[ALOOKUP_def] >>
  
  gvs[Once non_term_leaf_updt_cons] >>
  rgs[ALOOKUP_APPEND]>>
  gvs[AllCaseEqs()] >>
  
  PairCases_on ‘h’ >> 
  gvs[AllCaseEqs()] >>
  simp[non_term_leaf_updt_def] >-
  (Cases_on ‘p’ >> gvs[]) >>
        
  Cases_on ‘h1’ >> gvs[] >>
  Cases_on ‘p'’ >> gvs[] >>
  Cases_on ‘q’ >> gvs[]
QED



Theorem WF_imp_non_leaf_lbl:
  ∀ r edges labels n n' n'' h.      
    BDD_WF (r,edges,labels) ∧
    ALOOKUP edges n = SOME (n',n'') ⇒
    ∃ x p . ALOOKUP labels n = SOME (non_termn (SOME x,p))
Proof
  gvs[BDD_WF_def] >>
  rpt strip_tac >>
  ‘MEM n (dom_range_edges edges)’ by  imp_res_tac lookup_edges_in_domain >>
  last_x_assum (strip_assume_tac o (Q.SPECL [‘n’])) >>
  gvs[lookup_is_some_def, is_lookup_internal_def] 
QED



Theorem wf_lookup_if_edges_label:    
  ∀ r edges labels n n' n'' h.      
    BDD_WF (r,edges,labels) ∧
    ALOOKUP edges n = SOME (n',n'') ⇒
    ∃ x p . ALOOKUP (non_term_leaf_updt labels h) n = SOME (non_termn (SOME x,p))
Proof
  rpt strip_tac >>                                                                  
  imp_res_tac WF_imp_non_leaf_lbl >>
  imp_res_tac lookup_labels_in_updt >>                      
  gvs[]
QED



Theorem lookup_new_edges_simp_exists:
  ∀ simp_leaves' new_edges nn n c.
    ALOOKUP new_edges n = SOME nn ∧
    mk_new_edges simp_leaves' c = new_edges ⇒
    ∃ sll . ALOOKUP simp_leaves' n = SOME sll
Proof
  Induct >> 
  rgs[mk_new_edges_def]>>         
  rpt strip_tac >>
  PairCases_on ‘h’ >>
  rgs[mk_new_edges_def] >>
  rgs[AllCaseEqs()] >>
  res_tac >> gvs[]
QED



Theorem lookup_simp_leaves_determine_exists:
  ∀ simp_leaves simp_leaves' n sll rec.        
    ALOOKUP simp_leaves' n = SOME sll ∧        
    determine_termn_list rec simp_leaves = simp_leaves' ⇒
    ∃ sll' . ALOOKUP simp_leaves n = SOME sll'
Proof
  Induct >> 
  rgs[determine_termn_list_def]>>         
  rpt strip_tac >>
  PairCases_on ‘h’ >>
  rgs[determine_termn_def] >>
  rgs[AllCaseEqs()] >>
  res_tac >> gvs[]
QED



Theorem  lookup_simp_pred_leaves_sub_exists:      
  ∀ leaves_sub simp_leaves n sll rec.
    ALOOKUP simp_leaves n = SOME sll ∧        
    simp_pred_list rec leaves_sub = simp_leaves ⇒
    ∃ sll' . ALOOKUP leaves_sub n = SOME sll'
Proof
  Induct >> 
  rgs[simp_pred_list_def]>>         
  rpt strip_tac >>
  PairCases_on ‘h’ >>
  rgs[AllCaseEqs()] >>
  res_tac >> gvs[]
QED



Theorem lookup_leaves_sub_pred_exists:
  ∀ ntl  leaves_sub sll n h rec.       
    ALOOKUP leaves_sub n = SOME sll ∧
    leaves_pred_sub rec ntl h = leaves_sub ⇒
    ∃ p . ALOOKUP ntl n = SOME p
Proof
  Induct >> 
  rgs[leaves_pred_sub_def]>>         
  rpt strip_tac >>
  PairCases_on ‘h’ >>
  rgs[AllCaseEqs()] >>
  res_tac >> gvs[]
QED                



Theorem extract_nontermn_not_inner_node:                   
  ∀ leaves ntl n .                            
    extract_nontermn leaves = SOME ntl ⇒
    ∃ x p' . ALOOKUP leaves n ≠ SOME (non_termn (SOME x,p'))
Proof
  Induct >-
   rgs[extract_nontermn_def]>>         
  rpt strip_tac >>
  PairCases_on ‘h’ >>
  gvs[]>>
  Cases_on ‘h0=n’ >> gvs[] >> rgs[extract_nontermn_def] >>                   
  Cases_on ‘h1’ >> rgs[AllCaseEqs()]
QED



Theorem not_mem_alookup_none:
∀ l a b .
  ALL_DISTINCT (MAP FST l) ∧
  ¬MEM a (MAP FST l) ⇒
  ALOOKUP l a = NONE   
Proof
Induct >> gvs[] >>
rpt strip_tac >>
PairCases_on ‘h’ >> 
rgs[AllCaseEqs()] 
QED



Theorem all_distinct_mem_not:
  ∀ l l' n.
  MEM n l' ∧
 ALL_DISTINCT (l++l') ⇒       
  ~ MEM n l
Proof
rpt strip_tac >>
rgs[ALL_DISTINCT_APPEND]
QED



Theorem lookup_same_triviality:        
∀ l n n' p p'.
ALL_DISTINCT (MAP FST l) ∧
ALOOKUP l n' = SOME p ∧
ALOOKUP l n' = SOME p' ⇒
p = p'
Proof
Induct >> gvs[] >>
rpt strip_tac >>
PairCases_on ‘h’ >> rgs[]
QED



Theorem not_in_leaves_not_in_ntl:
  ∀ leaves_labels ntl n.        
    ¬MEM n (MAP FST leaves_labels) ∧       
    extract_nontermn leaves_labels = SOME ntl ⇒
    ALOOKUP ntl n = NONE
Proof
  Induct >- gvs[extract_nontermn_def] >>
  rpt strip_tac >>
  PairCases_on ‘h’ >> 
  rgs[AllCaseEqs()] >> 
  gvs[extract_nontermn_def] >>
  rgs[AllCaseEqs()] >>
  res_tac >>
  Cases_on ‘ntl’ >> gvs[]
QED                   



Theorem lookup_ntl_updt_none:
  ∀ labels h n .
    ALOOKUP (non_term_leaf_updt labels h) n = NONE ⇒
    ALOOKUP labels n = NONE
Proof
  Induct >- gvs[non_term_leaf_updt_def] >>                        
  rpt strip_tac >>
  gvs[Once non_term_leaf_updt_cons] >>
  gvs[] >>
  
  PairCases_on ‘h’>>
  rgs[AllCaseEqs()] >>
  
  gvs[ALOOKUP_APPEND] >>
  rgs[AllCaseEqs()] >>
  
  res_tac >> 
  gvs[non_term_leaf_updt_def] >>          
  Cases_on ‘h1’ >> gvs[] >>
  Cases_on ‘p’ >> gvs[] >>
  Cases_on ‘q’ >> gvs[]
QED



Theorem lookup_non_term_leaf_some:
∀ labels h n x.        
ALOOKUP (non_term_leaf_updt labels h) n = SOME x ⇒
∃ lbl. ALOOKUP labels n = SOME lbl
Proof
Induct >>
gvs[non_term_leaf_updt_def] >>
rpt strip_tac >>
PairCases_on ‘h’ >> gvs[] >>
rpt (BasicProvers.full_case_tac >> gvs[]) >>
res_tac >> gvs[]
QED



Theorem mk_body_map1:
  ∀ leaves labels leaves_labels .        
    getLabels labels leaves = SOME leaves_labels ⇒
    (leaves = MAP FST  leaves_labels)
Proof
  Induct >>
  rpt strip_tac >>
  gvs[getLabels_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  res_tac 
QED



Theorem mk_body_map2:
  ∀ ntl leaves_sub h rec.
    leaves_pred_sub rec ntl h = leaves_sub ⇒
    MAP FST ntl = MAP FST leaves_sub 
Proof
  Induct >>
  gvs[leaves_pred_sub_def] >>
  rpt strip_tac >>
  PairCases_on ‘h’ >> gvs[] 
QED



Theorem mk_body_map3:
  ∀ leaves_sub simp_leaves h rec.
    simp_pred_list rec leaves_sub = simp_leaves ⇒
    MAP FST leaves_sub = MAP FST simp_leaves 
Proof
  Induct >>
  gvs[simp_pred_list_def] >>
  rpt strip_tac >>
  PairCases_on ‘h’ >> gvs[] 
QED



Theorem mk_body_map4:
  ∀ leaves_simp leaves_simp' h rec.
    determine_termn_list rec leaves_simp = leaves_simp' ⇒
    MAP FST leaves_simp = MAP FST leaves_simp' 
Proof
  Induct >>
  gvs[determine_termn_list_def] >>
  rpt strip_tac >>
  PairCases_on ‘h’ >> gvs[] 
QED



Theorem mk_body_map5:
  ∀ leaves_simp' new_edges c .
    mk_new_edges leaves_simp' c = new_edges ⇒
    MAP FST leaves_simp' = MAP FST new_edges
Proof
  Induct >>
  gvs[mk_new_edges_def] >>
  rpt strip_tac >>
  PairCases_on ‘h’ >> gvs[mk_new_edges_def] 
QED



Theorem mk_body_map6:
  ∀ labels updated_labels x.
    non_term_leaf_updt labels x = updated_labels ⇒
    MAP FST labels = MAP FST updated_labels
Proof
  Induct >>
  gvs[non_term_leaf_updt_def] >>
  rpt strip_tac >>
  PairCases_on ‘h’ >>
  gvs[AllCaseEqs()] >>                      
  Cases_on ‘h1’ >> gvs[] >>
  Cases_on ‘p’ >> gvs[] >>
  Cases_on ‘q’ >> gvs[]
QED



Theorem length_new_labels:
  ∀ simp_leaves' new_labels c.       
    mk_new_labels simp_leaves' c = new_labels ⇒
    LENGTH new_labels = (LENGTH simp_leaves' + LENGTH simp_leaves')
Proof
  Induct >>
  gvs[mk_new_labels_def] >>
  rpt strip_tac >>
  PairCases_on ‘h’ >>
  gvs[mk_new_labels_def]
QED



Theorem counter_range_in_new_labels:
  ∀ simp_leaves' new_labels c n .       
    MEM n (MAP FST new_labels) ∧                        
    mk_new_labels simp_leaves' c = new_labels ⇒
    (n >= c ∧ n < (c + LENGTH new_labels)) 
Proof
  Induct >>
  gvs[mk_new_labels_def] >>
  rpt strip_tac >>
  PairCases_on ‘h’ >>
  gvs[mk_new_labels_def] >>
  res_tac >>
  decide_tac
QED



Theorem counter_range_in_new_exists:
  ∀ simp_leaves' new_labels c n .       
    MEM n (MAP FST new_labels) ∧                        
    mk_new_labels simp_leaves' c = new_labels ⇒
    (∃ i . n = c + i ∧ i < LENGTH new_labels) 
Proof
  Induct >>
  gvs[mk_new_labels_def] >>
  rpt strip_tac >>
  PairCases_on ‘h’ >>
  gvs[mk_new_labels_def] >>
  res_tac >>
  qexists_tac ‘2+i’ >> gvs[]
QED


               
Theorem term_not_in_ntl:       
∀ leaves_labels ntl q r n.
  ALL_DISTINCT (MAP FST leaves_labels) ∧
  ALOOKUP leaves_labels n = SOME (termn (q,r)) ∧      
  extract_nontermn leaves_labels = SOME ntl ⇒
  ALOOKUP ntl n = NONE   
Proof
  Induct >-
   gvs[extract_nontermn_def] >>
  rpt strip_tac >>
  PairCases_on ‘h’ >> gvs[] >>
  gvs[AllCaseEqs()] >|[
    imp_res_tac not_mem_alookup_none >>                
    imp_res_tac mk_body_map1 >>
    gvs[extract_nontermn_def] >>
    rgs[AllCaseEqs()] >>
    imp_res_tac not_in_leaves_not_in_ntl
    ,
    res_tac >>
    gvs[extract_nontermn_def] >>
    rgs[AllCaseEqs()] >>
    res_tac >>
    Cases_on ‘ntl’ >> gvs[]
  ]
QED  
        

        
Theorem extract_nonterm_mem_neg:        
  ∀ leaves_labels ntl h.
    ¬MEM h (MAP FST leaves_labels) ∧
    extract_nontermn leaves_labels = SOME ntl ⇒
    ¬MEM h (MAP FST ntl)
Proof
  Induct >>
  rpt strip_tac >>
  gvs[extract_nontermn_def] >>
  PairCases_on ‘h’ >> gvs[] >>
  gvs[extract_nontermn_def] >>
  gvs[AllCaseEqs()]                      
QED



Theorem mk_new_label_idx_mem:
  ∀ simp_leaves n c.
    n>0 ⇒
    ¬MEM c (MAP FST (mk_new_labels simp_leaves (c + n))) 
Proof
  Induct >>
  gvs[mk_new_labels_def] >>
  rpt gen_tac >>
  PairCases_on ‘h’ >>
  simp[mk_new_labels_def]
QED



Theorem all_distinct_leaves:
  ∀ edges r leaves .        
    ALL_DISTINCT (MAP FST edges) ∧
    getLeaves edges r = SOME leaves ⇒
    ALL_DISTINCT leaves
Proof
  Induct >>
  gvs[getLeaves_def] >>
  rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  PairCases_on ‘h’ >>
  gvs[get_leaves_list_def]
QED



Theorem all_distinct_leaves_labels:
  ∀ leaves labels leaves_labels .        
    ALL_DISTINCT leaves ∧
    getLabels labels leaves = SOME leaves_labels ⇒
    ALL_DISTINCT (MAP FST leaves_labels)
Proof
  rpt strip_tac >>
  imp_res_tac mk_body_map1 >>
  gvs[]
QED

        
        
Theorem all_distinct_ntl:
  ∀ leaves_labels ntl .
  ALL_DISTINCT (MAP FST leaves_labels) ∧
  extract_nontermn leaves_labels = SOME ntl ⇒
  ALL_DISTINCT (MAP FST ntl)                  
Proof
  Induct >>
  rpt strip_tac >>
  gvs[extract_nontermn_def] >>
  PairCases_on ‘h’ >> gvs[] >>
  gvs[extract_nontermn_def] >>
  gvs[AllCaseEqs()] >>
  imp_res_tac extract_nonterm_mem_neg
QED   



Theorem all_distinct_sub:
  ∀ ntl leaves_sub h rec.
    ALL_DISTINCT (MAP FST ntl) ∧
    leaves_pred_sub rec ntl h = leaves_sub ⇒
    ALL_DISTINCT (MAP FST leaves_sub) 
Proof
  rpt strip_tac >>
  imp_res_tac mk_body_map2 >>
  gvs[] 
QED


        
Theorem all_distinct_simp:
  ∀ simp_leaves leaves_sub h rec.
    ALL_DISTINCT (MAP FST leaves_sub) ∧
    simp_pred_list rec leaves_sub = simp_leaves ⇒
    ALL_DISTINCT (MAP FST simp_leaves)               
Proof
  rpt strip_tac >>
  imp_res_tac mk_body_map3 >>
  gvs[]  
QED



Theorem all_distinct_determine:
  ∀ simp_leaves simp_leaves' h rec.
    ALL_DISTINCT (MAP FST simp_leaves) ∧
    determine_termn_list rec simp_leaves = simp_leaves' ⇒
    ALL_DISTINCT (MAP FST simp_leaves')               
Proof
  rpt strip_tac >>
  imp_res_tac mk_body_map4 >>
  gvs[]  
QED


        
Theorem all_distinct_mk_edges:
  ∀ simp_leaves' new_edges c.
    ALL_DISTINCT (MAP FST simp_leaves') ∧
    mk_new_edges simp_leaves' c = new_edges ⇒
    ALL_DISTINCT (MAP FST new_edges)               
Proof
  rpt strip_tac >>
  imp_res_tac mk_body_map5 >>
  gvs[]  
QED


      
Theorem all_distinct_non_term_leaf_updt:        
  ∀ labels updated_labels h.
    ALL_DISTINCT (MAP FST labels) ∧
    non_term_leaf_updt labels h = updated_labels ⇒
    ALL_DISTINCT (MAP FST updated_labels)
Proof
  rpt strip_tac >>
  imp_res_tac mk_body_map6 >>
  gvs[]
QED


      
Theorem all_distinct_mk_labels:      
  ∀ simp_leaves' new_labels c.
    ALL_DISTINCT (MAP FST simp_leaves') ∧
    mk_new_labels simp_leaves' c = new_labels ⇒
    ALL_DISTINCT (MAP FST new_labels)               
Proof
  Induct >>
  rgs[Once mk_new_labels_def] >>
  rpt strip_tac >>
  rgs[Once mk_new_labels_def] >>
  PairCases_on ‘h’ >>
  simp[Once mk_new_labels_def] >>
  gvs[mk_new_label_idx_mem] >>
  assume_tac mk_new_label_idx_mem >>
  first_x_assum (strip_assume_tac o (Q.SPECL [‘simp_leaves'’,‘1’,‘c+1’])) >>
  gvs[]           
QED



Theorem get_leaves_list_domain:
  ∀ edges leaves n.     
    MEM n (MAP FST edges) ∧
    get_leaves_list edges = leaves
    ⇒
    ~ MEM n leaves
Proof
  Induct >>
  rpt strip_tac >- gvs[get_leaves_list_def] >>
  PairCases_on ‘h’ >>
  rgs[] >>
  res_tac >>
  rgs[Once get_leaves_list_def] >>
  gvs[get_leaves_list_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> rgs[]) >>
  rgs[MEM_FILTER]
QED


    
Theorem leaves_are_not_parents:         
  ∀ edges leaves n r.     
    MEM n (MAP FST edges) ∧
    getLeaves edges r = SOME leaves ⇒
    ~ MEM n leaves
Proof
  Cases_on ‘edges’ >>
  rpt strip_tac >>
  gvs[getLeaves_def] >>
  gvs[AllCaseEqs()] >>
  assume_tac get_leaves_list_domain >>
  PairCases_on ‘h’ >> gvs[]         
QED



Theorem alookup_map_local_thm:
  ∀ l l' n x.
    ALOOKUP l n = SOME x ∧
    MAP FST l = MAP FST l' ⇒
    ∃ x'.  ALOOKUP l' n = SOME x'  
Proof
  Induct >>
  gvs[] >>
  rpt strip_tac >>
  PairCases_on ‘h’ >> gvs[] >>
  gvs[AllCaseEqs()]>>
  Cases_on ‘l'’ >> gvs[] >>
  PairCases_on ‘h’ >> gvs[]
QED
        

 
Theorem alookup_nonterm_exsists:                          
  ∀ leaves_labels ntl n p.
    ALOOKUP ntl n = SOME p ∧        
    extract_nontermn leaves_labels = SOME ntl ⇒
    ∃ lbl. ALOOKUP leaves_labels n = SOME lbl 
Proof
  Induct >>                                        
  gvs[extract_nontermn_def] >>
  rpt strip_tac >>
  PairCases_on ‘h’ >>
  gvs[] >>
  rpt (BasicProvers.full_case_tac >> gvs[]) >>
  gvs[extract_nontermn_def] >>
  rpt (BasicProvers.full_case_tac >> gvs[])
QED



Theorem lbl_pred_rel_extract_nontermn:
  ∀ leaves_labels ntl n p lbl.
    ALL_DISTINCT (MAP FST leaves_labels) ∧
    extract_nontermn leaves_labels = SOME ntl ∧
    ALOOKUP leaves_labels n = SOME lbl ∧
    ALOOKUP ntl n = SOME p ⇒
    (lbl = non_termn (NONE,p))
Proof
  Induct >>                                        
  gvs[extract_nontermn_def] >>
  rpt strip_tac >>
  
  PairCases_on ‘h’ >>
  gvs[] >>
  rpt (BasicProvers.full_case_tac >> gvs[]) >>
  gvs[extract_nontermn_def] >>
  rpt (BasicProvers.full_case_tac >> gvs[]) >>
  res_tac >>
  imp_res_tac alookup_nonterm_exsists >>
  res_tac >>
  gvs[] >>
  imp_res_tac ALOOKUP_MEM >>
  imp_res_tac mem_fst_snd >>
  gvs[]
QED            



Theorem lookup_labels_of_leaves_same:
  ∀ leaves labels  leaves_labels n lbl.
    getLabels labels leaves = SOME leaves_labels ∧
    ALOOKUP leaves_labels n = SOME lbl ⇒
    ALOOKUP labels n = SOME lbl
Proof
  Induct >>
  rpt strip_tac >>
  gvs[getLabels_def] >>
  rpt (BasicProvers.full_case_tac >> gvs[])
QED



Theorem get_leaves_list_in_nodes:
  ∀ edges n.
    MEM n (get_leaves_list (edges)) ⇒
    MEM n (dom_range_edges (edges))
Proof
  Induct >>
  gvs[getLeaves_def] >>
  rpt strip_tac >>
  rgs[dom_range_edges_def, get_leaves_list_def] >>
  rgs[MEM_FILTER] >>
  PairCases_on ‘h’ >>
  gvs[]
QED



Theorem get_leaves_in_nodes:      
  ∀ edges leaves n r.
    ¬MEM n (dom_range_edges edges) ∧
    edges ≠ [] ∧
    getLeaves edges r = SOME leaves
    ⇒        
    ¬ MEM n leaves
Proof
  Induct_on ‘edges’ >>
  rpt strip_tac >>      
  gvs[getLeaves_def] >>
  gvs[AllCaseEqs()] >>
  imp_res_tac get_leaves_list_in_nodes
QED



Theorem dom_range_edges_in_append:
∀ edges new_edges n.
(MEM n (dom_range_edges new_edges) ⇒
 MEM n (dom_range_edges (edges++new_edges)))
∧
(MEM n (dom_range_edges edges) ⇒
 MEM n (dom_range_edges (edges++new_edges)))
Proof
  Induct >>
  gvs[dom_range_edges_def]
QED



Theorem not_in_leaves_not_in_res:
  ∀ leaves_labels leaves labels n.        
    ¬ MEM n leaves ∧                        
    getLabels labels leaves = SOME leaves_labels ⇒
    ALOOKUP leaves_labels n = NONE
Proof
  Induct_on ‘leaves’ >>
  rpt strip_tac >>
  gvs[ALOOKUP_NONE] >>
  gvs[getLabels_def] >>
  gvs[AllCaseEqs()] >>
  res_tac
QED  


   
Theorem determine_termn_list_cons:
  ∀ h simp_leaves rec.        
    determine_termn_list rec (h::simp_leaves) = (determine_termn_list rec [h]++(determine_termn_list rec simp_leaves))     
Proof
  gvs[determine_termn_list_def]
QED



Theorem determine_term_never_internal:        
  ∀p p' x rec. determine_termn rec p ≠ non_termn (SOME x,p')
Proof
  rpt strip_tac >>
  gvs[determine_termn_def] >>
  gvs[AllCaseEqs()]
QED



Theorem determine_term_list_never_internal1:
  ∀ simp_leaves simp_leaves' n rec.             
    determine_termn_list rec simp_leaves = simp_leaves'  ⇒
    (~ ∃ lbl lbl' x x' x'' p p' .
         ALOOKUP simp_leaves' n = SOME (x , lbl, lbl') ∧
         lbl = (non_termn (SOME x',p)) ∧
         lbl' = (non_termn (SOME x'',p')))
Proof
  Induct >>
  rpt strip_tac >>
  gvs[determine_termn_list_def] >>
  imp_res_tac mk_body_map4 >>
  PairCases_on ‘h’ >> gvs[] >>
  gvs[AllCaseEqs()] >>
  imp_res_tac determine_term_never_internal
QED



Theorem determine_term_list_never_internal_r:
  ∀ simp_leaves simp_leaves' n x lbl lbl' rec.             
    determine_termn_list rec simp_leaves = simp_leaves'  ⇒
    ALOOKUP simp_leaves' n = SOME (x , lbl, lbl') ⇒
    (~ ∃  x' x'' p p' . lbl = (non_termn (SOME x',p)))
Proof
  Induct >>
  rpt strip_tac >>
  gvs[determine_termn_list_def] >>
  imp_res_tac mk_body_map4 >>
  PairCases_on ‘h’ >> gvs[] >>
  gvs[AllCaseEqs()] >>
  imp_res_tac determine_term_never_internal >>
  res_tac >>
  metis_tac []
QED



Theorem determine_term_list_never_internal_l:
  ∀ simp_leaves simp_leaves' n x lbl lbl' rec.             
    determine_termn_list rec simp_leaves = simp_leaves'  ⇒
    ALOOKUP simp_leaves' n = SOME (x , lbl, lbl') ⇒
    (~ ∃  x' x'' p p' .
         lbl' = (non_termn (SOME x'',p')))
Proof
  Induct >>
  rpt strip_tac >>
  gvs[determine_termn_list_def] >>
  imp_res_tac mk_body_map4 >>
  PairCases_on ‘h’ >> gvs[] >>
  gvs[AllCaseEqs()] >>
  imp_res_tac determine_term_never_internal >>
  res_tac >>
  metis_tac []
QED


       
Theorem mk_new_labels_cons_imp:
  ∀ simp_leaves' h h1 h2 t c.
    mk_new_labels (h::simp_leaves') c = h1::h2::t ⇒
    mk_new_labels (simp_leaves') (c+2) = t
Proof
  rpt strip_tac >> 
  PairCases_on ‘h’ >> gvs[] >>
  PairCases_on ‘h1’ >> gvs[] >>
  PairCases_on ‘h2’ >> gvs[] >>
  gvs[mk_new_labels_def]
QED

                   
       
Theorem mk_new_labels_range_exsists:
  ∀   simp_leaves' new_labels  lbl n c.
    ALL_DISTINCT (MAP FST simp_leaves') ∧
    mk_new_labels simp_leaves' c = new_labels ∧
    ALOOKUP new_labels n = SOME (lbl) ⇒
    (∃ n' x lbl' . (ALOOKUP simp_leaves' n' = SOME (x,lbl,lbl') ∨
                    ALOOKUP simp_leaves' n' = SOME (x,lbl',lbl) ∨
                    ALOOKUP simp_leaves' n' = SOME (x,lbl,lbl))
    )
Proof
  Induct >-
   rgs[mk_new_labels_def] >>
  Induct_on ‘new_labels’ >-
   rgs[mk_new_labels_def] >>
  rpt strip_tac >>
  
  PairCases_on ‘h’ >> gvs[] >>
  PairCases_on ‘h'’ >> gvs[] >>
  
  gvs[AllCaseEqs()] >| [
    gvs[mk_new_labels_def] >>
    qexistsl_tac [‘h'0’,‘h'1’,‘h'3’] >>
    gvs[]
    ,
    
    Cases_on ‘new_labels’ >> gvs[] >>
    PairCases_on ‘h’ >> rgs[] >>
    gvs[mk_new_labels_def] >>
    gvs[AllCaseEqs()] >|[
        qexistsl_tac [‘h'0’,‘h'1’,‘h'2’] >>
             gvs[]
             ,
             rgs[] >>
             last_x_assum (strip_assume_tac o (Q.SPECL [‘lbl’, ‘n’, ‘c+2’])) >>
             gvs[] >>
             (qexistsl_tac [‘n'’, ‘x’, ‘lbl'’] >>
                  gvs[] >>
                  strip_tac >>
                  imp_res_tac ALOOKUP_MEM >>
                  imp_res_tac mem_triple_map_fst >>
                  gvs[])
      ]
  ]
QED



Theorem new_labels_are_not_internal:      
  ∀ simp_leaves' (simp_leaves: (num # string # 'a # 'a)list) new_labels c n rec.
    ALL_DISTINCT (MAP FST simp_leaves') ∧  
    determine_termn_list rec simp_leaves = simp_leaves' ∧
    mk_new_labels simp_leaves' c = new_labels ⇒
    ~ ∃ x p . ALOOKUP new_labels n = SOME (non_termn (SOME x,p))
Proof
 rpt strip_tac >>

 assume_tac (INST_TYPE [“:'a” |-> “:num” ,
                        “:'b” |-> “:string” ,
                        “:'c” |-> “:('a,'b) label” ] mk_new_labels_range_exsists)  >>

 first_x_assum (strip_assume_tac o (Q.SPECL [‘simp_leaves'’, ‘new_labels’, ‘(non_termn (SOME x,p))’, ‘n’, ‘c’])) >>
 rgs[] >|[

    assume_tac (INST_TYPE [“:'a” |-> “:num” , “:'b” |-> “:string”,  “:'c” |-> “:'a”,  “:'d” |-> “:'b” ] determine_term_list_never_internal_r)  >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘simp_leaves’, ‘simp_leaves'’, ‘n'’])) >>
    rgs[]
    ,
    assume_tac (INST_TYPE [“:'a” |-> “:num” , “:'b” |-> “:string”,  “:'c” |-> “:'a”,  “:'d” |-> “:'b” ] determine_term_list_never_internal_l)  >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘simp_leaves’, ‘simp_leaves'’, ‘n'’])) >>
    rgs[]
    ,
    assume_tac (INST_TYPE [“:'a” |-> “:num” , “:'b” |-> “:string”,  “:'c” |-> “:'a”,  “:'d” |-> “:'b” ] determine_term_list_never_internal_r)  >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘simp_leaves’, ‘simp_leaves'’, ‘n'’])) >>
    rgs[]
  ]               
QED



Theorem lookup_non_term_leaf_updt_internal:        
  ∀ labels h n x p.
    ALOOKUP (non_term_leaf_updt labels h) n = SOME (non_termn (SOME x,p)) ⇒
    (ALOOKUP labels n = SOME (non_termn (NONE,p)) ∧ x = h ∨
    ALOOKUP labels n = SOME (non_termn (SOME x,p)))
Proof
  Induct >>
  rpt strip_tac >>
  gvs[non_term_leaf_updt_def] >>
  PairCases_on ‘h’ >> gvs[] >>
  rgs[AllCaseEqs()] >>
  gvs[AllCaseEqs()] >>
  rpt(BasicProvers.FULL_CASE_TAC >> gvs[])
QED


        
Theorem leaf_parents_lookup:        
  ∀ edges  n.
    ALL_DISTINCT (MAP FST edges) ∧
    MEM n (dom_range_edges edges) ∧
    ALOOKUP edges n = NONE ⇒
    ∃ n' n''. (ALOOKUP edges n' = SOME (n'', n) ∨
               ALOOKUP edges n' = SOME (n, n'') ∨
               ALOOKUP edges n' = SOME (n, n)
              )
Proof
  Induct >-
   gvs[getLeaves_def, dom_range_edges_def] >>
  rpt strip_tac >>
  gvs[getLeaves_def, dom_range_edges_def] >>
  gvs[AllCaseEqs()] >|[
    PairCases_on ‘h’ >>
    gvs[] >| [
      qexistsl_tac [‘h0’,‘h2’] >>
      gvs[]
      ,
      qexistsl_tac [‘h0’,‘h1’] >>
      gvs[]
    ]
    ,
    
    first_x_assum (strip_assume_tac o (Q.SPECL [‘n’])) >>
    gvs[] >>
    
    PairCases_on ‘h’ >>
    gvs[] >>

    gvs[AllCaseEqs()] >>
        qexistsl_tac [‘n'’,‘n''’] >>
        gvs[] >>
        rpt strip_tac >>
        imp_res_tac ALOOKUP_MEM >>
        imp_res_tac mem_fst_snd >>
        gvs[ALOOKUP_MEM]
]
QED                    
                


Theorem get_leaves_list_thm_helper1:
  ∀ edges h0 h1 h2.
    h0 ≠ h1 ∧
    ALOOKUP edges h1 = NONE ⇒
    MEM h1 (get_leaves_list ((h0,h1,h2)::edges))
Proof
  gvs[get_leaves_list_def] >>
  rpt strip_tac >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  rgs[MEM_FILTER] >>
  rgs[ALOOKUP_NONE]
QED  



Theorem get_leaves_list_thm_helper2:
  ∀ edges h0 h1 h2.
    h0 ≠ h2 ∧
    ALOOKUP edges h2 = NONE ⇒
    MEM h2 (get_leaves_list ((h0,h1,h2)::edges))
Proof
  gvs[get_leaves_list_def] >>
  rpt strip_tac >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  rgs[MEM_FILTER] >>
  rgs[ALOOKUP_NONE]
QED 



Theorem MEM_FLAT_tri1:
  ∀ edges n.    
    ¬MEM n (MAP FST edges) ∧
    MEM n (FLAT (MAP (λ(k,v1,v2). [k; v1; v2]) edges)) ⇒
    MEM n (FLAT (MAP (λ(k,v1,v2). [v1; v2]) edges))
Proof
  Induct >>
  gvs[] >>
  rpt strip_tac >>
  PairCases_on ‘h’ >> gvs[]
QED


    
Theorem leafs_in_get_leaves_list_triv:
  ∀ edges n h0 h1 h2.
    h0 ≠ n ∧
    ALOOKUP edges n = NONE ∧
    MEM n (FLAT (MAP (λ(k,v1,v2). [k; v1; v2]) edges)) ⇒
    MEM n (get_leaves_list ((h0,h1,h2)::edges))
Proof
  rpt strip_tac >>
  gvs[get_leaves_list_def] >>
  rpt strip_tac >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  rgs[MEM_FILTER] >>
  rgs[ALOOKUP_NONE] >>
  gvs[MEM_FLAT_tri1]
QED      



Theorem leaves_in_get_leaves:    
  ∀  edges n r leaves  .
    ALL_DISTINCT (MAP FST edges) ∧
    ALOOKUP edges n = NONE ∧
    MEM n (dom_range_edges edges) ∧
    getLeaves edges r = SOME leaves ⇒
    MEM n leaves  
Proof                  
  Induct >-
   gvs[dom_range_edges_def] >>
  rpt strip_tac >>
  PairCases_on ‘h’ >> gvs[] >>
  gvs[AllCaseEqs()] >>
  gvs[getLeaves_def] >>
  gvs[AllCaseEqs()] >>
  
  gvs[dom_range_edges_def] >|[
    gvs[get_leaves_list_thm_helper1]
    ,
    gvs[get_leaves_list_thm_helper2]
    ,
    gvs[leafs_in_get_leaves_list_triv]
  ]
QED



Theorem leaves_in_ntl_lemma:
  ∀ leaves labels leaves_labels ntl p n.
    MEM n leaves ∧
    ALOOKUP labels n = SOME (non_termn (NONE,p)) ∧
    getLabels labels leaves = SOME leaves_labels  ∧
    extract_nontermn leaves_labels = SOME ntl ⇒
    ALOOKUP ntl n = SOME p
Proof
  Induct_on ‘leaves_labels’ >>                        
  rpt strip_tac >>
  imp_res_tac mk_body_map1 >>
  gvs[extract_nontermn_def] >>
  PairCases_on ‘h’ >> gvs[]  >>                  
  gvs[getLabels_def] >>
  gvs[AllCaseEqs()] >>
  gvs[extract_nontermn_def] >>
  gvs[AllCaseEqs()] >>
  res_tac >>
  gvs[] >>
  rpt strip_tac >>
  gvs[]     
QED



Theorem dom_range_edges_in_sec:
  ∀ edges new_edges n.
    MEM n (dom_range_edges (edges ⧺ new_edges)) ∧
    ¬MEM n (dom_range_edges edges) ⇒
    MEM n (dom_range_edges new_edges)
Proof
  rpt strip_tac >>
  gvs[dom_range_edges_def]
QED
       


Theorem mem_new_edges_labels_thm1:
  ∀ simp_leaves' n n' n'' c.       
    ¬MEM n (MAP FST (mk_new_edges simp_leaves' c)) ∧
    (MEM (n',n,n'') (mk_new_edges simp_leaves' c) ∨
     MEM (n',n'',n) (mk_new_edges simp_leaves' c) ∨
     MEM (n',n,n) (mk_new_edges simp_leaves' c)
    ) ⇒
    MEM n (MAP FST (mk_new_labels simp_leaves' c))
Proof
  Induct >>
  gvs[mk_new_edges_def] >>
  rpt strip_tac >>
  PairCases_on ‘h’ >> 
  gvs[mk_new_edges_def, mk_new_labels_def] >>
  Cases_on ‘n=c’ >> gvs[] >>
  Cases_on ‘n=c+1’ >> gvs[] >>
  res_tac
QED



Theorem distinct_mem_lookup_local:        
  ∀ l n .
    ALL_DISTINCT (MAP FST l) ∧
    MEM n (MAP FST l) ⇒
    ∃ elem. ALOOKUP l n= SOME elem
Proof
  Induct >>
  gvs[] >>
  rpt strip_tac >>
  PairCases_on ‘h’ >> gvs[] >>
  rgs[AllCaseEqs()]  >>
  res_tac >>
  gvs[] >>
  Cases_on ‘h0 = n’ >> gvs[]
QED
        
    

Theorem lookup_new_edges_labels_thm1:
  ∀ simp_leaves' new_edges new_labels n n' n'' c.
    ALL_DISTINCT (MAP FST (mk_new_labels simp_leaves' c)) ∧
    ALOOKUP new_edges n = NONE ∧
    mk_new_edges simp_leaves' c = new_edges ∧
    mk_new_labels simp_leaves' c = new_labels ∧
    ( ALOOKUP new_edges n' = SOME (n'',n) ∨
      ALOOKUP new_edges n' = SOME (n,n'') ∨
      ALOOKUP new_edges n' = SOME (n,n)) ⇒
    ∃ lbl . ALOOKUP new_labels n = SOME lbl
Proof
  gvs[mk_new_edges_def] >>
  rpt strip_tac >>
  imp_res_tac ALOOKUP_MEM >>
  gvs[ALOOKUP_NONE] >>
  
  ‘MEM n (MAP FST (mk_new_labels simp_leaves' c))’ by imp_res_tac mem_new_edges_labels_thm1 >>
  imp_res_tac distinct_mem_lookup_local >>
  gvs[]
QED                                     



Theorem dom_range_edges_none:
  ∀ edges n.                                        
    ¬MEM n (dom_range_edges edges) ⇒
    ALOOKUP edges n = NONE
Proof
  Induct >>
  gvs[dom_range_edges_def] >>
  rpt strip_tac>>
  PairCases_on ‘h’ >>
  gvs[dom_range_edges_def]
QED



Theorem non_term_leaf_updt_imp_not_ntl:
  ∀ labels h x n.
    ALL_DISTINCT (MAP FST (non_term_leaf_updt labels h)) ∧
    ALOOKUP (non_term_leaf_updt labels h) n = SOME x ⇒
    (~∃p. x = non_termn (NONE,p)) 
Proof
  Induct >-
   gvs[non_term_leaf_updt_def] >>
  rpt gen_tac>>
  strip_tac>>
  
  gvs[Once non_term_leaf_updt_cons] >>
  rgs[Once non_term_leaf_updt_cons] >>
  
  gvs[ALOOKUP_APPEND] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >|[
    gvs[ALL_DISTINCT_APPEND] >>
    res_tac >>
    gvs[]
    ,
    rgs[Once non_term_leaf_updt_def] >>
    PairCases_on ‘h’ >> gvs[] >>
    Cases_on ‘h1’ >> gvs[] >>
    Cases_on ‘p’ >> gvs[] >>
    Cases_on ‘q’ >> gvs[]
  ]
QED



Theorem non_term_leaf_updt_imp_term:
  ∀ labels h nt n.
    ALL_DISTINCT (MAP FST (non_term_leaf_updt labels h))  ∧
    ALOOKUP (non_term_leaf_updt labels h) n = SOME (termn nt) ⇒
    ALOOKUP labels n = SOME (termn nt)
Proof
  Induct >-
   gvs[non_term_leaf_updt_def] >>
  rpt gen_tac>>
  strip_tac>>
  
  gvs[Once non_term_leaf_updt_cons] >>
  rgs[Once non_term_leaf_updt_cons] >>
  gvs[ALL_DISTINCT_APPEND] >>  
  gvs[ALOOKUP_APPEND] >>
  
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >|[
    
    res_tac >>
    gvs[] >>
    PairCases_on ‘h’ >> gvs[] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
    gvs[non_term_leaf_updt_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[])
    ,
    
    PairCases_on ‘h’ >> gvs[] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
    gvs[non_term_leaf_updt_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[])
  ]
QED



Theorem leaves_labels_same_in_labels_some:
  ∀ labels leaves leaves_labels n x.        
    ALL_DISTINCT (MAP FST labels) ∧
    ALOOKUP labels n = SOME x ∧
    MEM n leaves ∧
    getLabels labels leaves = SOME leaves_labels ⇒                           
    ALOOKUP leaves_labels n = SOME x
Proof
  Induct_on ‘leaves’ >>
  rpt strip_tac >>
  imp_res_tac mk_body_map1 >>
  gvs[] >>
  Cases_on ‘leaves_labels’ >> gvs[] >>
  PairCases_on ‘h'’ >> gvs[] >>
  gvs[getLabels_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  res_tac
QED  
        




Theorem alookup_defined_append1:
  ∀ l l' n a b.
    ALOOKUP (l ++ l') n = SOME (a,b) ⇒
    ALOOKUP l n = NONE ⇒
    ∃ a' b' . ALOOKUP l' n = SOME (a',b') ∧ a' = a ∧  b' = b 
Proof
  gvs[ALOOKUP_APPEND] >>
  rpt strip_tac >>
  fs[AllCaseEqs()]
QED


Theorem alookup_defined_append2:
  ∀ l l' n a b a' b'.
    ALOOKUP (l ++ l') n = SOME (a,b) ∧
    ALOOKUP l n = SOME (a',b') ⇒
    a' = a ∧  b' = b 
Proof
  gvs[ALOOKUP_APPEND] >>
  rpt strip_tac >>
  fs[AllCaseEqs()]
QED


Theorem ADELKEY_APPEND_triv:
  ∀ l1 l2 n.
    ADELKEY n (l1++l2) = (ADELKEY n l1) ++ (ADELKEY n l2)
Proof
  Induct >>
  gvs[ADELKEY_def] >>
  rpt strip_tac >>
  rpt (BasicProvers.FULL_CASE_TAC >> rgs[]) 
QED



Theorem lookup_merge_uni_bs:
  ALOOKUP (merge_edges [(h0,h1,h2)] n n') n'' = SOME (x0,x1) 
  ⇒
  ((x0 = nr' ∧  nr = h1 ∧  nr ≠ nr' ⇒ (nr = n' ∧ nr' = n))
   ∧
   (x1 = nl' ∧  nl = h2 ∧  nl ≠ nl' ⇒ (nl = n' ∧ nl' = n)
   ))
Proof
  fs[Once merge_edges_def] >>
  rpt strip_tac >>
  fs[AllCaseEqs()]
QED



Theorem MEM_ALOOKUP_DISTINCT:                
  ∀ l  a  b.
    ALL_DISTINCT (MAP FST l) ⇒
    (MEM (a,b) l ⇔ (ALOOKUP l a = SOME b))
Proof
  Induct >> gvs[] >>
  rpt strip_tac >>
  PairCases_on ‘h’ >> gvs[] >>
  Cases_on ‘a = h0’ >> gvs[] >>
  Cases_on ‘b = h1’ >> gvs[] >>
  Cases_on ‘ALOOKUP l a’ >> gvs[] >>
  imp_res_tac ALOOKUP_NONE >>
  gvs[]
QED


Theorem list_mem_trio_not:
  ∀ l n h1 h2.
    ¬MEM n (MAP FST l) ⇒    
    ¬MEM (n,h1,h2) l
Proof
  Induct >>
  rw[] >>
  PairCases_on ‘h’ >>
  res_tac >>
  gvs[]
QED


Theorem mem_imp_adelkey_mem:
  ∀ l  n'' n'.
    n'' ≠ n' ∧
    MEM n'' (MAP FST l) ⇒
    MEM n'' (MAP FST (ADELKEY n' l))
Proof
  Induct >> rw[] >> fs[ADELKEY_def] >>
  Cases_on ‘h’ >> fs[ADELKEY_def] >>
  rw[] >> fs[] >>
  metis_tac[]
QED


        
Theorem adelkey_mem_imp_mem:
  ∀ l  n'' n'.
    n'' ≠ n' ∧
    MEM n'' (MAP FST (ADELKEY n' l)) ⇒
    MEM n'' (MAP FST l)
Proof
  
  Induct >> 
  fs[ADELKEY_def] >>
  Cases_on ‘h’ >> 
  rpt (BasicProvers.FULL_CASE_TAC >> rgs[ADELKEY_def]) >> rw[] >| [
    fs[MEM_MAP] >>
    ‘∃x. n'' = FST x ∧ MEM x l ∧ FST x ≠ n'’ by metis_tac[MEM_FILTER] >>
    
    Cases_on ‘FST y = q’ >> gvs[] >>
    qexists_tac ‘x’ >> gvs[]
    ,
    Cases_on ‘n'' = q’ >> fs[] >>
    metis_tac[] 
  ]     
QED

    

Theorem not_mem_imp_adelkey_mem:
  ∀ l  n'' n'.
    n'' ≠ n' ∧
    ¬MEM n'' (MAP FST l) ⇒
    ¬MEM n'' (MAP FST (ADELKEY n' l))
Proof
  Induct_on `l` >> rw[] >- gvs[ADELKEY_def, MAP, MEM] >>
  Cases_on `h` >> fs[ADELKEY_def] >>
  rw[] >> fs[]
QED

        
val _ = export_theory ();
