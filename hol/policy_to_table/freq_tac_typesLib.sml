structure freq_tac_typesLib :> freq_tac_typesLib = struct

open HolKernel boolLib simpLib Parse bossLib;

open bdd_auxTheory;



val body_of_mk_pred_tac =
( rename1 ‘getLeaves edges r = SOME leaves’ >>
  rename1 ‘getLabels labels leaves = SOME leaves_labels’ >>
  rename1 ‘extract_nontermn leaves_labels = SOME ntl’ >>

  ‘∃ leaves_sub . leaves_pred_sub rec ntl h = leaves_sub’ by gvs[] >>
  ‘∃ simp_leaves . simp_pred_list rec leaves_sub = simp_leaves’ by gvs[] >>
  ‘∃ simp_leaves' . determine_termn_list rec simp_leaves = simp_leaves'’ by gvs[] >>
  ‘∃ new_edges . mk_new_edges simp_leaves' c = new_edges’ by gvs[] >>
  ‘∃ new_labels . mk_new_labels simp_leaves' c = new_labels’ by gvs[] >>
  rgs[] );



val imp_res_tac_body =
(imp_res_tac mk_body_map1 >>
 imp_res_tac mk_body_map2 >>
 imp_res_tac mk_body_map3 >>
 imp_res_tac mk_body_map4 >>
 imp_res_tac mk_body_map5 >>
 imp_res_tac mk_body_map6);



val imp_res_tac_distinct =
(imp_res_tac all_distinct_leaves >>
 imp_res_tac all_distinct_leaves_labels >>
 imp_res_tac all_distinct_ntl >>
 imp_res_tac all_distinct_sub >>
 imp_res_tac all_distinct_simp >>
 imp_res_tac all_distinct_determine >>
 imp_res_tac all_distinct_mk_edges >>
 imp_res_tac all_distinct_non_term_leaf_updt >>
 imp_res_tac all_distinct_mk_labels
);


end;
