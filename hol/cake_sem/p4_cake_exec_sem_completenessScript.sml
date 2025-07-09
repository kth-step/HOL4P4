open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_cake_exec_sem_completeness";

open p4Theory p4_auxTheory p4_cake_exec_semTheory;
open p4_cake_transformTheory;

Definition dict_bij_def:
 dict_bij dict =
  !k v.
  MEM (k,v) dict ==>
  UNIQUE k (MAP FST dict) /\ UNIQUE v (MAP SND dict)
End

Theorem UNIQUE_HEAD:
!x xs. UNIQUE x (x::xs) <=> ~MEM x xs
Proof
rpt strip_tac >>
EQ_TAC >- (
 rpt strip_tac >>
 gs[listTheory.UNIQUE_DEF] >>
 Cases_on ‘L1’ >> (
   gvs[]
 )
) >>
rpt strip_tac >>
gs[listTheory.UNIQUE_DEF] >>
qexistsl_tac [‘[]’, ‘xs’] >>
gs[]
QED

Theorem UNIQUE_TAIL:
!x x' xs. (UNIQUE x (x'::xs) /\ x ≠ x') ==> UNIQUE x xs
Proof
rpt strip_tac >>
gs[listTheory.UNIQUE_DEF] >>
Cases_on ‘L1’ >> (
 gvs[]
) >>
qexistsl_tac [‘t’, ‘L2’] >>
gs[]
QED

Theorem TWO_UNIQUE_LEMMA:
!dict v.
UNIQUE v (MAP SND dict) ==>
!k. MEM (k,v) dict ==> !k'. k' ≠ k ==> ~MEM (k',v) dict
Proof
Induct >- (
 gvs[listTheory.MEM]
) >>
Cases_on ‘h’ >> rename1 ‘(key, val)::t’ >>
rpt strip_tac >>
gvs[UNIQUE_HEAD, listTheory.MEM, listTheory.MEM_MAP] >>
Cases_on ‘v = val’ >- (
 gs[listTheory.MEM_MAP, UNIQUE_HEAD]
) >>
metis_tac[UNIQUE_TAIL]
QED

(* TODO: Move *)
Theorem TWO_UNIQUE:
!k1 k2 v1 v2 dict.
dict_bij dict ==>
k1 <> k2 ==>
MEM (k1,v1) dict ==>
MEM (k2,v2) dict ==>
v1 ≠ v2
Proof
rpt strip_tac >>
gs[dict_bij_def] >>
res_tac >>
gvs[] >>
metis_tac[TWO_UNIQUE_LEMMA]
QED

Theorem dict_bij_injectivity:
!dict k1 k2 v.
dict_bij dict ==>
ALOOKUP dict k1 = SOME v ==>
ALOOKUP dict k2 = SOME v ==>
k1 = k2
Proof
rpt strip_tac >>
‘MEM (k1, v) dict’ by metis_tac[alistTheory.ALOOKUP_MEM] >>
‘MEM (k2, v) dict’ by metis_tac[alistTheory.ALOOKUP_MEM] >>
‘UNIQUE v (MAP SND dict)’ by metis_tac[dict_bij_def] >>
metis_tac[TWO_UNIQUE_LEMMA]
QED

(* TODO: Now the property is formulated in terms of a relation that is kept:

                  exec
              s1  ====> s2
               |         |
     translate |         |
               |         |
               v         v
              s'1 ====> s'2
                  exec'

instead of a simulation:

                  exec
              s1  ====> s2
               |         ^
     translate |         | translate'
               |         |
               v         |
              s'1 ====> s'2
                  exec'

*)

(* TODO: Generalise from just V1Model *)
Definition transform_ectx_def:
 transform_ectx dict (ext_map, func_map, b_func_map) =
  transform_ext_map dict ext_map >>=
  \ext_map'. transform_func_map dict func_map >>=
  \func_map'. transform_func_map dict b_func_map >>=
  \b_func_map'. SOME (ext_map':v1model_ascope' ext_map', func_map':func_map', b_func_map':b_func_map')
End

Definition transform_frame_def:
 transform_frame dict (funn, stmt_stack, scope_list) =
  transform_funn dict funn >>=
  \funn'. oFOLDR (transform_stmt dict) stmt_stack >>=
  \stmt_stack'. transform_scope_list dict scope_list >>=
  \scope_list'. SOME (funn':funn', stmt_stack':stmt' list, scope_list':scope_list')
End

Definition transform_frame_list_def:
 transform_frame_list dict frame_list =
  oFOLDR (transform_frame dict) frame_list
End

(* TODO: Generalise from V1Model *)
Definition e_exec'_complete_def:
 e_exec'_complete e'1 =
  !e1 dict ext_map func_map b_func_map g_scope_list' g_scope_list scope_list' scope_list e_ctx.
  dict_bij dict ==>
  transform_ectx dict (ext_map, func_map, b_func_map) = SOME e_ctx ==>
  transform_scope_list dict g_scope_list = SOME g_scope_list' ==>
  transform_scope_list dict scope_list = SOME scope_list' ==>
  transform_e dict e1 = SOME e'1 ==>
  !apply_table_f pars_map tbl_map e2 e'2 frame_list frame_list'.
  e_exec uninit_zero (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map) (g_scope_list:g_scope_list) (scope_list:scope_list) e1 = SOME (e2, frame_list) ==>
  transform_e dict e2 = SOME e'2 ==>
  transform_frame_list dict frame_list = SOME frame_list' ==>
  e_exec' (e_ctx:v1model_ascope' e_ctx) (g_scope_list':g_scope_list') (scope_list':scope_list') e'1 = SOME (e'2, frame_list')
End

Definition w_e_exec'_complete_def:
 (w_e_exec'_complete (w:word64, e) = e_exec'_complete e)
End

Definition l_complete_def:
 (l_complete [] = T) /\
 (l_complete (l:e' list) = 
  !i e. (SOME e = oEL i l) ==> e_exec'_complete e)
End
(* More convenient alternate form of the above *)
Definition l_complete_exec_def:
 (l_complete_exec [] = T) /\
 (l_complete_exec ((h::t):e' list) = 
  (e_exec'_complete h /\ l_complete_exec t))
End

Definition w_e_l_exec'_complete_def:
 (w_e_l_exec'_complete (w_e_l:(word64 # e') list) = l_complete (MAP SND w_e_l))
End

Theorem l_complete_cons:
!h l. l_complete (h::l) ==> l_complete l
Proof
rpt strip_tac >>
Induct_on ‘l’ >> (
 gs[l_complete_def]
) >>
rpt strip_tac >>
qpat_x_assum ‘!x e. _’ (fn thm => assume_tac $ Q.SPECL [‘SUC i’, ‘e’] thm) >>
gs[] >>
‘oEL i (h'::l) = oEL (SUC i) (h::h'::l)’ suffices_by (
 gs[]
) >>
Induct_on ‘i’ >> (
 gs[listTheory.oEL_def]
)
QED

Theorem l_complete_equiv:
!type l. l_complete l <=> l_complete_exec l
Proof
rpt strip_tac >>
EQ_TAC >| [
 Induct_on ‘l’ >> (
  gs[l_complete_def, l_complete_exec_def]
 ) >>
 rpt strip_tac >| [
  qpat_x_assum ‘!x e. _’ (fn thm => assume_tac $ Q.SPEC ‘0:num’ thm) >>
  gs[listTheory.oEL_def],

  ‘l_complete (h::l)’ suffices_by (
   metis_tac[l_complete_cons]
  ) >>
  metis_tac[l_complete_def]
 ],

 Induct_on ‘l’ >> (
  gs[l_complete_def, l_complete_exec_def]
 ) >>
 NTAC 3 strip_tac >>
 Induct_on ‘i’ >> (
  gs[listTheory.oEL_def]
 ) >>
 ‘!i e. SOME e = oEL i l ==> e_exec'_complete e’ suffices_by (
  metis_tac[oEL_cons_PRE]
 ) >>
 gs[] >>
 Cases_on ‘l’ >- (
  gs[listTheory.oEL_def]
 ) >>
 metis_tac[l_complete_def]
]
QED

Theorem l_complete_MEM:
 !e l.
 MEM e l ==>
 l_complete l ==>
 e_exec'_complete e
Proof
Induct_on ‘l’ >> (
 gs[]
) >>
rpt strip_tac >> (
 gs[l_complete_equiv, l_complete_exec_def]
)
QED

Definition reverse_dict_def:
  reverse_dict dict = MAP (\(a,b). (b,a)) dict
End

(*
(* TODO: This should rather be "reversibility under ALOOKUP" or something *)
Definition dict_bij_def:
 dict_bij dict =
  !a b.
  ALOOKUP dict a = SOME b <=>
  ALOOKUP (reverse_dict dict) b = SOME a
End
*)

(* TODO: Needed? *)
Theorem transform_v_struct_split:
!p p' l l' dict.
transform_v dict (v_struct (p::l)) = SOME (v'_struct (p'::l')) ==>
transform_v dict (v_struct [p]) = SOME (v'_struct [p']) /\
transform_v dict (v_struct l) = SOME (v'_struct l')
Proof
rpt strip_tac >- (
 gs[Once transform_v_def, AllCaseEqs()] >>
 simp[Once transform_v_def, AllCaseEqs()] >>
 simp[Once transform_v_def, AllCaseEqs()]
) >>
gs[Once transform_v_def, AllCaseEqs()]
QED

Theorem lookup_transform_v_struct:
!dict x w t t' v' v.
 dict_bij dict ==>
 transform_v dict (v_struct t) = SOME (v'_struct t') ==>
 ALOOKUP t x = SOME v ==>
 transform_v dict v = SOME v' ==>
 ALOOKUP dict x = SOME w ==>
 ALOOKUP t' w = SOME v'
Proof
rpt strip_tac >>
(* When transforming a struct, the names of fields are translated according to dict.
 * If an entry exists in the original table, the dictionary-translated entry must exist
 * in the translated struct - in fact, at the same location. The value is then the translated version
  * of the original entry. *)
cheat
QED
        
Theorem INDEX_FIND_index:
 !a l P b.
 INDEX_FIND 0 P l = SOME (a,b) ==>
 INDEX_FIND 1 P l = SOME (a+1,b)
Proof
rpt strip_tac >>
simp[Once listTheory.INDEX_FIND_add]
QED

(* TODO: Move? *)
Theorem alookup_find:
!l k v.
(FIND (λ(k',v'). k' = k) l = SOME (k,v)) <=>
ALOOKUP l k = SOME v
Proof
Induct >- (
 gs[listTheory.FIND_def, listTheory.INDEX_FIND_def]
) >>
rpt strip_tac >>
Cases_on ‘h’ >>
gs[listTheory.FIND_def, listTheory.INDEX_FIND_def, AllCaseEqs()] >>
Cases_on ‘q = k’ >> (
 gs[]
) >- (
 (* Why metis needed here? *)
 metis_tac[]
) >>
qpat_x_assum ‘!k v. _’ (fn thm => ASSUME_TAC $ Q.SPECL [‘k’, ‘v’] thm) >>
eq_tac >- (
 rpt strip_tac >>
 ‘?i. INDEX_FIND 0 (λ(k',v'). k' = k) l = SOME (i, (k,v))’ suffices_by (strip_tac >> gs[]) >>
 Cases_on ‘z’ >>
 qexists_tac ‘q' - 1’ >>
 gvs[] >>
 qpat_x_assum ‘(?z. INDEX_FIND 0 (λ(k',v'). k' = k) l = SOME z ∧ (k,v) = SND z) ⇔
        ALOOKUP l k = SOME v’ (fn thm => ALL_TAC) >>
 gs[Once listTheory.INDEX_FIND_add] >>
 Cases_on ‘z’ >>
 gs[]
) >>
rpt strip_tac >>
gvs[] >>
Cases_on ‘z’ >>
qexists_tac ‘(q' + 1, r)’ >>
gvs[INDEX_FIND_index]
QED

(* Completeness of acc, non-recursive case *)
Theorem e_exec'_acc_complete:
!dict e'1 e' x c e2 e'2.
 dict_bij dict ==>
 is_v' e'1 ==>
 transform_e dict e' = SOME e'1 ==>
 ALOOKUP dict x = SOME c ==>
 e_exec_acc (e_acc e' x) = SOME e2 ==>
 transform_e dict e2 = SOME e'2 ==>
 e_exec_acc' (e'_acc e'1 c) = SOME e'2
Proof
rpt strip_tac >>
Cases_on ‘e'’ >> (gs[p4_exec_semTheory.e_exec_acc_def]) >>
Cases_on ‘v’ >> (gvs[p4_exec_semTheory.e_exec_acc_def, p4_exec_semTheory.is_v_def, AllCaseEqs()]) >> (
 gvs[transform_e_def, AllCaseEqs()] >>
 qpat_x_assum ‘transform_v dict _ = SOME v'’ (fn thm => ASSUME_TAC $ ONCE_REWRITE_RULE [transform_v_def] thm >> gvs[listTheory.FIND_thm, e_exec_acc'_def, AllCaseEqs()]) >>
 DISJ2_TAC >>
 CONJ_TAC >- (
  ‘MEM (x,c) dict’ by gs[alistTheory.ALOOKUP_MEM] >>
  ‘MEM (x',w) dict’ by gs[alistTheory.ALOOKUP_MEM] >>
  ‘UNIQUE c (MAP SND dict)’ by metis_tac[dict_bij_def] >>
  ‘UNIQUE w (MAP SND dict)’ by metis_tac[dict_bij_def] >>
  metis_tac[TWO_UNIQUE]
 ) >>
 (* Reversibility of v transformation *)
 ‘ALOOKUP t x = SOME v’ by (
  gs[GSYM alookup_find] >>
  qpat_x_assum ‘FIND (\(k,v). k = x) t = SOME (f,v)’ (fn thm => ASSUME_TAC $ REWRITE_RULE [listTheory.FIND_def] thm) >>
  gs[] >>
  Cases_on ‘z’ >>
  imp_res_tac index_find_first >>
  gs[] >>
  Cases_on ‘r’ >>
  gs[]
 ) >>
 metis_tac[lookup_transform_v_struct]
)
QED

Theorem unop_exec'_subtypes:
  !uop v v'.
  unop_exec' uop v = SOME v' ==>
  ?b. v' = v'_bool b \/ ?bitv. v' = v'_bit bitv
Proof
rpt strip_tac >>
Cases_on ‘v’ >> Cases_on ‘uop’ >> (
 gs[unop_exec'_def]
) >- (
 metis_tac[]
) >- (
 Cases_on ‘p’ >>
 gs[unop_exec'_def] >>
 metis_tac[]
) >- (
 Cases_on ‘p’ >>
 gs[unop_exec'_def, AllCaseEqs()] >>
 metis_tac[]
) >>
metis_tac[]
QED

Theorem exec_cast'_subtypes:
  !uop e' v' c.
  e_exec_cast' c e' = SOME v' ==>
  ?b. v' = v'_bool b \/ ?bitv. v' = v'_bit bitv
Proof
rpt strip_tac >>
Cases_on ‘c’ >> Cases_on ‘e'’ >> (
 gs[e_exec_cast'_def]
) >- (
 Cases_on ‘v’ >> (
  gs[cast_exec_def]
 ) >>
 metis_tac[]
) >>
Cases_on ‘v’ >> (
 gs[cast_exec_def]
) >>
Cases_on ‘p’ >> (
 gs[to_bool_cast_exec_def, AllCaseEqs()]
) >>
metis_tac[]
QED

Theorem transform_v_struct:
 !v' x_v_l dict.
 transform_v dict (v_struct x_v_l) = SOME v' ==>
 ?w_v'_l. v' = (v'_struct w_v'_l)
Proof
Induct >> (
 rpt strip_tac >>
 gs[Once transform_v_def, AllCaseEqs()]
)
QED

Theorem transform_e_header:
!e' x_e_l dict b.
transform_e dict (e_header b x_e_l) = SOME e' ==>
?w_e'_l b'. e' = e'_header b' w_e'_l
Proof
Induct >> (
 rpt strip_tac >>
 gs[Once transform_e_def, AllCaseEqs()]
) >> (
 qpat_x_assum ‘transform_e dict (e_header _ _) = SOME _’ (fn thm => assume_tac $ ONCE_REWRITE_RULE [transform_e_def] thm >> gvs[AllCaseEqs()])
)
QED

Theorem transform_e_header_validity:
!x_e_l w_e'_l dict b b'.
transform_e dict (e_header b x_e_l) = SOME $ e'_header b' w_e'_l ==>
b = b'
Proof
Induct >> Induct >> (
 rpt strip_tac >>
 gs[Once transform_e_def, AllCaseEqs()]
) >- (
 gs[Once transform_e_def, AllCaseEqs()]
) >>
qpat_x_assum ‘!w_e'_l'. _’ (fn thm => irule thm) >>
qexistsl_tac [‘dict’] >>
Cases_on ‘x_e_l’ >- (
 gs[Once transform_e_def, AllCaseEqs()] >>
 qpat_x_assum ‘transform_e dict (e_header b []) = SOME (e'_header b' t')’ (fn thm => assume_tac $ ONCE_REWRITE_RULE [transform_e_def] thm >> gvs[AllCaseEqs()])
) >>
gs[] >>
Cases_on ‘h’ >>
gvs[] >>
qpat_x_assum ‘transform_e dict (e_header b _) = SOME _’ (fn thm => assume_tac $ ONCE_REWRITE_RULE [transform_e_def] thm >> gvs[AllCaseEqs()]) >>
qpat_x_assum ‘transform_e dict (e_header b _) = SOME _’ (fn thm => assume_tac $ ONCE_REWRITE_RULE [transform_e_def] thm >> gvs[AllCaseEqs()])
QED

Theorem transform_e_subtypes:
(!dict v e'. transform_e dict (e_v v) = SOME e' ==> ?v'. e' = e'_v v') /\
(!dict varn e'. transform_e dict (e_var varn) = SOME e' ==> ?varn'. e' = e'_var varn') /\
(!dict l e'. transform_e dict (e_list l) = SOME e' ==> ?l'. e' = e'_list l') /\
(!dict e x e'. transform_e dict (e_acc e x) = SOME e' ==> ?e'' w. e' = e'_acc e'' w) /\
(!dict u e e'. transform_e dict (e_unop u e) = SOME e' ==> ?e''. e' = e'_unop u e'') /\
(!dict c e e'. transform_e dict (e_cast c e) = SOME e' ==> ?e''. e' = e'_cast c e'') /\
(!dict e1 b e2 e'. transform_e dict (e_binop e1 b e2) = SOME e' ==> ?e1' e2'. e' = e'_binop e1' b e2') /\
(!dict e1 e2 e'. transform_e dict (e_concat e1 e2) = SOME e' ==> ?e1' e2'. e' = e'_concat e1' e2') /\
(!dict e1 e2 e3 e'. transform_e dict (e_slice e1 e2 e3) = SOME e' ==> ?e1' e2' e3'. e' = e'_slice e1' e2' e3') /\
(!dict funn l e'. transform_e dict (e_call funn l) = SOME e' ==> ?funn' l'. e' = e'_call funn' l') /\
(!dict e s_l_x_l x e'. transform_e dict (e_select e s_l_x_l x) = SOME e' ==> ?e'' s'_l_w_l w n_l_l. e' = e'_select e'' s'_l_w_l w n_l_l) /\
(!dict x_e_l e'. transform_e dict (e_struct x_e_l) = SOME e' ==> ?w_e'_l. e' = e'_struct w_e'_l) /\
(!dict b x_e_l e'. transform_e dict (e_header b x_e_l) = SOME e' ==> ?w_e'_l. e' = e'_header b w_e'_l)
Proof
rpt strip_tac >- (
 gs[transform_e_def] >>
 metis_tac[]
) >- (
 gs[transform_e_def] >>
 metis_tac[]
) >- (
 (* List *)
 Cases_on ‘l’ >- (
  gs[Once transform_e_def] >>
  metis_tac[]
 ) >>
 gs[Once transform_e_def, AllCaseEqs()] >>
 metis_tac[]
) >- (
 gs[Once transform_e_def] >>
 metis_tac[]
) >- (
 gs[Once transform_e_def] >>
 metis_tac[]
) >- (
 gs[Once transform_e_def] >>
 metis_tac[]
) >- (
 gs[Once transform_e_def] >>
 metis_tac[]
) >- (
 gs[Once transform_e_def] >>
 metis_tac[]
) >- (
 gs[Once transform_e_def] >>
 metis_tac[]
) >- (
 (* Call *)
 Cases_on ‘l’ >- (
  gs[Once transform_e_def] >>
  metis_tac[]
 ) >>
 gs[Once transform_e_def, AllCaseEqs()] >>
 metis_tac[]
) >- (
 (* Select *)
 gs[Once transform_e_def, listTheory.UNZIP_MAP] >>
 metis_tac[]
) >- (
 (* Struct *)
 Cases_on ‘x_e_l’ >- (
  gs[Once transform_e_def] >>
  metis_tac[]
 ) >>
 gs[Once transform_e_def, AllCaseEqs()] >>
 gs[] >>
 metis_tac[]
) >>
(* Header *)
imp_res_tac transform_e_header >>
rw[] >>
metis_tac[transform_e_header_validity]
QED

Theorem transform_e_is_v:
!dict e e'.
is_v e ==>
transform_e dict e = SOME e' ==>
is_v' e'
Proof
rpt strip_tac >>
Cases_on ‘e’ >> (
 gs[Once transform_e_def, AllCaseEqs()] >>
 Cases_on ‘e'’ >> ( gs[p4_exec_semTheory.is_v_def, is_v'_def] )
)
QED

Theorem transform_e_not_is_v:
!dict e e'.
~is_v e ==>
transform_e dict e = SOME e' ==>
~is_v' e'
Proof
rpt strip_tac >>
Cases_on ‘e’ >> (
 gs[Once transform_e_def, AllCaseEqs()] >>
 Cases_on ‘e'’ >> ( gs[p4_exec_semTheory.is_v_def, is_v'_def] )
) >>
gs[listTheory.UNZIP_MAP]
QED

Theorem transform_e_is_v_bit:
!dict e e'.
is_v_bit e ==>
transform_e dict e = SOME e' ==>
is_v_bit' e'
Proof
rpt strip_tac >>
Cases_on ‘e’ >> (
 gs[Once transform_e_def, Once transform_v_def, AllCaseEqs()] >>
 Cases_on ‘e'’ >> ( gvs[p4_exec_semTheory.is_v_bit_def, is_v_bit'_def] ) >>
 Cases_on ‘v’ >> Cases_on ‘v'’ >> ( gs[p4_exec_semTheory.is_v_bit_def, is_v_bit'_def] )
)
QED

Theorem transform_e_not_is_v_bit:
!dict e e'.
~is_v_bit e ==>
transform_e dict e = SOME e' ==>
~is_v_bit' e'
Proof
rpt strip_tac >>
gs[] >>
Cases_on ‘e’ >> (gs[p4_exec_semTheory.is_v_bit_def]) >- (
 Cases_on ‘v’ >> (gs[p4_exec_semTheory.is_v_bit_def]) >> (
  gvs[Once transform_e_def, AllCaseEqs()] >>
  Cases_on ‘v'’ >> (
   gs[is_v_bit'_def, Once transform_v_def, AllCaseEqs()]
  )
 )
) >> (
 gvs[Once transform_e_def, AllCaseEqs()] >>
 gs[is_v_bit'_def]
) >>
gvs[listTheory.UNZIP_MAP, is_v_bit'_def]
QED

(* Reverse implication *)
Theorem transform_scope_list_lookup:
!dict g_scope_list scope_list g_scope_list' scope_list' varn varn' v v'.
dict_bij dict ==>
transform_scope_list dict g_scope_list = SOME g_scope_list' ==>
transform_scope_list dict scope_list = SOME scope_list' ==>
transform_varn dict varn = SOME varn' ==>
lookup_vexp2 scope_list g_scope_list varn = SOME v ==>
transform_v dict v = SOME v' ==> 
lookup_vexp2' scope_list' g_scope_list' varn' = SOME v'
Proof
(* Looking up a variable in scopes will return the translated value of the
 * result of looking up the translated variable name. *)
rpt strip_tac >>
gvs[lookup_vexp2_def, lookup_vexp2'_def, lookup_map_def, lookup_map'_def, topmost_map_def, AllCaseEqs()] >>
(* TODO: Formulate separate theorem here, that states the correspondence between the scopes and index returned *)
cheat
QED

Theorem unred_mem_index_same:
unred_mem_index' [] = NONE <=>
unred_mem_index [] = NONE
Proof
gs[unred_mem_index_def, unred_mem_index'_def, unred_mem_def, unred_mem'_def, AllCaseEqs(), listTheory.INDEX_FIND_def]
QED

Theorem e_exec'_completeness_var:
!v.
e_exec'_complete (e'_var v)
Proof
gs[e_exec'_complete_def] >>
rpt strip_tac >>
(* 1. Rewrite transformation of initial state *)
qpat_x_assum ‘transform_e dict e1 = SOME (e'_var v)’ (fn thm => ASSUME_TAC $ ONCE_REWRITE_RULE [transform_e_def] thm >> gvs[listTheory.UNZIP_MAP, AllCaseEqs()]) >>
(* 2. Rewrite execution *)
gvs[e_exec'_def, p4_exec_semTheory.e_exec_def, AllCaseEqs()] >>
(* 3. Rewrite transformation of final state *)
gvs[transform_e_def, transform_frame_list_def, oFOLDR_def] >>
metis_tac[transform_scope_list_lookup]
QED

Theorem e_exec'_completeness_acc:
!e c.
e_exec'_complete e ==>
e_exec'_complete (e'_acc e c)
Proof
gs[e_exec'_complete_def] >>
rpt strip_tac >>
(* 1. Rewrite transformation of initial state *)
qpat_x_assum ‘transform_e dict e1 = SOME (e'_acc e c)’ (fn thm => ASSUME_TAC $ ONCE_REWRITE_RULE [transform_e_def] thm >> gvs[listTheory.UNZIP_MAP, AllCaseEqs()]) >>
(* 2. Rewrite execution *)
gvs[e_exec'_def, p4_exec_semTheory.e_exec_def, AllCaseEqs()] >> (
 gvs[transform_frame_list_def, oFOLDR_def]
) >- (
 (* Case 2a: e' is value *)
 ‘is_v' e’ by metis_tac[transform_e_is_v] >> gs[] >>
 metis_tac[e_exec'_acc_complete]
) >>
(* Case 2b: e' is not value *)
‘~is_v' e’ by metis_tac[transform_e_not_is_v] >> gs[] >>
(* 3. Rewrite transformation of final state *)
qpat_x_assum ‘transform_e dict (e_acc e_v_struct' x) = SOME e'2’ (fn thm => ASSUME_TAC $ ONCE_REWRITE_RULE [transform_e_def] thm >> gvs[app_opt_def, AllCaseEqs()]) >>
(* 4. Use induction hypothesis *)
metis_tac[]
QED

Theorem e_exec'_completeness_unop:
!e u.
e_exec'_complete e ==>
e_exec'_complete (e'_unop u e)
Proof
gs[e_exec'_complete_def] >>
rpt strip_tac >>
(* 1. Rewrite transformation of initial state *)
qpat_x_assum ‘transform_e dict e1 = SOME (e'_unop u e)’ (fn thm => ASSUME_TAC $ ONCE_REWRITE_RULE [transform_e_def] thm >> gvs[listTheory.UNZIP_MAP, AllCaseEqs()]) >>
(* 2. Rewrite execution *)
gvs[e_exec'_def, p4_exec_semTheory.e_exec_def, AllCaseEqs()] >> (
 gvs[transform_frame_list_def, oFOLDR_def]
) >- (
 (* Case 2a: e' is value *)
 ‘is_v' e’ by metis_tac[transform_e_is_v] >> gs[] >>
(* TODO: Make separate lemma from the below... *)
 qpat_x_assum ‘!e1. _’ (fn thm => ALL_TAC) >>
 gvs[Once transform_e_def] >>
 (* Obtain the e_v subtypes *)
 Cases_on ‘e'’ >> (
  gs[p4_exec_semTheory.is_v_def]
 ) >>
 Cases_on ‘e’ >> (
  gs[is_v'_def]
 ) >> 
 Cases_on ‘u’ >> (
  gs[e_exec_unop'_def, p4_exec_semTheory.e_exec_unop_def]
 ) >> (
  Cases_on ‘v''’ >> Cases_on ‘v'''’ >>
  gs[Once transform_e_def] >>
  rfs[Once transform_v_def] >>
  gvs[unop_exec'_def, p4_exec_semTheory.e_exec_unop_def, p4_exec_semTheory.unop_exec_def] >>
  gvs[AllCaseEqs()] >>
  Cases_on ‘p’ >> (
   gs[unop_exec'_def, bitv_1comp_def, bitv_bl_unop_def, bitstringTheory.bnot_def] >>
   gs[bitv_2comp_def, AllCaseEqs()] >>
   (* TODO: Issues for "bitv_unop unop_neg_signed" since this is only defined for up to
    * a certain bitwidth... :(
    *
    * Solutions: Either make the CakeML-exportable semantics return NONE for widths over
    * 128 at an earlier stage, or have a fallback solution in the regular semantics for
    * widths over 128 *)
   cheat
  )
 )
) >>
(* Case 2b: e' is not value *)
‘~is_v' e’ by metis_tac[transform_e_not_is_v] >> gs[] >>
(* 3. Rewrite transformation of final state *)
qpat_x_assum ‘transform_e dict (e_unop u e'') = SOME e'2’ (fn thm => ASSUME_TAC $ ONCE_REWRITE_RULE [transform_e_def] thm >> gvs[app_opt_def, AllCaseEqs()]) >>
(* 4. Use induction hypothesis *)
metis_tac[]
QED

Theorem e_exec'_completeness_cast:
!e c.
e_exec'_complete e ==>
e_exec'_complete (e'_cast c e)
Proof
gs[e_exec'_complete_def] >>
rpt strip_tac >>
(* 1. Rewrite transformation of initial state *)
qpat_x_assum ‘transform_e dict e1 = SOME (e'_cast c e)’ (fn thm => ASSUME_TAC $ ONCE_REWRITE_RULE [transform_e_def] thm >> gvs[listTheory.UNZIP_MAP, AllCaseEqs()]) >>
(* 2. Rewrite execution *)
gvs[e_exec'_def, p4_exec_semTheory.e_exec_def, AllCaseEqs()] >> (
 gvs[transform_frame_list_def, oFOLDR_def]
) >- (
 (* Case 2a: e' is value *)
 ‘is_v' e’ by metis_tac[transform_e_is_v] >> gs[] >>
(* TODO: Make separate lemma from the below... *)
 qpat_x_assum ‘!e1. _’ (fn thm => ALL_TAC) >>
 gvs[Once transform_e_def] >>
 Cases_on ‘e''’ >> (
  gs[p4_exec_semTheory.is_v_def]
 ) >>
 Cases_on ‘e’ >> (
  gs[is_v'_def]
 ) >> 
 Cases_on ‘c’ >> (
  gs[e_exec_cast'_def, p4_exec_semTheory.e_exec_cast_def]
 ) >> (
  Cases_on ‘v''’ >> Cases_on ‘v'''’ >>
  gs[Once transform_e_def] >>
  rfs[Once transform_v_def] >>
  gvs[cast_exec_def, p4_exec_semTheory.e_exec_cast_def, p4_exec_semTheory.cast_exec_def, to_bool_cast_exec_def, p4_exec_semTheory.to_bool_cast_exec_def] >>
  gvs[AllCaseEqs()]
 )
) >>
(* Case 2b: e' is not value *)
‘~is_v' e’ by metis_tac[transform_e_not_is_v] >> gs[] >>
(* 3. Rewrite transformation of final state *)
qpat_x_assum ‘transform_e dict (e_cast c e') = SOME e'2’ (fn thm => ASSUME_TAC $ ONCE_REWRITE_RULE [transform_e_def] thm >> gvs[app_opt_def, AllCaseEqs()]) >>
(* 4. Use induction hypothesis *)
metis_tac[]
QED

(* If you transform a struct used for matching in select,
 * and if you transform the s_list_x_list used for matching,
 * then a NONE result in matching is preserved. *)
Theorem transform_select_NONE:
transform_e dict (e_v (v_struct x_v_l)) =
 SOME (e'_v (v'_struct w_v'_l)) ==>
FIND (\(s_list,x'). match_all (ZIP (SND (UNZIP x_v_l),s_list)))
 s_list_x_list = NONE ==>
oFOLDR (oFOLDR (transform_s dict)) (MAP FST s_list_x_list) =
 SOME s_n_list_list' ==>
oFOLDR (ALOOKUP dict) (MAP SND s_list_x_list) = SOME x_list' ==>
match_all_first (SND (UNZIP w_v'_l))
 (ZIP (MAP FST (MAP UNZIP s_n_list_list'),x_list')) = NONE
Proof
cheat
QED

Theorem transform_select_SOME:
transform_v dict (v_struct x_v_l) =
 SOME (v'_struct w_v'_l) ==>
FIND (\(s_list,x'). match_all (ZIP (SND (UNZIP x_v_l),s_list)))
 s_list_x_list = SOME (s_list,x'') ==>
oFOLDR (oFOLDR (transform_s dict)) (MAP FST s_list_x_list) =
 SOME s_n_list_list' ==>
oFOLDR (ALOOKUP dict) (MAP SND s_list_x_list) = SOME x_list' ==>
match_all_first (SND (UNZIP w_v'_l))
 (ZIP (MAP FST (MAP UNZIP s_n_list_list'),x_list')) = SOME word'
Proof
cheat
QED

Theorem e_exec'_completeness_select:
!e l0 c l.
e_exec'_complete e ==>
e_exec'_complete (e'_select e l0 c l)
Proof
gs[e_exec'_complete_def] >>
rpt strip_tac >>
(* 1. Rewrite transformation of initial state *)
qpat_x_assum ‘transform_e dict e1 = SOME (e'_select e l0 c l)’ (fn thm => ASSUME_TAC $ ONCE_REWRITE_RULE [transform_e_def] thm >> gvs[listTheory.UNZIP_MAP, AllCaseEqs()]) >>
(* 2. Rewrite execution *)
gvs[e_exec'_def, p4_exec_semTheory.e_exec_def, AllCaseEqs()] >> (
 gvs[transform_frame_list_def, oFOLDR_def]
) >- (
 (* Case 2a: e''' is a value *)
 qpat_x_assum ‘!e1. _’ (fn thm => ALL_TAC) >>
 ‘is_v' e’ by metis_tac[transform_e_is_v] >> gs[] >>
 (* First, get result of operation on cake_sem in proof goal *)
 Cases_on ‘e’ >> (gs[is_v'_def]) >>
 simp[e_exec_select'_def, AllCaseEqs()] >>
 gs[] >>
 (* Then, obtain everything involved
  * in the operation from regular semantics by case analysis *)
 Cases_on ‘e'''’ >> (gs[p4_exec_semTheory.is_v_def]) >>
 (* Apply regular operation *)
 gvs[p4_exec_semTheory.e_exec_select_def, AllCaseEqs()] >- (
  (* Connect the concrete values via translation *)
  qexists_tac ‘c’ >>
  gvs[transform_e_def, transform_v_def]
 ) >- (
  qexists_tac ‘c’ >>
  gvs[transform_e_def, transform_v_def]
 ) >- ( 
  qexists_tac ‘c’ >>
  gvs[transform_e_def, transform_v_def]
 ) >- (
  (* Struct: case no match *)
  qexists_tac ‘c’ >>
  CONJ_TAC >- (
   NTAC 3 DISJ2_TAC >> DISJ1_TAC >>
   (* TODO: Result of transforming v_struct is a v'_struct *)
   ‘?w_v'_l. v = v'_struct w_v'_l’ by (gs[transform_e_def] >> metis_tac[transform_v_struct]) >>
   gvs[] >>
   DISJ1_TAC >>
   (* Property of how the s_list_x_list is transformed -
    * the result of no matches must be preserved *)
   metis_tac[transform_select_NONE]
  ) >>
  gvs[Once transform_e_def, transform_v_def]
 ) >- (
  (* Struct: case SOME match *)
  qpat_x_assum ‘transform_e dict (e_v (v_str x'')) = SOME e'2’ (fn thm => assume_tac $ ONCE_REWRITE_RULE [transform_e_def] thm >> gvs[AllCaseEqs()]) >>
  gs[transform_v_def] >>
  qexists_tac ‘word'’ >>
  CONJ_TAC >- (
   NTAC 3 DISJ2_TAC >> DISJ1_TAC >>
   (* Property of how the s_list_x_list is transformed -
    * the result of matches must be preserved *)
   qpat_x_assum ‘transform_e dict (e_v (v_struct x_v_l)) = SOME (e'_v v)’ (fn thm => assume_tac $ ONCE_REWRITE_RULE [transform_e_def] thm >> gvs[AllCaseEqs()]) >>
   ‘?w_v'_l. v = v'_struct w_v'_l’ by metis_tac[transform_v_struct] >>
   gvs[] >>
   DISJ2_TAC >>
   metis_tac[transform_select_SOME]
  ) >>
  gvs[]
 ) >- (
  (* Header *)
  qexists_tac ‘c’ >>
  gvs[Once transform_e_def, transform_v_def] >>
  gvs[transform_e_def, Once transform_v_def, AllCaseEqs()]
 ) >> (
  gvs[transform_e_def, transform_v_def]
 )
) >>
(* Case 2b: e2' is not value *)
‘~is_v' e’ by metis_tac[transform_e_not_is_v] >> gs[] >>
(* 3. Rewrite transformation of final state *)
qpat_x_assum ‘transform_e dict (e_select e' s_list_x_list x') = SOME e'2’ (fn thm => ASSUME_TAC $ ONCE_REWRITE_RULE [transform_e_def] thm >> gvs[listTheory.UNZIP_MAP, AllCaseEqs()]) >>
(* 4. Use induction hypothesis *)
metis_tac[]
QED

Theorem transform_list_LENGTH:
!t t' dict.
transform_e dict (e_list t) = SOME (e'_list t') ==>
LENGTH t = LENGTH t'
Proof
Induct >> (
 rpt strip_tac >>
 gs[Once transform_e_def, AllCaseEqs()]
) >>
qpat_x_assum ‘transform_e dict (e_list _) = SOME _’ (fn thm => assume_tac $ ONCE_REWRITE_RULE [transform_e_def] thm >> gvs[AllCaseEqs()]) >>
qpat_x_assum ‘!t'' dict'. _’ (fn thm => irule thm) >>
qexists_tac ‘dict’ >>
Cases_on ‘t’ >> Cases_on ‘t''’ >> (
 gs[]
) >> (
qpat_x_assum ‘transform_e dict (e_list _) = SOME _’ (fn thm => assume_tac $ ONCE_REWRITE_RULE [transform_e_def] thm >> gvs[AllCaseEqs()])
)
QED

Theorem transform_list_MEM:
!t t' e' dict.
transform_e dict (e_list t) = SOME (e'_list t') ==>
MEM e' t' ==>
?e. transform_e dict e = SOME e'
Proof
Induct_on ‘t’ >- (
 gs[transform_e_def]
) >>
rpt strip_tac >>
qpat_x_assum ‘transform_e dict (e_list (h::t)) = SOME (e'_list t')’
 (fn thm => assume_tac $ ONCE_REWRITE_RULE [transform_e_def] thm >> 
  gvs[AllCaseEqs()]) >>
metis_tac[]
QED

(* TODO: Requires injectivity of transform_e? *)
Theorem transform_list_EL:
!l l' ei ei' i dict.
transform_e dict (e_list l) = SOME (e'_list l') ==>
oEL i l' = SOME ei' ==>
oEL i l = SOME ei ==>
transform_e dict ei = SOME ei'
Proof
Induct_on ‘l’ >- (
 rpt strip_tac >>
 gvs[Once transform_e_def, listTheory.oEL_def]
) >>
rpt strip_tac >>
qpat_x_assum ‘transform_e dict (e_list (h::l)) = SOME (e'_list l')’
 (fn thm => assume_tac $ ONCE_REWRITE_RULE [transform_e_def] thm >> 
  gvs[AllCaseEqs()]) >>
Cases_on ‘i’ >> (
 gvs[listTheory.oEL_def]
) >>
gs[listTheory.oEL_EQ_EL]
QED

Theorem l_complete_mem:
!l e.
l_complete l ==>
MEM e l ==>
e_exec'_complete e
Proof
Cases_on ‘l’ >> (
 gs[l_complete_def]
) >>
rpt strip_tac >- (
 gvs[] >>
 qpat_x_assum ‘!i e. _’ (fn thm => irule thm) >>
 qexists_tac ‘0’ >>
 gs[listTheory.oEL_def]
) >>
qpat_x_assum ‘!i e. _’ (fn thm => irule thm) >>
gs[listTheory.MEM_EL] >>
qexists_tac ‘SUC n’ >>
gs[listTheory.oEL_EQ_EL]
QED

Theorem transform_arg_SOME:
!arg arg' dict.
transform_arg dict arg = SOME arg' ==>
SND arg = SND arg'
Proof
Induct >>
rpt strip_tac >> (
 gvs[transform_arg_def]
)
QED

Theorem transform_args_SOME:
!args args' dict.
transform_args dict args = SOME args' ==>
LENGTH args = LENGTH args' /\ MAP SND args = MAP SND args'
Proof
Induct >- (
 rpt strip_tac >> (
  gvs[transform_args_def, oFOLDR_def]
 )
) >>
rpt strip_tac >> (
 gvs[transform_args_def, oFOLDR_def]
) >- (
 metis_tac[]
) >>
metis_tac[transform_arg_SOME]
QED

Theorem transform_func_map_ALOOKUP_SOME:
!func_map func_map' s w dict x_d_l stmt.
dict_bij dict ==>
ALOOKUP dict s = SOME w ==>
transform_func_map dict func_map = SOME func_map' ==>
ALOOKUP func_map s = SOME (stmt,x_d_l) ==>
?stmt' w_d_l. ALOOKUP func_map' w = SOME (stmt',w_d_l) /\
LENGTH x_d_l = LENGTH w_d_l /\
MAP SND x_d_l = MAP SND w_d_l /\
transform_stmt dict stmt = SOME stmt'
Proof
Induct >- (
 rpt strip_tac >>
 gvs[transform_func_map_def, oFOLDR_def]
) >>
rpt strip_tac >>
PairCases_on ‘h’ >>
gvs[transform_func_map_def, AllCaseEqs()] >- (
 gvs[oFOLDR_def, transform_func_def] >>
 metis_tac[transform_args_SOME]
) >>
gvs[oFOLDR_def, transform_func_def] >>
‘x' ≠ w’ by (
 metis_tac[dict_bij_injectivity]
) >>
gs[] >>
first_x_assum irule >>
gs[] >>
metis_tac[]
QED

Theorem transform_func_map_ALOOKUP_NONE:
!func_map func_map' s w dict x_d_l.
dict_bij dict ==>
ALOOKUP dict s = SOME w ==>
transform_func_map dict func_map = SOME func_map' ==>
ALOOKUP func_map s = NONE ==>
ALOOKUP func_map' w = NONE
Proof
Induct >- (
 rpt strip_tac >>
 gvs[transform_func_map_def, oFOLDR_def]
) >>
rpt strip_tac >>
PairCases_on ‘h’ >>
rename1 ‘(func_name, (stmt, args))::func_map_tail’ >>
gvs[transform_func_map_def] >>
Cases_on ‘ALOOKUP dict func_name’ >- (
 gvs[oFOLDR_def, transform_func_def, AllCaseEqs()]
) >>
rename1 ‘ALOOKUP dict func_name = SOME func_word’ >>
Cases_on ‘transform_stmt dict stmt’ >- (
 gvs[oFOLDR_def, transform_func_def, AllCaseEqs()]
) >>
Cases_on ‘transform_args dict args’ >- (
 gvs[oFOLDR_def, transform_func_def, AllCaseEqs()]
) >>
rename1 ‘transform_stmt dict stmt = SOME stmt'’ >>
rename1 ‘transform_args dict args = SOME args'’ >>
gvs[oFOLDR_def, transform_func_def] >>
gvs[alistTheory.ALOOKUP_def] >>
Cases_on ‘w = func_word’ >- (
 ‘ALOOKUP dict s = SOME w ∧ ALOOKUP dict func_name = SOME func_word ∧ s ≠ func_name’ by gvs[] >>
 ‘w ≠ func_word’ by (
  metis_tac[dict_bij_injectivity]
 ) >>
 gvs[]
) >>
(* Use induction hypothesis *)
metis_tac[]
QED

(* TODO: ext_map transformation will have to be done more guardedly:
 * Probably, check that old parameter lengths and directions agree with
 * the hard-coded new map, otherwise return NONE. *)
Theorem transform_ext_map_ALOOKUP_SOME:
!ext_map ext_map' s w dict inst funs x_d_l stmt.
ALOOKUP dict s = SOME w ==>
transform_ext_map dict ext_map = SOME ext_map' ==>
ALOOKUP ext_map s = SOME (SOME (x_d_l, inst), funs) ==>
?inst' funs' w_d_l. ALOOKUP ext_map' w = SOME (SOME (w_d_l, inst'), funs') /\
LENGTH x_d_l = LENGTH w_d_l /\
MAP SND x_d_l = MAP SND w_d_l
Proof
Induct >- (
 rpt strip_tac >>
 gvs[transform_ext_map_def, oFOLDR_def]
) >>
rpt strip_tac >>
PairCases_on ‘h’ >>
gvs[transform_ext_map_def, AllCaseEqs()] >- (
 first_x_assum irule >>
 qexistsl_tac [‘dict’, ‘funs’, ‘inst’, ‘h0’] >>
 gs[] >>
 cheat
) >>
first_x_assum irule >>
qexistsl_tac [‘dict’, ‘funs’, ‘inst’, ‘s’] >>
gs[]
QED

(* TODO: ext_map transformation will have to be done more guardedly:
 * Probably, check that old parameter lengths and directions agree with
 * the hard-coded new map, otherwise return NONE. *)
Theorem transform_ext_map_fun_ALOOKUP_SOME:
!s1 w1 s2 w2 dict construct_info funs fun_x_d_l ext_map ext_map' ext_fun_map fun.
ALOOKUP dict s1 = SOME w1 ==>
ALOOKUP dict s2 = SOME w2 ==>
transform_ext_map dict ext_map = SOME ext_map' ==>
ALOOKUP ext_map s1 = SOME (construct_info, funs) ==>
ALOOKUP ext_fun_map s2 = SOME (fun_x_d_l,fun) ==>
?construct_info' funs' w_d_l fun'. ALOOKUP ext_map' w1 = SOME (construct_info', funs') /\
 ALOOKUP funs' w2 = SOME (w_d_l, fun') /\
LENGTH fun_x_d_l = LENGTH w_d_l /\
MAP SND fun_x_d_l = MAP SND w_d_l
Proof
cheat
QED

(* TODO: If function can be looked up in regular sem, it can also be looked up in
 * cake_sem, with same length of args. *)
Theorem transform_ectx_lookup_funn_sig_body:
!stmt x_d_l dict funn f ext_map func_map b_func_map e_ctx0 e_ctx1 e_ctx2.
dict_bij dict ==>
 transform_ectx dict (ext_map,func_map,b_func_map) =
        SOME (e_ctx0,e_ctx1,e_ctx2) ==>
transform_funn dict funn = SOME f ==>
lookup_funn_sig_body funn func_map b_func_map ext_map = SOME (stmt,x_d_l) ==>
?stmt' w_d_l. lookup_funn_sig_body' f e_ctx1 e_ctx2 e_ctx0 = SOME (stmt', w_d_l) /\
LENGTH x_d_l = LENGTH w_d_l /\
MAP SND x_d_l = MAP SND w_d_l /\
transform_stmt dict stmt = SOME stmt'
Proof
rpt strip_tac >>
gvs[transform_ectx_def, AllCaseEqs()] >>
Cases_on ‘funn’ >> (
 gvs[transform_funn_def, lookup_funn_sig_body_def, lookup_funn_sig_body'_def, AllCaseEqs()]
) >- (
 ‘?stmt' w_d_l. ALOOKUP e_ctx1 word' = SOME (stmt', w_d_l) /\
  LENGTH x_d_l = LENGTH w_d_l /\ MAP SND x_d_l = MAP SND w_d_l /\
  transform_stmt dict stmt = SOME stmt'’ by (
  metis_tac[transform_func_map_ALOOKUP_SOME]
 ) >>
 qexistsl_tac [‘stmt'’, ‘w_d_l’] >>
 metis_tac[transform_func_map_ALOOKUP_NONE]
) >- (
 metis_tac[transform_func_map_ALOOKUP_SOME]
) >- (
 simp[transform_stmt_def] >>
 metis_tac[transform_ext_map_ALOOKUP_SOME]
) >- (
 simp[transform_stmt_def] >>
 metis_tac[transform_ext_map_fun_ALOOKUP_SOME]
)
QED

Theorem transform_e_preserves_is_arg_red:
!e e' dict d.
transform_e dict e = SOME e' ==>
(is_arg_red d e <=> is_arg_red' d e')
Proof
(* Need to induct, since this is dependent on nested es *)
Induct >> (
 rpt strip_tac >>
 imp_res_tac transform_e_subtypes >>
 gvs[is_arg_red_def, is_arg_red'_def, is_const_def, is_const'_def, is_e_lval_def, is_e_lval'_def, get_lval_of_e_def, get_lval_of_e'_def]
) >> (
 Cases_on ‘is_d_out d’ >> (
  gs[]
 ) >>
 qpat_x_assum ‘transform_e dict _ = SOME _’
  (fn thm => assume_tac $ ONCE_REWRITE_RULE [transform_e_def] thm >> 
             gvs[AllCaseEqs()])
) >- (
 qpat_x_assum ‘!e'''. _’
  (fn thm => assume_tac $ Q.SPECL [‘e''’, ‘dict’, ‘d’] thm) >>
 gs[] >>
 Cases_on ‘get_lval_of_e e’ >> Cases_on ‘get_lval_of_e' e''’ >> (
  gs[]
 )
) >>
qpat_x_assum ‘!e' dict' d.
         transform_e dict' e = SOME e' ==> _’
 (fn thm => assume_tac $ Q.SPECL [‘e1'’, ‘dict’, ‘d’] thm) >>
gs[] >>
Cases_on ‘get_lval_of_e e’ >> Cases_on ‘get_lval_of_e' e1'’ >> (
 gs[]
)
QED

Theorem INDEX_FIND_preserved:
!P P' l l' i x.
LENGTH l = LENGTH l' ==>
(!j. j < LENGTH l ==> (P (EL j l) <=> P' (EL j l'))) ==>
INDEX_FIND 0 P l = SOME (i, x) ==>
?x'. INDEX_FIND 0 P' l' = SOME (i, x')
Proof
rpt strip_tac >>
‘i < LENGTH l /\ EL i l = x /\ P x /\ 
 !j. j < i ==> ~P (EL j l)’ by (
 imp_res_tac INDEX_FIND_EQ_SOME_0 >>
 gs[]
) >>
‘i < LENGTH l'’ by gs[] >>
qexists_tac ‘EL i l'’ >>
simp[INDEX_FIND_EQ_SOME_0] >>
gs[] >>
‘P (EL i l)’ suffices_by metis_tac[] >>
gvs[]
QED

Theorem transform_list_unred_arg_index_SOME:
!l l' d_l i dict.
LENGTH d_l = LENGTH l ==>
unred_arg_index d_l l = SOME i ==>
transform_e dict (e_list l) = SOME (e'_list l') ==>
unred_arg_index' d_l l' = SOME i
Proof
rpt strip_tac >>
gs[unred_arg_index_def, unred_arg_index'_def, find_unred_arg_def, find_unred_arg'_def, AllCaseEqs()] >>
‘LENGTH l = LENGTH l'’ by (
 imp_res_tac transform_list_LENGTH >>
 fs[]
) >>
‘!j. j < LENGTH l ==> 
     (is_arg_red (EL j d_l) (EL j l) <=> is_arg_red' (EL j d_l) (EL j l'))’ by (
 rpt strip_tac >>
 irule transform_e_preserves_is_arg_red >>
 ‘?ej ej'. EL j l = ej /\ EL j l' = ej' /\ transform_e dict ej = SOME ej'’ by (
   imp_res_tac transform_list_EL >>
   qexistsl_tac [‘EL j l’, ‘EL j l'’] >>
   fs[listTheory.oEL_EQ_EL]
 ) >>
 metis_tac[]
) >>
‘?de. INDEX_FIND 0 (\(d,e). ~is_arg_red' d e) (ZIP (d_l,l')) = SOME (i,de)’ suffices_by metis_tac[] >>
irule (Q.ISPECL [‘(\(d,e). ~is_arg_red d e)’] INDEX_FIND_preserved) >>
qexistsl_tac [‘ZIP(d_l, l)’, ‘de’] >>
gvs[] >>
rpt strip_tac >>
(* TODO: Looks easy... *)
Cases_on ‘EL j (ZIP(d_l, l))’ >>
Cases_on ‘EL j (ZIP(d_l, l'))’ >>
simp[] >>
‘q = EL j d_l /\ q' = EL j d_l /\ r = EL j l /\ r' = EL j l'’ suffices_by metis_tac[] >>
‘j < LENGTH l’ by gs[] >>
‘LENGTH d_l = LENGTH l’ suffices_by (
 rpt strip_tac >> (
  imp_res_tac listTheory.EL_ZIP >>
  gvs[]
 ) >> (
  ‘LENGTH d_l = LENGTH l'’ by gs[] >>
  imp_res_tac listTheory.EL_ZIP >>
  gvs[]
 )
) >>
gs[]
QED

Theorem transform_list_unred_arg_index_NONE:
!l l' d_l dict.
LENGTH d_l = LENGTH l ==>
unred_arg_index d_l l = NONE ==>
transform_e dict (e_list l) = SOME (e'_list l') ==>
unred_arg_index' d_l l' = NONE
Proof
cheat
QED

Theorem transform_e_call_arg:
!l l' funn f e e' dict.
transform_e dict (e_call funn l) = SOME $ e'_call f l' ==>
MEM e l ==>
?e'. transform_e dict e = SOME e'
Proof
Induct >- (
 gs[listTheory.MEM]
) >>
rpt strip_tac >>
qpat_x_assum ‘transform_e dict (e_call funn (h::t)) = SOME (e'_call f l')’
 (fn thm => assume_tac $ ONCE_REWRITE_RULE [transform_e_def] thm >> 
  gvs[AllCaseEqs()]) >>
Cases_on ‘e = h’ >- (
 gs[]
) >>
qpat_x_assum ‘!l''. _’
 (fn thm => irule thm) >>
gs[] >>
qexistsl_tac [‘f’, ‘funn’, ‘t'’] >>
simp[Once transform_e_def, AllCaseEqs()] >>
Cases_on ‘l’ >> Cases_on ‘t'’ >> (
 gs[listTheory.MEM]
) >> (
qpat_x_assum ‘transform_e dict (e_list (h'::t)) = SOME _’
 (fn thm => assume_tac $ ONCE_REWRITE_RULE [transform_e_def] thm >> 
  gvs[AllCaseEqs()])
)
QED

Theorem transform_e_call_LUPDATE:
!l l' funn f ei ei' i dict.
transform_funn dict funn = SOME f ==>
transform_e dict (e_list l) = SOME (e'_list l') ==>
transform_e dict ei = SOME ei' ==>
transform_e dict (e_call funn (LUPDATE ei i l)) = SOME $ e'_call f (LUPDATE ei' i l')
Proof
Induct >- (
 rpt strip_tac >>  
 gs[listTheory.LUPDATE_def] >>
 ‘l' = []’ by gs[Once transform_e_def] >>
 simp[Once transform_e_def]
) >>
rpt strip_tac >>
qpat_x_assum ‘transform_e dict (e_list (h::t)) = SOME (e'_list l')’
 (fn thm => assume_tac $ ONCE_REWRITE_RULE [transform_e_def] thm >> 
            gvs[AllCaseEqs()]) >>
Cases_on ‘i’ >- (
 gs[listTheory.LUPDATE_def] >>
 simp[Once transform_e_def]
) >>
gs[listTheory.LUPDATE_def] >>
simp[Once transform_e_def] >>
qexists_tac ‘e'_list (LUPDATE ei' n t')’ >>
simp[] >>
‘transform_e dict (e_call funn (LUPDATE ei n l)) = SOME (e'_call f (LUPDATE ei' n t'))’ suffices_by (
 rpt strip_tac >>
 qpat_x_assum ‘transform_e dict (e_call funn (LUPDATE ei n l)) =
                SOME (e'_call f (LUPDATE ei' n t'))’
  (fn thm => assume_tac $ ONCE_REWRITE_RULE [transform_e_def] thm >> 
             gvs[AllCaseEqs()]) >> (
  simp[listTheory.LUPDATE_def, Once transform_e_def]
 )
) >>
first_x_assum irule >>
gs[]
QED

(* Describes how copyin behaviour is preserved over translation *)
Theorem transform_scope_copyin:
transform_ectx dict (ext_map,func_map,b_func_map) = SOME (e_ctx0,e_ctx1,e_ctx2) ==>
transform_scope_list dict g_scope_list = SOME g_scope_list' ==>
transform_scope_list dict scope_list = SOME scope_list' ==>
lookup_funn_sig_body funn func_map b_func_map ext_map = SOME (stmt,x_d_l) ==>
copyin_exec uninit_zero (MAP FST x_d_l) (MAP SND x_d_l) (h::t) g_scope_list scope_list = SOME scope ==>
transform_scope dict scope = SOME res'' ==>
lookup_funn_sig_body' f e_ctx1 e_ctx2 e_ctx0 = SOME (res',x_d_l') ==>
copyin' (MAP FST x_d_l') (MAP SND x_d_l') (e'::t') g_scope_list' scope_list' = SOME res''
Proof
cheat
QED

Theorem e_exec'_completeness_call:
!f l.
l_complete l ==>
e_exec'_complete (e'_call f l)
Proof
gs[e_exec'_complete_def] >>
rpt strip_tac >>
PairCases_on ‘e_ctx’ >>
qpat_x_assum ‘transform_e dict e1 = SOME (e'_call f l)’ (fn thm => assume_tac $ ONCE_REWRITE_RULE [transform_e_def] thm >> gvs[listTheory.UNZIP_MAP, AllCaseEqs()]) >- (
 (* Case: No args - then no args can also be unreduced *)
 gvs[p4_exec_semTheory.e_exec_def, unred_arg_index_def, find_unred_arg_def, listTheory.INDEX_FIND_def, transform_frame_list_def, oFOLDR_def, AllCaseEqs()] >>
 (* TODO: The new frame needs to be properly resolved... *)
 gvs[e_exec'_def, p4_exec_semTheory.e_exec_def, AllCaseEqs()] >>
‘?v1. lookup_funn_sig_body' f e_ctx1 e_ctx2 e_ctx0 = SOME v1 /\
 ?stmt'. v1 = (stmt', []) /\ transform_stmt dict stmt = SOME stmt'’ by (
  imp_res_tac transform_ectx_lookup_funn_sig_body >>
  qexists_tac ‘(stmt',[])’ >>
  gs[] >>
  metis_tac[transform_list_LENGTH]
 ) >> gvs[] >>
 gvs[unred_arg_index'_def, find_unred_arg'_def, listTheory.INDEX_FIND_def, copyin'_def, all_arg_update_for_newscope'_def, transform_e_def, transform_varn_def, transform_frame_def, transform_scope_list_def, p4_exec_semTheory.copyin_exec_def, p4_exec_semTheory.all_arg_update_for_newscope_exec_def, transform_scope_def, oFOLDR_def, AllCaseEqs()]
) >>
(* Case: Args *)
gvs[e_exec'_def, p4_exec_semTheory.e_exec_def, AllCaseEqs()] >- (
 (* Fully reduced *)
 gvs[transform_frame_list_def, transform_frame_def, oFOLDR_def] >>
‘?v1. lookup_funn_sig_body' f e_ctx1 e_ctx2 e_ctx0 = SOME v1 /\
 ?stmt' x_d_l. v1 = (stmt', x_d_l) /\ LENGTH x_d_l = SUC (LENGTH t') /\ transform_stmt dict stmt = SOME stmt'’ by (
  imp_res_tac transform_ectx_lookup_funn_sig_body >>
  qexists_tac ‘(stmt',w_d_l)’ >>
  gs[] >>
  metis_tac[transform_list_LENGTH]
 ) >> gvs[] >>
 (* TODO: Do nicer *)
 ‘unred_arg_index' (MAP SND x_d_l') (e'::t') = NONE’ by (
  irule transform_list_unred_arg_index_NONE >>
  qexistsl_tac [‘dict’, ‘h::t’] >>
  imp_res_tac transform_list_LENGTH >>
  gs[] >>
  simp[transform_e_def] >>
  ‘MAP SND x_d_l' = MAP SND x_d_l’ by (
   imp_res_tac transform_ectx_lookup_funn_sig_body >>
   gvs[]
  ) >>
  gs[]
 ) >>
 gs[] >>
 qpat_x_assum ‘transform_e dict (e_var (varn_star funn)) = SOME e'2’ (fn thm => assume_tac $ ONCE_REWRITE_RULE [transform_e_def] thm >> gvs[AllCaseEqs()]) >>
 qpat_x_assum ‘transform_scope_list dict [scope] = SOME scope_list''’ (fn thm => assume_tac $ ONCE_REWRITE_RULE [transform_scope_list_def] thm >> gvs[AllCaseEqs()]) >>
 gvs[transform_varn_def, oFOLDR_def] >>
 metis_tac[transform_scope_copyin]
) >>
‘?v1. lookup_funn_sig_body' f e_ctx1 e_ctx2 e_ctx0 = SOME v1 /\
 ?stmt' x_d_l'.
  v1 = (stmt', x_d_l') /\ LENGTH x_d_l' = SUC (LENGTH t') /\ MAP SND x_d_l = MAP SND x_d_l'’ by (
  imp_res_tac transform_ectx_lookup_funn_sig_body >>
  qexists_tac ‘(stmt',w_d_l)’ >>
  gs[] >>
  metis_tac[transform_list_LENGTH]
 ) >> gvs[] >>
‘unred_arg_index' (MAP SND x_d_l') (e'::t') = SOME i’ by (
 irule transform_list_unred_arg_index_SOME >>
 qexistsl_tac [‘dict’, ‘h::t’] >>
 gs[] >>
 simp[Once transform_e_def] >>
 metis_tac[transform_list_LENGTH]
) >> gs[] >>
‘?ei. EL i (h::t) = ei’ by metis_tac[unred_arg_index_in_range] >>
‘?e'i. oEL i (e'::t') = SOME e'i’ by (
 imp_res_tac unred_arg_index_in_range >>
 imp_res_tac oEL_SOME >>
 imp_res_tac transform_list_LENGTH >>
 ‘i < LENGTH (e'::t')’ suffices_by metis_tac[oEL_SOME] >>
 gvs[]
) >> gs[] >>
‘?e''i. transform_e dict e'' = SOME e''i’ by (
 (* TODO: Do before? *)
 imp_res_tac transform_e_subtypes >>
 gvs[] >>
 irule transform_e_call_arg >>
 qexistsl_tac [‘funn'’, ‘funn’, ‘(LUPDATE e'' i (h::t))’, ‘l''’] >>
 gs[listTheory.MEM_LUPDATE, listTheory.oEL_EQ_EL] >>
 imp_res_tac oEL_SOME >>
 metis_tac[transform_list_LENGTH]
) >>
qexists_tac ‘(e''i, frame_list')’ >>
CONJ_TAC >- (
 (* Use induction hypothesis on the ith position *)
 ‘e_exec'_complete e'i’ by (
  metis_tac[l_complete_mem, listTheory.MEM_EL, listTheory.oEL_EQ_EL]
 ) >>
 gs[e_exec'_complete_def] >>
 ‘!e1.
   transform_e dict e1 = SOME e'i ==>
   !tbl_map pars_map frame_list e2 apply_table_f.
     e_exec uninit_zero
       (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)
       g_scope_list scope_list e1 =
     SOME (e2,frame_list) ==>
     !e'2.
       transform_e dict e2 = SOME e'2 ==>
       !frame_list'.
         transform_frame_list dict frame_list = SOME frame_list' ==>
         e_exec' (e_ctx0,e_ctx1,e_ctx2) g_scope_list' scope_list' e'i =
         SOME (e'2,frame_list')’ by (
  res_tac
 ) >>
 qpat_x_assum ‘!e1 dict. _’ (fn thm => ALL_TAC) >>
 qpat_x_assum ‘!e1. _’ (fn thm => irule thm) >>
 qexistsl_tac [‘apply_table_f’, ‘ei’, ‘e''’, ‘frame_list’, ‘pars_map’, ‘tbl_map’] >>
 gs[] >>
 irule transform_list_EL >>
 qexistsl_tac [‘i’, ‘h::t’, ‘e'::t'’] >>
 gs[listTheory.oEL_EQ_EL] >>
 simp[Once transform_e_def] >>
 metis_tac[transform_list_LENGTH]
) >>
qexists_tac ‘e''i’ >>
gvs[] >>
‘transform_e dict (e_call funn (LUPDATE e'' i (h::t))) = SOME $ e'_call f (LUPDATE e''i i (e'::t'))’ by (
 irule transform_e_call_LUPDATE >>
 gs[] >>
 simp[Once transform_e_def]
) >>
gvs[]
QED

(* TODO: Change form, only use e_struct l? *)
(* Proof similar to transform_list_unred_arg_index_SOME *)
Theorem transform_struct_unred_mem_index_NONE:
!t t' e e' dict.
unred_mem_index (e::MAP SND t) = NONE ==>
transform_e dict e = SOME e' ==>
transform_e dict (e_struct t) = SOME (e'_struct t') ==>
unred_mem_index' (e'::MAP_SND t') = NONE
Proof
cheat
(*
Induct >> (
 rpt strip_tac >>
 gvs[Once transform_e_def, MAP_SND_EQ, unred_mem_index'_def, unred_mem'_def, listTheory.INDEX_FIND_def, is_const'_def, AllCaseEqs()]
) >> (
 qpat_x_assum ‘transform_e dict (e_struct _) = SOME _’ (fn thm => assume_tac $ ONCE_REWRITE_RULE [transform_e_def] thm >> gvs[AllCaseEqs()]) >>
 gvs[listTheory.INDEX_FIND_def, is_const'_def, unred_mem_index_def, unred_mem_def, is_const_def, AllCaseEqs()]
) >>
gs[AllCaseEqs()]
)
*)
QED

(* TODO: Change form, only use e_struct l? *)
(* Proof similar to transform_list_unred_arg_index_NONE *)
Theorem transform_struct_unred_mem_index_SOME:
!e e' t t' i dict.
unred_mem_index (e::MAP SND t) = SOME i ==>
transform_e dict e = SOME e' ==>
transform_e dict (e_struct t) = SOME (e'_struct t') ==>
unred_mem_index' (e'::MAP_SND t') = SOME i
Proof
cheat
QED

(* Relates e and v transformations of structs *)
(* TODO: What if the expressions in the struct are not values? *)
Theorem transform_e_v_struct:
!t t' t'' dict.
transform_e dict (e_struct t) = SOME (e'_struct t') ==>
transform_v dict
          (v_struct (ZIP (MAP FST t,MAP (\e. THE (v_of_e e)) (MAP SND t)))) =
        SOME (v'_struct t'') ==>
vl_of_el' (MAP_SND t') = SOME (MAP SND t'') /\
        ZIP (MAP_FST t',MAP SND t'') = t''
Proof
cheat
QED

Theorem transform_e_struct_LENGTH:
!t t' dict.
transform_e dict (e_struct t) = SOME (e'_struct t') ==>
LENGTH t = LENGTH t'
Proof
Induct >> (
 rpt strip_tac >>
 gs[Once transform_e_def, AllCaseEqs()]
) >>
qpat_x_assum ‘transform_e dict (e_struct _) = SOME _’ (fn thm => assume_tac $ ONCE_REWRITE_RULE [transform_e_def] thm >> gvs[AllCaseEqs()]) >>
qpat_x_assum ‘!t'' dict'. _’ (fn thm => irule thm) >>
qexists_tac ‘dict’ >>
Cases_on ‘t’ >> Cases_on ‘t''’ >> (
 gs[]
) >> (
qpat_x_assum ‘transform_e dict (e_struct _) = SOME _’ (fn thm => assume_tac $ ONCE_REWRITE_RULE [transform_e_def] thm >> gvs[AllCaseEqs()])
)
QED

(* TODO: Fix *)
Theorem MAP_SND_EQUIV:
!l.
MAP_SND l = MAP SND l
Proof
gs[p4_cake_exec_semTheory.MAP_SND_EQ]
QED

(* TODO: Fix *)
Theorem MAP_FST_EQUIV:
!l.
MAP_FST l = MAP FST l
Proof
gs[p4_cake_exec_semTheory.MAP_FST_EQ]
QED

(* TODO: Formulate in a nicer way *)
Theorem struct_lemma:
transform_e dict (e_struct t) = SOME (e'_struct t') ==>
transform_e dict (e_struct t'') = SOME (e'_struct t'3') ==>
transform_e dict e'3' = SOME e'2 ==>
transform_e dict e'4' = SOME e'5'==>
ALOOKUP dict x = SOME x' ==>
ZIP (x::MAP FST t,LUPDATE e'3' i (e'::MAP SND t)) = (x,e'4')::t'' ==>
ZIP (x'::MAP FST t',LUPDATE e'2 i (e''::MAP SND t')) = (x',e'5')::t'3'
Proof
cheat
QED

Theorem e_exec'_completeness_struct:
!l.
w_e_l_exec'_complete l ==>
e_exec'_complete (e'_struct l)
Proof
gs[e_exec'_complete_def] >>
rpt strip_tac >>
(* 1. Rewrite transformation of initial state *)
qpat_x_assum ‘transform_e dict e1 = SOME (e'_struct l)’ (fn thm => assume_tac $ ONCE_REWRITE_RULE [transform_e_def] thm >> gvs[listTheory.UNZIP_MAP, AllCaseEqs()]) >- (
 (* Case: empty struct *)
 (* 2. Rewrite execution *)
 gvs[p4_exec_semTheory.e_exec_def, e_exec'_def, AllCaseEqs()] >> (
 gvs[transform_frame_list_def, oFOLDR_def]
) >- (  
  gs[vl_of_el'_def, vl_of_el_def, MAP_SND_def, MAP_FST_def, AllCaseEqs()] >>
  gvs[AllCaseEqs(), transform_e_def, transform_v_def] >>
  metis_tac[unred_mem_index_same]
 ) >>
 gvs[unred_mem_index_def, unred_mem_def, listTheory.INDEX_FIND_def, AllCaseEqs()]
) >>
(* Case: non-empty struct *)
gvs[p4_exec_semTheory.e_exec_def, e_exec'_def, AllCaseEqs()] >- (
 (* No unreduced fields *)
 DISJ1_TAC >>
 gs[vl_of_el'_def, vl_of_el_def, MAP_SND_def, MAP_FST_def, AllCaseEqs()] >>
 (* From unred_mem_index *)
 imp_res_tac unred_mem_index_NONE >>
 gs[is_consts_def] >>
 Cases_on ‘e'’ >> (gs[is_const_def]) >>
 gvs[Once transform_e_def, listTheory.UNZIP_MAP, AllCaseEqs()] >>
 gvs[v_of_e_def, MAP_SND_def, MAP_FST_def, vl_of_el'_def, Once transform_v_def, AllCaseEqs()] >>
 CONJ_TAC >- (
  (* Ok *)
  metis_tac[transform_struct_unred_mem_index_NONE]
 ) >>
 qpat_x_assum ‘transform_e dict (e_v v) = SOME e''’ (fn thm => assume_tac $ ONCE_REWRITE_RULE [transform_e_def] thm >> gvs[listTheory.UNZIP_MAP, AllCaseEqs()]) >>
 gs[v_of_e'_def] >>
 qexists_tac ‘v''::MAP SND t''’ >>
 gvs[transform_frame_list_def, oFOLDR_def] >>
 metis_tac[transform_e_v_struct]
) >>
DISJ2_TAC >>
gs[w_e_l_exec'_complete_def] >>
gs[l_complete_def] >>
qexists_tac ‘i’ >>
CONJ_TAC >- (
 gvs[MAP_SND_def] >>
 metis_tac[transform_struct_unred_mem_index_SOME]
) >>
‘?e. SOME e = oEL i (e''::MAP SND t')’ by (
 imp_res_tac unred_mem_index_in_range >>
 imp_res_tac oEL_SOME >>
 imp_res_tac transform_e_struct_LENGTH >>
 ‘i < LENGTH (e''::MAP SND t')’ suffices_by metis_tac[oEL_SOME] >>
 gvs[]
) >>     
res_tac >>
qexists_tac ‘e’ >>
CONJ_TAC >- (
 gvs[p4_cake_exec_semTheory.MAP_SND_def, MAP_SND_EQUIV]
) >>
qpat_x_assum ‘transform_e dict
          (e_struct (ZIP (x::MAP FST t,LUPDATE e'³' i (e'::MAP SND t)))) =
        SOME e'2’ (fn thm => ASSUME_TAC $ ONCE_REWRITE_RULE [transform_e_def] thm >> gvs[listTheory.UNZIP_MAP, listTheory.ZIP_EQ_NIL, AllCaseEqs()]) >>
gs[e_exec'_complete_def] >>
‘!e1.
 transform_e dict e1 = oEL i (e''::MAP SND t') ==>
 !tbl_map pars_map frame_list e2 apply_table_f.
   e_exec uninit_zero
     (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)
     g_scope_list scope_list e1 =
   SOME (e2,frame_list) ==>
   !e'2.
     transform_e dict e2 = SOME e'2 ==>
     !frame_list'.
       transform_frame_list dict frame_list = SOME frame_list' ==>
       e_exec' e_ctx g_scope_list' scope_list' e =
       SOME (e'2,frame_list')’ by (
 res_tac
) >>
(* More fiddling needed *)
qpat_x_assum ‘!e1.
          transform_e dict e1 = oEL i (e''::MAP SND t') ==>
          !tbl_map pars_map frame_list e2 apply_table_f.
            e_exec uninit_zero
              (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)
              g_scope_list scope_list e1 =
            SOME (e2,frame_list) ==>
            !e'2.
              transform_e dict e2 = SOME e'2 ==>
              !frame_list'.
                transform_frame_list dict frame_list = SOME frame_list' ==>
                e_exec' e_ctx g_scope_list' scope_list' e =
                SOME (e'2,frame_list')’ (fn thm => ASSUME_TAC $ Q.SPECL [‘EL i (e'::MAP SND (t:(string # e) list))’] thm >> gs[]) >>
(* TODO: Why? *)
‘transform_e dict (EL i (e'::MAP SND t)) = oEL i (e''::MAP SND t')’ by cheat >>
gvs[] >>
‘!e'2.
          transform_e dict e'3' = SOME e'2 ==>
          !frame_list'.
            transform_frame_list dict frame_list = SOME frame_list' ==>
            e_exec' e_ctx g_scope_list' scope_list' e =
            SOME (e'2,frame_list')’ by (
 res_tac
) >>
(* TODO: Why? *)
‘?e'2. transform_e dict e'3' = SOME e'2’ by cheat >>
gvs[MAP_FST_EQUIV, MAP_SND_EQUIV] >>
qpat_x_assum ‘!e1. _ ’ (fn thm => ALL_TAC) >>
qpat_x_assum ‘!e1. _ ’ (fn thm => ALL_TAC) >>
qpat_x_assum ‘!e1. _ ’ (fn thm => ALL_TAC) >>
(* TODO: Why? *)
‘x = x''’ by cheat >> gvs[] >>
irule struct_lemma >>
qexistsl_tac [‘dict’, ‘e'’, ‘e'3'’, ‘e'4'’, ‘t’, ‘t''’, ‘x’] >>
gs[]
QED

Theorem e_exec'_completeness_binop:
!e b e0.
e_exec'_complete e ==>
e_exec'_complete e0 ==>
e_exec'_complete (e'_binop e b e0)
Proof
gs[e_exec'_complete_def] >>
rpt strip_tac >>
(* 1. Rewrite transformation of initial state *)
qpat_x_assum ‘transform_e dict e1 = SOME (e'_binop e b e0)’ (fn thm => ASSUME_TAC $ ONCE_REWRITE_RULE [transform_e_def] thm >> gvs[listTheory.UNZIP_MAP, AllCaseEqs()]) >>
(* 2. Rewrite execution *)
qpat_x_assum ‘e_exec uninit_zero
         (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)
         g_scope_list scope_list (e_binop e1' b e2') =
       SOME (e2,frame_list)’ (fn thm => ASSUME_TAC $ ONCE_REWRITE_RULE [p4_exec_semTheory.e_exec_def] thm >> simp[e_exec'_def] >> gvs[listTheory.UNZIP_MAP, AllCaseEqs()]) >> (
 gvs[transform_frame_list_def, oFOLDR_def] >>
 imp_res_tac transform_e_subtypes >>
 imp_res_tac transform_e_is_v >>
 imp_res_tac transform_e_not_is_v >>
 gvs[]
) >- (
 (* Non-recursive case: Short-circuit *)
 Cases_on ‘v’ >> Cases_on ‘b’ >> (
  gs[p4_exec_semTheory.e_exec_short_circuit_def]
 ) >- (
  qpat_x_assum ‘transform_e dict (e_v (v_bool b')) = SOME (e'_v v')’ (fn thm => ASSUME_TAC $ ONCE_REWRITE_RULE [transform_e_def] thm >> gvs[AllCaseEqs()] >> gs[transform_v_def]) >>
  Cases_on ‘b'’ >> (
   gvs[p4_exec_semTheory.e_exec_short_circuit_def, e_exec_short_circuit'_def] >>
   qpat_x_assum ‘transform_e dict (e_v (v_bool F)) = SOME e'2’ (fn thm => ASSUME_TAC $ ONCE_REWRITE_RULE [transform_e_def] thm >> gvs[AllCaseEqs()] >> gs[transform_v_def])
  )
 ) >>
 qpat_x_assum ‘transform_e dict (e_v (v_bool b')) = SOME (e'_v v')’ (fn thm => ASSUME_TAC $ ONCE_REWRITE_RULE [transform_e_def] thm >> gvs[AllCaseEqs()] >> gs[transform_v_def]) >>
 Cases_on ‘b'’ >> (
  gvs[p4_exec_semTheory.e_exec_short_circuit_def, e_exec_short_circuit'_def] >>
  qpat_x_assum ‘transform_e dict (e_v (v_bool T)) = SOME e'2’ (fn thm => ASSUME_TAC $ ONCE_REWRITE_RULE [transform_e_def] thm >> gvs[AllCaseEqs()] >> gs[transform_v_def])
 )
) >- (
 (* Non-recursive case *)
 qpat_x_assum ‘!e1. _’ (fn thm => ALL_TAC) >>
 qpat_x_assum ‘!e1. _’ (fn thm => ALL_TAC) >>
 (* TODO: Bitwidth issue *)
 Cases_on ‘e2'’ >> (
  gvs[p4_exec_semTheory.is_v_def]
 ) >>
 Cases_on ‘e0’ >> (
  gvs[is_v'_def]
 ) >>
 fs[Once transform_e_def] >>
 Cases_on ‘b’ >> Cases_on ‘v’ >> Cases_on ‘v''''’ >> (
  gvs[p4_exec_semTheory.binop_exec_def, p4_exec_semTheory.e_exec_binop_def, e_exec_binop'_def, AllCaseEqs()]
 ) >> (
  fs[Once transform_v_def] >>
  gvs[] >>
  gs[binop_exec'_def, AllCaseEqs()] >>
  Cases_on ‘p’ >> Cases_on ‘p'’ >> (
   gs[bitv_binop_def, bitv_binop'_def, get_bitv_binop'_def, AllCaseEqs()]
  )
 ) >>
 (* TODO: Bitwidth problem *)
 cheat
) >- (
 (* Recursive: 2nd arg red *)
 qpat_x_assum ‘transform_e dict (e_binop (e_v v) b e2'') = SOME (e'_binop e1' b e2'³')’ (fn thm => ASSUME_TAC $ ONCE_REWRITE_RULE [transform_e_def] thm >> gvs[AllCaseEqs()]) >>
 metis_tac[]
) >> (
 (* Recursive cases *)
 qpat_x_assum ‘transform_e dict (e_binop e1'' b e2') = SOME (e'_binop _ b _)’ (fn thm => ASSUME_TAC $ ONCE_REWRITE_RULE [transform_e_def] thm >> gvs[AllCaseEqs()]) >>
 metis_tac[]
)
QED

Theorem e_exec'_completeness_concat:
!e e0.
e_exec'_complete e ==>
e_exec'_complete e0 ==>
e_exec'_complete (e'_concat e e0)
Proof
gs[e_exec'_complete_def] >>
rpt strip_tac >>
(* 1. Rewrite transformation of initial state *)
qpat_x_assum ‘transform_e dict e1 = SOME (e'_concat e e0)’ (fn thm => ASSUME_TAC $ ONCE_REWRITE_RULE [transform_e_def] thm >> gvs[listTheory.UNZIP_MAP, AllCaseEqs()]) >>
(* 2. Rewrite execution *)
gvs[e_exec'_def, p4_exec_semTheory.e_exec_def, AllCaseEqs()] >- (
 gvs[transform_frame_list_def, oFOLDR_def] >>
 qpat_x_assum ‘!e1. _’ (fn thm => ALL_TAC) >>
 qpat_x_assum ‘!e1. _’ (fn thm => ALL_TAC) >>
 (* Case 2a: e1' and e2' are both values *)
 ‘is_v_bit' e’ by metis_tac[transform_e_is_v_bit] >> gs[] >>
 ‘is_v_bit' e0’ by metis_tac[transform_e_is_v_bit] >> gs[] >>
 (* First, get result of operation on cake_sem in proof goal *)
 Cases_on ‘e’ >> (gs[is_v_bit'_def]) >>
 Cases_on ‘e0’ >> (gs[is_v_bit'_def]) >>
 Cases_on ‘v'’ >> (gs[is_v_bit'_def]) >>
 Cases_on ‘v''’ >> (gs[is_v_bit'_def]) >>
 simp[e_exec_concat'_def] >>
 (* Then, obtain everything involved
  * in the operation from regular semantics by case analysis *)
 Cases_on ‘e1'’ >> (gs[p4_exec_semTheory.is_v_bit_def]) >>
 Cases_on ‘e2'’ >> (gs[p4_exec_semTheory.is_v_bit_def]) >>
 Cases_on ‘v'’ >> (gs[p4_exec_semTheory.is_v_bit_def]) >>
 Cases_on ‘v''’ >> (gs[p4_exec_semTheory.is_v_bit_def]) >>
 (* Apply regular operation *)
 gvs[p4_exec_semTheory.e_exec_concat_def] >>
 (* Connect the concrete values via translation *)
 gvs[transform_e_def, transform_v_def]
) >- (
 (* Case 2b: e2' is not value *)
 ‘is_v_bit' e’ by metis_tac[transform_e_is_v_bit] >> gs[] >>
 ‘~is_v_bit' e0’ by metis_tac[transform_e_not_is_v_bit] >> gs[] >>
 (* 3. Rewrite transformation of final state *)
 qpat_x_assum ‘transform_e dict (e_concat e1' e2'') = SOME e'2’ (fn thm => ASSUME_TAC $ ONCE_REWRITE_RULE [transform_e_def] thm >> gvs[app_opt_def, AllCaseEqs()]) >>
 (* 4. Use induction hypothesis *)
 metis_tac[]
) >>
‘~is_v_bit' e’ by metis_tac[transform_e_not_is_v_bit] >> gs[] >>
(* 3. Rewrite transformation of final state *)
qpat_x_assum ‘transform_e dict (e_concat e1'' e2') = SOME e'2’ (fn thm => ASSUME_TAC $ ONCE_REWRITE_RULE [transform_e_def] thm >> gvs[app_opt_def, AllCaseEqs()]) >>
(* 4. Use induction hypothesis *)
metis_tac[]
QED

Theorem e_exec'_completeness_slice:
!e e0 e1.
e_exec'_complete e ==>
e_exec'_complete e0 ==>
e_exec'_complete e1 ==>
e_exec'_complete (e'_slice e e0 e1)
Proof
gs[e_exec'_complete_def] >>
rpt strip_tac >>
(* 1. Rewrite transformation of initial state *)
qpat_x_assum ‘transform_e dict e1' = SOME (e'_slice e e0 e1)’ (fn thm => ASSUME_TAC $ ONCE_REWRITE_RULE [transform_e_def] thm >> gvs[listTheory.UNZIP_MAP, AllCaseEqs()]) >>
(* 2. Rewrite execution *)
gvs[e_exec'_def, p4_exec_semTheory.e_exec_def, AllCaseEqs()] >- (
 (* Case 2a: e1'', e2'' and e3 are all values *)
 gvs[transform_frame_list_def, oFOLDR_def] >>
 qpat_x_assum ‘!e1. _’ (fn thm => ALL_TAC) >>
 qpat_x_assum ‘!e1. _’ (fn thm => ALL_TAC) >>
 qpat_x_assum ‘!e1'. _’ (fn thm => ALL_TAC) >>
 ‘is_v_bit' e’ by metis_tac[transform_e_is_v_bit] >> gs[] >>
 ‘is_v_bit' e0’ by metis_tac[transform_e_is_v_bit] >> gs[] >>
 ‘is_v_bit' e1’ by metis_tac[transform_e_is_v_bit] >> gs[] >>
 (* First, get result of operation on cake_sem in proof goal *)
 Cases_on ‘e’ >> (gs[is_v_bit'_def]) >>
 Cases_on ‘e0’ >> (gs[is_v_bit'_def]) >>
 Cases_on ‘e1’ >> (gs[is_v_bit'_def]) >>
 Cases_on ‘v'’ >> (gs[is_v_bit'_def]) >>
 Cases_on ‘v''’ >> (gs[is_v_bit'_def]) >>
 Cases_on ‘v'''’ >> (gs[is_v_bit'_def]) >>
 simp[e_exec_slice'_def, AllCaseEqs()] >>
 (* Then, obtain everything involved
  * in the operation from regular semantics by case analysis *)
 Cases_on ‘e1''’ >> (gs[p4_exec_semTheory.is_v_bit_def]) >>
 Cases_on ‘e2''’ >> (gs[p4_exec_semTheory.is_v_bit_def]) >>
 Cases_on ‘e3’ >> (gs[p4_exec_semTheory.is_v_bit_def]) >>
 Cases_on ‘v'’ >> (gs[p4_exec_semTheory.is_v_bit_def]) >>
 Cases_on ‘v''’ >> (gs[p4_exec_semTheory.is_v_bit_def]) >>
 Cases_on ‘v'''’ >> (gs[p4_exec_semTheory.is_v_bit_def]) >>
 (* Apply regular operation *)
 gvs[p4_exec_semTheory.e_exec_slice_def] >>
 (* Connect the concrete values via translation *)
 gvs[transform_e_def, transform_v_def] >>
 (* Slice operation requires some extra stuff *)
 Cases_on ‘p’ >>
 Cases_on ‘p'’ >>
 Cases_on ‘p''’ >>
 gs[slice'_def, slice_def] >>
 (* TODO: Slice operation in cake_sem also requires
  * v2n q'' <= v2n q' /\ v2n q' < r /\ LENGTH q = r, which is a problem since the
  * regular version just lets things be undefined... *)
 cheat
) >>
(* Case 2b: e2' is not value *)
‘is_v_bit' e0’ by metis_tac[transform_e_is_v_bit] >> gs[] >>
‘is_v_bit' e1’ by metis_tac[transform_e_is_v_bit] >> gs[] >>
‘~is_v_bit' e’ by metis_tac[transform_e_not_is_v_bit] >> gs[] >>
(* 3. Rewrite transformation of final state *)
qpat_x_assum ‘transform_e dict (e_slice e1' e2'' e3) = SOME e'2’ (fn thm => ASSUME_TAC $ ONCE_REWRITE_RULE [transform_e_def] thm >> gvs[app_opt_def, AllCaseEqs()]) >>
(* 4. Use induction hypothesis *)
metis_tac[]
QED

Theorem e_exec'_completeness:
!e'1.
e_exec'_complete e'1
Proof
‘(!e1. e_exec'_complete e1) /\ (!l. w_e_l_exec'_complete l) /\ (!p. w_e_exec'_complete p) /\ (!l. l_complete l)’ suffices_by (
 fs []
) >>
irule e'_induction >>
rpt strip_tac >- (
 gs[w_e_l_exec'_complete_def, l_complete_def]
) >- (
 gs[l_complete_def]
) >- (
 (* Slice *)
 metis_tac[e_exec'_completeness_slice]
) >- (
 (* Concatenation *)
 metis_tac[e_exec'_completeness_concat]
) >- (
 (* Binary operation *)
 metis_tac[e_exec'_completeness_binop]
) >- (
 (* Special: l_complete, recursive case *)
 gs[l_complete_equiv, l_complete_exec_def]
) >- (
 (* Field access *)
 metis_tac[e_exec'_completeness_acc]
) >- (
 (* Special: w_e_exec'_complete *)
 gs[w_e_exec'_complete_def]
) >- (
 (* Cast *)
 metis_tac[e_exec'_completeness_cast]
) >- (
 (* Select *)
 metis_tac[e_exec'_completeness_select]
) >- (
 (* Unary operation *)
 metis_tac[e_exec'_completeness_unop]
) >- (
 (* List *)
 gs[e_exec'_complete_def] >>
 rpt strip_tac >>
 qpat_x_assum ‘transform_e dict e1 = SOME (e'_list l)’ (fn thm => assume_tac $ ONCE_REWRITE_RULE [transform_e_def] thm >> gvs[listTheory.UNZIP_MAP, AllCaseEqs()]) >> (
  gs[p4_exec_semTheory.e_exec_def]
 )
) >- (
 (* Function call *)
 metis_tac[e_exec'_completeness_call]
) >- (
 (* Struct *)
 metis_tac[e_exec'_completeness_struct]
) >- (
 (* Header *)
 gs[e_exec'_complete_def] >>
 rpt strip_tac >>
 qpat_x_assum ‘transform_e dict e1 = SOME (e'_header b l)’ (fn thm => assume_tac $ ONCE_REWRITE_RULE [transform_e_def] thm >> gvs[listTheory.UNZIP_MAP, AllCaseEqs()]) >> (
  gs[p4_exec_semTheory.e_exec_def]
 )
) >- (
 (* w_e list: inductive case *)
 Cases_on ‘p’ >>
 gs[w_e_l_exec'_complete_def, l_complete_def, w_e_exec'_complete_def] >>
 rpt strip_tac >>
 Cases_on ‘i’ >> (
  gs[listTheory.oEL_def]
 ) >>
 subgoal ‘MEM e (MAP SND l)’ >- (
  gs[listTheory.oEL_EQ_EL, rich_listTheory.EL_MEM]
 ) >>
 metis_tac[l_complete_MEM]
) >- (
 (* Constant *)
 gs[e_exec'_complete_def] >>
 rpt strip_tac >>
 qpat_x_assum ‘transform_e dict e1 = SOME (e'_v v)’ (fn thm => assume_tac $ ONCE_REWRITE_RULE [transform_e_def] thm >> gvs[listTheory.UNZIP_MAP, AllCaseEqs()]) >>
 gs[p4_exec_semTheory.e_exec_def]
) >>
metis_tac[e_exec'_completeness_var]
QED

(**************)
(* STMT-LEVEL *)
(**************)

(* TODO: Move *)
(* TODO: Generalise from V1Model *)
Definition transform_ctx_def:
 transform_ctx dict ((apply_table_f, ext_map, func_map, b_func_map, pars_map, tbl_map):v1model_ascope ctx) =
  transform_ext_map dict ext_map >>=
  \ext_map'. transform_func_map dict func_map >>=
  \func_map'. transform_func_map dict b_func_map >>=
  \b_func_map'. transform_pars_map dict pars_map >>=
  \pars_map'. transform_tbl_map dict tbl_map >>=
  \tbl_map'. SOME (v1model_apply_table_f'', ext_map':v1model_ascope' ext_map', func_map':func_map', b_func_map':b_func_map', pars_map', tbl_map')
End

(* TODO: Move *)
Definition transform_state_def:
 transform_state dict ((ascope, g_scope_list, frame_list, status):v1model_ascope state) ctrl' =
  transform_ascope dict ascope ctrl' >>=
  \ascope'. transform_scope_list dict g_scope_list >>=
  \g_scope_list'. transform_frame_list dict frame_list >>=
  \frame_list'. transform_status dict status >>=
  \status'. SOME ((ascope', g_scope_list', frame_list', status'):v1model_ascope' state')
End

(* TODO: Move *)
Definition transform_stmt_list_def:
 transform_stmt_list dict stmt_list =
 oFOLDR (transform_stmt dict) stmt_list
End

(* TODO: Fix ctrl transformation *)
Definition stmt_exec'_complete_def:
 stmt_exec'_complete stmt'1 ctrl' =
  !dict ctx ctx' ascope1 ascope'1 g_scope_list1 g_scope_list'1 funn1 funn'1 stmt1 stmt_stack1 stmt_stack'1 scope_list1 scope_list'1 status1 status'1 ctrl.
  dict_bij dict ==>
  transform_ctx dict ctx = SOME ctx' ==>
  transform_ascope dict ascope1 ctrl = SOME ascope'1 ==>
  transform_scope_list dict g_scope_list1 = SOME g_scope_list'1 ==>
  transform_funn dict funn1 = SOME funn'1 ==>
  transform_stmt dict stmt1 = SOME stmt'1 ==>
  transform_stmt_list dict stmt_stack1 = SOME stmt_stack'1 ==>
  transform_scope_list dict scope_list1 = SOME scope_list'1 ==>
  transform_status dict status1 = SOME status'1 ==>
  ?ctrl'.
  !state2 state'2.
  stmt_exec uninit_zero (ctx:v1model_ascope ctx) (ascope1, g_scope_list1:g_scope_list, [(funn1, stmt1::stmt_stack1, scope_list1)], status1) = SOME state2 ==>
  transform_state dict state2 ctrl' = SOME state'2 ==>
  stmt_exec' (ctx':v1model_ascope' ctx') (ascope'1, g_scope_list'1:g_scope_list', [(funn'1, stmt'1::stmt_stack'1, scope_list'1)], status'1) = SOME state'2
End

val stmt_exec'_completeness_tac =
 simp[stmt_exec'_complete_def] >>
 rpt strip_tac >>
 (* The ctrl used in transform_ascope *)
 qexists_tac ‘ctrl’ >>
 rpt strip_tac >>
 qpat_x_assum ‘transform_stmt dict stmt1 = SOME _’ (fn thm => assume_tac $ ONCE_REWRITE_RULE [transform_stmt_def] thm >> gvs[AllCaseEqs()]) >>
 (* 2. Rewrite execution *)
 PairCases_on ‘ctx’ >>
 rename1 ‘(apply_table_f, ext_map, func_map, b_func_map, pars_map, tbl_map)’ >>
 Cases_on ‘status1’ >> (
  gvs[p4_exec_semTheory.stmt_exec_def, AllCaseEqs()]
 ) >>
 gvs[transform_status_def] >>
 Cases_on ‘scope_list1’ >> (
  gvs[p4_exec_semTheory.stmt_exec_def, AllCaseEqs()]
 ) >>
 gvs[transform_scope_list_def, oFOLDR_def] >>
 Cases_on ‘state2’ >>
 PairCases_on ‘r’ >>
 rename1 ‘transform_state dict (ascope2,g_scope_list2,frame_list2,status2) ctrl = SOME state'2’
;

(* Simplifies the below theorem *)
Definition transform_v_init_v_from_tau_def:
transform_v_init_v_from_tau tau =
 !tau' v' dict.
 transform_v dict (arb_from_tau_gen uninit_zero tau) = SOME v' ==>
 transform_tau dict tau = SOME tau' ==>
 init_v_from_tau_cake tau' = v'
End


Theorem transform_v_struct_SOME:
!s_l v_l w_v'_l dict.
transform_v dict (v_struct $ ZIP(s_l, v_l)) = SOME (v'_struct w_v'_l) ==>
?w_l. oFOLDR (ALOOKUP dict) s_l = SOME w_l /\
?v'_l. oFOLDR (transform_v dict) v_l = SOME v'_l /\
w_v'_l = ZIP(w_l, v'_l) /\
LENGTH w_l = LENGTH s_l /\ LENGTH v'_l = LENGTH v_l
Proof
cheat
QED

Theorem transform_tau_xtl_SOME:
!s_l tau_l w_tau'_l sty dict.
transform_tau dict (tau_xtl sty (ZIP (s_l,tau_l))) = SOME (tau'_xtl sty w_tau'_l) ==>
?w_l. oFOLDR (ALOOKUP dict) s_l = SOME w_l /\
?tau'_l. oFOLDR (transform_tau dict) tau_l = SOME tau'_l /\
w_tau'_l = ZIP(w_l, tau'_l) /\
LENGTH w_l = LENGTH s_l /\ LENGTH tau'_l = LENGTH tau_l
Proof
cheat
QED

(* TODO: Move *)
Definition OPTION_diamond_def:
OPTION_diamond lf1 lf2 rf1 rf2 l =
 !e1 e2.
 MEM e1 l ==>
 lf2 $ lf1 e1 = SOME e2 ==>
 OPTION_BIND (rf1 e1) (SOME o rf2) = SOME e2
End

(* TODO: Move *)
Theorem OPTION_diamond_oFOLDR_MAP:
!l1 lf1 lf2 ll rf1 rl2 rf2.
OPTION_diamond lf1 lf2 rf1 rf2 l1 ==>
oFOLDR lf2 (MAP lf1 l1) = SOME ll ==>
oFOLDR rf1 l1 = SOME rl2 ==>
MAP rf2 rl2 = ll
Proof
Induct_on ‘l1’ >- (
 gvs[oFOLDR_def, listTheory.MAP, OPTION_diamond_def]
) >>  
rpt strip_tac >>
gvs[oFOLDR_def, listTheory.MAP] >>
CONJ_TAC >- (
 gs[OPTION_diamond_def] >>
 qpat_x_assum ‘!e1 e2.
          e1 = h \/ MEM e1 l1 ==>
          lf2 (lf1 e1) = SOME e2 ==>
          ?x. rf1 e1 = SOME x /\ rf2 x = e2’
  (fn thm => assume_tac $ Q.SPECL [‘h’, ‘res’] thm) >>
 gs[]
) >>
‘OPTION_diamond lf1 lf2 rf1 rf2 l1’ by (
 gs[OPTION_diamond_def]
) >>
metis_tac[]
QED

Theorem transform_tau_oFOLDR:
!tau_l tau'_l tau tau' dict.
oFOLDR (transform_tau dict) tau_l = SOME tau'_l ==>
MEM tau tau_l ==>
?tau'. transform_tau dict tau = SOME tau'
Proof
Induct >> (
 gvs[listTheory.MEM]
) >>
rpt strip_tac >> (
 gs[oFOLDR_def]
)
QED

Theorem transform_v_init_v_from_tau:
!tau tau' v' dict.
transform_v dict (arb_from_tau_gen uninit_zero tau) = SOME v' ==>
transform_tau dict tau = SOME tau' ==>
init_v_from_tau_cake tau' = v'
Proof
‘(!tau. transform_v_init_v_from_tau tau) /\
 (!l:(string # tau) list. (\xtl. EVERY transform_v_init_v_from_tau $ MAP SND xtl) l) /\
 !p:(string # tau). (\xt. transform_v_init_v_from_tau $ SND xt) p’ suffices_by (
 metis_tac[transform_v_init_v_from_tau_def]
) >>
irule tau_induction >>
gs[transform_v_init_v_from_tau_def] >>
rpt strip_tac >- (
 gvs[Once transform_tau_def, p4_exec_semTheory.arb_from_tau_gen_def] >>
 gvs[p4_exec_semTheory.uninit_bit_def, p4_exec_semTheory.uninit_num_def, transform_v_def, init_v_from_tau_cake_def]
) >- (
 gvs[Once transform_tau_def, p4_exec_semTheory.arb_from_tau_gen_def] >>
 gvs[p4_exec_semTheory.uninit_bit_def, p4_exec_semTheory.uninit_num_def, transform_v_def, init_v_from_tau_cake_def]
) >- (
 gvs[Once transform_tau_def, p4_exec_semTheory.arb_from_tau_gen_def] >>
 gvs[p4_exec_semTheory.uninit_bit_def, p4_exec_semTheory.uninit_num_def, transform_v_def, init_v_from_tau_cake_def]
) >- (
 Cases_on ‘s’ >> (
   gvs[Once transform_v_def, Once transform_tau_def, p4_exec_semTheory.arb_from_tau_gen_def, 
       init_v_from_tau_cake_def, AllCaseEqs()] >- (
    gs[transform_tau_def, init_v_from_tau_cake_def, p4_exec_semTheory.uninit_bit_def]
   )
 ) >- (
  (* TODO: Get this in a better way to unify cases *)
  ‘struct_ty' = struct_ty_struct’ by cheat >> gvs[] >>
   gvs[init_v_from_tau_cake_def] >>
  CONJ_TAC >- (
   qpat_x_assum ‘transform_v_init_v_from_tau tau''’ (fn thm => assume_tac $ REWRITE_RULE [transform_v_init_v_from_tau_def] thm) >>
   metis_tac[]
  ) >>
  (* TODO: The interesting part... *)
  ‘?s_l tau_l. t'' = ZIP(s_l, tau_l) /\ LENGTH s_l = LENGTH tau_l’ by cheat >> gvs[] >>
  gvs[listTheory.MAP_ZIP] >>
  (* Clarification of t': *)
  ‘MAP (\(x,t). (x,arb_from_tau_gen uninit_zero t)) (ZIP (s_l,tau_l)) = ZIP (s_l, MAP (arb_from_tau_gen uninit_zero) tau_l)’ by cheat >> gvs[] >>
  imp_res_tac transform_v_struct_SOME >>
  gvs[] >>
  imp_res_tac transform_tau_xtl_SOME >>
  gvs[] >>
  ‘MAP (\(x,t). (x,init_v_from_tau_cake t)) (ZIP (w_l,tau'_l)) = (ZIP (w_l, MAP init_v_from_tau_cake tau'_l))’ by cheat >> gvs[] >>
  ‘MAP init_v_from_tau_cake tau'_l = v'_l’ suffices_by gs[] >>
  irule $ ISPECL [“tau_l:tau list”, “arb_from_tau_gen uninit_zero”] OPTION_diamond_oFOLDR_MAP >>
  qexistsl_tac[‘transform_v dict’, ‘transform_tau dict’, ‘tau_l’] >>
  gs[OPTION_diamond_def] >>
  rpt strip_tac >>
  gs[listTheory.EVERY_MEM] >>
  res_tac >>
  gs[transform_v_init_v_from_tau_def] >>
  ‘?tau1. transform_tau dict e1 = SOME tau1’ by metis_tac[transform_tau_oFOLDR] >>
  metis_tac[]
 ) >>
 (* Header: *)
 ‘struct_ty' = struct_ty_header’ by cheat >> gvs[] >>
  gvs[init_v_from_tau_cake_def, p4_exec_semTheory.uninit_bit_def] >>
 CONJ_TAC >- (
  qpat_x_assum ‘transform_v_init_v_from_tau tau''’ (fn thm => assume_tac $ REWRITE_RULE [transform_v_init_v_from_tau_def] thm) >>
  metis_tac[]
 ) >>
 ‘?s_l tau_l. t'' = ZIP(s_l, tau_l) /\ LENGTH s_l = LENGTH tau_l’ by cheat >> gvs[] >>
 gvs[listTheory.MAP_ZIP] >>
 (* Clarification of t': *)
 ‘MAP (\(x,t). (x,arb_from_tau_gen uninit_zero t)) (ZIP (s_l,tau_l)) = ZIP (s_l, MAP (arb_from_tau_gen uninit_zero) tau_l)’ by cheat >> gvs[] >>
 imp_res_tac transform_v_struct_SOME >>
 gvs[] >>
 imp_res_tac transform_tau_xtl_SOME >>
 gvs[] >>
 ‘MAP (\(x,t). (x,init_v_from_tau_cake t)) (ZIP (w_l,tau'_l)) = (ZIP (w_l, MAP init_v_from_tau_cake tau'_l))’ by cheat >> gvs[] >>
 ‘MAP init_v_from_tau_cake tau'_l = v'_l’ suffices_by gs[] >>
 irule $ ISPECL [“tau_l:tau list”, “arb_from_tau_gen uninit_zero”] OPTION_diamond_oFOLDR_MAP >>
 qexistsl_tac[‘transform_v dict’, ‘transform_tau dict’, ‘tau_l’] >>
 gs[OPTION_diamond_def] >>
 rpt strip_tac >>
 gs[listTheory.EVERY_MEM] >>
 res_tac >>
 gs[transform_v_init_v_from_tau_def] >>
 ‘?tau1. transform_tau dict e1 = SOME tau1’ by metis_tac[transform_tau_oFOLDR] >>
 metis_tac[]
) >>
gvs[transform_tau_def, p4_exec_semTheory.arb_from_tau_gen_def] >>
gvs[p4_exec_semTheory.uninit_bit_def, p4_exec_semTheory.uninit_num_def, transform_v_def, init_v_from_tau_cake_def] >>
gs[rich_listTheory.REPLICATE_GENLIST] >>
irule listTheory.GENLIST_CONG >>
simp[combinTheory.K_THM]
QED

Theorem transform_t_scope_list_declare_fresh_scope_equiv:
!t_scope t_scope' scope' dict.
transform_scope dict (declare_list_in_fresh_scope_exec uninit_zero t_scope) = SOME scope' ==>
transform_t_scope_list dict t_scope = SOME t_scope' ==>
declare_list_in_fresh_scope' t_scope' = scope'
Proof
Induct >- (
rpt strip_tac >>
gvs[p4_exec_semTheory.declare_list_in_fresh_scope_exec_def, declare_list_in_fresh_scope'_def,
   transform_scope_def, transform_t_scope_list_def, oFOLDR_def]
) >>
rpt strip_tac >>
PairCases_on ‘h’ >>
rename1 ‘(varn, tau, lval_opt)’ >>
gvs[p4_exec_semTheory.declare_list_in_fresh_scope_exec_def, declare_list_in_fresh_scope'_def,
   transform_scope_def, transform_t_scope_list_def, oFOLDR_def] >>
CONJ_TAC >- (
 PairCases_on ‘res'’ >>
 gs[] >>
 PairCases_on ‘res’ >>
 gvs[transform_scope_entry_def, transform_t_scope_def, AllCaseEqs()] >>
 metis_tac[transform_v_init_v_from_tau]
) >>
qpat_x_assum ‘!t_scope''. _’ (fn thm => irule thm) >>
metis_tac[]
QED

Theorem stmt_exec'_completeness:
!ctrl' stmt'1.
stmt_exec'_complete stmt'1 ctrl'
Proof
assume_tac e_exec'_completeness >>
strip_tac >>
‘!stmt'1. (\stmt'. !ctrl'. stmt_exec'_complete stmt' ctrl') stmt'1’ suffices_by (
 fs[]
) >>
irule stmt'_induction >> (
 gs[]
) >>
rpt strip_tac >- (
 (*********)
 (* Empty *)
 gs[stmt_exec'_complete_def] >>
 rpt strip_tac >>
 (* The ctrl used in transform_ascope *)
 qexists_tac ‘ctrl’ >>
 rpt strip_tac >>
 qpat_x_assum ‘transform_stmt dict stmt1 = SOME _’ (fn thm => assume_tac $ ONCE_REWRITE_RULE [transform_stmt_def] thm >> gvs[AllCaseEqs()]) >>
 (* 2. Rewrite execution *)
 PairCases_on ‘ctx’ >>
 rename1 ‘(apply_table_f, ext_map, func_map, b_func_map, pars_map, tbl_map)’ >>
 Cases_on ‘status1’ >> Cases_on ‘scope_list1’ >> Cases_on ‘stmt_stack1’ >> (
  gvs[p4_exec_semTheory.stmt_exec_def, AllCaseEqs()]
 ) >>
 (* 3. Finish transformations with the results *)
 gvs[transform_status_def, transform_stmt_list_def, transform_scope_list_def, transform_state_def, transform_frame_list_def, transform_frame_def, oFOLDR_def, AllCaseEqs()] >>
 (* 4. Rewrite the cake_sem execution *)
 gvs[stmt_exec'_def, AllCaseEqs()]
) >- (
 (**********)
 (* Extern *)
 (* TODO: This has to go through all the cases of the extern functions... *)
 gs[stmt_exec'_complete_def] >>
 rpt strip_tac >>
 (* The ctrl used in transform_ascope *)
 qexists_tac ‘ctrl’ >>
 rpt strip_tac >>
 qpat_x_assum ‘transform_stmt dict stmt1 = SOME _’ (fn thm => assume_tac $ ONCE_REWRITE_RULE [transform_stmt_def] thm >> gvs[AllCaseEqs()]) >>
 (* 2. Rewrite execution *)
 PairCases_on ‘ctx’ >>
 rename1 ‘(apply_table_f, ext_map, func_map, b_func_map, pars_map, tbl_map)’ >>
 Cases_on ‘status1’ >> Cases_on ‘scope_list1’ >> Cases_on ‘stmt_stack1’ >> (
  gvs[p4_exec_semTheory.stmt_exec_def, AllCaseEqs()]
 ) >- (
  (* Case 1: At bottom of stmt_stack *)
  (* 3. Finish transformations with the results *)
  gvs[transform_status_def, transform_stmt_list_def, transform_scope_list_def, transform_state_def, transform_frame_list_def, transform_frame_def, oFOLDR_def, AllCaseEqs()] >> (
   (* 4. Rewrite the cake_sem execution *)
   PairCases_on ‘ctx'’ >>
   rename1 ‘(apply_table_f', ext_map', func_map', b_func_map', pars_map', tbl_map')’ >>
   gvs[stmt_exec'_def, AllCaseEqs()] >>
   cheat
  )
 ) >>
 (* Case 2: Some stmt_stack below *)
 (* 3. Finish transformations with the results *)
 gvs[transform_status_def, transform_stmt_list_def, transform_scope_list_def, transform_state_def, transform_frame_list_def, transform_frame_def, oFOLDR_def, AllCaseEqs()] >> (
  (* 4. Rewrite the cake_sem execution *)
  PairCases_on ‘ctx'’ >>
  rename1 ‘(apply_table_f', ext_map', func_map', b_func_map', pars_map', tbl_map')’ >>
  gvs[stmt_exec'_def, AllCaseEqs()] >>
  cheat
 )
) >- (
 (*********************)
 (* Table application *)
 gs[stmt_exec'_complete_def] >>
 rpt strip_tac >>
 (* The ctrl used in transform_ascope *)
 qexists_tac ‘ctrl’ >>
 rpt strip_tac >>
 qpat_x_assum ‘transform_stmt dict stmt1 = SOME _’ (fn thm => assume_tac $ ONCE_REWRITE_RULE [transform_stmt_def] thm >> gvs[AllCaseEqs()]) >>
 (* 2. Rewrite execution *)
 PairCases_on ‘ctx’ >>
 rename1 ‘(apply_table_f, ext_map, func_map, b_func_map, pars_map, tbl_map)’ >>
 Cases_on ‘status1’ >> Cases_on ‘scope_list1’ >> Cases_on ‘stmt_stack1’ >> (
  gvs[p4_exec_semTheory.stmt_exec_def, AllCaseEqs()]
 ) >>
 cheat
(*
 (* 3. Finish transformations with the results *)
 gvs[transform_status_def, transform_stmt_list_def, transform_scope_list_def, transform_state_def, transform_frame_list_def, transform_frame_def, oFOLDR_def, AllCaseEqs()] >>
 (* 4. Rewrite the cake_sem execution *)
 PairCases_on ‘ctx'’ >>
 rename1 ‘(apply_table_f', ext_map', func_map', b_func_map', pars_map', tbl_map')’ >>
 gvs[stmt_exec'_def, AllCaseEqs()] >>
 (* Preservation of all the properties... *)
 cheat
*)
) >- (
 (**********)
 (* Return *)
 gs[stmt_exec'_complete_def] >>
 rpt strip_tac >>
 (* The ctrl used in transform_ascope *)
 qexists_tac ‘ctrl’ >>
 rpt strip_tac >>
 qpat_x_assum ‘transform_stmt dict stmt1 = SOME _’ (fn thm => assume_tac $ ONCE_REWRITE_RULE [transform_stmt_def] thm >> gvs[AllCaseEqs()]) >>
 (* 2. Rewrite execution *)
 PairCases_on ‘ctx’ >>
 rename1 ‘(apply_table_f, ext_map, func_map, b_func_map, pars_map, tbl_map)’ >>
 Cases_on ‘status1’ >> Cases_on ‘scope_list1’ >> Cases_on ‘stmt_stack1’ >> (
  gvs[p4_exec_semTheory.stmt_exec_def, AllCaseEqs()]
 ) >> (
  cheat
  (*
  (* 5 different combinations possible *)
  (* 3. Finish transformations with the results *)
  gvs[transform_status_def, transform_stmt_list_def, transform_scope_list_def, transform_state_def, transform_frame_list_def, transform_frame_def, oFOLDR_def, AllCaseEqs()] >>
  (* 4. Rewrite the cake_sem execution *)
  PairCases_on ‘ctx'’ >>
  rename1 ‘(apply_table_f', ext_map', func_map', b_func_map', pars_map', tbl_map')’ >>
  gvs[stmt_exec'_def, AllCaseEqs()] >>
  (* Preservation of all the properties... *)
  cheat
*)
 )
) >- (
 (*********)
 (* Trans *)
 gs[stmt_exec'_complete_def] >>
 rpt strip_tac >>
 (* The ctrl used in transform_ascope *)
 qexists_tac ‘ctrl’ >>
 rpt strip_tac >>
 qpat_x_assum ‘transform_stmt dict stmt1 = SOME _’ (fn thm => assume_tac $ ONCE_REWRITE_RULE [transform_stmt_def] thm >> gvs[AllCaseEqs()]) >>
 (* 2. Rewrite execution *)
 PairCases_on ‘ctx’ >>
 rename1 ‘(apply_table_f, ext_map, func_map, b_func_map, pars_map, tbl_map)’ >>
 Cases_on ‘status1’ >> Cases_on ‘scope_list1’ >> Cases_on ‘stmt_stack1’ >> (
  gvs[p4_exec_semTheory.stmt_exec_def, AllCaseEqs()]
 ) >> (
  cheat
(*
  (* 5 different combinations possible *)
  (* 3. Finish transformations with the results *)
  gvs[transform_status_def, transform_stmt_list_def, transform_scope_list_def, transform_state_def, transform_frame_list_def, transform_frame_def, oFOLDR_def, AllCaseEqs()] >>
  (* 4. Rewrite the cake_sem execution *)
  PairCases_on ‘ctx'’ >>
  rename1 ‘(apply_table_f', ext_map', func_map', b_func_map', pars_map', tbl_map')’ >>
  gvs[stmt_exec'_def, AllCaseEqs()] >>
  (* Preservation of all the properties... *)
  cheat
*)
 )
) >- (
 (**************)
 (* Assignment *)
 gs[stmt_exec'_complete_def] >>
 rpt strip_tac >>
 (* The ctrl used in transform_ascope *)
 qexists_tac ‘ctrl’ >>
 rpt strip_tac >>
 qpat_x_assum ‘transform_stmt dict stmt1 = SOME _’ (fn thm => assume_tac $ ONCE_REWRITE_RULE [transform_stmt_def] thm >> gvs[AllCaseEqs()]) >>
 (* 2. Rewrite execution *)
 PairCases_on ‘ctx’ >>
 rename1 ‘(apply_table_f, ext_map, func_map, b_func_map, pars_map, tbl_map)’ >>
 Cases_on ‘status1’ >> Cases_on ‘scope_list1’ >> Cases_on ‘stmt_stack1’ >> (
  gvs[p4_exec_semTheory.stmt_exec_def, AllCaseEqs()]
 ) >> (
  cheat
(*
  (* 5 different combinations possible *)
  (* 3. Finish transformations with the results *)
  gvs[transform_status_def, transform_stmt_list_def, transform_scope_list_def, transform_state_def, transform_frame_list_def, transform_frame_def, oFOLDR_def, AllCaseEqs()] >>
  (* 4. Rewrite the cake_sem execution *)
  PairCases_on ‘ctx'’ >>
  rename1 ‘(apply_table_f', ext_map', func_map', b_func_map', pars_map', tbl_map')’ >>
  gvs[stmt_exec'_def, AllCaseEqs()] >>
  (* Preservation of all the properties... *)
  cheat
*)
 )
) >- (
 (************)
 (* Sequence *)
 simp[stmt_exec'_complete_def] >>
 rpt strip_tac >>
 (* The ctrl used in transform_ascope *)
 qexists_tac ‘ctrl’ >>
 rpt strip_tac >>
 qpat_x_assum ‘transform_stmt dict stmt1 = SOME _’ (fn thm => assume_tac $ ONCE_REWRITE_RULE [transform_stmt_def] thm >> gvs[AllCaseEqs()]) >>
 (* 2. Rewrite execution *)
 PairCases_on ‘ctx’ >>
 rename1 ‘(apply_table_f, ext_map, func_map, b_func_map, pars_map, tbl_map)’ >>
 Cases_on ‘status1’ >> (
  gvs[p4_exec_semTheory.stmt_exec_def, AllCaseEqs()]
 ) >>
 gvs[transform_status_def] >>
 Cases_on ‘scope_list1’ >> (
  gvs[p4_exec_semTheory.stmt_exec_def, AllCaseEqs()]
 ) >>
 gvs[transform_scope_list_def, oFOLDR_def] >>
 Cases_on ‘state2’ >>
 PairCases_on ‘r’ >>
 rename1 ‘transform_state dict (ascope2,g_scope_list2,frame_list2,status2) ctrl = SOME state'2’ >>
 gs[p4_exec_semTheory.exec_stmt_seq_SOME_REWRS] >>
 Cases_on ‘is_empty stmt1'’ >> (
  gvs[]
 ) >> (
  (* 4 different combinations possible *)
  (* 3. Finish transformations with the results *)
  gvs[transform_status_def, transform_stmt_list_def, transform_scope_list_def, transform_state_def, transform_frame_list_def, transform_frame_def, oFOLDR_def, AllCaseEqs()] >>
  (* 4. Rewrite the cake_sem execution *)
  PairCases_on ‘ctx'’ >>
  rename1 ‘(apply_table_f', ext_map', func_map', b_func_map', pars_map', tbl_map')’ >>
  gvs[stmt_exec'_def, AllCaseEqs()] >>
  (* Apply induction hypothesis depending on whether you end up with stmt_exec in assums *)
  cheat
 )
) >- (
 (***************)
 (* Conditional *)
 (* Shared incipit tactic: *)
 simp[stmt_exec'_complete_def] >>
 rpt strip_tac >>
 (* The ctrl used in transform_ascope *)
 qexists_tac ‘ctrl’ >>
 rpt strip_tac >>
 qpat_x_assum ‘transform_stmt dict stmt1 = SOME _’ (fn thm => assume_tac $ ONCE_REWRITE_RULE [transform_stmt_def] thm >> gvs[AllCaseEqs()]) >>
 (* 2. Rewrite execution *)
 PairCases_on ‘ctx’ >>
 rename1 ‘(apply_table_f, ext_map, func_map, b_func_map, pars_map, tbl_map)’ >>
 Cases_on ‘status1’ >> (
  gvs[p4_exec_semTheory.stmt_exec_def, AllCaseEqs()]
 ) >>
 gvs[transform_status_def] >>
 Cases_on ‘scope_list1’ >> (
  gvs[p4_exec_semTheory.stmt_exec_def, AllCaseEqs()]
 ) >>
 gvs[transform_scope_list_def, oFOLDR_def] >>
 Cases_on ‘state2’ >>
 PairCases_on ‘r’ >>
 rename1 ‘transform_state dict (ascope2,g_scope_list2,frame_list2,status2) ctrl = SOME state'2’ >>
 (* End of shared incipit *)

 gs[p4_exec_semTheory.exec_stmt_cond_SOME_REWRS] >>
 Cases_on ‘is_v_bool e'’ >> (
  gs[]
 ) >- (
  (* Case condition is reduced *)
  Cases_on ‘b’ >> (
   gs[]
  ) >- (
   (* Case condition holds *)
   cheat
  ) >>
  (* Case condition doesn't hold *)
  cheat
 ) >>
 (* Case condition is not reduced: use expression completeness *)
 cheat
) >>
(*********)
(* Block *)
(* 1. Common incipit tactic *)
stmt_exec'_completeness_tac >>
(* 2. Use rewriting theorem *)
gvs[p4_exec_semTheory.exec_stmt_block_SOME_REWRS] >>
(* 3. Perform transformations *)
gvs[transform_state_def, transform_frame_list_def, transform_frame_def, transform_status_def, transform_scope_list_def, oFOLDR_def, AllCaseEqs()] >>
qpat_x_assum ‘transform_stmt dict stmt_empty = SOME _’ (fn thm => assume_tac $ ONCE_REWRITE_RULE [transform_stmt_def] thm >> gvs[AllCaseEqs()]) >>

(* 4. Now try to rewrite the stmt_exec' in the goal *)
PairCases_on ‘ctx'’ >>
rename1 ‘(apply_table_f', ext_map', func_map', b_func_map', pars_map', tbl_map')’ >>
Cases_on ‘stmt_stack1’ >> (
 gvs[transform_stmt_list_def, oFOLDR_def, AllCaseEqs()]
) >> (
 (* Same lemma needed for both cases *)
 gvs[stmt_exec'_def, AllCaseEqs()] >>
 metis_tac[transform_t_scope_list_declare_fresh_scope_equiv]
)
QED

(***************)
(* FRAME-LEVEL *)
(***************)

Definition frames_exec'_complete_def:
 frames_exec'_complete frame_list'1 ctrl' =
  !dict ctx ctx' ascope1 ascope'1 g_scope_list1 g_scope_list'1 frame_list1 status1 status'1 ctrl.
  dict_bij dict ==>
  transform_ctx dict ctx = SOME ctx' ==>
  transform_ascope dict ascope1 ctrl = SOME ascope'1 ==>
  transform_scope_list dict g_scope_list1 = SOME g_scope_list'1 ==>
  transform_frame_list dict frame_list1 = SOME frame_list'1 ==>
  transform_status dict status1 = SOME status'1 ==>
  ?ctrl'.
  !state2 state'2.
  frames_exec uninit_zero (ctx:v1model_ascope ctx) (ascope1, g_scope_list1:g_scope_list, frame_list1, status1) = SOME state2 ==>
  transform_state dict state2 ctrl' = SOME state'2 ==>
  frames_exec' (ctx':v1model_ascope' ctx') (ascope'1, g_scope_list'1:g_scope_list', frame_list'1, status'1) = SOME state'2
End

Theorem scopes_to_pass_transform:
!funn funn' dict func_map func_map' b_func_map b_func_map' g_scope_list1 g_scope_list'1 g_scope_list2 .
scopes_to_pass funn func_map b_func_map g_scope_list1 = SOME g_scope_list2 ==>
transform_funn dict funn = SOME funn' ==>
transform_func_map dict func_map = SOME func_map' ==>
transform_func_map dict b_func_map = SOME b_func_map' ==>
transform_scope_list dict g_scope_list1 = SOME g_scope_list'1 ==>
?g_scope_list'2.
transform_scope_list dict g_scope_list2 = SOME g_scope_list'2 /\
scopes_to_pass' funn' func_map' b_func_map' g_scope_list'1 = SOME g_scope_list'2
Proof
(* TODO: This "theorem" is problematic, since scopes_to_pass is formulated in such a way it
 * tells us nothing about the size of g_scope_list. This can be solved by switching the version
 * in the executable semantics to a version of the current scopes_to_pass', naming it scopes_to_pass_exec.
 * (Double-check this is OK for the soundness proof)
 * Cannot have a separate transform_g_scope_list that ensures this, since those lists must have 1 or 2 entries. *)
cheat
QED

(* TODO: Note the slightly different form at the end: at this point, we have the transformation for the final scope list *)
Theorem scopes_to_retrieve_transform:
!funn funn' dict func_map func_map' b_func_map b_func_map' g_scope_list1 g_scope_list'1 g_scope_list2 g_scope_list'2 g_scope_list3 g_scope_list'3.
scopes_to_retrieve funn func_map b_func_map g_scope_list1 g_scope_list2 = SOME g_scope_list3 ==>
transform_funn dict funn = SOME funn' ==>
transform_func_map dict func_map = SOME func_map' ==>
transform_func_map dict b_func_map = SOME b_func_map' ==>
transform_scope_list dict g_scope_list1 = SOME g_scope_list'1 ==>
transform_scope_list dict g_scope_list2 = SOME g_scope_list'2 ==>
transform_scope_list dict g_scope_list3 = SOME g_scope_list'3 ==>
scopes_to_retrieve' funn' func_map' b_func_map' g_scope_list'1 g_scope_list'2 = SOME g_scope_list'3
Proof
(* TODO: Same issue as above *)
cheat
QED

Theorem map_to_pass_transform:
!funn funn' dict b_func_map1 b_func_map2 b_func_map'1.
dict_bij dict ==>
map_to_pass funn b_func_map1 = SOME b_func_map2 ==>
transform_funn dict funn = SOME funn' ==>
transform_func_map dict b_func_map1 = SOME b_func_map'1 ==>
?b_func_map'2.
transform_func_map dict b_func_map2 = SOME b_func_map'2 /\
map_to_pass' funn' b_func_map'1 = SOME b_func_map'2
Proof
rpt strip_tac >>
Cases_on ‘funn’ >> (
 gvs[map_to_pass_def, transform_funn_def, oFOLDR_def, map_to_pass'_def, AllCaseEqs()]
) >- (
  qexists_tac ‘[]’ >>
  simp[transform_func_map_def, oFOLDR_def] >>
  metis_tac[transform_func_map_ALOOKUP_NONE]
) >- (
 PairCases_on ‘v’ >>
 metis_tac[transform_func_map_ALOOKUP_SOME]
) >> (
 simp[transform_func_map_def, oFOLDR_def]
)
QED

Theorem tbl_to_pass_transform:
!funn funn' dict b_func_map b_func_map' tbl_map1 tbl_map'1 tbl_map2.
dict_bij dict ==>
tbl_to_pass funn b_func_map tbl_map1 = SOME tbl_map2 ==>
transform_funn dict funn = SOME funn' ==>
transform_func_map dict b_func_map = SOME b_func_map' ==>
transform_tbl_map dict tbl_map1 = SOME tbl_map'1 ==>
?tbl_map'2.
transform_tbl_map dict tbl_map2 = SOME tbl_map'2 /\
tbl_to_pass' funn' b_func_map' tbl_map'1 = SOME tbl_map'2
Proof
rpt strip_tac >>
Cases_on ‘funn’ >> (
 gvs[tbl_to_pass_def, transform_funn_def, oFOLDR_def, tbl_to_pass'_def, AllCaseEqs()]
) >- (
  qexists_tac ‘[]’ >>
  simp[transform_tbl_map_def, oFOLDR_def] >>
  metis_tac[transform_func_map_ALOOKUP_NONE]
) >- (
 PairCases_on ‘v’ >>
 metis_tac[transform_func_map_ALOOKUP_SOME]
) >> (
 simp[transform_tbl_map_def, oFOLDR_def]
)
QED

Theorem frames_exec'_completeness:
!frame_list'1 ctrl'.
frames_exec'_complete frame_list'1 ctrl'
Proof
(* TODO: Induction not needed? *)
Induct >> (
 simp[frames_exec'_complete_def] >>
 rpt strip_tac >>
 Cases_on ‘status1’ >> (
  gvs[transform_status_def, transform_frame_list_def, oFOLDR_def] >>
  Cases_on ‘frame_list1’ >> (
   gvs[transform_frame_def, oFOLDR_def, p4_exec_semTheory.frames_exec_def]
  )
 )
) >>
PairCases_on ‘h'’ >>
PairCases_on ‘ctx’ >>
gvs[transform_frame_def, oFOLDR_def] >>
qexists_tac ‘ctrl’ >>
rpt strip_tac >>
Cases_on ‘t’ >- (
 (* Case: bottom frame *)
 gvs[transform_frame_def, oFOLDR_def, p4_exec_semTheory.frames_exec_def, AllCaseEqs()] >>
 gvs[transform_ctx_def] >>
 gvs[frames_exec'_def, AllCaseEqs()] >>
 Cases_on ‘h'1’ >- (
  gvs[oFOLDR_def] >>
  Cases_on ‘h'2’ >> (
   gvs[transform_scope_list_def, oFOLDR_def, p4_exec_semTheory.stmt_exec_def]
  )
 ) >>
 
 imp_res_tac scopes_to_pass_transform >> gvs[] >>
 imp_res_tac map_to_pass_transform >> gvs[] >>
 imp_res_tac tbl_to_pass_transform >> gvs[] >>
 
 gvs[oFOLDR_def] >>
 qpat_x_assum ‘!ctrl'. _’ (fn thm => ALL_TAC) >>
 (* Use stmt completeness *)
 imp_res_tac $ REWRITE_RULE [stmt_exec'_complete_def] stmt_exec'_completeness >>
 qpat_x_assum ‘!ctx' ctx. _’
  (fn thm => assume_tac $ Q.SPECL [‘(v1model_apply_table_f'',ext_map',func_map',b_func_map'2,pars_map',tbl_map'2)’,
                                   ‘(ctx0,ctx1,ctx2,b_func_map',ctx4,tbl_map')’] thm) >>
 gvs[transform_ctx_def] >>
 ‘!stmt_stack1 stmt_stack'1.
          transform_stmt_list dict stmt_stack1 = SOME stmt_stack'1 ==>
          !scope_list1 scope_list'1.
            transform_scope_list dict scope_list1 = SOME scope_list'1 ==>
            !status1 status'1.
              transform_status dict status1 = SOME status'1 ==>
              ?ctrl'. !state2 state'2.
                stmt_exec uninit_zero
                  (ctx0,ctx1,ctx2,b_func_map',ctx4,tbl_map')
                  (ascope1,g_scope_list',[(h'0,h::stmt_stack1,scope_list1)],
                   status1) =
                SOME state2 ==>
                transform_state dict state2 ctrl' = SOME state'2 ==>
                stmt_exec'
                  (v1model_apply_table_f'',ext_map',func_map',b_func_map'2,
                   pars_map',tbl_map'2)
                  (ascope'1,g_scope_list'2,
                   [(funn',res::stmt_stack'1,scope_list'1)],status'1) =
                SOME state'2’ by res_tac >>
 qpat_x_assum ‘!ctrl ascope1 ascope'1.
               transform_ascope dict ascope1 ctrl = SOME ascope'1 ==> _’ (fn thm => ALL_TAC) >>
 gs[GSYM transform_stmt_list_def] >>
 ‘!status1 status'1.
          transform_status dict status1 = SOME status'1 ==>
          ?ctrl'. !state2 state'2.
            stmt_exec uninit_zero (ctx0,ctx1,ctx2,b_func_map',ctx4,tbl_map')
              (ascope1,g_scope_list',[(h'0,h::t,h'2)],status1) =
            SOME state2 ==>
            transform_state dict state2 ctrl' = SOME state'2 ==>
            stmt_exec'
              (v1model_apply_table_f'',ext_map',func_map',b_func_map'2,
               pars_map',tbl_map'2)
              (ascope'1,g_scope_list'2,[(funn',res::res_list,scope_list')],
               status'1) =
            SOME state'2’ by res_tac >>
 qpat_x_assum ‘!stmt_stack1 stmt_stack'1.
               transform_stmt_list dict stmt_stack1 = SOME stmt_stack'1 ==> _’ (fn thm => ALL_TAC) >>
 qpat_x_assum ‘!status1 status'1. _’ (fn thm => assume_tac $ Q.SPECL [‘status_running’, ‘status'_running’] thm) >>
 gvs[transform_status_def, transform_state_def] >>
 (* Different cases for different final statuses, but can be treated the same *)
 Cases_on ‘status'’ >> (
  gvs[transform_state_def, transform_status_def] >>
  (* TODO: Fix ctrl *)
  ‘transform_ascope dict ascope' ctrl' = SOME ascope''’ by cheat >> gvs[] >>
  (* TODO: From where can this be obtained? *)
  ‘?g_scope_list'''. transform_scope_list dict g_scope_list'' = SOME g_scope_list'''’ by cheat >> gvs[] >>
 imp_res_tac scopes_to_retrieve_transform >>
 gs[]
 )
) >>
(* Case: more frames below *)
PairCases_on ‘h’ >>
gvs[transform_frame_def, oFOLDR_def, p4_exec_semTheory.frames_exec_def, AllCaseEqs()] >> (
 gvs[transform_state_def, transform_status_def]
) >- (
 (* stmt_exec result status running *)
 (* Virtually identical to the above, except res_list' *)
 gvs[transform_ctx_def] >>
 gvs[frames_exec'_def, AllCaseEqs()] >>
 imp_res_tac scopes_to_pass_transform >> gvs[] >>
 imp_res_tac map_to_pass_transform >> gvs[] >>
 imp_res_tac tbl_to_pass_transform >> gvs[] >>
 (* Expose the top statement in the statement stack x*)
 Cases_on ‘h'1’ >- (
  gvs[oFOLDR_def] >>
  Cases_on ‘h'2’ >> (
   gvs[transform_scope_list_def, oFOLDR_def, p4_exec_semTheory.stmt_exec_def]
  )
 ) >>
 gvs[oFOLDR_def] >>
 (* Use stmt completeness to get proof goal *)
 imp_res_tac $ REWRITE_RULE [stmt_exec'_complete_def] stmt_exec'_completeness >>
 qpat_x_assum ‘!ctx' ctx. _’
  (fn thm => assume_tac $ Q.SPECL [‘(v1model_apply_table_f'',ext_map',func_map',b_func_map'2,pars_map',tbl_map'2)’,
                                   ‘(ctx0,ctx1,ctx2,b_func_map',ctx4,tbl_map')’] thm) >>
 gvs[transform_ctx_def] >>
 ‘!stmt_stack1 stmt_stack'1.
  transform_stmt_list dict stmt_stack1 = SOME stmt_stack'1 ==>
  !scope_list1 scope_list'1.
    transform_scope_list dict scope_list1 = SOME scope_list'1 ==>
    !status1 status'1.
      transform_status dict status1 = SOME status'1 ==>
      ?ctrl'. !state2 state'2.
        stmt_exec uninit_zero
          (ctx0,ctx1,ctx2,b_func_map',ctx4,tbl_map')
          (ascope1,g_scope_list',[(h'0,h::stmt_stack1,scope_list1)],
           status1) =
        SOME state2 ==>
        transform_state dict state2 ctrl' = SOME state'2 ==>
        stmt_exec'
          (v1model_apply_table_f'',ext_map',func_map',b_func_map'2,
           pars_map',tbl_map'2)
          (ascope'1,g_scope_list'2,
           [(funn',res::stmt_stack'1,scope_list'1)],status'1) =
        SOME state'2’ by res_tac >>
 qpat_x_assum ‘!ctrl ascope1 ascope'1.
               transform_ascope dict ascope1 ctrl = SOME ascope'1 ==> _’ (fn thm => ALL_TAC) >>
 gs[GSYM transform_stmt_list_def] >>
 ‘!status1 status'1.
  transform_status dict status1 = SOME status'1 ==>
  ?ctrl'. !state2 state'2.
    stmt_exec uninit_zero (ctx0,ctx1,ctx2,b_func_map',ctx4,tbl_map')
      (ascope1,g_scope_list',[(h'0,h::t,h'2)],status1) =
    SOME state2 ==>
    transform_state dict state2 ctrl' = SOME state'2 ==>
    stmt_exec'
      (v1model_apply_table_f'',ext_map',func_map',b_func_map'2,
       pars_map',tbl_map'2)
      (ascope'1,g_scope_list'2,[(funn',res::res_list',scope_list')],
       status'1) =
    SOME state'2’ by res_tac >>
 qpat_x_assum ‘!stmt_stack1 stmt_stack'1.
               transform_stmt_list dict stmt_stack1 = SOME stmt_stack'1 ==> _’ (fn thm => ALL_TAC) >>
 qpat_x_assum ‘!status1 status'1. _’ (fn thm => assume_tac $ Q.SPECL [‘status_running’, ‘status'_running’] thm) >>
 gvs[transform_status_def, transform_state_def] >>
 (* TODO: Fix ctrl *)
 ‘transform_ascope dict ascope' ctrl' = SOME ascope''’ by cheat >> gvs[] >>
 (* TODO: From where can this be obtained? *)
 ‘?g_scope_list'''. transform_scope_list dict g_scope_list'' = SOME g_scope_list'''’ by cheat >> gvs[] >>
 (* TODO: Since frame_list' ++ (h0,h1,h2)::t' can be transformed, frame_list' can also be transformed
  * into something by itself. The second conjunct formalises the result of all frame transformations *)
 ‘?frame_list'3'. transform_frame_list dict frame_list' = SOME frame_list'3' /\
  frame_list'' = frame_list'3' ++ [(funn'',stmt_stack'',scope_list'')] ++ res_list’ by cheat >> gvs[] >> 
 (* TODO: Second scopes_to_retrieve left: This looks OK *)
 imp_res_tac scopes_to_retrieve_transform >>
 gs[]
) >- (
 (* Return *)
 (* Same as above, but ending after obtaining the tansformed ascope is different... *)
 cheat
) >>
(* Transition *)
(* Can be handled the exact same as the Running case *)
cheat
QED

(*************)
(* TOP-LEVEL *)
(*************)

Definition transform_arch_frame_list_def:
 (transform_arch_frame_list dict (arch_frame_list_regular frame_list) =
  transform_frame_list dict frame_list >>=
  \frame_list'. SOME $ arch_frame_list'_regular frame_list') /\
 (transform_arch_frame_list dict arch_frame_list_empty =
  SOME arch_frame_list'_empty)
End

Theorem arch_exec'_completeness:
!dict ab_list pblock_map ffblock_map input_f output_f copyin_pbl copyout_pbl apply_table_f ext_map func_map ab_list' pblock_map' ffblock_map' input_f' output_f' copyin_pbl' copyout_pbl' apply_table_f' ext_map' func_map' ctrl aenv1 aenv'1 g_scope_list1 g_scope_list'1 arch_frame_list1 arch_frame_list'1 status1 status'1 s2 s'2.
dict_bij dict ==>
transform_actx dict (ab_list,pblock_map,ffblock_map,input_f,output_f,copyin_pbl,
                     copyout_pbl,apply_table_f,ext_map,func_map) = SOME (ab_list',pblock_map',ext_map',func_map') ==>
(* TODO: Need to state and assume completeness of the following:
ffblock_map'
input_f'
output_f'
copyin_pbl'
copyout_pbl'
apply_table_f'
*)
  transform_aenv dict aenv1 ctrl = SOME aenv'1 ==>
  transform_scope_list dict g_scope_list1 = SOME g_scope_list'1 ==>
  transform_arch_frame_list dict arch_frame_list1 = SOME arch_frame_list'1 ==>
  transform_status dict status1 = SOME status'1 ==>
  
arch_exec uninit_zero (ab_list,pblock_map,ffblock_map,input_f,output_f,
                 copyin_pbl,copyout_pbl,apply_table_f,ext_map,func_map) (aenv1, g_scope_list1, arch_frame_list1, status1) = SOME s2 ==>
transform_astate dict s2 ctrl = SOME s'2 ==>
arch_exec' (ab_list',pblock_map',ffblock_map',input_f',output_f',
                  copyin_pbl',copyout_pbl',apply_table_f',ext_map',func_map') (aenv'1, g_scope_list'1, arch_frame_list'1, status'1) = SOME s'2
Proof
rpt strip_tac >>
PairCases_on ‘aenv1’ >>
PairCases_on ‘aenv'1’ >>
Cases_on ‘status1’ >> (
 gvs[transform_status_def] >>
 Cases_on ‘arch_frame_list1’ >> (
  gvs[arch_exec'_def, p4_exec_semTheory.arch_exec_def, AllCaseEqs()]
 )
) >- (
 (* Input *)
 gvs[transform_arch_frame_list_def] >>
 gvs[arch_exec'_def, AllCaseEqs()] >>
 qexists_tac ‘arch_block'_inp’ >>
 CONJ_TAC >- (
  gvs[transform_astate_def, transform_aenv_def, transform_actx_def] >>
  ‘EL aenv'10 ab_list = arch_block_inp ==>
   transform_ab_list dict ab_list = SOME ab_list' ==>
   oEL aenv'10 ab_list' = SOME arch_block'_inp’ by cheat >>
  metis_tac[]
 ) >>
 gs[] >>
 PairCases_on ‘s'2’ >>
 qexists_tac ‘(s'21,(s'23,s'24,s'25,s'26))’ >>
 CONJ_TAC >- (
  PairCases_on ‘scope'’ >>
  gvs[transform_astate_def, transform_aenv_def, transform_actx_def, transform_ascope_def] >>
  (* TODO: Some stuff still missing here for stating input lemma... *)
  (* TODO: Input functions have to be specialised in the theorem *)
  cheat
 ) >>
 qexistsl_tac [‘s'21’, ‘(s'23,s'24,s'25,s'26)’] >>
 gvs[transform_astate_def, transform_status_def, transform_aenv_def]
) >- (
 (* Entry into pblock *)
 gvs[transform_arch_frame_list_def] >>
 gvs[arch_exec'_def, AllCaseEqs()] >>
 cheat
) >- (
 (* Fixed-function block *)
 gvs[transform_arch_frame_list_def] >>
 gvs[arch_exec'_def, AllCaseEqs()] >>
 (* TODO: Translation between fixed-function block? This has to be specialised in the
  * theorem *)
 cheat
) >- (
 (* Output *)
 gvs[transform_arch_frame_list_def] >>
 gvs[arch_exec'_def, AllCaseEqs()] >>
 qexists_tac ‘arch_block'_out’ >>
 CONJ_TAC >- (
  gvs[transform_astate_def, transform_aenv_def, transform_actx_def] >>
  ‘EL aenv'10 ab_list = arch_block_out ==>
   transform_ab_list dict ab_list = SOME ab_list' ==>
   oEL aenv'10 ab_list' = SOME arch_block'_out’ by cheat >>
  metis_tac[]
 ) >>
 gs[] >>
 PairCases_on ‘s'2’ >>
 qexists_tac ‘(s'22,(s'23,s'24,s'25,s'26))’ >>
 CONJ_TAC >- (
  PairCases_on ‘scope'’ >>
  gvs[transform_astate_def, transform_aenv_def, transform_actx_def, transform_ascope_def] >>
  (* TODO: Some stuff still missing here for stating output lemma... *)
  (* TODO: Output functions have to be specialised in the theorem *)
  cheat
 ) >>
 qexistsl_tac [‘s'22’, ‘(s'23,s'24,s'25,s'26)’] >>
 gvs[transform_astate_def, transform_status_def, transform_aenv_def]
) >- (
 (* Exit from pblock *)
 cheat
) >- (
 (* Regular execution *)
 cheat
) >- (
 (* Exit from pblock via return *)
 cheat
) >- (
 (* Finish block via transition to accept *)
 cheat
) >>
(* Transition *)
cheat
QED

(* TODO: Copy-paste of p4_contract'_def from p4_symb_execScript.sml *)
Definition p4_contract_def:
 p4_contract P ctx Q <=>
  !s.
   P s ==>
   ?n. arch_multi_exec ctx s n <> NONE /\
       !s'. arch_multi_exec ctx s n = SOME s' ==> Q s'
End

Definition p4_contract'_def:
 p4_contract' P ctx Q <=>
  !s.
   P s ==>
   ?n. arch_multi_exec' ctx s n <> NONE /\
       !s'. arch_multi_exec' ctx s n = SOME s' ==> Q s'
End

(* TODO: Translating total-correctness contract requires completeness... *)
(* TODO: Formulate new version of arch_multi_exec using uninit_zero that can be used by
 * symbolic execution *)
Theorem arch_multi_exec'_completeness:
!dict ab_list pblock_map ffblock_map input_f output_f copyin_pbl copyout_pbl apply_table_f ext_map func_map ab_list' pblock_map' ffblock_map' input_f' output_f' copyin_pbl' copyout_pbl' apply_table_f' ext_map' func_map' ctrl s1 s2 s'1 s'2 n.
dict_bij dict ==>
transform_actx dict (ab_list,pblock_map,ffblock_map,input_f,output_f,copyin_pbl,
                     copyout_pbl,apply_table_f,ext_map,func_map) = SOME (ab_list',pblock_map',ext_map',func_map') ==>
(* TODO: Need to state and assume completeness of the following:
ffblock_map'
input_f'
output_f'
copyin_pbl'
copyout_pbl'
apply_table_f'
*)
transform_astate dict s1 ctrl = SOME s'1 ==>
arch_multi_exec (ab_list,pblock_map,ffblock_map,input_f,output_f,
                 copyin_pbl,copyout_pbl,apply_table_f,ext_map,func_map) s1 n = SOME s2 ==>
transform_astate dict s2 ctrl = SOME s'2 ==>
arch_multi_exec' (ab_list',pblock_map',ffblock_map',input_f',output_f',
                  copyin_pbl',copyout_pbl',apply_table_f',ext_map',func_map') s'1 n = SOME s'2
Proof
rpt strip_tac >>
cheat
QED

Theorem cake_sem_contract:
!dict ab_list pblock_map ffblock_map input_f output_f copyin_pbl copyout_pbl apply_table_f ext_map func_map ab_list' pblock_map' ffblock_map' input_f' output_f' copyin_pbl' copyout_pbl' apply_table_f' ext_map' func_map' ctrl P' P Q Q'.
dict_bij dict ==>
(* TODO: Need to state and assume completeness of the following:
ffblock_map'
input_f'
output_f'
copyin_pbl'
copyout_pbl'
apply_table_f'
*)
transform_actx dict (ab_list,pblock_map,ffblock_map,input_f,output_f,copyin_pbl,
                     copyout_pbl,apply_table_f,ext_map,func_map) = SOME (ab_list',pblock_map',ext_map',func_map') ==>
(* Note this has to be computed *)
(!s s'. transform_astate dict s ctrl = SOME s' ==>
     (P' s' ==> P s) /\ (Q s ==> Q' s')) ==>
p4_contract P (ab_list,pblock_map,ffblock_map,input_f,output_f,copyin_pbl,
               copyout_pbl,apply_table_f,ext_map,func_map) Q ==>
               
p4_contract' P' (ab_list',pblock_map',ffblock_map',input_f',output_f',copyin_pbl',copyout_pbl',apply_table_f',ext_map',func_map') Q'
Proof
gvs[p4_contract_def] >>
rpt strip_tac >>
gs[p4_contract'_def] >>
rpt strip_tac >>
rename1 ‘P' s'’ >>
(* TODO: In order for this to be provable, the contracts need to also include a notion of
 * "valid state" in both precondition and postcondition, which entails the astates can always be
 * translated using some dictionary (computed from the individual program).
 *
 * valid_astate dict s
 *
 * Look into what the causes of NONE may be in transform_astate, if it's only dictionary lookup
 * or something else. This has some similarity to the prerequisites of the BIR lifting *)
(* TODO: Note that the current transform_astate definition would only allow to prove this for
 * states with empty arch frame lists (arch_frame_list'_empty), but that's probably OK. *)
‘?s. transform_astate dict s ctrl = SOME s'’ by cheat >>
‘(P' s' ⇒ P s) ∧ (Q s ⇒ Q' s')’ by metis_tac[] >>
‘P s’ by metis_tac[] >>
‘?n. arch_multi_exec
                  (ab_list,pblock_map,ffblock_map,input_f,output_f,
                   copyin_pbl,copyout_pbl,apply_table_f,ext_map,func_map) s n ≠
                NONE ∧
                ∀s'.
                  arch_multi_exec
                    (ab_list,pblock_map,ffblock_map,input_f,output_f,
                     copyin_pbl,copyout_pbl,apply_table_f,ext_map,func_map) s
                    n =
                  SOME s' ⇒
                  Q s'’ by metis_tac[] >>
‘?s2. arch_multi_exec
            (ab_list,pblock_map,ffblock_map,input_f,output_f,copyin_pbl,
             copyout_pbl,apply_table_f,ext_map,func_map) s n = SOME s2’ by (
 Cases_on ‘arch_multi_exec
           (ab_list,pblock_map,ffblock_map,input_f,output_f,copyin_pbl,
            copyout_pbl,apply_table_f,ext_map,func_map) s n’ >> (gs[])
) >>
‘Q s2’ by metis_tac[] >>
qexists_tac ‘n’ >>
gs[] >>
(* TODO: By "valid_state" *)
‘?s'2. transform_astate dict s2 ctrl = SOME s'2’ by cheat >>
‘!output_f' input_f' ffblock_map' copyout_pbl' copyin_pbl'
     apply_table_f'.
   arch_multi_exec'
     (ab_list',pblock_map',ffblock_map',input_f',output_f',
      copyin_pbl',copyout_pbl',apply_table_f',ext_map',func_map') s' n =
   SOME s'2’ by metis_tac[arch_multi_exec'_completeness] >>
gvs[] >>
metis_tac[]
QED

val _ = export_theory ();
