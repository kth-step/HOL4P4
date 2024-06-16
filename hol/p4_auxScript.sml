open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_aux";

open listTheory rich_listTheory;
open pairTheory optionTheory arithmeticTheory;
open p4Theory;

(* OPTION_BIND as infix *)
Definition app_opt_def:
 $>>= x_opt f =
  OPTION_BIND x_opt f
End
val _ = set_fixity ">>=" (Infixl 801);

Theorem SUC_ADD_ONE:
!n. SUC n = n + 1
Proof
fs[]
QED

val oCONS_def = Define `
 (oCONS (h, SOME t) =
  SOME (h::t)
 ) /\
 (oCONS (_, NONE) =
  NONE
 )
`;

val oLASTN_def = Define `
 (oLASTN n l =
  case oTAKE n (REVERSE l) of
  | SOME l' => SOME (REVERSE l')
  | NONE => NONE)
`;

Theorem oTAKE_imp_TAKE:
!i l l'.
oTAKE i l = SOME l' ==>
TAKE i l = l'
Proof
Induct_on `i` >> (
 fs [oTAKE_def]
) >>
rpt strip_tac >>
Cases_on `l` >> (
 fs [oTAKE_def, TAKE_def]
) >>
Cases_on `oTAKE i t` >> (
 fs []
) >>
metis_tac []
QED

Theorem oLASTN_imp_LASTN:
!i l l'.
oLASTN i l = SOME l' ==>
LASTN i l = l'
Proof
rpt strip_tac >>
fs [LASTN_def, oLASTN_def] >>
Cases_on `oTAKE i (REVERSE l)` >> (
 fs []
) >>
metis_tac [oTAKE_imp_TAKE]
QED

Theorem oTAKE_SOME:
!i l l'.
i > 0 ==>
oTAKE i l = SOME l' ==>
l <> []
Proof
Cases_on `i` >> (
 fs [oTAKE_def]
)
QED

Theorem oDROP_DROP:
!l n.
n <= LENGTH l ==>
oDROP n l = SOME (DROP n l)
Proof
Induct >> (
 fs[oDROP_def]
) >>
rpt strip_tac >>
Cases_on ‘n’ >> (
 fs[oDROP_def]
)
QED

Theorem oTAKE_TAKE:
!l n.
n <= LENGTH l ==>
oTAKE n l = SOME (TAKE n l)
Proof
Induct >> (
 fs[oTAKE_def]
) >>
rpt strip_tac >>
Cases_on ‘n’ >> (
 fs[oTAKE_def]
)
QED

Theorem oDROP_APPEND:
!l1 l2.
oDROP (LENGTH l1) (l1 ++ l2) = SOME l2
Proof
rpt strip_tac >>
subgoal ‘oDROP (LENGTH l1) (l1 ++ l2) = SOME (DROP (LENGTH l1) (l1 ++ l2))’ >- (
 fs[oDROP_DROP]
) >>
fs[rich_listTheory.DROP_LENGTH_APPEND]
QED

Theorem oTAKE_APPEND:
!l1 l2.
oTAKE (LENGTH l1) (l1 ++ l2) = SOME l1
Proof
rpt strip_tac >>
subgoal ‘oTAKE (LENGTH l1) (l1 ++ l2) = SOME (TAKE (LENGTH l1) (l1 ++ l2))’ >- (
 fs[oTAKE_TAKE]
) >>
fs[rich_listTheory.TAKE_LENGTH_APPEND]
QED

(* e_size: size of an e
 * e1_size: size of a (string # e) list
 * e2_size: size of a string # e
 * e3_size: size of an e list *)

Theorem EL_pair_list:
!i l.
i < LENGTH l ==>
EL i l = (EL i (MAP FST l), EL i (MAP SND l))
Proof
rpt strip_tac >>
subgoal `?l1 l2. LENGTH l1 = LENGTH l2 /\ l = ZIP (l1,l2)` >- (
 qexists_tac `MAP FST l` >>
 qexists_tac `MAP SND l` >>
 fs [GSYM listTheory.UNZIP_MAP]
) >>
fs [listTheory.MAP_ZIP, listTheory.EL_ZIP]
QED

Theorem e_e2_size_less:
 !x e. e_size e < e2_size (x,e)
Proof
 fs [e_size_def]
QED

Theorem e1_size_append:
 !x_e_l1 x_e_l2. e1_size (x_e_l1 ++ x_e_l2) = (e1_size x_e_l1 + e1_size x_e_l2)
Proof
 Induct_on `x_e_l1` >> (
  fs [e_size_def]
 )
QED

Theorem e3_size_append:
 !e_l1 e_l2. e3_size (e_l1 ++ e_l2) = (e3_size e_l1 + e3_size e_l2)
Proof
 Induct_on `e_l1` >> (
  fs [e_size_def]
 )
QED

Theorem e1_size_mem:
 !x_e x_e_l. MEM x_e x_e_l ==> e2_size x_e < e1_size x_e_l
Proof
 REPEAT STRIP_TAC >>
 fs [listTheory.MEM_SPLIT, e1_size_append, e_size_def]
QED

Theorem e1_tuple_size_mem:
 !x e x_e_l. MEM (x,e) x_e_l ==> e_size e < e1_size x_e_l
Proof
 REPEAT STRIP_TAC >>
 fs [listTheory.MEM_SPLIT, e1_size_append, e_size_def]
QED

Theorem e3_size_mem:
 !e e_l. MEM e e_l ==> e_size e < e3_size e_l
Proof
 REPEAT STRIP_TAC >>
 fs [listTheory.MEM_SPLIT, e3_size_append, e_size_def]
QED

Theorem index_find_length:
 !l i f j e. (INDEX_FIND i f l = SOME (j, e)) ==> (j - i < LENGTH l)
Proof
 Induct_on `l` >> (
  fs [listTheory.INDEX_FIND_def]
 ) >>
 REPEAT STRIP_TAC >>
 fs [] >>
 Cases_on `f h` >> (
  fs []
 ) >>
 Q.PAT_X_ASSUM `!i f j e. _` (ASSUME_TAC o Q.SPECL [`SUC i`, `f`, `j`, `e`]) >>
 rfs []
QED

Theorem index_find_first:
 !l f e i j.
 (INDEX_FIND i f l = SOME (j, e)) ==>
 (f e /\ (!j'. (i <= j' /\ j' < j) ==> ~(f (EL (j' - i) l))))
Proof
 Induct_on `l` >> (
  fs [listTheory.INDEX_FIND_def]
 ) >>
 REPEAT STRIP_TAC >>
 fs [] >>
 Cases_on `f h` >> (
  fs []
 ) >> (
  Q.PAT_X_ASSUM `!f e i j. _` (ASSUME_TAC o Q.SPECL [`f`, `e`, `SUC i`, `j`]) >>
  rfs []
 ) >>
 Q.PAT_X_ASSUM `!j'. _` (ASSUME_TAC o Q.SPEC `j'`) >>
 subgoal `SUC i <= j'` >- (
  Cases_on `i = j'` >- (
   fs []
  ) >>
  fs []
 ) >>
 fs [] >>
 rfs [] >>
 subgoal `j' - i = (SUC (j' - SUC i))` >- (
  fs []
 ) >>
 fs [listTheory.EL_restricted]
QED

Theorem unred_arg_index_in_range:
 !d_l e_l i. unred_arg_index d_l e_l = SOME i ==> i < LENGTH e_l
Proof
 REPEAT STRIP_TAC >>
 fs [unred_arg_index_def, find_unred_arg_def] >>
 Cases_on `INDEX_FIND 0 (\(d,e). ~is_arg_red d e) (ZIP (d_l,e_l))` >> (
  fs []
 ) >>
 Cases_on `x` >>
 IMP_RES_TAC index_find_length >>
 fs []
QED

Theorem unred_mem_index_in_range:
 !e_l i. unred_mem_index e_l = SOME i ==> i < LENGTH e_l
Proof
 REPEAT STRIP_TAC >>
 fs [unred_mem_index_def, unred_mem_def] >>
 Cases_on `INDEX_FIND 0 (\e. ~is_const e) e_l` >> (
  fs []
 ) >>
 Cases_on `x` >>
 IMP_RES_TAC index_find_length >>
 fs []
QED

Theorem ZIP_MAP_FST_SND:
 !l. ZIP (MAP FST l, MAP SND l) = l
Proof
fs [GSYM listTheory.UNZIP_MAP]
QED

Theorem lambda_FST:
!l. MAP (\(a_, b_). a_) l = MAP FST l
Proof
strip_tac >> (
 Induct_on `l` >> (
  fs []
 ) >>
 rpt strip_tac >>
 PairCases_on `h` >>
 fs []
)
QED

Theorem lambda_SND:
!l. MAP (\(a_, b_). b_) l = MAP SND l
Proof
strip_tac >> (
 Induct_on `l` >> (
  fs []
 ) >>
 rpt strip_tac >>
 PairCases_on `h` >>
 fs []
)
QED

Theorem lambda_unzip_tri:
(!l. MAP (\(a_,b_,c_). a_) l = (FST o UNZIP) l) /\
(!l. MAP (\(a_,b_,c_). b_) l = (FST o UNZIP o SND o UNZIP) l) /\
(!l. MAP (\(a_,b_,c_). c_) l = (SND o UNZIP o SND o UNZIP) l)
Proof
REPEAT STRIP_TAC >> (
 Induct_on `l` >> (
  fs []
 ) >>
 REPEAT STRIP_TAC >>
 PairCases_on `h` >>
 fs []
)
QED

Theorem lambda_snd_unzip_tri:
!l. MAP (\(a_,b_,c_). (b_, c_)) l = (SND o UNZIP) l
Proof
Induct_on `l` >> (
 fs []
) >>
REPEAT STRIP_TAC >>
PairCases_on `h` >>
fs []
QED

Theorem lambda_12_unzip_tri:
!l. MAP (\(a_,b_,c_). (a_, b_)) l = ZIP ((FST o UNZIP) l, MAP FST ((SND o UNZIP) l))
Proof
Induct_on `l` >> (
 fs []
) >>
REPEAT STRIP_TAC >>
PairCases_on `h` >>
fs []
QED

Theorem lambda_23_unzip_tri:
!l. MAP (\(a_,b_,c_). (a_, c_)) l = ZIP ((FST o UNZIP) l, MAP SND ((SND o UNZIP) l))
Proof
Induct_on `l` >> (
 fs []
) >>
REPEAT STRIP_TAC >>
PairCases_on `h` >>
fs []
QED

(* TODO: More cases as needed *)
Theorem map_tri_zip12:
!(al:'a list) (bcl:('b # 'c) list).
LENGTH bcl = LENGTH al ==>
(MAP (\(a_,b_,c_). a_) (ZIP (al,bcl)) = al) /\
(MAP (\(a_,b_,c_). b_) (ZIP (al,bcl)) = MAP FST bcl) /\
(MAP (\(a_,b_,c_). c_) (ZIP (al,bcl)) = MAP SND bcl) /\
(MAP (\(a_,b_,c_). (a_, b_)) (ZIP (al,bcl)) = ZIP (al, MAP FST bcl)) /\
(MAP (\(a_,b_,c_). (a_, c_)) (ZIP (al,bcl)) = ZIP (al, MAP SND bcl)) /\
(MAP (\(a_,b_,c_). (b_, c_)) (ZIP (al,bcl)) = bcl)
Proof
REPEAT STRIP_TAC >> (
 fs [lambda_unzip_tri, lambda_12_unzip_tri, lambda_23_unzip_tri, lambda_snd_unzip_tri, UNZIP_MAP]
)
QED

Theorem lambda_unzip_quad:
(!l. MAP (\(a,b,c,d). a) l = (FST o UNZIP) l) /\
(!l. MAP (\(a,b,c,d). b) l = (FST o UNZIP o SND o UNZIP) l) /\
(!l. MAP (\(a,b,c,d). c) l = (FST o UNZIP o SND o UNZIP o SND o UNZIP) l) /\
(!l. MAP (\(a,b,c,d). d) l = (SND o UNZIP o SND o UNZIP o SND o UNZIP) l)
Proof
REPEAT STRIP_TAC >> (
 Induct_on `l` >> (
  fs []
 ) >>
 REPEAT STRIP_TAC >>
 PairCases_on `h` >>
 fs []
)
QED

Theorem lambda_snd_snd_unzip_quad:
!l. MAP (\(a,b,c,d). (c,d)) l = (SND o UNZIP o SND o UNZIP) l
Proof
Induct_on `l` >> (
 fs []
) >>
REPEAT STRIP_TAC >>
PairCases_on `h` >>
fs []
QED

Theorem map_quad_zip112:
!(al:'a list) (bl:'b list) (cdl:('c # 'd) list).
LENGTH al = LENGTH (ZIP (bl,cdl)) ==>
LENGTH bl = LENGTH cdl ==>
(MAP (\(a_,b_,c_,d_). a_) (ZIP (al, ZIP (bl,cdl))) = al) /\
(MAP (\(a_,b_,c_,d_). b_) (ZIP (al, ZIP (bl,cdl))) = bl) /\
(MAP (\(a_,b_,c_,d_). c_) (ZIP (al, ZIP (bl,cdl))) = MAP FST cdl) /\
(MAP (\(a_,b_,c_,d_). d_) (ZIP (al, ZIP (bl,cdl))) = MAP SND cdl) /\
(MAP (\(a_,b_,c_,d_). (c_, d_)) (ZIP (al, ZIP (bl,cdl))) = cdl)
Proof
REPEAT STRIP_TAC >> (
 fs [lambda_unzip_quad, lambda_snd_snd_unzip_quad, UNZIP_MAP, MAP_ZIP]
)
QED

Theorem INDEX_FIND_NONE_EXISTS:
!l i P.
INDEX_FIND i P l = NONE <=> ~(EXISTS P l)
Proof
Induct_on `l` >> (
 fs [INDEX_FIND_def]
) >>
REPEAT STRIP_TAC >>
Cases_on `P h` >> (
 fs []
)
QED

Theorem INDEX_FIND_SOME_EXISTS:
!l i P.
IS_SOME $ INDEX_FIND i P l <=> (EXISTS P l)
Proof
rpt strip_tac >>
eq_tac >> (
 strip_tac >>
 CCONTR_TAC
) >- (
 imp_res_tac (GSYM INDEX_FIND_NONE_EXISTS) >>
 fs[]
) >>
FULL_SIMP_TAC std_ss [INDEX_FIND_NONE_EXISTS]
QED

Theorem INDEX_FIND_NONE_EVERY:
!l P.
(INDEX_FIND 0 (\x. ~P x) l = NONE) ==>
EVERY (\x. P x) l
Proof
Induct_on `l` >> (
 fs []
) >>
REPEAT STRIP_TAC >| [
 fs [INDEX_FIND_def] >>
 Cases_on `~P h` >> (
  fs []
 ),

 fs [INDEX_FIND_NONE_EXISTS]
]
QED

Theorem unred_arg_index_NONE:
!dl el.
(unred_arg_index dl el = NONE) ==>
check_args_red dl el
Proof
fs [unred_arg_index_def, find_unred_arg_def, ZIP_def, INDEX_FIND_def, check_args_red_def] >>
REPEAT STRIP_TAC >>
Cases_on `INDEX_FIND 0 (\(d,e). ~is_arg_red d e) (ZIP (dl,el))` >> (
 fs []
) >| [
 ASSUME_TAC (ISPECL [``(ZIP (dl,el)):(d # e) list``, ``UNCURRY is_arg_red``] INDEX_FIND_NONE_EVERY) >>
 fs [pairTheory.ELIM_UNCURRY],

 Cases_on `x` >>
 fs []
]
QED

Theorem unred_mem_index_NONE:
!el.
(unred_mem_index el = NONE) ==>
is_consts el
Proof
fs [unred_mem_index_def, unred_mem_def, is_consts_def, ZIP_def, INDEX_FIND_def] >>
rpt strip_tac >>
Cases_on `INDEX_FIND 0 (\e. ~is_const e) el` >> (
 fs []
) >| [
 ASSUME_TAC (ISPECL [``el:e list``, ``($~ o (\e. ~is_const e))``] INDEX_FIND_NONE_EVERY) >>
 fs [combinTheory.o_ABS_R],

 Cases_on `x` >>
 fs []
]
QED

Theorem is_v_is_const:
!e. is_v e = is_const e
Proof
strip_tac >>
Cases_on ‘e’ >> (
 fs[is_v, is_const_def]
)
QED

(* TODO: Merge with the above? *)
Theorem EVERY_is_v_unred_mem_index:
!e_l.
EVERY is_v e_l ==>
unred_mem_index e_l = NONE
Proof
rpt strip_tac >>
CCONTR_TAC >>
fs[GSYM quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE, optionTheory.IS_SOME_EXISTS] >>
imp_res_tac unred_mem_not_const >>
fs[is_consts_def] >>
FULL_SIMP_TAC pure_ss [EVERY_NOT_EXISTS] >>
fs[is_v_is_const] >>
metis_tac[EVERY_NOT_EXISTS]
QED

Theorem not_EVERY_is_v_unred_mem_index:
!e_l.
~EVERY is_v e_l ==>
?i. unred_mem_index e_l = SOME i
Proof
rpt strip_tac >>
fs [unred_mem_index_def, unred_mem_def, is_consts_def, ZIP_def, INDEX_FIND_def] >>
Cases_on ‘INDEX_FIND 0 (\e. ~is_const e) e_l’ >> (
 fs[]
) >- (
 imp_res_tac INDEX_FIND_NONE_EVERY >>
 fs[GSYM is_v_is_const] >>
 metis_tac[EVERY_NOT_EXISTS]
) >>
PairCases_on ‘x’ >>
fs[]
QED

(* TODO: Bake this into the definition instead? *)
Theorem unred_arg_index_empty:
!dl.
(unred_arg_index dl [] = NONE)
Proof
fs [unred_arg_index_def, find_unred_arg_def, ZIP_def, INDEX_FIND_def]
QED

Theorem unred_arg_index_max:
!dl el i.
(unred_arg_index dl el = SOME i) ==> i < (LENGTH el)
Proof
fs [unred_arg_index_def, find_unred_arg_def, ZIP_def, INDEX_FIND_def] >>
REPEAT STRIP_TAC >>
Cases_on `INDEX_FIND 0 (\(d,e). ~is_arg_red d e) (ZIP (dl,el))` >> (
 fs []
) >>
Cases_on `x` >>
fs [] >>
IMP_RES_TAC index_find_length >>
fs [LENGTH_ZIP_MIN]
QED

Theorem index_not_const_NONE:
!el.
index_not_const el = NONE ==>
is_consts el
Proof
rpt strip_tac >>
fs [index_not_const_def, is_consts_def] >>
Cases_on `INDEX_FIND 0 (\e. ~is_const e) el` >> (
 fs []
) >| [
 IMP_RES_TAC INDEX_FIND_NONE_EVERY >>
 fs [combinTheory.o_ABS_R],

 Cases_on `x` >>
 fs []
]
QED

Theorem vl_of_el_LENGTH:
!el.
LENGTH (vl_of_el el) = LENGTH el
Proof
fs [vl_of_el_def]
QED

Theorem initialise_LENGTH:
!ss varn v ss'.
initialise ss varn v = ss' ==>
LENGTH ss = LENGTH ss'
Proof
fs [initialise_def] >>
rw []
QED


Theorem lemma_v_red_forall:
! c s sl e l fl.
~ e_red c s sl (e_v (l)) e fl
Proof
RW_TAC (srw_ss()) [Once e_red_cases]
QED



(*********Mapping equv. lemmas ************)

val MAP_LIST_TAC =  (Induct_on `l` >>
                 Induct_on `l'` >>
                 FULL_SIMP_TAC list_ss [] >>
                 REPEAT STRIP_TAC>>
                 PairCases_on `h` >>
                 PairCases_on `h'` >>
                 REV_FULL_SIMP_TAC list_ss []);
                  
Theorem lemma_MAP1:
! l l'  .
        (MAP (λ(a,b,d). (b,d)) l = MAP (λ(a,c,b,d). (b,d)) l') ==> 
        ((MAP (λ(a,b,d). d) l) = (MAP (λ(a,c,b,d). d) l')) /\
        ((MAP (λ(a,b,d). b) l) = (MAP (λ(a,c,b,d). b) l'))
Proof
MAP_LIST_TAC
QED


Theorem lemma_MAP2:
! l l' .
        (MAP (λ(a,b,c,d). (c,d)) l = MAP (λ(a,b,c,d). (c,d)) l') ==>
	(MAP (λ(a,b,c,d). d) l = MAP (λ(a,b,c,d). d) l') 
Proof
MAP_LIST_TAC
QED


Theorem lemma_MAP3:
!l l' .
        (MAP (λ(a,b,d). (b,d)) l = MAP (λ(a,b,d). (b,d)) l') ==>
	(MAP (λ(a,b,d). (b)) l = MAP (λ(a,b,d). (b)) l') /\
	(MAP (λ(a,b,d). (d)) l = MAP (λ(a,b,d). (d)) l') 
Proof
MAP_LIST_TAC
QED


Theorem lemma_MAP4:
!l l' .
        ( l =  l') ==>
	(MAP (λ(x,d). (x)) l  = MAP (λ(x,d). (x)) l) /\
	(MAP (λ(x,d). (d)) l' = MAP (λ(x,d). (d)) l') 
Proof
MAP_LIST_TAC
QED


Theorem lemma_MAP5:
!l l' .
    ( MAP (λ(a,b,c). (a,b)) l = MAP (λ(a,b,c). (a,b)) l') ==>
	(MAP (λ(a,b,c). (a)) l = MAP (λ(a,b,c). (a)) l') /\
	(MAP (λ(a,b,c). (b)) l = MAP (λ(a,b,c). (b)) l') 
Proof
MAP_LIST_TAC
QED



Theorem lemma_MAP6:
!l l'. (MAP (λ(a,b,c). a) l = MAP (λ(a,b,c). a) l') /\
       (MAP (λ(a,b,c). b) l = MAP (λ(a,b,c). b) l') /\
       (MAP (λ(a,b,c). c) l = MAP (λ(a,b,c). c) l') ==>
 MAP (λ(a,b,c). (a,c)) l =
        MAP (λ(a,b,c). (a,c)) l' 
Proof        
MAP_LIST_TAC
QED


Theorem lemma_MAP7:
!l l'. MAP (λ(a,b,c). (a,b)) l = MAP (λ(a,b,g). (a,b)) l' ==>
       MAP (λ(a,b,c). (b)) l = MAP (λ(a,b,g). (b)) l' 
Proof        
MAP_LIST_TAC
QED




Theorem lemma_MAP8:

! l l' . MAP (λ(a,b,c). (a,b)) l = MAP (λ(a,b,c,d). (a,b)) l' ==>
       ((MAP (λ(a,b,c). (a)) l = MAP (λ(a,b,c,d). (a)) l') /\
        (MAP (λ(a,b,c). (b)) l = MAP (λ(a,b,c,d). (b)) l')) 
Proof
MAP_LIST_TAC
QED



Theorem MAP_snd_quad_12_1:
!l .  MAP SND (MAP (λ(e_,t_,d_,b_). (t_,d_)) l) =
              (MAP (λ(e_,t_,d_,b_). d_) l)
Proof              
Induct >>
REPEAT STRIP_TAC >>
gvs[] >>
PairCases_on `h` >>
gvs[]
QED

(********* lval and is_const lemmas ************)

val lemma_const_notlval =
prove (``!e. is_const e ==> ~ is_e_lval e``,
Cases_on `e` >>
EVAL_TAC
);

val lemma_lval_notconst =
prove (``!e. is_e_lval e ==> ~ is_const e``,
Cases_on `e` >>
EVAL_TAC
);

val lemma_dir_EQ =
prove (``!d. (¬is_d_out d = is_d_none_in d) /\ (is_d_out d = ¬is_d_none_in d) ``,
Cases_on `d` >>
EVAL_TAC
);



(********* Proving the mono P Q  lemmas ************)

(**************************
P is (is_d_none_in d ∧ ¬is_const e)
Q is ((is_d_none_in d ⇒ is_const e) ∧ (¬is_d_none_in d ⇒ is_e_lval e))
show that P ==> not Q
**************************)

val dir_const_imp1 =
prove(`` ! d e.(is_d_none_in d ∧ ¬is_const e)
	     ==> ~((is_d_none_in d ⇒ is_const e) ∧ (¬is_d_none_in d ⇒ is_e_lval e)) ``,
NTAC 3 STRIP_TAC >>
SIMP_TAC std_ss [] >>
DISJ1_TAC>>
METIS_TAC[]
);


val dir_const_imp2 =
prove(``
(∀y. (λ(d,e). is_d_none_in (d) ∧ ¬is_const (e)) y ⇒
             ($¬ ∘
              (λ(d,e).
                   (is_d_none_in (d) ⇒ is_const (e)) ∧
                   (¬is_d_none_in (d) ⇒ is_e_lval (e)))) y)``,

STRIP_TAC>>
Cases_on `y`>>
FULL_SIMP_TAC std_ss [dir_const_imp1] 
);



val dir_const_imp3 =
prove(`` ! d e. ((is_d_none_in d ⇒ is_const e) ∧ (¬is_d_none_in d ⇒ is_e_lval e))
                     ==> ~(is_d_none_in d ∧ ¬is_const e) ``,
NTAC 3 STRIP_TAC >>
SIMP_TAC std_ss [] >>
METIS_TAC[]
);


val dir_const_imp4 =
prove(``
(∀y. (λ(d,e). ¬is_arg_red d e) y ⇒
             ¬(λ(d,e). is_arg_red d e) y)``,

STRIP_TAC>>
Cases_on `y`>>
FULL_SIMP_TAC std_ss [dir_const_imp1, is_arg_red_def, lemma_dir_EQ]
);


(***************************
Show that
INDEX_FIND 0 P l = SOME x ==> P(x)
****************************)

val index_some1 =
prove(``!l n. ((INDEX_FIND n (λ(d,e). is_d_none_in d ∧ ¬is_const e) l) = SOME x)  ==> 
               (λ(d,e). is_d_none_in d ∧ ¬is_const e) (SND x) ``,
Induct >| [
FULL_SIMP_TAC list_ss [INDEX_FIND_def]
,
REPEAT STRIP_TAC >>
FULL_SIMP_TAC list_ss [INDEX_FIND_def]>>
Cases_on `(λ(d,e). is_d_none_in d ∧ ¬is_const e) h` >>
RW_TAC (list_ss) [] >>
Q.PAT_X_ASSUM `∀n. _`
( STRIP_ASSUME_TAC o (Q.SPECL [`SUC n`])) >>
FULL_SIMP_TAC list_ss [INDEX_FIND_def]>>
RW_TAC (list_ss) [] 
]
);


(***************************
Show that 
(INDEX_FIND n P l = NONE) = ~ EXISTS P l
****************************)

val index_some2 =
prove(``! l n. (( INDEX_FIND n (λ(d,e). is_d_none_in d ∧ ¬is_const e) l) = NONE) =
       ~(EXISTS (λ(d,e). is_d_none_in d ∧ ¬is_const e) l)``,
Induct >|[
FULL_SIMP_TAC list_ss [INDEX_FIND_def]
,
FULL_SIMP_TAC list_ss [INDEX_FIND_def]>>
Cases_on `(λ(d,e). is_d_none_in d ∧ ¬is_const e) h` >|[
FULL_SIMP_TAC list_ss [SND]
,
FULL_SIMP_TAC list_ss [INDEX_FIND_def]
]
]
);


(***************************
Show that for a generic P (Lemma T4)
(INDEX_FIND n P l = NONE) = ~ EXISTS P
****************************)

val index_none_not_exist =
prove(``! l  n P. (( INDEX_FIND n P l) = NONE) = ~(EXISTS (P) l)``,
Induct >|[
FULL_SIMP_TAC list_ss [INDEX_FIND_def]
,
FULL_SIMP_TAC list_ss [INDEX_FIND_def]>>
REPEAT STRIP_TAC >>
Cases_on `P h` >>
FULL_SIMP_TAC list_ss []
]
);


(***************************
Show that (equivelnt to above)
(INDEX_FIND n P l = NONE) = EVERY ~P l
Here just write P and substitute later.
****************************)

Theorem index_none_not_every:
! l P n. (( INDEX_FIND n (P) l) = NONE) = (EVERY ($¬ ∘ P) l)
Proof
FULL_SIMP_TAC list_ss [NOT_EXISTS, index_none_not_exist]
QED



(***************************
WE CANT SHOW THIS:
! l P n. (( INDEX_FIND n P l) = NONE) = ~(( INDEX_FIND n P l) = SOME x)
BUT WE CAN SHOW
! l P n. (( INDEX_FIND n P l) = NONE) ==> ~(( INDEX_FIND n P l) = SOME x)
Here just write P and substitute later.
****************************)

Theorem index_none_not_some:
! l P n. (( INDEX_FIND n P l) = NONE) ==> ~(( INDEX_FIND n P l) = SOME x)
Proof
FULL_SIMP_TAC (std_ss++optionSimps.OPTION_ss) [NOT_SOME_NONE, option_CLAUSES]
QED


Theorem index_none_not_none:
! l P n. (( INDEX_FIND n P l) = SOME x) ==> ~(( INDEX_FIND n P l) = NONE)
Proof
FULL_SIMP_TAC (std_ss++optionSimps.OPTION_ss) [NOT_SOME_NONE, option_CLAUSES]
QED

(***************************
Show that Lemma T6
(?x . INDEX_FIND n P l = SOME x) = EXISTS P l
Here just write P and substitute later.
****************************)

Theorem not_index_none_exist:
∀ l n P. ~ (INDEX_FIND n P l = NONE) ⇔ EXISTS P l
Proof
REPEAT GEN_TAC >>
ASSUME_TAC index_none_not_exist>>
Q.PAT_X_ASSUM `∀l n P. _`
( STRIP_ASSUME_TAC o (Q.SPECL [`l`, `n`, `P`])) >>
FULL_SIMP_TAC (std_ss) [combinTheory.o_DEF]
QED


Theorem not_index_none_some:
∀ l n P.~ (INDEX_FIND n P l = NONE) = ? x. ( INDEX_FIND n P l) = SOME x
Proof
REPEAT GEN_TAC >>
Cases_on `INDEX_FIND n P l ` >>
FULL_SIMP_TAC (std_ss) [NOT_SOME_NONE,option_CLAUSES ]
QED


Theorem exists_index_some:
!  l P n. (?x .(( INDEX_FIND n P l) = SOME x)) = (EXISTS P l)
Proof
REPEAT GEN_TAC >>
ASSUME_TAC index_none_not_exist>>
Q.PAT_X_ASSUM `∀l n P. _`
( STRIP_ASSUME_TAC o (Q.SPECL [`l`, `n`, `P`])) >>
ASSUME_TAC not_index_none_exist >>
Q.PAT_X_ASSUM `∀l n P. _`
( STRIP_ASSUME_TAC o (Q.SPECL [`l`, `n`, `P`])) >>
ASSUME_TAC not_index_none_some>>
Q.PAT_X_ASSUM `∀l n P. _`
( STRIP_ASSUME_TAC o (Q.SPECL [`l`, `n`, `P`])) >>

FULL_SIMP_TAC (srw_ss()) [not_index_none_some, not_index_none_exist , index_none_not_exist ]
QED





(***************************
Show Lemma T2.1
! PQ . (∀x. P x ⇒ Q x) ⇒ (∃x. FI n P x) ⇒ ∃x. FI n Q x
****************************)


val P_Q_mono1 =
prove (``! P Q l. ((! (x) . (P x ==>  Q x) ) ==>
((EXISTS P l) ==>
(EXISTS Q l)))``,
metis_tac[MONO_EXISTS, EXISTS_MEM]
);


Theorem P_Q_mono2:
! P Q l n. ((!  (y) . (P y ==>  Q y) ) ==>
((? v. INDEX_FIND n P l = SOME v) ==>
(? v. INDEX_FIND n Q l = SOME v)))
Proof
REPEAT STRIP_TAC >>
ASSUME_TAC (ISPECL [``P: (α -> bool)``, ``Q:(α -> bool)``, ``l:(α list)``] P_Q_mono1) >>
(*twice*)
ASSUME_TAC  exists_index_some >>
Q.PAT_X_ASSUM `∀l P n. (∃x. INDEX_FIND n P l = SOME x) ⇔ EXISTS P l`
( STRIP_ASSUME_TAC o (Q.SPECL [`l`, `P`, `n`])) >>

ASSUME_TAC  exists_index_some >>
Q.PAT_X_ASSUM `∀l P n. (∃x. INDEX_FIND n P l = SOME x) ⇔ EXISTS P l`
( STRIP_ASSUME_TAC o (Q.SPECL [`l`, `Q`, `n`])) >>
RES_TAC>>
fs []
QED


(***************************
If a minimum index found, then the arg list is unreduced
****************************)

Theorem lemma_args:
! dl el i. (unred_arg_index dl el = SOME i) ==> ~ check_args_red dl el
Proof
Cases_on `dl`>>
Cases_on `el` >|[

rfs [unred_arg_index_def, check_args_red_def] >>
Cases_on ` find_unred_arg [] []`>>
rfs [find_unred_arg_def, INDEX_FIND_def]
,

rfs [unred_arg_index_def, check_args_red_def] >>
Cases_on ` find_unred_arg [] (h::t)`>>
rfs [find_unred_arg_def, INDEX_FIND_def, ZIP_def]
,

rfs [unred_arg_index_def, check_args_red_def] >>
Cases_on ` find_unred_arg (h::t) []`>>
rfs [find_unred_arg_def, INDEX_FIND_def, ZIP_def]
,

SIMP_TAC (list_ss) [unred_arg_index_def]>>
REWRITE_TAC [check_args_red_def]>>
Cases_on ` find_unred_arg (h::t) (h'::t')`
>|[
REPEAT STRIP_TAC >>
rfs [find_unred_arg_def, INDEX_FIND_def, ZIP_def]
,

rfs [find_unred_arg_def] >>
rfs [INDEX_FIND_def, ZIP_def]>>
Cases_on `¬is_arg_red h h'`>| [
rfs [is_arg_red_def] 
,
STRIP_TAC >>
FULL_SIMP_TAC (list_ss) [] >>

ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:d#e``] P_Q_mono2) >>

Q.PAT_X_ASSUM `∀P Q l n. _`
( STRIP_ASSUME_TAC o (Q.SPECL [
`λ(d,e). ¬is_arg_red d e `,
`($¬ ∘ (λ(d,e). is_arg_red d e))`,
`ZIP (t,t')`,
`1`
])) >>
FULL_SIMP_TAC std_ss [dir_const_imp4] >>

RES_TAC>>
ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:d#e``] exists_index_some) >>

Q.PAT_X_ASSUM `∀l P n. _`
( STRIP_ASSUME_TAC o (Q.SPECL [
`ZIP (t,t') `,
`($¬ ∘ (λ(d,e). is_arg_red d e))`,
`1`
])) >>
fs[]

]]]
QED



(*******list of const and const thms  **************)
val not_exist_every =
prove(``  ! el . ~(EXISTS (\e. ~(is_const e)) el) = (EVERY (\e. is_const e ) el) ``,
STRIP_TAC >>
EQ_TAC >>
REWRITE_TAC[EVERY_NOT_EXISTS]>>
fs[]
);


val lconst_every =
prove(``  ! el . is_consts el = (EVERY (\e. is_const e ) el) ``,
REWRITE_TAC[is_consts_def]>>
fs[not_exist_every]
);



Theorem lconst_const_imp:
!l i.  (index_not_const l = SOME i) ==> ~ is_consts l
Proof
STRIP_TAC>>
FULL_SIMP_TAC std_ss [index_not_const_def, INDEX_FIND_def] >>
Cases_on `INDEX_FIND 0 (λe. ¬is_const e) l ` >>
fs[] >>
STRIP_TAC >>
rw[is_consts_def] >>
ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:e``] exists_index_some) >>

Q.PAT_X_ASSUM `∀l P n. _`
( STRIP_ASSUME_TAC o (Q.SPECL [
`l`,
`(λe. ¬is_const e)`,
`0`
])) >>

rfs[combinTheory.o_DEF]
QED


Theorem unred_mem_not_const:
!l i. unred_mem_index (l) = SOME i ==> ~ is_consts (l)
Proof
NTAC 3 STRIP_TAC>>
FULL_SIMP_TAC std_ss [unred_mem_index_def] >>
Cases_on `unred_mem l` >>
fs[is_consts_def, unred_mem_def] >>
IMP_RES_TAC index_none_not_none >>
FULL_SIMP_TAC (std_ss) [combinTheory.o_DEF] >>
IMP_RES_TAC index_none_not_none >>
IMP_RES_TAC not_index_none_exist
QED


Theorem ured_mem_length:
!l i . (unred_mem_index l = SOME i) ==> i < LENGTH l
Proof
REPEAT STRIP_TAC >>
fs[unred_mem_index_def] >>
Cases_on `unred_mem l`>>
fs[] >>
fs[unred_mem_def] >>
Cases_on `x` >>
IMP_RES_TAC index_find_length >>
fs []
QED


(* Mapping, EL and MEM thms*)
Theorem map_snd_EQ:
!l . MAP (λx. SND x) l = MAP SND l
Proof
Induct >>
RW_TAC list_ss [MAP]
QED

Theorem map_fst_EQ:
!l . MAP (λx. FST x) l = MAP FST l
Proof
Induct >>
RW_TAC list_ss [MAP]
QED

val map_fst_snd_EQ =
prove(``
!l. MAP (λx. FST (SND x)) l = (MAP SND (MAP (λx. (FST x,FST (SND x))) l)) ``,
Induct >>
RW_TAC list_ss [MAP]
);



val mem_el_map1 =
prove(`` ! l i .
MEM (EL i (MAP (λ(f_,e_). e_) l))
               (MAP (λ(f_,e_). e_) l) ==>
MEM (EL i (MAP (λ(f_,e_). e_) l))
               (SND (UNZIP (MAP (λ(f_,e_). (f_,e_)) l)))	``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC list_ss [UNZIP_MAP] >>
FULL_SIMP_TAC list_ss [SND_EQ_EQUIV, SND_PAIR_MAP] >>
fs [ELIM_UNCURRY] >>
FULL_SIMP_TAC list_ss [map_snd_EQ]
);


Theorem mem_el_map2:
! l i .
MEM (EL i (MAP (λ(f_,e_,e'_). e_) l))
               (MAP (λ(f_,e_,e'_). e_) l) ==>
MEM (EL i (MAP (λ(f_,e_,e'_). e_) l))
               (SND (UNZIP (MAP (λ(f_,e_,e'_). (f_,e_)) l)))
Proof               

REPEAT STRIP_TAC >>
FULL_SIMP_TAC list_ss [UNZIP_MAP] >>
FULL_SIMP_TAC list_ss [SND_EQ_EQUIV, SND_PAIR_MAP] >>
fs [ELIM_UNCURRY] >>
FULL_SIMP_TAC list_ss [map_snd_EQ, map_fst_snd_EQ] 
QED







(****** List manipluation theories and lemmas  ******)


(** bitv theories section **)
(* The bitv_binop_innershould return the same width as the input bitstrings *)

Theorem bitv_binop_inner_lemma:
! q q' q'' r r' binop . bitv_binop_inner binop q q' r = SOME (q'',r') ==>
(r = r') 
Proof
REPEAT GEN_TAC >>
SIMP_TAC (srw_ss()) [Once bitv_binop_inner_def] >>
NTAC 128 (IF_CASES_TAC >>
FULL_SIMP_TAC std_ss [])
QED

Theorem bitv_binop_width_lemma:
! bitv bitv' bitv'' binop . bitv_binop binop bitv bitv' = SOME bitv'' ==>
(SND bitv = SND bitv') /\ (SND bitv' = SND bitv'') 
Proof
REPEAT STRIP_TAC >>
Cases_on `bitv` >>
Cases_on `bitv'` >>
Cases_on `bitv''` >>
rfs[bitv_binop_def] >>
IMP_RES_TAC bitv_binop_inner_lemma
QED




Theorem binop_bs_width: 
! bitv bitv' bitv'' op . 
bs_width bitv' = bs_width bitv /\
bitv_binop op bitv bitv' = SOME bitv'' ==>
bs_width bitv = bs_width bitv'' 
Proof
Cases_on `op` >>
REPEAT STRIP_TAC >>
PairCases_on `bitv` >>
PairCases_on `bitv'` >>
PairCases_on `bitv''` >>
rfs[bs_width_def, bitv_binop_inner_def, bitv_bl_binop_def] >>
rfs[bitv_binop_def] >>
IMP_RES_TAC bitv_binop_inner_lemma
QED


Theorem bitv_bl_binop_width:
! bitv bitv' op . 
bs_width bitv' = bs_width bitv /\
 (op = shiftl \/ op = shiftr)==>
bs_width bitv =
        bs_width (bitv_bl_binop op bitv ((λ(bl,n). (v2n bl,n)) bitv')) 
Proof	
Cases_on `bitv` >>
Cases_on `bitv'` >>
rw[] >> gvs[] >>
rfs[bs_width_def, bitv_binop_inner_def, bitv_bl_binop_def] >>
gvs[bitv_binop_def] >>
IMP_RES_TAC bitv_binop_inner_lemma
QED





Theorem bit_range:
! (r:num) .
r > 0 /\
r ≤ 64 ==>
(r = 1 \/ r = 2 \/ r = 3 \/ r = 4 \/ r = 5 \/
r = 6 \/ r = 7 \/ r = 8 \/ r = 9 \/ r = 10 \/
r = 11 \/ r = 12 \/ r = 13 \/ r = 14 \/ r = 15 \/
r = 16 \/ r = 17 \/ r = 18 \/ r = 19 \/ r = 20 \/
r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/
r = 26 \/ r = 27 \/ r = 28 \/ r = 29 \/ r = 30 \/
r = 31 \/ r = 32 \/ r = 33 \/ r = 34 \/ r = 35 \/
r = 36 \/ r = 37 \/ r = 38 \/ r = 39 \/ r = 40 \/
r = 41 \/ r = 42 \/ r = 43 \/ r = 44 \/ r = 45 \/
r = 46 \/ r = 47 \/ r = 48 \/ r = 49 \/ r = 50 \/
r = 51 \/ r = 52 \/ r = 53 \/ r = 54 \/ r = 55 \/
r = 56 \/ r = 57 \/ r = 58 \/ r = 59 \/ r = 60 \/
r = 61 \/ r = 62 \/ r = 63 \/ r = 64 )
Proof
intLib.COOPER_TAC
QED



Theorem bs_width_neg_signed:
 ! r q .
r > 0 /\
r ≤ 64 ==>
r = bs_width (bitv_unop unop_neg_signed (q,r))
Proof
rpt strip_tac >>
IMP_RES_TAC  bit_range >> fs[] >>
gvs[bitv_unop_def, get_word_unop_def, bs_width_def]
QED






Theorem v_typed_bv_op:
! op w bitv bitv' bitv'' b b'.
w ≤ 64 /\ w > 0 /\
is_bv_op (op) /\
bitv_binop op bitv bitv' = SOME bitv'' /\
v_typ (v_bit bitv) (t_tau (tau_bit w)) b /\
v_typ (v_bit bitv') (t_tau (tau_bit w)) b' ==>
v_typ (v_bit bitv'') (t_tau (tau_bit w)) F 
Proof
REPEAT STRIP_TAC >>
FULL_SIMP_TAC (srw_ss()) [Once v_typ_cases] >>
PairCases_on `bitv` >>
PairCases_on `bitv'` >>
PairCases_on `bitv''` >>
rw[] >>
rfs[bs_width_def, bitv_binop_inner_def, bitv_bl_binop_def] >>
rfs[bitv_binop_def] >>
IMP_RES_TAC bitv_binop_inner_lemma 
QED





(** INDEX_FIND theories section **)


(* If the property P holds on one list member in index i, then the index is
   indeed within the range of the list *)
Theorem prop_in_range:
 !l P i f. ( INDEX_FIND 0 P l = SOME (i,f)) ==> (i < LENGTH l) 
Proof
 REPEAT STRIP_TAC >>
 Cases_on `INDEX_FIND 0 P l = SOME (i,f)` >> 
 fs[] >>
 IMP_RES_TAC index_find_length >>
 fs[]
QED



(* P should hold on the member it finds. *)
Theorem P_holds_on_curent:
  !l P i m. INDEX_FIND i P l = SOME m  ==>
  P (SND m) 
Proof
  Induct_on `l` >>
  fs[INDEX_FIND_def] >>
  NTAC 2 GEN_TAC >>
  CASE_TAC >>
  rw[]
QED





(* if a property found in some range, then if we started from a previous
   index i we should find it. *)
Theorem P_hold_on_next:
  !i l P m.  (INDEX_FIND (SUC i) P l = SOME m) =
             (INDEX_FIND i P l = SOME (FST m - 1, SND m) /\ (0 < FST m))
Proof
Induct_on `l` >>
REPEAT STRIP_TAC >>
EQ_TAC >>
fs[INDEX_FIND_def] >>
rw[] >>
fs[] >>
PairCases_on `m` >>
fs[]
QED


(* if a property holds on some index i starting from 0, then it should hold on the
   ith position if starting from 1 *)
Theorem P_implies_next:
    !l P i m. INDEX_FIND 0 P l = SOME (i, m) ==>
              INDEX_FIND 1 P l = SOME (SUC i, m)
Proof
Induct >>
REPEAT STRIP_TAC >>
fs[INDEX_FIND_def] >>
Cases_on `P h` >>
fs[] >>
rw[ADD1] >>
fs[Once INDEX_FIND_add] >> (*my new fav thm*)
PairCases_on `z` >>
rw[] >>
fs[INDEX_FIND_def] 
QED


(* if the property holds on some index, starting from
   0 or 1 th positions, then the result are the same for for both finds *)
Theorem P_current_next_same:
    !l P m n. INDEX_FIND 0 P l = SOME m /\
              INDEX_FIND 1 P l = SOME n ==> SND n = SND m
Proof
Induct >>
REPEAT STRIP_TAC >>
fs[INDEX_FIND_def] >>
Cases_on `P h` >>
fs[] >>
rw[] >>
fs[Once INDEX_FIND_add] >> 
PairCases_on `z` >>
rw[] >>
fs[INDEX_FIND_def]
QED



(* if we find a property to hold on the ith index, and also we try
   to retrive that element using EL, then the reuslt should be the same *)
Theorem  EL_relation_to_INDEX_lesseq:
!l P i m n. INDEX_FIND 0 P l = SOME (i,n) /\ 
            EL i l  = (m) /\
            i <= LENGTH l ==>
            m = n 
Proof

Induct >>
REPEAT STRIP_TAC >>
fs[INDEX_FIND_def] >>
Cases_on `P h` >|[
   fs[Once EL_compute] >>
   rfs[]
   ,
   fs[INDEX_FIND_def] >>
   rw[] >>
   SIMP_TAC arith_ss [Once EL_compute] >>
   CASE_TAC >>
   
   ASSUME_TAC P_hold_on_next >>
   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`0`])) >>
   gvs[GSYM ADD1] >> 
   rw[] >>
   IMP_RES_TAC P_holds_on_curent >>
   IMP_RES_TAC index_find_first >>
   rfs[] >>
   rw[] >>
   fs[numeralTheory.numeral_pre, PRE_SUB1, PRE_SUC_EQ] >>
   fs[Once INDEX_FIND_add] >> 
   PairCases_on `z` >>
   rw[] >>
   fs[INDEX_FIND_def] >>
     rw[] >>
     RES_TAC >>
     fs[] >>
     rw[] 
]
QED




(* same as above, but it holds on strictly less than l *)
Theorem EL_relation_to_INDEX_less:
!l P i m n. INDEX_FIND 0 P l = SOME (i,n) /\
            EL i l  = (m) /\
            i < LENGTH l ==>
            m = n
Proof	    
`!l i. i < LENGTH l ==> i <= LENGTH l ` by FULL_SIMP_TAC arith_ss [] >>
REPEAT STRIP_TAC >>
RES_TAC >>
IMP_RES_TAC EL_relation_to_INDEX_lesseq
QED



(* if P does not hold on any member of list l starting from index 0,
   then P does not hold starting from any index n in the list *)
Theorem P_NONE_hold:
!P l n .  (INDEX_FIND 0 P l = NONE) ==> (INDEX_FIND n P l = NONE) 
Proof
 Induct_on `l` >>
 REPEAT STRIP_TAC >>
 fs[INDEX_FIND_def] >>
 Cases_on `P h` >>
 fs[] >>
 rw[ADD1] >>
 fs[Once INDEX_FIND_add] 
QED



Theorem P_NONE_hold2:
!P l n .  (INDEX_FIND n P l = NONE) ==> (INDEX_FIND 0 P l = NONE) 
Proof
 Induct_on `l` >>
 REPEAT STRIP_TAC >>
 fs[INDEX_FIND_def] >>
 Cases_on `P h` >>
 fs[] >>
 rw[ADD1] >>
 fs[Once INDEX_FIND_add] 
QED




Theorem INDEX_FIND_EL:
∀ l e  P j . 
INDEX_FIND 0 P l = SOME (j,e) ⇒
EL j l = e
Proof

Induct >>
REPEAT STRIP_TAC >>
IMP_RES_TAC index_find_first >> gvs[] >>
gvs[INDEX_FIND_def] >>
Cases_on ‘P h’ >> gvs[] >>
ASSUME_TAC P_hold_on_next >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘0’, ‘l’, ‘P’, ‘(j,e)’])) >>
gvs[ADD1] >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘e’, ‘P’, ‘j-1’])) >>
gvs[EL_CONS, PRE_SUB1]    
QED




val EL_not_prob_on_list = prove ( “
∀ l h P j.
j < LENGTH l + 1 ∧  
(∀j'. j' < j ⇒ ¬P (EL j' (h::l))) ⇒
∀j'. j' < j − 1 ⇒ ¬P (EL j' l) ”, 


REPEAT STRIP_TAC >>
gvs[] >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘j'+1’])) >>
gvs[] >>
Cases_on ‘l’ >>     
gvs[ADD1]>>
gvs[EL_CONS, PRE_SUB1] 
);                         


                

        


Theorem index_find_concat1:
! l1 l2 n P.
INDEX_FIND 0 P l1 = NONE  /\
INDEX_FIND 0 P (l2 ⧺ l1) = SOME n ==>
INDEX_FIND 0 P (l2) = SOME n 
Proof
Induct_on `l1` >>
Induct_on `l2` >>
fs[INDEX_FIND_def] >>
REPEAT STRIP_TAC >>
CASE_TAC >| [
 rfs[]
 ,
 Cases_on `P h'` >| [
  gvs[]
  ,
  gvs[] >>

  ASSUME_TAC P_hold_on_next>> 
  FIRST_X_ASSUM
  (STRIP_ASSUME_TAC o (Q.SPECL [`0`,`(l2 ⧺ h'::l1)`,`P`,`n`])) >>
  gvs[GSYM ADD1] >> 
  RES_TAC >>
  gvs[] >>

  IMP_RES_TAC P_implies_next >>
  Cases_on `n` >>
  fs[]
  ]
 ]
QED




Theorem index_find_concat2:
! l1 l2 a b P.
INDEX_FIND 0 P l2 = NONE  /\
INDEX_FIND 0 P (l2 ++ l1) = SOME a /\
INDEX_FIND 0 P (l1) = SOME b ==>
(SND a = SND b )
Proof
Induct_on `l1` >>
Induct_on `l2` >>
fs[INDEX_FIND_def] >>
REPEAT STRIP_TAC >>

Cases_on `P h` >>
fs[] >>

Cases_on `P h'` >>
fs[] >> gvs[] >>

ASSUME_TAC P_hold_on_next >>
LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`0`])) >>
gvs[GSYM ADD1] >> rw[] >|[

 (*show that if the property holds on some element,
 then if we append it to a lost, we will find it *)

  subgoal `! i l P h'.
    P h' ==>
    INDEX_FIND i P (h'::l) = SOME (i, h')` >-
    fs[INDEX_FIND_def] >>


 Q.PAT_X_ASSUM ` ∀i l P h'. P h' ⇒ INDEX_FIND i P (h'::l) = SOME (i,h') `
 (STRIP_ASSUME_TAC o (Q.SPECL [`0`,`l1`,`P`,`h'`])) >>
 RES_TAC >>

 Cases_on `a` >>
 fs[] >>

 subgoal `(INDEX_FIND 0 P l2 = NONE)` >-  IMP_RES_TAC P_NONE_hold2 >>

 FIRST_X_ASSUM
 (STRIP_ASSUME_TAC o (Q.SPECL [`h'`,`(q-1,r)`,`(0,h')`,`P`])) >>

 gvs[]  

 ,

 (*Inductive case*)
 (*show that if the property holds on some element,
 then if we append it to a lost, we will find it *)

 subgoal `(INDEX_FIND 0 P l2 = NONE)` >- 
 IMP_RES_TAC P_NONE_hold2 >>

 Cases_on `a` >>
 Cases_on `b` >>
 gvs[] >>

 FIRST_X_ASSUM
 (STRIP_ASSUME_TAC o (Q.SPECL [`h'`,`(q-1,r)`,`(q',r')`,`P`])) >>
 gvs[]
 ]
QED








(** EL simplication section **)

Theorem  EL_simp1:
!l i q r t.
 i<LENGTH l /\
(q,r,t) = EL i (MAP (λ(a,b,c). (a,b,c)) l) ==>
(q) = EL i (MAP (λ(a,b,c). (a)) l) 
Proof
Induct >>
REPEAT STRIP_TAC >>
IMP_RES_TAC EL_pair_list >>
rw[] >> fs[ELIM_UNCURRY] >>
EVAL_TAC >> METIS_TAC[]
QED


Theorem  EL_simp2:
!l i q r t.
 i<LENGTH l /\
(q,r,t) = EL i (MAP (λ(a,b,c). (a,b,c)) l) ==>
(r,t) = EL i (MAP (λ(a,b,c). (b,c)) l) 
Proof
REPEAT STRIP_TAC >>
IMP_RES_TAC EL_pair_list >>
rw[] >>
fs[ELIM_UNCURRY] >>
METIS_TAC[]
QED


Theorem  EL_simp3:
!l i q r t.
 i<LENGTH l /\
(q,r,t) = EL i (MAP (λ(a,b,c). (a,b,c)) l) ==>
((r) = EL i (MAP (λ(a,b,c). (b)) l) /\
(t) = EL i (MAP (λ(a,b,c). (c)) l)
)
Proof

REPEAT STRIP_TAC >>
NTAC 2 (
IMP_RES_TAC EL_pair_list >> rw[] >>
IMP_RES_TAC EL_simp1 >>
IMP_RES_TAC EL_simp2) >>
gvs[ELIM_UNCURRY] >>


rfs[EL_pair_list,EL_simp1,EL_simp2] >>
rfs[Once MAP_o] >>
AP_TERM_TAC >>
FULL_SIMP_TAC list_ss [MAP_MAP_o, FST,SND] >>
FULL_SIMP_TAC (std_ss) [combinTheory.o_DEF]
QED


Theorem  EL_simp4:
!l i q r t.
 i<LENGTH l /\
(q,r,t) = EL i (MAP (λ(a,b,c). (a,b,c)) l) ==>
((q) = EL i (MAP (λ(a,b,c). (a)) l) /\
(r) = EL i (MAP (λ(a,b,c). (b)) l) /\
(t) = EL i (MAP (λ(a,b,c). (c)) l)) 
Proof
REPEAT STRIP_TAC >>
IMP_RES_TAC EL_simp1 >>
IMP_RES_TAC EL_simp2 >>
IMP_RES_TAC EL_simp3 
QED



Theorem EL_simp5:
!l i q r .
 i<LENGTH l /\
(q,r) = EL i (MAP (λ(a,b,c). (a,b)) l) ==>
((q) = EL i (MAP (λ(a,b,c). (a)) l) /\
(r) = EL i (MAP (λ(a,b,c). (b)) l) )
Proof
REPEAT STRIP_TAC >>
rfs[EL_pair_list,EL_simp1,EL_simp2] >>
fs[ELIM_UNCURRY] >>
rfs[] >>
rfs[Once MAP_o] >>
EVAL_TAC >>
AP_TERM_TAC >>
FULL_SIMP_TAC list_ss [MAP_MAP_o, FST,SND] >>
FULL_SIMP_TAC (std_ss) [combinTheory.o_DEF] >>
METIS_TAC []
QED


Theorem EL_exists1:
!l i q r .
 i<LENGTH l /\
(q,r) = EL i (MAP (λ(a,b,c). (a,b)) l) ==>
?t . (t) = EL i (MAP (λ(a,b,c). (c)) l) 
Proof
REPEAT STRIP_TAC >>
rfs[EL_pair_list,EL_simp1,EL_simp2] 
QED



Theorem EL_LENGTH_simp:
! l x0 x1 x2 a.
EL (LENGTH l) (MAP (λ(d,x,e). d) l ⧺ [x0]) = x0 ∧
EL (LENGTH l) (MAP (λ(d,x,e). x) l ⧺ [x1]) = x1 ∧
EL (LENGTH l) (MAP (λ(d,x,e). e) l ⧺ [x2]) = x2 ∧
EL (LENGTH l) (l ⧺ [a]) = a 
Proof
Induct_on `l` >>
fs[] 
QED



Theorem P_on_any_EL:
!l i P. i < LENGTH l ==> P (EL i (l)) = EL i (MAP P (l))
Proof
Induct >> fs[] >> REPEAT STRIP_TAC >>
rw[Once EL_compute] >>
fs[EL_CONS] >>
fs[PRE_SUB1] 
QED



Theorem list_length1:
! l1 l2 .
LENGTH l1 = SUC (LENGTH l2) ==>
LENGTH (TL l1) = LENGTH l2  
Proof
Induct_on `l1` >> Induct_on `l2` >> fs[]
QED


(*
Given that we want to find the member that matches with k ,
and given two lists of tuples where the type of the first member
is the same for both lists, then the property should have
the same index for both lists, since we are looking for k in both lists that
are literally the same
*)

Theorem INDEX_FIND_same_list:
! l P i i' x x' v r q'.
INDEX_FIND 0 (λ(k,v). k = q') (MAP (λ(a,b,c). (a,b)) l) =
        SOME (i,x,v) /\
INDEX_FIND 0 (λ(k,v). k = q') (MAP (λ(a,b,c). (a,c)) l) =
        SOME (i',x',r) ==>
	(i = i' /\ r = EL i (MAP (λ(a,b,c). c) l)) 
Proof
Induct >>
REPEAT GEN_TAC >>
fs[INDEX_FIND_def] >>
CASE_TAC  >>
gvs[] >>
STRIP_TAC >|[
  fs[] >>
  FULL_SIMP_TAC list_ss [] >>
  Cases_on `(λ(k,v). k = q') ((λ(a,b,c). (a,c)) h)` >>
  fs[] >>
  fs[ELIM_UNCURRY] >>
  rfs[] 
  ,
  fs[] >>
  FULL_SIMP_TAC list_ss [] >>
  Cases_on `(λ(k,v). k = q') ((λ(a,b,c). (a,c)) h)` >|[
   fs[] >>
   fs[ELIM_UNCURRY]
   ,

   gvs[] >>
   
   ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:('a#γ)``] P_hold_on_next)  >>
   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   				  [`0`, `(MAP (λ(a,b,c). (a,c)) l)`,
				  `(λ(k,v). k = q')`, `(i',x',r)`])) >>
   gvs[GSYM ADD1] >>

   
   ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:('a#'b)``] P_hold_on_next)  >>
   LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
   				  [`0`, `(MAP (λ(a,b,c). (a,b)) l)`,
				  `(λ(k,v). k = q')`, `(i,x,v)`])) >>
   gvs[GSYM ADD1] >>
   RES_TAC >>
   `i=i'` by fs[] >>
   rw[] >>
   fs[Once EL_compute] >>
   CASE_TAC >> gvs[] >| [
   `i=1` by fs[] >> rw[]
   ,
   `i>1` by fs[] >> rw[] >>
   gvs[GSYM EL_compute] >>
  fs[EL_CONS] >>
  fs[PRE_SUB1] >>

  rfs[GSYM EL] >>
  gvs[ADD1]
]]]
QED



(* if the field name q has the type tau, and tau is in the list of the
   feild types in position i, then it is indeed true that the feild name q
   and its type tau can be found in the list (l) at a specific index i *)
Theorem correct_field_index_lemma:
! (l:(string#v#tau)list ) i q r tau .
INDEX_FIND 0 (λ(k,v). k = q) (MAP (λ(a,b,c). (a,b)) l) =
          SOME (i,EL i (MAP (λ(a,b,c). (a,b)) l)) ∧
          correct_field_type (MAP (λ(a,b,c). (a,c)) l) q tau ∧
          (q,r) = EL i (MAP (λ(a,b,c). (a,b)) l) ⇒
          tau = EL i (MAP (λ(a,b,c). c) l)
Proof
REPEAT STRIP_TAC >>
rfs[correct_field_type_def] >>
rfs[tau_in_rec_def] >>
Cases_on `FIND (λ(xm,tm). xm = q) (MAP (λ(a,b,c). (a,c)) l)` >>
fs[FIND_def] >>
PairCases_on `z` >>
rw[] >>
Cases_on `SND (z0,z1,z2)` >>
fs[] >>
rw[] >> 

Cases_on `r' = tau` >>
fs[] >>
rw[] >>
IMP_RES_TAC INDEX_FIND_same_list >>
fs[ELIM_UNCURRY] >>
`INDEX_FIND 0 (λx. FST x = q) (MAP (λx. (FST x,FST (SND x))) l) =
        SOME (i,EL i (MAP (λx. (FST x,FST (SND x))) l)) ==>
INDEX_FIND 0 (λx. FST x = q) (MAP (λx. (FST x,FST (SND x))) l) =
        SOME (i,q,r)
` by METIS_TAC[] >>
RES_TAC >>
IMP_RES_TAC INDEX_FIND_same_list >>
fs[ELIM_UNCURRY]
QED




(* If INDEX_FIND for some property P finds an element v in list l,
   then that element is a member of the list l *)
Theorem index_mem:
!l P n v. INDEX_FIND 0 P l = SOME (n,v) ==> MEM v l
Proof
Induct >>
fs[] >> rw[] >>
fs[INDEX_FIND_def] >>

Cases_on `P h` >>
fs[] >> rw[] >>

ASSUME_TAC P_hold_on_next>>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`0`,`l`,`P`,`(n,v)`])) >>
gvs[GSYM ADD1] >> 
RES_TAC >>
fs[]
QED



Theorem index_find_not_mem:
 ! l P e n. (INDEX_FIND n P l = NONE) /\ P e ==> ~ MEM e l 
Proof

Induct >>
fs[INDEX_FIND_def] >>
REPEAT GEN_TAC >>
CASE_TAC >>
STRIP_TAC >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
[`P`, `e` , `SUC n`])) >>
IMP_RES_TAC P_NONE_hold2 >>
Cases_on `e=h` >>
fs[]
QED



Theorem mem_fst_snd:
!l m. MEM m l ==>
      MEM (SND m) (MAP SND l) /\
      MEM (FST m) (MAP FST l) 
Proof
Induct >>
REPEAT STRIP_TAC >>
fs[]
QED


(** MAP theories and simplifications section **)
(** ZIP & UNZIP theorems **)

Theorem map_distrub:
! l l' l''.
(LENGTH l = LENGTH l' /\
LENGTH l' = LENGTH l'') ==>

(MAP (\(a,b,c). a) (ZIP (l,ZIP (l',l''))) = l /\
MAP (\(a,b,c). b) (ZIP (l,ZIP (l',l''))) = l' /\
MAP (\(a,b,c). c) (ZIP (l,ZIP (l',l''))) = l'' /\
MAP (\(a,b,c). (a,b)) (ZIP (l,ZIP (l',l''))) = ZIP (l,l') /\
MAP (\(a,b,c). (a,c)) (ZIP (l,ZIP (l',l''))) = ZIP (l,l'') 
)

Proof
rw[lambda_unzip_tri] >>
rw[lambda_12_unzip_tri] >>
rw[map_tri_zip12] >>
EVAL_TAC >>
fs[GSYM UNZIP_MAP] >>
fs[MAP_ZIP]
QED



Theorem map_rw1:
!l . (MAP (\(a,b,c). (a,c)) l = ZIP (MAP (\(a,b,c). a) l,MAP (\(a,b,c). c) l)) /\
     (MAP (\(a,b,c). (a,b)) l = ZIP (MAP (\(a,b,c). a) l,MAP (\(a,b,c). b) l)) /\
     (MAP (\(a,b,c). (b,c)) l = ZIP (MAP (\(a,b,c). b) l,MAP (\(a,b,c). c) l)) 
Proof
Induct >>
REPEAT STRIP_TAC >>
fs[GSYM UNZIP_MAP] >>
PairCases_on `h` >>
EVAL_TAC
QED



Theorem map_rw2:
!l . MAP (\(a,b,c,d). (a,b)) l = ZIP (MAP (\(a,b,c,d). a) l, MAP (\(a,b,c,d). b) l) /\
     MAP (\(a,b,c,d). (a,c)) l = ZIP (MAP (λ(a,b,c,d). a) l, MAP (\(a,b,c,d). c) l) /\
     MAP (\(a,b,c,d). (a,d)) l = ZIP (MAP (λ(a,b,c,d). a) l, MAP (\(a,b,c,d). d) l) /\
     MAP (\(a,b,c,d). (b,c)) l = ZIP (MAP (λ(a,b,c,d). b) l, MAP (\(a,b,c,d). c) l) /\
     MAP (\(a,b,c,d). (b,d)) l = ZIP (MAP (λ(a,b,c,d). b) l, MAP (\(a,b,c,d). d) l) /\
     MAP (\(a,b,c,d). (c,d)) l = ZIP (MAP (λ(a,b,c,d). c) l, MAP (\(a,b,c,d). d) l) 
Proof
REPEAT CONJ_TAC >>
Induct >>
REPEAT STRIP_TAC >>
fs[GSYM UNZIP_MAP] >>
PairCases_on `h` >>
EVAL_TAC
QED


Theorem map_rw5_3:
!l . MAP (\(a,b,c,d,e). (a,b,c)) l = ZIP (MAP (\(a,b,c,d,e). a) l, ZIP ( MAP (\(a,b,c,d,e). b) l, MAP (\(a,b,c,d,e). c) l)) /\
     MAP (\(a,b,c,d,e). (b,c,d)) l = ZIP (MAP (\(a,b,c,d,e). b) l, ZIP ( MAP (\(a,b,c,d,e). c) l, MAP (\(a,b,c,d,e). d) l)) /\
     MAP (\(a,b,c,d,e). (c,d,e)) l = ZIP (MAP (\(a,b,c,d,e). c) l, ZIP ( MAP (\(a,b,c,d,e). d) l, MAP (\(a,b,c,d,e). e) l)) 
Proof
REPEAT CONJ_TAC >>
Induct >>
REPEAT STRIP_TAC >>
fs[GSYM UNZIP_MAP] >>
PairCases_on `h` >>
EVAL_TAC
QED

Theorem map_simp_1: 
! l1 l2.
          MAP SND (MAP (λ(e_,tau_,d_,b_). (tau_,d_)) l1 ) =
          MAP SND (MAP (λ(e_,e'_,x_,d_). (x_,d_)) l2) ==>
	  MAP (λ(e_,e'_,x_,d_). d_) l2=
          MAP (λ(e_,tau_,d_,b_). d_) l1
Proof

Induct_on `l1` >>
Induct_on `l2` >>
FULL_SIMP_TAC list_ss [] >>
REPEAT STRIP_TAC>>

PairCases_on `h` >>
PairCases_on `h'` >>
fs[]
QED


Theorem map_simp_2:
! l1 l2.
          l1 = MAP FST (MAP (λ(a,b,c). (b,c)) l2) <=>
	  l1 = MAP (λ(a,b,c). b) l2 
Proof

Induct_on `l1` >>
Induct_on `l2` >>
FULL_SIMP_TAC list_ss [] >>
REPEAT STRIP_TAC>>

PairCases_on `h` >>
fs[]
QED



Theorem map_simp_3: 
! l1 l2.
          l1 = MAP FST (MAP (λ(a,b,c,d). (b,c)) l2) <=>
	  l1 = MAP (λ(a,b,c,d). (b)) l2 
Proof

Induct_on `l1` >>
Induct_on `l2` >>
FULL_SIMP_TAC list_ss [] >>
REPEAT STRIP_TAC>>

PairCases_on `h` >>
fs[]
QED


Theorem map_rw_doub:
!l l'.
(LENGTH l = LENGTH l') ==>
MAP (\(a,b). a)  (ZIP (l,l')) = l /\
MAP (\(a,b). b)  (ZIP (l,l')) = l'
Proof
Induct_on `l` >>
Induct_on `l'` >>
rw[]
QED


Theorem map_rw_quad:
!l l' l''.
(LENGTH l = LENGTH l' /\
LENGTH l' = LENGTH l'') ==>
(MAP (\(a,b,c,d). a) (ZIP (l,ZIP (l',l''))) = l /\
MAP (\(a,b,c,d). b) (ZIP (l,ZIP (l',l''))) = l' /\
MAP (\(a,b,c,d). c) (ZIP (l,ZIP (l',l''))) = FST (UNZIP l'') /\
MAP (\(a,b,c,d). d) (ZIP (l,ZIP (l',l''))) = SND (UNZIP l'') /\
MAP (\(a,b,c,d). (a,b)) (ZIP (l,ZIP (l',l''))) = ZIP (l,l')  /\
MAP (\(a,b,c,d). (a,c)) (ZIP (l,ZIP (l',l''))) = ZIP (l, FST (UNZIP l'') ) /\
MAP (\(a,b,c,d). (b,c)) (ZIP (l,ZIP (l',l''))) = ZIP (l', FST (UNZIP l'') ) /\
MAP (\(a,b,c,d). (a,b,c)) (ZIP (l,ZIP (l',l''))) = ZIP (l, ZIP ( l' , FST (UNZIP l'') ) )
)
Proof
Induct_on `l` >>
Induct_on `l'` >>
Induct_on `l''` >>
rw[lambda_unzip_quad] >>
fs[ELIM_UNCURRY]
QED


Theorem map_distrub_penta:
! l1 l2 l3 l4 l5.
(LENGTH l1 = LENGTH l2 /\
LENGTH l2 = LENGTH l3 /\
LENGTH l3 = LENGTH l4 /\
LENGTH l4 = LENGTH l5) ==>
((MAP (λ(a,b,c,d,e). a) (ZIP (l1,ZIP (l2,ZIP (l3,ZIP (l4,l5)))))) = l1 /\
 (MAP (λ(a,b,c,d,e). b) (ZIP (l1,ZIP (l2,ZIP (l3,ZIP (l4,l5)))))) = l2 /\
 (MAP (λ(a,b,c,d,e). c) (ZIP (l1,ZIP (l2,ZIP (l3,ZIP (l4,l5)))))) = l3 /\
 (MAP (λ(a,b,c,d,e). d) (ZIP (l1,ZIP (l2,ZIP (l3,ZIP (l4,l5)))))) = l4 /\
 (MAP (λ(a,b,c,d,e). e) (ZIP (l1,ZIP (l2,ZIP (l3,ZIP (l4,l5)))))) = l5 ∧
 (MAP (λ(a,b,c,d,e). (b,c,d)) (ZIP (l1,ZIP (l2,ZIP (l3,ZIP (l4,l5)))))) = ZIP(l2,ZIP(l3,l4))    
) 
Proof
Induct_on `l1` >>
Induct_on `l2` >>
Induct_on `l3` >>
Induct_on `l4` >>
Induct_on `l5` >>

REPEAT STRIP_TAC >>
gvs[]
QED



Theorem ZIP_tri_id1:
(∀l . l = ZIP (MAP (λx. FST x) l, ZIP (MAP (λx. FST (SND x)) l,MAP (λx. SND (SND x)) l)))
Proof          
Induct >>
gvs[] 
QED


Theorem ZIP_tri_id2:        
∀l.  l = ZIP (MAP (λ(a,b,c). a) l, ZIP (MAP (λ(a,b,c). b) l,MAP (λ(a,b,c). c) l))
Proof          
Induct >>
gvs[] >>
REPEAT STRIP_TAC >>
PairCases_on ‘h’ >> gvs[]
QED



Theorem ZIP_tri_sep_ind:
∀ l al bl cl a b c .
LENGTH al = LENGTH bl ∧ LENGTH bl = LENGTH cl ∧  
(a,b,c)::l =  (ZIP (al,ZIP (bl,cl))) ⇒
(a::MAP (λ(al_,bl_,cl_). al_) l) = al ∧
(b::MAP (λ(al_,bl_,cl_). bl_) l) = bl ∧
(c::MAP (λ(al_,bl_,cl_). cl_) l) = cl 
Proof
Induct_on ‘al’ >>
Induct_on ‘bl’ >>
Induct_on ‘cl’ >>
REPEAT STRIP_TAC >>
gvs[] >>
gvs[map_distrub]
QED







Theorem mem_triple_map_fst:
! l a b c . MEM (a,b,c) l ==> MEM a (MAP FST l)
Proof
Induct_on `l` >>
fs[] >>
REPEAT STRIP_TAC >| [
PairCases_on `h` >>
fs[]
,
RES_TAC >>
fs[]
]
QED



Theorem UNZIP_rw:
 !l l'.
(FST (UNZIP (MAP (\(a,b,c). (a,b)) l)) = MAP (\(a,b,c). (a)) l) /\
(FST (UNZIP (MAP (\(a,b,c). (b,c)) l)) = MAP (\(a,b,c). (b)) l) /\
(FST (UNZIP (MAP (\(a,b,c). (a,c)) l)) = MAP (\(a,b,c). (a)) l) /\
(SND (UNZIP (MAP (\(a,b,c). (a,b)) l)) = MAP (\(a,b,c). (b)) l) /\
(SND (UNZIP (MAP (\(a,b,c). (b,c)) l)) = MAP (\(a,b,c). (c)) l) /\
(SND (UNZIP (MAP (\(a,b,c). (a,c)) l)) = MAP (\(a,b,c). (c)) l) /\


(FST (UNZIP (MAP (\(a,b,c,d). (a,b)) l')) = MAP (\(a,b,c,d). (a)) l') /\
(FST (UNZIP (MAP (\(a,b,c,d). (a,c)) l')) = MAP (\(a,b,c,d). (a)) l') /\
(FST (UNZIP (MAP (\(a,b,c,d). (a,d)) l')) = MAP (\(a,b,c,d). (a)) l') /\
(FST (UNZIP (MAP (\(a,b,c,d). (b,c)) l')) = MAP (\(a,b,c,d). (b)) l') /\
(FST (UNZIP (MAP (\(a,b,c,d). (b,d)) l')) = MAP (\(a,b,c,d). (b)) l') /\
(FST (UNZIP (MAP (\(a,b,c,d). (c,d)) l')) = MAP (\(a,b,c,d). (c)) l') /\

(SND (UNZIP (MAP (\(a,b,c,d). (a,b)) l')) = MAP (\(a,b,c,d). (b)) l') /\
(SND (UNZIP (MAP (\(a,b,c,d). (a,c)) l')) = MAP (\(a,b,c,d). (c)) l') /\
(SND (UNZIP (MAP (\(a,b,c,d). (a,d)) l')) = MAP (\(a,b,c,d). (d)) l') /\
(SND (UNZIP (MAP (\(a,b,c,d). (b,c)) l')) = MAP (\(a,b,c,d). (c)) l') /\
(SND (UNZIP (MAP (\(a,b,c,d). (b,d)) l')) = MAP (\(a,b,c,d). (d)) l') /\
(SND (UNZIP (MAP (\(a,b,c,d). (c,d)) l')) = MAP (\(a,b,c,d). (d)) l') 
Proof
Induct_on `l` >>
Induct_on `l'` >>
rw[lambda_unzip_quad] >>
fs[ELIM_UNCURRY]
QED


Theorem zipped_list: 
! (l : ('a # 'b # 'c ) list ) .
 l = (ZIP (MAP (λ(d,x,e). d) l,
      ZIP (MAP (λ(d,x,e). x) l,
            MAP (λ(d,x,e). e) l)))
Proof
Induct >-
fs[] >>
STRIP_TAC >>
PairCases_on `h` >>
fs[]
QED



Theorem EL_ZIP_simp:
! l a x i.
 i < LENGTH (MAP (λ(x,v,t). (x,t)) l) /\
 EL i (MAP (λ(x,v,t). (x,t)) l) = (x,a) ==>
 EL i (MAP (λ(x,v,t). t ) l) = (a) 
Proof

Induct >-
fs[Once EL_compute] >>


REPEAT STRIP_TAC >>
fs[Once EL_compute] >>
Cases_on `i=0` >| [
 PairCases_on `h` >>
 fs[]
 ,

 FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL
 [`a`,`x`, `(i:num)-1`])) >>

 gvs[] >>
 fs[numeralTheory.numeral_pre, PRE_SUB1, PRE_SUC_EQ ,ADD1] >>
 rw[] >>
 Cases_on `i = 1` >>
 fs[] >>

 `~ (i ≤ 1)` by fs[] >>
 gvs[] >>


 subgoal ` EL (i − 1) (HD ((MAP (λ(x,v,t). (x,t)) l))::TL ((MAP (λ(x,v,t). (x,t)) l))) =
           EL (PRE (i − 1)) (TL ((MAP (λ(x,v,t). (x,t)) l)))  ` >- (
   `0 < i - 1` by fs[] >>
    ASSUME_TAC EL_CONS >>
    Q.PAT_X_ASSUM `∀n. 0 < n ⇒ ∀x l. EL n (x::l) = EL (PRE n) l`
    ( STRIP_ASSUME_TAC o (Q.SPECL [`i-1`])) >>
    RES_TAC >>
    fs[EL_CONS] ) >>

 fs[EL_CONS] >>
 fs[PRE_SUB1] >>
 gvs[] >>

 subgoal ` (HD (MAP (λ(x,v,t). (x,t)) l) ::TL (MAP (λ(x,v,t). (x,t)) l) ) =
            (MAP (λ(x,v,t). (x,t)) l) ` >- (
   `0 < i` by fs[] >>
   `0 < LENGTH l` by fs[] >>
   ` ~(0 >= LENGTH l)` by fs[] >>
   `0 ≥ LENGTH l ⇔ l = []` by fs[quantHeuristicsTheory.LIST_LENGTH_0] >>
   ` ~(l = [])` by fs[] >>
   fs[NULL] >>

   ASSUME_TAC NULL_LENGTH >>
   ASSUME_TAC CONS >>
   RES_TAC >>
   FULL_SIMP_TAC list_ss [CONS, NULL_LENGTH, NULL_DEF, NULL_EQ]
   ) >>

 subgoal `0 < (i-1)` >- (
  fs[]
 ) >>
 metis_tac[]
]
QED




Theorem INDEX_FIND_EQ_SOME_0:
!l P j e. (INDEX_FIND 0 P l = SOME (j, e)) <=> (
       (j < LENGTH l) /\
       (EL j l = e) /\ P e /\
       (!j'. j' < j ==> ~(P (EL j' l))))
Proof

Induct >-
gvs[INDEX_FIND_def] >>
REPEAT STRIP_TAC >>
EQ_TAC >> STRIP_TAC >| [
    
 IMP_RES_TAC P_holds_on_curent >> fs[] >>
 IMP_RES_TAC index_find_length >> fs[] >>
 IMP_RES_TAC index_find_first >> fs[] >>
 IMP_RES_TAC INDEX_FIND_EL               
 ,
        
 SIMP_TAC list_ss [INDEX_FIND_def] >>
 CASE_TAC >> gvs[] >| [
          
     SIMP_TAC list_ss [Once EL_compute] >>
     CASE_TAC >> gvs[] >>
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘0’])) >>
     gvs[]
     ,
     
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘P’, ‘j-1’, ‘EL (j-1) l’])) >>
     gvs[] >>
     ‘0 < LENGTH l’ by (Cases_on ‘l’ >>
                        gvs[]>>
                        ‘j=0’ by fs[] >> lfs[] ) >> gvs[] >>
        
     IMP_RES_TAC EL_not_prob_on_list >>
     gvs[] >>
     
     ASSUME_TAC P_hold_on_next >>
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘0’, ‘l’, ‘P’, ‘(j,EL j (h::l))’])) >>
     rfs[ADD1] >>
     
     ‘0<j’ by (Cases_on ‘j’ >> gvs[ADD1]) >> gvs[] >>
     
     Cases_on ‘l’ >>     
     gvs[ADD1]>>
     gvs[EL_CONS, PRE_SUB1]                
]]        
QED



Theorem index_not_const_in_range:
  ∀ el i.
index_not_const el = SOME i ⇒
i < LENGTH el
Proof
REPEAT STRIP_TAC >>
fs[index_not_const_def] >>
Cases_on ‘INDEX_FIND 0 (λe. ¬is_const e) el’ >>
gvs[] >>
PairCases_on ‘x’ >> gvs[] >>
gvs[INDEX_FIND_EQ_SOME_0]
QED



        
Theorem ZIP_EQ_NIL_tri: 
∀ al bl cl.
LENGTH al = LENGTH bl ∧
LENGTH bl = LENGTH cl ∧
ZIP (al,ZIP (bl,cl)) = [] ⇒
al = [] ∧ bl = [] ∧ cl = []
Proof                         
Cases_on ‘al’ >>
Cases_on ‘bl’ >>
Cases_on ‘cl’ >>
gvs[]
QED
                                

Theorem ZIP_LENGTH_tri_1:
∀ al bl cl a b c .
 LENGTH al = LENGTH bl ∧ LENGTH bl = LENGTH cl ∧
 [(a,b,c)] = ZIP (al,ZIP (bl,cl)) ⇒
  LENGTH al = 1
Proof  
Cases_on ‘al’ >>
Cases_on ‘bl’ >>
Cases_on ‘cl’ >>
gvs[] >> 
REPEAT STRIP_TAC >>
IMP_RES_TAC ZIP_EQ_NIL_tri
QED


Theorem ZIP_LENGTH_tri:
∀ al bl cl l .
  LENGTH al = LENGTH bl ∧ LENGTH bl = LENGTH cl ∧
  l = ZIP (al,ZIP (bl,cl)) ⇒
  LENGTH l = LENGTH al ∧
  LENGTH l = LENGTH bl ∧
  LENGTH l = LENGTH cl 
Proof
Cases_on ‘al’ >>
Cases_on ‘bl’ >>
Cases_on ‘cl’ >>
gvs[]
QED



              

Theorem ZIP_HD_tri_1:
∀ al bl cl a b c .
  LENGTH al = LENGTH bl ∧ LENGTH bl = LENGTH cl ∧
 [(a,b,c)] = ZIP (al,ZIP (bl,cl)) ⇒
  HD al = a ∧
  HD bl = b ∧
  HD cl = c
Proof  
Cases_on ‘al’ >>
Cases_on ‘bl’ >>
Cases_on ‘cl’ >>
gvs[] 
QED


Definition v_to_tau_def:
  (v_to_tau (v_bool boolv) = SOME tau_bool) /\
  (v_to_tau (v_bit (bl, n)) = SOME (tau_bit n)) /\
  (v_to_tau (v_struct ((x,v)::t)) =
   OPTION_BIND (v_to_tau (v_struct t))
    (\ res. case res of
            | tau_xtl struct_ty_struct t' =>
             (case v_to_tau v of
              | SOME tau => SOME (tau_xtl struct_ty_struct ((x,tau)::t'))
              | NONE => NONE)
            | _ => NONE)) /\
  (v_to_tau (v_struct []) = SOME (tau_xtl struct_ty_struct [])) /\
  (v_to_tau (v_header boolv ((x,v)::t)) =
   OPTION_BIND (v_to_tau (v_header boolv t))
    (\ res. case res of
            | tau_xtl struct_ty_header t' =>
             (case v_to_tau v of
              | SOME tau => SOME (tau_xtl struct_ty_header ((x,tau)::t'))
              | NONE => NONE)
            | _ => NONE)) /\
  (v_to_tau (v_header boolv []) = SOME (tau_xtl struct_ty_header [])) /\
  (v_to_tau v_bot = SOME tau_bot) /\
  (v_to_tau _ = NONE)
  (* TODO: tau_str? *)
Termination
 WF_REL_TAC `measure v_size` >>
 fs [v_size_def] >>
 REPEAT STRIP_TAC >>
 `v_size v' < v1_size t` suffices_by (
  fs []
 ) >>
 METIS_TAC [v1_size_mem]
End

Definition v_to_tau_list_def:
 (v_to_tau_list [] = SOME []) /\
 (v_to_tau_list ((e_v h)::t) =
  case v_to_tau_list t of
  | SOME taus =>
   (case v_to_tau h of
    | SOME tau => SOME (tau::taus)
    | NONE => NONE)
  | NONE => NONE) /\
 (v_to_tau_list _ = NONE)
End

(* TODO: Hack to eliminate lots of syntax fiddling in p4_testLib *)
Definition ext_map_replace_impl_def:
 (ext_map_replace_impl ext_map ext_name method_name new_impl =
  case ALOOKUP ext_map ext_name of
  | SOME (constructor, methods) =>
   (case ALOOKUP methods method_name of
    | SOME (args, old_impl) =>
     SOME $ AUPDATE ext_map (ext_name, (constructor, AUPDATE methods (method_name, (args, new_impl))))
    | NONE => NONE)
  | NONE => NONE
 )
End

(* Replaces the input list with a single input in a given architectural state *)
Definition p4_replace_input_def:
 p4_replace_input input (astate:'a astate) =
  case astate of
  | (aenv, gscope, afl, status) =>
   (case aenv of
    | (ab_index, inputl, outputl, ascope) => 
     ((ab_index, [input], outputl, ascope), gscope, afl, status))
End

Definition p4_append_input_list_def:
 (p4_append_input_list [] (astate:'a astate) = astate) /\
 (p4_append_input_list (h::t) (astate:'a astate) =
   case astate of
   | (aenv, gscope, afl, status) =>
    p4_append_input_list t
     (case aenv of
      | (ab_index, inputl, outputl, ascope) => 
       ((ab_index, inputl++[h], outputl, ascope), gscope, afl, status)))
End


(* TODO: Hack to eliminate lots of syntax fiddling in p4_testLib *)
Definition ext_map_replace_impl_def:
 (ext_map_replace_impl ext_map ext_name method_name new_impl =
  case ALOOKUP ext_map ext_name of
  | SOME (constructor, methods) =>
   (case ALOOKUP methods method_name of
    | SOME (args, old_impl) =>
     SOME $ AUPDATE ext_map (ext_name, (constructor, AUPDATE methods (method_name, (args, new_impl))))
    | NONE => NONE)
  | NONE => NONE
 )
End

Theorem assign_LENGTH:
!scope_list v lval scope_list'.
assign scope_list v lval = SOME scope_list' ==>
LENGTH scope_list' = LENGTH scope_list
Proof
Induct_on ‘lval’ >> (
 fs[assign_def]
) >| [
 rpt strip_tac >>
 Cases_on ‘find_topmost_map scope_list v’ >> (
  fs[]
 ) >>
 PairCases_on ‘x’ >>
 fs[] >>
 Cases_on ‘lookup_out scope_list v’ >> (
  fs[]
 ) >>
 metis_tac[listTheory.LENGTH_LUPDATE],

 rpt strip_tac >>
 Cases_on ‘lookup_lval scope_list lval’ >> (
  fs[]
 ) >>
 Cases_on ‘x’ >> (
  fs[]
 ) >> (
  Cases_on ‘INDEX_OF s (MAP FST l)’ >> (
   fs[]
  ) >>
  res_tac
 ),

 rpt strip_tac >>
 Cases_on ‘v’ >> (
  fs[]
 ) >>
 Cases_on ‘lookup_lval scope_list lval’ >> (
  fs[]
 ) >>
 Cases_on ‘x’ >> (
  fs[]
 ) >>
 Cases_on ‘assign_to_slice p p' e0 e’ >> (
  fs[]
 ) >>
 res_tac,

 metis_tac[]
]
QED

(*************************)
(* Types with parameters *)

(* This is defined as an extension to "tau" (defined in p4Theory) that also
 * includes type parameters *)
Datatype:
p_tau =
   p_tau_bool   (* Note that the integer width must be a compile-time known value *)
 | p_tau_bit num_exp
 | p_tau_bot
 (* Note that structs can be type-parametrized *)
 | p_tau_xtl struct_ty ((x#p_tau) list)
 (* The string is the name of the extern object *)
 | p_tau_ext string
 (* The string is the name of the programmable block *)
 | p_tau_blk string
 (* The string is the name of the package *)
 | p_tau_pkg string
 (* The string is the name of the type parameter *)
 | p_tau_par string
End

(* TODO: Rewrite the below to use list of p_taus instead of list of string, p_tau tuples? *)
Definition deparameterise_tau_def:
(deparameterise_tau t =
  case t of
  | p_tau_bool => SOME tau_bool
  | p_tau_bit num_exp => SOME (tau_bit num_exp)
  | p_tau_bot => SOME tau_bot
  | p_tau_xtl struct_ty fields =>
   deparameterise_x_taus fields >>= \fields'.
   SOME (tau_xtl struct_ty fields')
  | p_tau_ext ext_name => SOME tau_ext
  | p_tau_blk blk_name => NONE
  | p_tau_pkg pkg_name => NONE
  | p_tau_par param_name => NONE) /\
(deparameterise_x_taus [] = SOME []) /\
(deparameterise_x_taus ((name, p_tau)::t) =
  deparameterise_tau p_tau >>=
  \tau. deparameterise_x_taus t >>=
  \tau_l. SOME ((name, tau)::tau_l))
Termination
WF_REL_TAC `measure ( \ t. case t of | (INL p_tau) => p_tau_size p_tau | (INR p_tau_list) => p_tau1_size p_tau_list)`
End

Definition deparameterise_taus_def:
(deparameterise_taus p_tau_l =
 deparameterise_x_taus (ZIP(REPLICATE (LENGTH p_tau_l) "",p_tau_l)) >>=
 \x_tau_l. SOME (SND $ UNZIP x_tau_l))
End

Definition parameterise_tau_def:
(parameterise_tau t =
  case t of
  | tau_bool => p_tau_bool
  | tau_bit num_exp => (p_tau_bit num_exp)
  | tau_bot => p_tau_bot
  | tau_xtl struct_ty fields =>
   (p_tau_xtl struct_ty (parameterise_x_taus fields))
  | tau_ext => p_tau_ext "") /\
(parameterise_x_taus [] = []) /\
(parameterise_x_taus ((name, tau)::t) = ((name, parameterise_tau tau)::(parameterise_x_taus t)))
Termination
WF_REL_TAC `measure ( \ t. case t of | (INL tau) => tau_size tau | (INR tau_list) => tau1_size tau_list)`
End

Definition parameterise_taus_def:
 parameterise_taus tau_l =
  SND $ UNZIP $ parameterise_x_taus (ZIP(REPLICATE (LENGTH tau_l) "",tau_l))
End

Definition deparameterise_ftymap_entries_def:
 (deparameterise_ftymap_entries [] = SOME []) /\
 (deparameterise_ftymap_entries ((funn, (argtys, ret_ty))::t) =
  case funn of
  | (funn_ext _ _) => deparameterise_ftymap_entries t
  | (funn_inst _) => deparameterise_ftymap_entries t
  | (funn_name _) =>
   (case deparameterise_taus argtys of
    | SOME argtys' =>
     (case deparameterise_tau ret_ty of
      | SOME ret_ty' =>
       (case deparameterise_ftymap_entries t of
	| SOME res =>
	 SOME ((funn, (argtys', ret_ty'))::res)
	| NONE => NONE)
      | NONE => NONE)
    | NONE => NONE)
 )
End

Definition deparameterise_b_ftymap_entries_def:
 (deparameterise_b_ftymap_entries [] = SOME []) /\
 (deparameterise_b_ftymap_entries ((b_name, ftymap)::t) =
  case deparameterise_ftymap_entries ftymap of
  | SOME ftymap' =>
   (case deparameterise_b_ftymap_entries t of
    | SOME res => SOME ((b_name, ftymap')::res)
    | NONE => NONE)
  | NONE => NONE
 )
End


(**************************)
(* For symbolic execution *)

(* Used for path unification *)
Theorem IMP_HYP_CASES:
!A B C.
(A /\ C ==> B) ==>
(~A /\ C ==> B) ==>
C ==> B
Proof
metis_tac[]
QED

val _ = export_theory ();
