open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_aux";

open listTheory;

open p4Theory;

(* e_size: size of an e
 * e1_size: size of a (string # e) list
 * e2_size: size of a string # e
 * e3_size: size of an e list *)

Theorem EL_pair_list:
!i l. EL i l = (EL i (MAP FST l), EL i (MAP SND l))
Proof
cheat
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

(* TODO: More cases as needed *)
Theorem map_tri_zip12:
!(al:'a list) (bcl:('b # 'c) list).
LENGTH bcl = LENGTH al ==>
(MAP (\(a_,b_,c_). a_) (ZIP (al,bcl)) = al) /\
(MAP (\(a_,b_,c_). b_) (ZIP (al,bcl)) = MAP FST bcl) /\
(MAP (\(a_,b_,c_). c_) (ZIP (al,bcl)) = MAP SND bcl) /\
(MAP (\(a_,b_,c_). (b_, c_)) (ZIP (al,bcl)) = bcl)
Proof
REPEAT STRIP_TAC >> (
 fs [lambda_unzip_tri, lambda_snd_unzip_tri, UNZIP_MAP]
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

val _ = export_theory ();
