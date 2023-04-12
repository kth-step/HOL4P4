open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_aux";

open listTheory rich_listTheory;

open p4Theory;

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
  (v_to_tau (v_err errmsg) = SOME tau_err) /\
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

val _ = export_theory ();
