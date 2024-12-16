open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_exec_sem_e_cakeProg";

open p4Syntax;
open p4Theory;
open p4_auxTheory;
open p4_exec_semTheory;

(* CakeML: *)
open preamble ml_translatorLib ml_translatorTheory ml_progLib basisProgTheory mlmapTheory basisFunctionsLib
     astPP comparisonTheory;

intLib.deprecate_int();
val _ = (max_print_depth := 100);

(* TODO: Backport smarter ctx types, other stuff to exec sem *)

(* cv_compute notes:
(* Ext maps can be the same as the usual ones, but without the ext_fun implementation.
 * These maps now only hold the directions of the arguments, and implicitly the
 * function names. This is to avoid the polymorphic types *)
Type ext_fun_map_v1model = “:((string, ((string # d) list)) alist)”
Type ext_map_v1model = “:((string, ((((string # d) list) option) # ext_fun_map_v1model)) alist)”

(* Same as regular ctx specialised for v1model, but missing the apply function, the pars_map and the
 * tbl_map *)
Type e_ctx_v1model = “:(ext_map_v1model # func_map # b_func_map)”;
*)

(* TODO: Backport this to exec sem *)
Type e_ctx = “:('a ext_map # func_map # b_func_map)”;

Definition e_state_size'_def:
 (e_state_size' ((ctx:'a e_ctx), (g_scope_list:g_scope_list), (scope_list:scope_list), (e:e)) = e_size e)
End

(* TODO: Backport FIND->ALOOKUP to exec sem *)
Definition e_exec_acc'_def:
 (e_exec_acc' (e_acc (e_v (v_struct f_v_list)) f) =
  case ALOOKUP f_v_list f of
  | SOME v => SOME (e_v v)
  | NONE => NONE)
  /\
 (e_exec_acc' (e_acc (e_v (v_header boolv f_v_list)) f) =
  case ALOOKUP f_v_list f of
  | SOME v => SOME (e_v v)
  | NONE => NONE)
  /\
 (e_exec_acc' _ = NONE)
End

Definition vl_of_el'_def:
 (vl_of_el' [] = SOME []) /\
 (vl_of_el' (h::t) =
   case v_of_e h of
    | SOME v =>
     (case vl_of_el' t of
      | SOME v_l => SOME (v::v_l)
      | NONE => NONE)
    | NONE => NONE)
End

(* TODO: These two are probably overkill... *)        
Definition MAP_FST_def:
 (MAP_FST [] = []) /\
 (MAP_FST (h::t) =
  ((FST h)::MAP_FST t))
End
Definition MAP_SND_def:
 (MAP_SND [] = []) /\
 (MAP_SND (h::t) =
  ((SND h)::MAP_SND t))
End
Theorem MAP_FST_EQ:
!l. MAP_FST l = MAP FST l 
Proof
Induct \\ (
 fs[MAP_FST_def]
)
QED
Theorem MAP_SND_EQ:
!l. MAP_SND l = MAP SND l 
Proof
Induct \\ (
 fs[MAP_SND_def]
)
QED

(* TODO: Make this entire thing more efficient... *)
(* TODO: Prpbably overkill to forgo INDEX_FIND here? *)
Definition find_topmost_map'_def:
 (find_topmost_map' ([]:scope list) (x:varn) = NONE) /\
 (find_topmost_map' (h::t) x =
    if IS_SOME $ ALOOKUP h x
    then SOME h
    else find_topmost_map' t x)
End
Definition lookup_map'_def:
  lookup_map' (ss:scope list) (x:varn) =
    case find_topmost_map' ss x of
    | SOME sc => 
      (case ALOOKUP sc x of
       | SOME y => SOME y
       | _ => NONE)
    | _ => NONE
End
Definition lookup_vexp2'_def:
  lookup_vexp2' (ss:scope list) (g_scope_list:scope list) x =
    case lookup_map' (ss++g_scope_list) x of
    | SOME (v, str_opt) => SOME v
    | _ => NONE
End

(* TODO: This function initialises everything to zeroes instead of using ARBs,
 * which are not compatible with CakeML. Use this as a placeholder before you have
 * deep-embedded uninitialised values. *)
Definition init_out_v_cake_def:
  (init_out_v_cake (v_bool boolv) = v_bool F) /\
  (init_out_v_cake (v_bit (bl, n)) = v_bit (extend F n [], n)) /\
  (init_out_v_cake (v_str x) = v_str "") /\
  (init_out_v_cake (v_struct ((x,v)::t)) = v_struct (((x, init_out_v_cake v))::(MAP (\(x',v'). (x', init_out_v_cake v')) t))) /\
  (init_out_v_cake (v_struct []) = v_struct []) /\
  (init_out_v_cake (v_header boolv ((x,v)::t)) =
    v_header F (( (x, init_out_v_cake v) )::(MAP (\(x',v'). (x', init_out_v_cake v')) t))) /\
  (init_out_v_cake (v_header boolv []) = v_header F []) /\
  (init_out_v_cake (v_ext_ref i) = v_ext_ref i) /\
  (init_out_v_cake v_bot = v_bot)
Termination
 WF_REL_TAC `measure v_size` \\
 fs [v_size_def] \\
 REPEAT STRIP_TAC \\
 `v_size v' < v1_size t` suffices_by (
  fs []
 ) \\
 METIS_TAC [v1_size_mem]
End


Definition one_arg_val_for_newscope'_def:
 one_arg_val_for_newscope' d e ss =
  if is_d_out d
  then
   (case get_lval_of_e e of
    | SOME lval =>
     (case lookup_lval' ss lval of
      | SOME v =>
       if is_d_in d
       then SOME (v, SOME lval)
       else SOME (init_out_v_cake v, SOME lval)
      | NONE => NONE)
    | NONE => NONE)
  else
   (case v_of_e e of
    | SOME v => SOME (v, NONE)
    | NONE => NONE)
End

Definition update_arg_for_newscope'_def:
 update_arg_for_newscope' ss f_opt (d, x, e) =
  case f_opt of
  | SOME f =>
   (case one_arg_val_for_newscope' d e ss of
    | SOME (v, lval_opt) => SOME (AUPDATE f (varn_name x, (v, lval_opt)))
    | NONE => NONE)
  | NONE => NONE
End

Definition all_arg_update_for_newscope'_def:
 all_arg_update_for_newscope' xlist dlist elist ss = 
  FOLDL (update_arg_for_newscope' ss) (SOME []) (ZIP (dlist, ZIP(xlist, elist)))
End

Definition copyin'_def:
 copyin' xlist dlist elist gsl ss_curr = 
  all_arg_update_for_newscope' xlist dlist elist (ss_curr++gsl)
End

(**************)
(* ARITHMETIC *)

(** unops and predicates for bitvectors **)
Definition bitv_1comp_def:
 bitv_1comp (v:bool list) = MAP $~ v
End

Definition bitv_2comp_def:
 bitv_2comp (v:bool list) = n2v ((LENGTH v) - v2n v)
End

Definition bitv_unplus_def:
 bitv_unplus (v:bool list) = v
End

(* Translations:
 word_msb to HD
 equality with 0w to "all elements equal F"
 BIT (dimindex(:a)) b to BIT (LENGTH a) b ("is (0-indexed, counting from tail) element a T?")
*)
Definition nzcv'_def:
 nzcv' a b =
  let
   q = v2n a + v2n (bitv_2comp b);
   r = fixwidth (LENGTH a) $ n2v q
  in
   (HD r,
    EVERY (\el. ~el) r,
    BIT (LENGTH a) q \/ (EVERY (\el. ~el) b),
    (HD a <> HD b) /\ (HD r <> HD a))
End

(* Forgoing nzcv': see WORD_LS, WORD_HS, WORD_LO, WORD_HI *)
(* Note these can only be used when length of arguments is the same *)
Definition bitv_ls_def:
 bitv_ls a b = (v2n a <= v2n b)
End
Definition bitv_hs_def:
 bitv_hs a b = (v2n a >= v2n b)
End
Definition bitv_lo_def:
 bitv_lo a b = (v2n a < v2n b)
End
Definition bitv_hi_def:
 bitv_hi a b = (v2n a > v2n b)
End
Definition bitv_eq_def:
 bitv_eq a b = AND_EL (MAP bit_eq (ZIP (a, b)))
End
Definition bitv_neq_def:
 bitv_neq a b = ~bitv_eq a b
End


Definition unop_exec'_def:
 (unop_exec' unop_neg (v_bool b) = SOME (v_bool ~b))
 /\
 (unop_exec' unop_compl (v_bit (bl,n)) = SOME (v_bit (bitv_1comp bl, n)))
 /\
 (unop_exec' unop_neg_signed (v_bit (bl,n)) = SOME (v_bit (bitv_2comp bl, n)))
 /\
 (unop_exec' unop_un_plus (v_bit bitv) = SOME (v_bit bitv))
 /\
 (unop_exec' unop v = NONE)
End

Definition e_exec_unop'_def:
 (e_exec_unop' unop (e_v v) = unop_exec' unop v)
  /\
 (e_exec_unop' _ _ = NONE)
End


(** binops **)
(* Translation: dimword (:a) to (v2n (REPLICATE (LENGTH a) T) + 1)
 * UINT_MAXw to above minus 1 *)
Definition bitv_saturate_add_def:
 bitv_saturate_add a b l =
  let res = (v2n a) + (v2n b) in
  let limit = (v2n (REPLICATE l T) + 1) in
  if limit <= res
  then SOME $ (fixwidth l $ n2v (limit - 1), l)
  else SOME $ (fixwidth l $ n2v res, l)
End

Definition bitv_saturate_sub_def:
 bitv_saturate_sub a b l =
  SOME $ (fixwidth l $ n2v (v2n a - v2n b), l)
End

Definition bitv_lsl_bv_def:
 bitv_lsl_bv a b l =
  SOME $ (fixwidth l (a++(REPLICATE (v2n b) F)), l)
End

(* We could use l instead of LENGTH a, but that gives a precondition *)
Definition bitv_lsr_bv_def:
 bitv_lsr_bv a b l =
  SOME $ (TAKE (LENGTH a) ((REPLICATE (v2n b) F)++a), l)
End

Definition bitv_mul_def:
 bitv_mul a b l = SOME $ (fixwidth l $ n2v (v2n a * v2n b), l)
End

Definition bitv_div_def:
 bitv_div a b l =
  let divisor = v2n b in
  if divisor <> 0
  then
   SOME $ (fixwidth l $ n2v (v2n a DIV divisor), l)
  else NONE
End

Definition bitv_mod_def:
 bitv_mod a b l =
  let modulus = v2n b in
  if modulus <> 0
  then
   SOME $ (fixwidth l $ n2v (v2n a MOD modulus), l)
  else NONE
End

Definition bitv_add_def:
 bitv_add a b (l:num) = SOME $ (fixwidth l $ n2v (v2n a + v2n b), l)
End

Definition bitv_sub_def:
 bitv_sub a b (l:num) = bitv_add a (bitv_2comp b) l
End

Definition band'_def:
 band' a b = MAP (\(x,y). x /\ y) (ZIP(a, b))
End
Definition bitv_and_def:
 bitv_and a b (l:num) = SOME $ (band' a b, l)
End

Definition bor'_def:
 bor' (a:bool list) b = MAP (\(x,y). (x \/ y)) (ZIP(a, b))
End
Definition bitv_or_def:
 bitv_or a b (l:num) = SOME $ (bor' a b, l)
End

Definition bitv_xor_def:
 bitv_xor a b (l:num) = SOME $ (bxor a b, l)
End

(* TODO: Split the binop type into binops and binpreds, more efficient... *)
Definition get_bitv_binpred'_def:
 get_bitv_binpred' binop =
  case binop of
  | binop_le => SOME bitv_ls
  | binop_ge => SOME bitv_hs
  | binop_lt => SOME bitv_lo
  | binop_gt => SOME bitv_hi
  | binop_neq => SOME bitv_neq
  | binop_eq => SOME bitv_eq
  | _ => NONE
End

Definition bitv_binpred'_def:
  bitv_binpred' binpred (v, n) (v', n') =
    if n = n'
    then
     (case get_bitv_binpred' binpred of
      | SOME bp =>
       SOME $ bp v v'
      | NONE => NONE)
    else NONE
End

Definition get_bitv_binop'_def:
 get_bitv_binop' binop =
  case binop of
  | binop_mul => SOME bitv_mul
  | binop_div => SOME bitv_div
  | binop_mod => SOME bitv_mod
  | binop_add => SOME bitv_add
  | binop_sat_add => SOME bitv_saturate_add
  | binop_sub => SOME bitv_sub
  | binop_sat_sub => SOME bitv_saturate_sub
  | binop_shl => SOME bitv_lsl_bv
  | binop_shr => SOME bitv_lsr_bv
  | binop_and => SOME bitv_and
  | binop_xor => SOME bitv_xor
  | binop_or => SOME bitv_or
  | _ => NONE
End

Definition bitv_binop'_def:
  bitv_binop' binop (v, n) (v', n') =
    if n = n'
    then
     (case get_bitv_binop' binop of
      | SOME bo => bo v v' n
      | NONE => NONE)
    else NONE
End

Definition binop_exec'_def:
 (binop_exec' binop_mul (v_bit bitv1) (v_bit bitv2) =
  case bitv_binop' binop_mul bitv1 bitv2 of
  | SOME bitv3 => SOME (v_bit bitv3)
  | NONE => NONE)
 /\
 (binop_exec' binop_div (v_bit bitv1) (v_bit bitv2) =
  case bitv_binop' binop_div bitv1 bitv2 of
  | SOME bitv3 => SOME (v_bit bitv3)
  | NONE => NONE)
 /\
 (binop_exec' binop_mod (v_bit bitv1) (v_bit bitv2) =
  case bitv_binop' binop_mod bitv1 bitv2 of
  | SOME bitv3 => SOME (v_bit bitv3)
  | NONE => NONE)
 /\
 (binop_exec' binop_add (v_bit bitv1) (v_bit bitv2) =
  case bitv_binop' binop_add bitv1 bitv2 of
  | SOME bitv3 => SOME (v_bit bitv3)
  | NONE => NONE)
 /\
 (binop_exec' binop_sat_add (v_bit bitv1) (v_bit bitv2) =
  case bitv_binop' binop_sat_add bitv1 bitv2 of
  | SOME bitv3 => SOME (v_bit bitv3)
  | NONE => NONE)
 /\
 (binop_exec' binop_sub (v_bit bitv1) (v_bit bitv2) =
  case bitv_binop' binop_sub bitv1 bitv2 of
  | SOME bitv3 => SOME (v_bit bitv3)
  | NONE => NONE)
 /\
 (binop_exec' binop_sat_sub (v_bit bitv1) (v_bit bitv2) =
  case bitv_binop' binop_sat_sub bitv1 bitv2 of
  | SOME bitv3 => SOME (v_bit bitv3)
  | NONE => NONE)
 /\
 (binop_exec' binop_shl (v_bit bitv1) (v_bit bitv2) =
  SOME (v_bit (bitv_bl_binop shiftl bitv1 ((\(bl, n). (v2n bl, n)) bitv2))))
 /\
 (binop_exec' binop_shr (v_bit bitv1) (v_bit bitv2) =
  SOME (v_bit (bitv_bl_binop shiftr bitv1 ((\(bl, n). (v2n bl, n)) bitv2))))
 /\
 (binop_exec' binop_le (v_bit bitv1) (v_bit bitv2) =
  case bitv_binpred' binop_le bitv1 bitv2 of
  | SOME b => SOME (v_bool b)
  | NONE => NONE)
 /\
 (binop_exec' binop_ge (v_bit bitv1) (v_bit bitv2) =
  case bitv_binpred' binop_ge bitv1 bitv2 of
  | SOME b => SOME (v_bool b)
  | NONE => NONE)
 /\
 (binop_exec' binop_lt (v_bit bitv1) (v_bit bitv2) =
  case bitv_binpred' binop_lt bitv1 bitv2 of
  | SOME b => SOME (v_bool b)
  | NONE => NONE)
 /\
 (binop_exec' binop_gt (v_bit bitv1) (v_bit bitv2) =
  case bitv_binpred' binop_gt bitv1 bitv2 of
  | SOME b => SOME (v_bool b)
  | NONE => NONE)
 /\
 (* TODO: This would generalize easily in theory, but
  * gives rise to enormously many autogenerated cases *)
 (binop_exec' binop_neq (v_bit bitv1) (v_bit bitv2) =
  SOME (v_bool (bitv1 <> bitv2)))
 /\
 (binop_exec' binop_neq (v_bool b1) (v_bool b2) =
  SOME (v_bool (b1 <> b2)))
 /\
 (binop_exec' binop_eq (v_bit bitv1) (v_bit bitv2) =
  SOME (v_bool (bitv1 = bitv2)))
 /\
 (binop_exec' binop_eq (v_bool b1) (v_bool b2) =
  SOME (v_bool (b1 = b2)))
 /\
 (binop_exec' binop_and (v_bit bitv1) (v_bit bitv2) =
  SOME (v_bit (bitv_bl_binop band' bitv1 bitv2)))
 /\
 (binop_exec' binop_xor (v_bit bitv1) (v_bit bitv2) =
  SOME (v_bit (bitv_bl_binop bxor bitv1 bitv2)))
 /\
 (binop_exec' binop_or (v_bit bitv1) (v_bit bitv2) =
  SOME (v_bit (bitv_bl_binop bor' bitv1 bitv2)))
 /\
 (binop_exec' binop v1 v2 = NONE)
End

Definition e_exec_binop'_def:
 (e_exec_binop' (e_v v1) binop (e_v v2) = binop_exec' binop v1 v2)
  /\
 (e_exec_binop' _ _ _ = NONE)
End

Definition p4_match_mask'_def:
 p4_match_mask' val mask k =
  (case k of
   | v_bit (v', n') =>
    (case bitv_binop' binop_and (v', n') mask of
     | SOME res =>
      (case bitv_binop' binop_and val mask of
       | SOME res' => 
        (case bitv_binpred' binop_eq res res' of
         | SOME bool => bool
         | NONE => F)
       | NONE => F)
     | NONE => F)
   | _ => F)
End

Definition p4_match_range'_def:
 p4_match_range' lo hi k =
  case k of
   | v_bit (v', n') =>
    (case bitv_binpred' binop_ge (v', n') lo of
     | SOME T =>
      (case bitv_binpred' binop_le (v', n') hi of
       | SOME T => T
       | _ => F)
     | _ => F)
   | _ => F
End

Definition match'_def:
 match' v s =
  case s of
  | s_sing v' => (v = v')
  | s_range bitv bitv' => p4_match_range' bitv bitv' v
  | s_mask bitv bitv' => p4_match_mask' bitv bitv' v
  | s_univ => T
End

Definition match_all'_def:
 (match_all' [] = T) /\
 (match_all' ((h, h')::t) =
   if match' h h'
   then match_all' t
   else F)
End
        
Definition match_all_first'_def:
 (match_all_first' i v_list ([]:(s list # x) list) = NONE) /\
 (match_all_first' i v_list (h::t) =
  if (match_all' (ZIP(v_list, FST h)))
  then SOME (SND h)
  else match_all_first' (SUC i) v_list t)
End
Definition match_all_first_def:
 match_all_first v_list s_l_x_l = match_all_first' 0 v_list s_l_x_l
End

Definition e_exec_select'_def:
 (e_exec_select' (e_v v) s_l_x_l x =
  case v of
  | v_struct x_v_l =>
   (case match_all_first (SND $ UNZIP x_v_l) s_l_x_l of
    | SOME x' => SOME x'
    | NONE => SOME x)
  | _ => SOME x) /\
 (e_exec_select' _ _ _ = NONE)
End

Definition e_exec_slice'_def:
 (e_exec_slice' (e_v (v_bit bitv1)) (e_v (v_bit bitv2)) (e_v (v_bit bitv3)) =
  case slice' bitv1 bitv2 bitv3 of
  | SOME bitv => SOME $ v_bit bitv
  | NONE => NONE)
  /\
 (e_exec_slice' _ _ _ = NONE)
End


Definition e_exec'_def:
 (********************)
 (* Variable look-up *)
 (e_exec' (ctx:'a e_ctx) (g_scope_list:g_scope_list) (scope_list:scope_list) (e_var x) =
  case lookup_vexp2' scope_list g_scope_list x of
  | SOME v => SOME (e_v v, [])
  | NONE => NONE)
  /\
 (******************************)
 (* Struct/header field access *)
 (e_exec' ctx g_scope_list scope_list (e_acc e_v_struct x) =
  if is_v e_v_struct
  then
   (case e_exec_acc' (e_acc e_v_struct x) of
    | SOME v => SOME (v, [])
    | NONE => NONE)
   else
    (case e_exec' ctx g_scope_list scope_list e_v_struct of
     | SOME (e_v_struct', frame_list) =>
      SOME (e_acc e_v_struct' x, frame_list)
     | NONE => NONE))
  /\
 (*********************************)
 (* Struct/header field reduction *)
 (e_exec' ctx g_scope_list scope_list (e_struct x_e_l) =
  case unred_mem_index (MAP_SND x_e_l) of
  | SOME i =>
   (case oEL i (MAP_SND x_e_l) of
    | SOME x_e =>
     (case e_exec' ctx g_scope_list scope_list x_e of
      | SOME (e', frame_list) => SOME (e_struct (ZIP (MAP_FST x_e_l, (LUPDATE e' i (MAP_SND x_e_l)))), frame_list)
      | NONE => NONE)
    | NONE => NONE)
  | NONE =>
   (case vl_of_el' (MAP_SND x_e_l) of
    | SOME v_l => SOME (e_v (v_struct (ZIP (MAP_FST x_e_l, v_l))), [])
    | NONE => NONE))
  /\
 (************************)
 (* Function/extern call *)
 (e_exec' (ext_map, func_map, b_func_map) g_scope_list scope_list (e_call funn e_l) =
  (case lookup_funn_sig_body funn func_map b_func_map ext_map of
    | SOME (stmt, x_d_l) =>
     if LENGTH x_d_l = LENGTH e_l
     then
      (case unred_arg_index (MAP SND x_d_l) e_l of
       | SOME i =>
        (case oEL i e_l of
         | SOME elem =>
          (case e_exec' (ext_map, func_map, b_func_map) g_scope_list scope_list elem of
           | SOME (e', frame_list) => SOME (e_call funn (LUPDATE e' i e_l), frame_list)
           | NONE => NONE)
         | NONE => NONE)
       | NONE =>
        (case copyin' (MAP FST x_d_l) (MAP SND x_d_l) e_l g_scope_list scope_list of
         | SOME scope => 
          SOME (e_var (varn_star funn), [(funn, [stmt], [scope])])
         | NONE => NONE))
     else NONE
    | NONE => NONE))
  /\
 (********)
 (* Cast *)
 (e_exec' ctx g_scope_list scope_list (e_cast cast e) =
  if is_v e
  then
   (case e_exec_cast cast e of
    | SOME v => SOME (e_v v, [])
    | NONE => NONE)
  else
   (case e_exec' ctx g_scope_list scope_list e of
    | SOME (e', frame_list) => SOME (e_cast cast e', frame_list)
    | NONE => NONE))
  /\
 (********************)
 (* Unary arithmetic *)
 (e_exec' ctx g_scope_list scope_list (e_unop unop e) =
  if is_v e
  then 
   (case e_exec_unop' unop e of
    | SOME v => SOME (e_v v, [])
    | NONE => NONE)
  else
   (case e_exec' ctx g_scope_list scope_list e of
    | SOME (e', frame_list) => SOME (e_unop unop e', frame_list)
    | NONE => NONE))
  /\
 (*********************)
 (* Binary arithmetic *)
 (e_exec' ctx g_scope_list scope_list (e_binop e1 binop e2) =
  (case e1 of
   | (e_v v) =>
    if is_short_circuitable binop
    then
     (case e_exec_short_circuit v binop e2 of
      | SOME e' => SOME (e', [])
      | NONE => NONE)
    else if is_v e2
    then
     (case e_exec_binop' e1 binop e2 of
      | SOME v' => SOME (e_v v', [])
      | NONE => NONE)
    else
     (case e_exec' ctx g_scope_list scope_list e2 of
      | SOME (e2', frame_list) => SOME (e_binop e1 binop e2', frame_list)
      | NONE => NONE)
   | _ =>
    (case e_exec' ctx g_scope_list scope_list e1 of
     | SOME (e1', frame_list) => SOME (e_binop e1' binop e2, frame_list)
     | NONE => NONE)))
  /\
 (**********)
 (* Select *)
 (e_exec' ctx g_scope_list scope_list (e_select e s_l_x_l x) =
  if is_v e
  then
   (case e_exec_select' e s_l_x_l x of
    | SOME x' => SOME (e_v (v_str x'), [])
    | NONE => NONE)
  else
   (case e_exec' ctx g_scope_list scope_list e of
    | SOME (e', frame_list) => SOME (e_select e' s_l_x_l x, frame_list)
    | NONE => NONE))
  /\
 (*****************)
 (* Concatenation *)
 (e_exec' ctx g_scope_list scope_list (e_concat e1 e2) =
  if is_v_bit e1
  then 
   (if is_v_bit e2
    then 
     (case e_exec_concat e1 e2 of
      | SOME v => SOME (e_v v, [])
      | NONE => NONE)
    else
     (case e_exec' ctx g_scope_list scope_list e2 of
      | SOME (e2', frame_list) => SOME (e_concat e1 e2', frame_list)
      | NONE => NONE))
  else
   (case e_exec' ctx g_scope_list scope_list e1 of
    | SOME (e1', frame_list) => SOME (e_concat e1' e2, frame_list)
    | NONE => NONE))
  /\
 (***********)
 (* Slicing *)
 (e_exec' ctx g_scope_list scope_list (e_slice e1 e2 e3) =
  if (is_v_bit e2 /\ is_v_bit e3)
  then
   (if is_v_bit e1
    then 
     (case e_exec_slice' e1 e2 e3 of
      | SOME v => SOME (e_v v, [])
      | NONE => NONE)
    else
     (case e_exec' ctx g_scope_list scope_list e1 of
      | SOME (e1', frame_list) => SOME (e_slice e1' e2 e3, frame_list)
      | NONE => NONE))
   else NONE)
  /\
 (e_exec' _ _ _ _ = NONE)
Termination
WF_REL_TAC `measure e_state_size'` \\
fs [e_state_size'_def, e_size_def, MAP_SND_EQ, listTheory.oEL_EQ_EL] \\
REPEAT STRIP_TAC >| [
  IMP_RES_TAC unred_arg_index_in_range \\
  IMP_RES_TAC rich_listTheory.EL_MEM \\
  IMP_RES_TAC e3_size_mem \\
  fs [],

  IMP_RES_TAC unred_mem_index_in_range \\
  IMP_RES_TAC rich_listTheory.EL_MEM \\
  `e_size (EL i (MAP SND x_e_l)) < e1_size x_e_l` suffices_by (
   fs []
  ) \\
  `e2_size (EL i (MAP FST x_e_l), EL i (MAP SND x_e_l)) < e1_size x_e_l` suffices_by (
   rpt strip_tac \\
   irule arithmeticTheory.LESS_TRANS \\
   qexists_tac `e2_size (EL i (MAP FST x_e_l),EL i (MAP SND x_e_l))` \\
   fs [e_e2_size_less]
  ) \\
  subgoal `MEM (EL i x_e_l) x_e_l` >- (
   irule rich_listTheory.EL_MEM \\
   fs [listTheory.LENGTH_MAP]
  ) \\
  imp_res_tac e1_size_mem \\
  metis_tac [EL_pair_list, listTheory.LENGTH_MAP]
]
End


val _ = translation_extends "basisProg";

val _ = ml_prog_update (open_module "p4_exec_sem_e_cake");
(*
val _ = ml_prog_update (add_dec
  ``Dtabbrev unknown_loc [] "p4_exec_sem_e_cake" (Atapp [] (Short "p4_exec_sem_e_cake"))`` I);

val _ = generate_sigs := true;
*)

val _ = translate numposrepTheory.l2n_def;
val _ = translate bitstringTheory.bitify_def;
val _ = translate bitstringTheory.v2n_def;
Theorem l2n_side_thm:
!n l. l2n_side n l <=> (l <> [] ==> n <> 0)
Proof
strip_tac \\
Induct \\ (
 rpt strip_tac \\
 ONCE_REWRITE_TAC[theorem "l2n_side_def"] \\
 gs[]
) \\
Cases_on ‘l’ \\ (
 gs[]
)
QED
val _ = update_precondition l2n_side_thm;
Theorem v2n_side:
!v1. v2n_side v1
Proof
gs[definition "v2n_side_def", l2n_side_thm, bitstringTheory.bitify_def]
QED
val _ = update_precondition v2n_side;

val _ = translate numposrepTheory.n2l_def;
val _ = translate bitstringTheory.boolify_def;
val _ = translate bitstringTheory.n2v_def;
Theorem n2l_side_thm:
!n m. n2l_side n m <=> n <> 0
Proof
strip_tac \\
completeInduct_on ‘m’ \\
rpt strip_tac \\
ONCE_REWRITE_TAC[theorem "n2l_side_def"] \\
gs[]
QED
val _ = update_precondition n2l_side_thm;
Theorem n2v_side:
!v. n2v_side v
Proof
gs[definition "n2v_side_def", n2l_side_thm]
QED
val _ = update_precondition n2v_side;

val _ = translate find_topmost_map'_def;
val _ = translate lookup_map'_def;
val _ = translate lookup_vexp2'_def;
val _ = translate is_v_def;
val _ = translate e_exec_acc'_def;
val _ = translate INDEX_FIND_def;
val _ = translate is_const_def;
val _ = translate unred_mem_def;
val _ = translate unred_mem_index_def;
val _ = translate MAP_SND_def;
val _ = translate v_of_e_def;
val _ = translate vl_of_el'_def;
val _ = translate MAP_FST_def;
val _ = translate oEL_def;
val _ = translate listTheory.LUPDATE_DEF;


(*****************)
(* Function call *)
val _ = translate lookup_funn_sig_body_def;
val _ = translate is_d_out_def;
val _ = translate get_lval_of_e_def;
val _ = translate is_e_lval_def;
val _ = translate is_arg_red_def;
val _ = translate find_unred_arg_def;
val _ = translate unred_arg_index_def;
val _ = translate listTheory.FOLDL;
val _ = translate find_topmost_map_def;
val _ = translate topmost_map_def;
val _ = translate lookup_map_def;
val _ = translate lookup_v_def;
val _ = translate acc_f_def;

val _ = translate rich_listTheory.SEG;
Theorem seg_side_thm:
!len start l. seg_side len start l <=> (len <> 0 ==> (start + len <= LENGTH l))
Proof
strip_tac \\
completeInduct_on ‘len’ \\
completeInduct_on ‘start’ \\
rpt strip_tac \\
ONCE_REWRITE_TAC[theorem "seg_side_def"] \\
gs[] \\
eq_tac >- (
 rpt strip_tac >- (
  res_tac \\
  gs[]
 ) \\
 gs[] \\
 qpat_x_assum ‘!m. m < SUC x4 ==>
               !l'. seg_side (SUC x3) m l' <=> m + SUC x3 <= LENGTH l'’
              (fn thm => ASSUME_TAC $ Q.SPEC ‘x4’ thm) \\
 gs[arithmeticTheory.SUC_ONE_ADD]
) \\
rpt strip_tac \\ (
 gs[]
) >- (
 Cases_on ‘len’ \\ Cases_on ‘start’ \\ (
  gs[]
 ) >- (
  Cases_on ‘l’ \\ (
   gs[]
  )
 ) \\
 Cases_on ‘l’ \\ (
  gs[]
 )
) \\
qpat_x_assum ‘!m. m < SUC x10 ==>
              !l'. seg_side (SUC x13) m l' <=> m + SUC x13 <= LENGTH l'’
             (fn thm => ASSUME_TAC $ Q.SPEC ‘x10’ thm) \\
gvs[] \\
gs[arithmeticTheory.SUC_ONE_ADD]
QED
val _ = update_precondition seg_side_thm;
val _ = translate bitv_bitslice_def;
val _ = translate slice'_def;
Theorem slice'_side:
!v1 v2 v3. slice'_side v1 v2 v3
Proof
simp[Once $ definition "slice'_side_def"] \\
simp[Once $ definition "bitv_bitslice_side_def"]
QED
val _ = update_precondition slice'_side;
val _ = translate slice_lval'_def;
val _ = translate lookup_lval'_def;

val _ = translate is_d_in_def;
val _ = translate bitstringTheory.extend_def;
val _ = translate init_out_v_cake_def;
val _ = translate one_arg_val_for_newscope'_def;
val _ = translate AFUPDKEY_def;
val _ = translate AUPDATE_def;
val _ = translate update_arg_for_newscope'_def;
val _ = translate all_arg_update_for_newscope'_def;
val _ = translate copyin'_def;

(* Cast *)
val _ = translate bitstringTheory.zero_extend_def;
val _ = translate listTheory.DROP_def;
val _ = translate bitstringTheory.fixwidth_def;
val _ = translate bool_cast_def;
val _ = translate bitv_cast_def;
val _ = translate cast_exec_def;
val _ = translate e_exec_cast_def;

(* Unops *)
val _ = translate bitv_1comp_def;
val _ = translate bitv_2comp_def;
val _ = translate unop_exec'_def;
val _ = translate e_exec_unop'_def;

(* Select *)
val _ = translate bitv_ls_def;
val _ = translate bitv_hs_def;
val _ = translate bitv_lo_def;
val _ = translate bitv_hi_def;
val _ = translate rich_listTheory.AND_EL_DEF;
val _ = translate bit_eq_def;
val _ = translate bitv_eq_def;
val _ = translate bitv_neq_def;
val _ = translate get_bitv_binpred'_def;
val _ = translate bitv_binpred'_def;
val _ = translate p4_match_range'_def;
val _ = translate bitv_mul_def;
val _ = translate bitv_div_def;
val _ = translate bitv_mod_def;
val _ = translate bitv_add_def;
val _ = translate bitv_sub_def;

val _ = translate band'_def;
val _ = translate bitv_and_def;
val _ = translate bor'_def;
val _ = translate bitv_or_def;
val _ = translate bitstringTheory.bitwise_def;
val _ = translate bitstringTheory.bxor_def;
val _ = translate bitv_xor_def;

val _ = translate rich_listTheory.REPLICATE;
val _ = translate bitv_saturate_add_def;
val _ = translate bitv_saturate_sub_def;
val _ = translate bitv_lsl_bv_def;
val _ = translate rich_listTheory.TAKE;
val _ = translate bitv_lsr_bv_def;
Theorem take_1_side_thm:
!n l. take_1_side n l <=> n <= LENGTH l
Proof
Induct \\ (
 simp[Once $ theorem "take_1_side_def"]
) \\
rpt strip_tac \\
Cases_on ‘l’ \\ (
 gs[]
)
QED
val _ = update_precondition take_1_side_thm;
Theorem bitv_lsr_bv_side:
!v1 v2 l. bitv_lsr_bv_side v1 v2 l
Proof
simp[Once $ definition "bitv_lsr_bv_side_def", take_1_side_thm]
QED
val _ = update_precondition bitv_lsr_bv_side;
val _ = translate p4Theory.binop2num_thm;
val _ = translate p4Theory.binop_CASE;
val _ = translate get_bitv_binop'_def;
val _ = translate bitv_binop'_def;
val _ = translate p4_match_mask'_def;
val _ = translate match'_def;
val _ = translate match_all'_def;
val _ = translate match_all_first'_def;
val _ = translate match_all_first_def;
val _ = translate e_exec_select'_def;

(* Binops *)
val _ = translate is_short_circuitable_def;
val _ = translate e_exec_short_circuit_def;
val _ = translate bitv_bl_binop_def;
val _ = translate bitstringTheory.shiftl_def;
val _ = translate bitstringTheory.shiftr_def;
val _ = translate binop_exec'_def;
val _ = translate e_exec_binop'_def;
    
(* Concatenation *)
val _ = translate bitv_concat_def;
val _ = translate e_exec_concat_def;
val _ = translate is_v_bit_def;

(* Slicing *)
val _ = translate e_exec_slice'_def;


(* The whole expression-level semantics: *)
val _ = translate e_exec'_def;

val _ = ml_prog_update (close_module NONE);

val _ = export_theory ();
