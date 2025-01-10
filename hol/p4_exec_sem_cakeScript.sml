open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_exec_sem_cake";

open p4Syntax;
open ottTheory;
open p4Theory p4_auxTheory;

(******************************************)
(* New types, and downstream consequences *)

Type word64 = “:word64”

(* TODO: Make funns words64s later *)
(* TODO: Fix things so that variable names with strings are no longer needed *)
Datatype:
 varn' = 
    varn'_name word64 (* CakeML-friendly variable name *)
  | varn'_star funn (* function return placeholder *)
End

val _ = Hol_datatype ` 
e' =  (* expression *)
   e'_v of v (* value *)
 | e'_var of varn' (* variable *)
 | e'_list of e' list (* expression list *)
 | e'_acc of e' => x (* field access *)
 | e'_unop of unop => e' (* unary operation *)
 | e'_cast of cast => e' (* cast *)
 | e'_binop of e' => binop => e' (* binary operation *)
 | e'_concat of e' => e' (* concatenation of bit-strings *)
 | e'_slice of e' => e' => e' (* bit-slice *)
 | e'_call of funn => e' list (* function or extern call *)
 | e'_select of e' => (s_list#x) list => x (* select *)
 | e'_struct of (x#e') list (* struct *)
 | e'_header of boolv => (x#e') list (* header *)
`;

val _ = Hol_datatype ` 
lval' = 
   lval'_varname of varn' (* variable name *)
 | lval'_null (* null variable *)
 | lval'_field of lval' => x (* field access *)
 | lval'_slice of lval' => e' => e' (* slice array *)
 | lval'_paren of lval'
`;

Type e_list' = ``:(e' list)``

Type scope' = ``:((varn', (v # lval' option)) alist)``

Type g_scope' = ``:scope'``

Type g_scope_list' = ``:(scope' list)``

Type scope_list' = ``:(scope' list)``

Type ext_fun = ``:(('a # g_scope_list' # scope_list') -> (('a # scope_list' # status) option))``

Type t_scope' = ``:((varn', (tau # lval' option)) alist)``

val _ = Hol_datatype ` 
stmt' =  (* statement *)
   stmt'_empty (* empty statement *)
 | stmt'_ass of lval' => e' (* assignment *)
 | stmt'_cond of e' => stmt' => stmt' (* conditional *)
 | stmt'_block of t_scope' => stmt' (* block *)
 | stmt'_ret of e' (* return *)
 | stmt'_seq of stmt' => stmt' (* sequence *)
 | stmt'_trans of e' (* transition *)
 | stmt'_app of x => e' list (* apply *)
 | stmt'_ext (* extern *)
`;

Type b_func_map' = ``:((string, (stmt' # (q # d) list)) alist)``

Type func_map' = ``:((string, (stmt' # (q # d) list)) alist)``

Type ext_fun_map' = ``:((string, ((q # d) list # 'a ext_fun)) alist)``

Type pars_map' = ``:((string, stmt') alist)``

Type ext_map' = ``:((string, ((((q # d) list # 'a ext_fun) option) # 'a ext_fun_map')) alist)``

Type tbl_map' = ``:((string, ((mk list) # (x # e_list'))) alist)``

Type pblock' = ``:(pbl_type # ((q # d) list) # b_func_map' # t_scope' # pars_map' # tbl_map')``

Type pblock_map' = ``:((string, pblock') alist)``

Type pblock_list' = ``:(pblock' list)``
val _ = Hol_datatype ` 
arch_block' =  (* architectural block *)
   arch_block'_inp
 | arch_block'_pbl of x => e' list
 | arch_block'_ffbl of x
 | arch_block'_out
`;

Type apply_table_f' = ``:((x # e_list' # mk_list # (x # e_list') # 'a) -> (x # e_list') option)``

Type copyout_pbl' = ``:((g_scope' list # 'a # d list # q list # status) -> 'a option)``

Type copyin_pbl' = ``:((q list # d list # e' list # 'a) -> scope' option)``

Type output_f = ``:((in_out_list # 'a) -> (in_out_list # 'a) option)``

Type input_f = ``:((in_out_list # 'a) -> (in_out_list # 'a) option)``

Type ab_list' = ``:(arch_block' list)``

(* New to executable semantics *)
Type e_ctx = “:('a ext_map' # func_map' # b_func_map')”;

Type ctx' = ``:('a apply_table_f' # 'a ext_map' # func_map' # b_func_map' # pars_map' # tbl_map')``

Type actx' = ``:(ab_list' # pblock_map' # 'a ffblock_map # 'a input_f # 'a output_f # 'a copyin_pbl' # 'a copyout_pbl' # 'a apply_table_f' # 'a ext_map' # func_map')``

Type stmt_stack' = ``:(stmt' list)``

Type frame' = ``:(funn # stmt_stack' # scope_list')``

Type frame_list' = ``:(frame' list)``

Type state' = ``:('a # g_scope_list' # frame_list' # status)``

val _ = Hol_datatype ` 
arch_frame_list' =  (* architecture-level frame list *)
   arch_frame_list'_empty (* empty architecture-level frame list *)
 | arch_frame_list'_regular of frame_list' (* regular frame list *)
`;

Type astate' = ``:('a aenv # g_scope_list' # arch_frame_list' # status)``

(**********************************)
(* Semantics function definitions *)

val is_const'_def = Define `
  (is_const' (e'_v _) = T) /\
  (is_const' _ = F)
`;

val is_consts'_def = Define `
  is_consts' el = ~(EXISTS (\e. ~(is_const' e)) el)
`;

val slice_lval'_def = Define `
  (slice_lval' (v_bit (v, bl)) e1 e2 =
     (case e1 of
     | (e'_v (v_bit (v1, bl1))) =>
       (case e2 of
       | (e'_v (v_bit (v2, bl2))) => SOME (v_bit (slice (v, bl) (v1, bl1) (v2, bl2)) )
       | _ => NONE )
     | _ => NONE
     ))
`;

Definition is_var'_def:
 (is_var' (e'_var x) = T) /\
 (is_var' _ = F)
End

val varname_of_e'_def = Define `
  (varname_of_e' (e'_var varn) = SOME varn) /\
  (varname_of_e' _ = NONE)
`;

val v_of_e'_def = Define `
  (v_of_e' (e'_v v) = SOME v) /\
  (v_of_e' _ = NONE)
`;

Definition vl_of_el'_def:
 (vl_of_el' [] = SOME []) /\
 (vl_of_el' (h::t) =
   case v_of_e' h of
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

val index_not_const'_def = Define `
  index_not_const' elist =
    case INDEX_FIND 0 (\e. ~(is_const' e)) elist of
    |SOME (i, e) => SOME i
    |_ => NONE
`;

(* TODO: Changed from CakeML-exportable exec sem *)
Definition find_topmost_map'_def:
 (find_topmost_map' ([]:scope' list) (x:varn') = NONE) /\
 (find_topmost_map' (h::t) x =
    if IS_SOME $ ALOOKUP h x
    then SOME (0:num, h)
    else
     (case find_topmost_map' t x of
      | SOME (i, scope) => SOME (i+1, scope)
      | NONE => NONE))
End
Definition lookup_map'_def:
  lookup_map' (ss:scope' list) (x:varn') =
    case find_topmost_map' ss x of
    | SOME (i, sc) => 
      (case ALOOKUP sc x of
       | SOME y => SOME y
       | _ => NONE)
    | _ => NONE
End

val lookup_v'_def = Define `
  lookup_v' (ss:scope' list) x =
    case lookup_map' ss x of
    | SOME (v, str_opt) => SOME v
    | _ => NONE
`;

val lookup_out'_def = Define `
  lookup_out' (ss:scope' list) x =
    case lookup_map' ss x of
    | SOME (v, str_opt) => SOME str_opt
    | _ => NONE
`;

Definition lookup_vexp2'_def:
  lookup_vexp2' (ss:scope' list) (g_scope_list:scope' list) x =
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

val lookup_lval'_def = Define `
  (lookup_lval' (ss:scope' list) (lval'_varname x) = lookup_v' ss x) /\
  (lookup_lval' ss (lval'_field lval f) =
     case lookup_lval' ss lval of
     | SOME v => acc_f v f
     | NONE => NONE) /\
 (lookup_lval' ss (lval'_slice lval e1 e2) =
    case lookup_lval' ss lval of
     | SOME (v_bit (v, bl)) => (slice_lval' (v_bit (v, bl)) e1 e2)
     | _ => NONE
     ) /\
 (lookup_lval' ss (lval'_null) = NONE ) /\
 (lookup_lval' ss (lval'_paren lval) = lookup_lval' ss lval) 
`;

val get_lval_of_e'_def = Define `
  (get_lval_of_e' (e'_var x) = SOME (lval'_varname x)) /\
  (get_lval_of_e' (e'_acc e x) =
   case get_lval_of_e' e of
   | SOME lval => SOME (lval'_field lval x)
   | NONE => NONE) /\
   (get_lval_of_e' (e'_slice e ev1 ev2) =
   case get_lval_of_e' e of
   | SOME lval => SOME (lval'_slice lval ev1 ev2)
   | NONE => NONE) /\
  (get_lval_of_e' _ = NONE)
`;

val is_e_lval'_def = Define `
  (is_e_lval' e =
    case get_lval_of_e' e of
    | SOME lval => T
    | NONE => F)
`;

val unred_mem'_def = Define `
  unred_mem' elist = 
    INDEX_FIND 0 (\e. ~(is_const' e)) elist
`;

val unred_mem_index'_def = Define `
  unred_mem_index' elist = 
    case unred_mem' elist of
    | SOME (i, e) => SOME i
    | _ => NONE
`;

val is_arg_red'_def = Define `
  is_arg_red' d e =
   ((~(is_d_out d) ==> is_const' e) /\ (is_d_out d ==> is_e_lval' e))
`;

val find_unred_arg'_def = Define `
  find_unred_arg' dlist elist = 
    (INDEX_FIND 0 (\(d, e). ~(is_arg_red' d e)) (ZIP (dlist, elist)))
`;

val unred_arg_index'_def = Define `
  unred_arg_index' dlist elist  = 
    case find_unred_arg' dlist elist of
    | SOME (i, de) => SOME i
    | _ => NONE
`;

val check_arg_red'_def = Define `
  check_arg_red' dlist e i =
    is_arg_red' (EL i dlist) e
`;

val check_args_red'_def = Define `
  check_args_red' dlist elist = EVERY (\(d, e). is_arg_red' d e) (ZIP(dlist, elist))
`;

Definition one_arg_val_for_newscope'_def:
 one_arg_val_for_newscope' d e ss =
  if is_d_out d
  then
   (case get_lval_of_e' e of
    | SOME lval =>
     (case lookup_lval' ss lval of
      | SOME v =>
       if is_d_in d
       then SOME (v, SOME lval)
       else SOME (init_out_v_cake v, SOME lval)
      | NONE => NONE)
    | NONE => NONE)
  else
   (case v_of_e' e of
    | SOME v => SOME (v, NONE)
    | NONE => NONE)
End

Definition update_arg_for_newscope'_def:
 update_arg_for_newscope' ss f_opt (d, x, e) =
  case f_opt of
  | SOME f =>
   (case one_arg_val_for_newscope' d e ss of
    | SOME (v, lval_opt) => SOME (p4$AUPDATE f (varn'_name x, (v, lval_opt)))
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

Definition assign_to_slice'_def:
 assign_to_slice' vb vb' ev1 ev2 =
  (case ev1 of
   | (e'_v (v_bit (bl1, n1))) =>
    (case ev2 of
     | (e'_v (v_bit (bl2, n2))) =>
      (case replace_bits vb vb' (v2n bl1) (v2n bl2) of
       | SOME bitv =>
        SOME $ v_bit (bitv, SND vb')
       | NONE => NONE)
     | _ => NONE)
   | _ => NONE)
End

Definition assign'_def:
 (assign' ss v (lval'_varname x) =
  case find_topmost_map' ss x of
  | SOME (i, sc) =>
   (case lookup_out' ss x of
    | SOME str_opt =>
      SOME (LUPDATE (AUPDATE sc (x, (v, str_opt))) i ss)
    | NONE => NONE)
  | _ => NONE) /\
 (assign' ss v (lval'_field lval f) =
  case lookup_lval' ss lval of
  | SOME (v_struct f_v_l) =>
   (case INDEX_OF f (MAP FST f_v_l) of
    | SOME i => assign' ss (v_struct (LUPDATE (f, v) i f_v_l)) lval
    | NONE => NONE)
  | SOME (v_header validity f_v_l) =>
   (case INDEX_OF f (MAP FST f_v_l) of
    | SOME i => assign' ss (v_header validity (LUPDATE (f, v) i f_v_l)) lval
    | NONE => NONE)
   | _ => NONE) /\    
 (assign' ss v (lval'_slice lval ev1 ev2) =
  case v of
  | v_bit vb =>
   (case lookup_lval' ss lval of
    | SOME (v_bit vb') =>
     (case assign_to_slice' vb vb' ev1 ev2 of
      | SOME v_res => assign' ss v_res lval
      | _ => NONE)
    | _ => NONE)
  | _ => NONE) /\
 (assign' ss v lval'_null = SOME ss) /\
 (assign' ss v (lval'_paren lval) = assign' ss v lval)
End

val initialise'_def = Define `
  (initialise' (ss:scope_list') varn v =
    LUPDATE (AUPDATE (LAST ss) (varn, (v, NONE))) (LENGTH ss - 1) ss
  )
`;

val var_star_updates_of_func_map'_def = Define `
  (var_star_updates_of_func_map' (func_map:func_map') =
   let varnames = (MAP FST func_map) in
   MAP ( \x. (varn'_star (funn_name x), (v_bot, (NONE:lval' option)))) varnames
  )
`;

val var_star_updates_of_ext_map'_def = Define `
 (var_star_updates_of_ext_map' ([]:'a ext_map') = []) /\
 (var_star_updates_of_ext_map' (((ext_obj_name, ext_obj_funs)::t):'a ext_map') =
  case ext_obj_funs of
  | (SOME _, ext_fun_map) =>
   ((varn'_star (funn_inst ext_obj_name), (v_bot, (NONE:lval' option)))::(MAP ( \x. (varn'_star (funn_ext ext_obj_name x), (v_bot, (NONE:lval' option)))) (MAP FST ext_fun_map)))++(var_star_updates_of_ext_map' t)
  | (NONE, ext_fun_map) =>
   MAP ( \x. (varn'_star (funn_ext ext_obj_name x), (v_bot, (NONE:lval' option)))) (MAP FST ext_fun_map)++(var_star_updates_of_ext_map' t)
 )
`;

val initialise_var_stars'_def = Define `
  (initialise_var_stars' func_map b_func_map ext_map g_scope_list =
   case g_scope_list of
   | [bg_scope; gg_scope] =>
    SOME ([AUPDATE_LIST bg_scope (var_star_updates_of_func_map' b_func_map); AUPDATE_LIST gg_scope ((var_star_updates_of_func_map' func_map)++(var_star_updates_of_ext_map' ext_map))])
   | _ => NONE
  )
`;

(* TODO: This function initialises everything to zeroes instead of using ARBs,
 * which are not compatible with CakeML. Use this as a placeholder before you have
 * deep-embedded uninitialised values. *)
Definition init_v_from_tau_cake_def:
 (init_v_from_tau_cake tau_bool = v_bool F) /\
 (init_v_from_tau_cake (tau_bit w) = v_bit (GENLIST (\x. F) w, w)) /\
 (init_v_from_tau_cake tau_bot = v_bot) /\
 (init_v_from_tau_cake tau_ext = v_ext_ref 0) /\
 (init_v_from_tau_cake (tau_xtl struct_ty_struct []) = v_struct []) /\
 (init_v_from_tau_cake (tau_xtl struct_ty_struct ((x0,t0)::xtl)) =
  v_struct ((x0, init_v_from_tau_cake t0)::(MAP (\(x,t). (x, init_v_from_tau_cake t)) xtl))) /\
 (init_v_from_tau_cake (tau_xtl struct_ty_header [] ) = v_header F [] ) /\
 (init_v_from_tau_cake (tau_xtl struct_ty_header ((x0,t0)::xtl)) =
   v_header F ((x0, init_v_from_tau_cake t0)::(MAP (\(x,t). (x, init_v_from_tau_cake t)) xtl)))
Termination
WF_REL_TAC `measure tau_size`
End

Definition declare_list_in_scope'_def:
 declare_list_in_scope' (t_scope:t_scope', scope:scope') =
  FOLDR (\(x, (t, lvalop)) f. p4$AUPDATE f (x, (init_v_from_tau_cake t, NONE))) scope t_scope
End

Definition declare_list_in_fresh_scope'_def:
 declare_list_in_fresh_scope' (t_scope:t_scope') =
  MAP (\(x, (t, lvalop)). (x, (init_v_from_tau_cake t, NONE))) t_scope
End

val lookup_funn_sig_body'_def = Define `
  (lookup_funn_sig_body' (funn:funn) (func_map:func_map') (b_func_map:b_func_map') (ext_map:'a ext_map') =
    case funn of
    | (funn_name x) =>
     (case ALOOKUP b_func_map x of
      | SOME (stmt, x_d_l) => SOME (stmt, x_d_l)
      | NONE =>
       (case ALOOKUP func_map x of
        | SOME (stmt, x_d_l) => SOME (stmt, x_d_l)
        | NONE => NONE
       )
     )
    | (funn_inst x) =>
     (case ALOOKUP ext_map x of
      | SOME (SOME (x_d_l, _), _) => SOME (stmt'_ext, x_d_l)
      | _ => NONE)
    | (funn_ext x x') =>
     (case ALOOKUP ext_map x of
      | SOME (_, ext_fun_map) =>
       (case ALOOKUP ext_fun_map x' of
	      | SOME (x_d_l, _) => SOME (stmt'_ext, x_d_l)
	      | _ => NONE)
      | _ => NONE)
  )
`;

val lookup_funn_sig'_def = Define `
  (lookup_funn_sig' funn func_map b_func_map ext_map =
    case lookup_funn_sig_body' funn func_map b_func_map ext_map of
    | SOME (_, x_d_l) => SOME x_d_l
    | NONE => NONE
  )
`;

val lookup_block_body'_def = Define `
 lookup_block_body' f b_func_map =
  case ALOOKUP b_func_map f of
  | SOME res => SOME $ FST res
  | NONE => NONE
`;

Definition update_return_frame'_def:
 update_return_frame' xlist dlist ss ss_curr = 
  FOLDL
   (\ss_temp_opt (x,d).
    if (is_d_none_in d)
    then ss_temp_opt
    else
     case ss_temp_opt of
     | SOME ss_temp =>
      (case lookup_map' ss_curr (varn'_name x) of
       | SOME (v, stret_opt) =>
        (case stret_opt of
         | SOME stret => assign' ss_temp v stret
         | NONE => NONE)
       | _ => NONE)
     | NONE => NONE
   )
   (SOME ss)
   (ZIP(xlist, dlist))
End

Definition copyout'_def:
 copyout' xlist dlist gsl ss ss_curr =
  if ss_curr <> []
  then
   (case update_return_frame' xlist dlist (ss++gsl) [LAST ss_curr] of
    | SOME updated_return_ss =>
     (case (LENGTH updated_return_ss) of
      | 0 => NONE
      | i => SOME (THE (oDROP (i-2) updated_return_ss), THE(oTAKE (i-2) updated_return_ss)))
    | NONE => NONE)
  else NONE
End

val fully_reduced'_def = Define `
  fully_reduced' e =
    case e of
    | (e'_v (v_str _)) => T
    | _ => F
`;

val state_fin'_def = Define `
 state_fin' status frame_list =
  ((status = status_trans "accept") \/
   (status = status_trans "reject") \/
   (?v. status = status_returnv v) \/
   (?funn scope_list. frame_list = [(funn, [stmt'_empty], scope_list)] /\
    ((?state_name. status = status_trans state_name) ==>
     ((status = status_trans "accept") \/
      (status = status_trans "reject"))))
  )
`;

val not_top_return'_def = Define `
  not_top_return' frame_list =
    case frame_list of
    | [(funn, stmt, scope_list)] =>
      (case stmt of
      | stmt'_ret e => T
      | stmt'_seq (stmt'_ret e) _ => T
      | _ => F)
    | _ => F
`;

val decl_init_star'_def = Define `
  decl_init_star' scope_list v (varn'_star funn) =
    AUPDATE (HD scope_list) ((varn'_star funn), (v , NONE))
`;

val init_in_highest_scope'_def = Define `
  init_in_highest_scope' scope_list v (varn'_star funn) =
    LUPDATE (decl_init_star' scope_list v (varn'_star funn)) 0 scope_list
`;

val lookup_ext_fun'_def = Define `
  (lookup_ext_fun' (funn_ext f f') (ext_map:'a ext_map') =
   case ALOOKUP ext_map f of
   | SOME (_, ext_fun_map) =>
    (case ALOOKUP ext_fun_map f' of
     | SOME (_, ext_fun) => SOME ext_fun
     | NONE => NONE)
   | NONE => NONE) /\
  (lookup_ext_fun' (funn_inst f) ext_map =
   case ALOOKUP ext_map f of
   | SOME (SOME (_, ext_fun), _) => SOME ext_fun
   | _ => NONE) /\
  (lookup_ext_fun' (funn_name f) ext_map = NONE)
`;

Definition scopes_to_pass'_def:
 scopes_to_pass' (funn:funn) (func_map_g:func_map') (b_func_map:b_func_map') (g_scope_list:g_scope_list') =
  case g_scope_list of
  | [block_scope; global_scope] =>
   (case funn of
    | (funn_name x) =>
     (case ALOOKUP b_func_map x of
      | SOME (stmt, x_d_l) => SOME [block_scope; global_scope]
      | NONE =>
       (case ALOOKUP func_map_g x of
        | SOME (stmt, x_d_l) => SOME ([[]; global_scope])
        | NONE => SOME [block_scope; global_scope]
       )
     )
    | _ => SOME ([[]; global_scope]))
  | _ => NONE
End

Definition scopes_to_retrieve'_def:
 scopes_to_retrieve' (funn:funn) (func_map_g:func_map') (b_func_map:b_func_map') (g_scope_list_og:g_scope_list') (g_scope_list:g_scope_list') =
  case g_scope_list_og of
   | [block_scope_og; global_scope_og] =>
    (case g_scope_list of
     | [block_scope; global_scope] =>
      (case funn of
       | (funn_name x) =>
        (case ALOOKUP b_func_map x of
         | SOME (stmt, x_d_l) => SOME [block_scope; global_scope]
         | NONE =>
          (case ALOOKUP func_map_g x of
           | SOME (stmt, x_d_l) => SOME [block_scope_og; global_scope]
           | NONE => SOME [block_scope; global_scope]))
       | _ => SOME [block_scope_og; global_scope])
     | _ => NONE)
   | _ => NONE
End


val map_to_pass'_def = Define `
 map_to_pass' (funn:funn) (b_func_map:b_func_map') =
  case funn of
   | (funn_name x) =>
    (case ALOOKUP b_func_map x of
     | SOME (stmt, x_d_l) => SOME b_func_map
     | NONE => SOME []
    )
   | _ => SOME []
`;

val tbl_to_pass'_def = Define `
 tbl_to_pass' (funn:funn) (b_func_map:b_func_map') (tbl_map:tbl_map') = 
  case funn of
   | (funn_name x) =>
    (case ALOOKUP b_func_map x of
     | SOME (stmt, x_d_l) => SOME tbl_map
     | NONE => SOME []
    )
   | _ => SOME []
`;


(**********************************************************************)
(* Expression-related shorthands (from original executable semantics) *)

Definition is_v'_def:
 (is_v' (e'_v v) = T) /\
 (is_v' _ = F)
End

Definition get_v'_def:
 (get_v' (e'_v v) = SOME v) /\
 (get_v' _ = NONE)
End

Definition is_v_bool'_def:
 (is_v_bool' (e'_v (v_bool b)) = T) /\
 (is_v_bool' _ = F)
End

Definition is_v_bit'_def:
 (is_v_bit' (e'_v (v_bit bitv)) = T) /\
 (is_v_bit' _ = F)
End

(* NOTE: Error messages serialised using 32 bits *)
Definition is_v_err'_def:
 (is_v_err' (e'_v (v_bit (bl, 32))) = T) /\
 (is_v_err' _ = F)
End

Definition is_v_str'_def:
 (is_v_str' (e'_v (v_str x)) = T) /\
 (is_v_str' _ = F)
End

Definition to_bool_cast_exec_def:
 to_bool_cast_exec bitv =
  case oHD $ REVERSE $ FST bitv of
  | SOME bit => SOME $ v_bool bit
  | NONE => NONE
End


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
 (e_exec_unop' unop (e'_v v) = unop_exec' unop v)
  /\
 (e_exec_unop' _ _ = NONE)
End

Definition cast_exec_def:
 (cast_exec (cast_unsigned n) (v_bit bitv) = SOME (v_bit $ bitv_cast n bitv))
 /\
 (cast_exec (cast_unsigned n) (v_bool b) = SOME (v_bit $ bool_cast n b))
 /\
 (cast_exec cast_bool (v_bit bitv) = to_bool_cast_exec bitv)
 /\
 (cast_exec _ _ = NONE)
End

Definition e_exec_cast'_def:
 (e_exec_cast' (cast_unsigned n) (e'_v v) = cast_exec (cast_unsigned n) v)
  /\
 (e_exec_cast' (cast_bool) (e'_v v) = cast_exec (cast_bool) v)
  /\
 (e_exec_cast' _ _ = NONE)
End

(** binops **)
(* Translation: dimword (:a) to (v2n (REPLICATE (LENGTH a) T) + 1)
 * UINT_MAXw to above minus 1 *)

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
 (e_exec_binop' (e'_v v1) binop (e'_v v2) = binop_exec' binop v1 v2)
  /\
 (e_exec_binop' _ _ _ = NONE)
End

Definition e_exec_short_circuit'_def:
 (e_exec_short_circuit' (v_bool T) binop_bin_and e = SOME e)
  /\
 (e_exec_short_circuit' (v_bool F) binop_bin_and e = SOME (e'_v (v_bool F)))
  /\
 (e_exec_short_circuit' (v_bool T) binop_bin_or e = SOME (e'_v (v_bool T)))
  /\
 (e_exec_short_circuit' (v_bool F) binop_bin_or e = SOME e)
  /\
 (e_exec_short_circuit' _ _ _ = NONE)
End

(* Field access *)
Definition e_exec_acc'_def:
 (e_exec_acc' (e'_acc (e'_v (v_struct f_v_list)) f) =
  case ALOOKUP f_v_list f of
  | SOME v => SOME (e'_v v)
  | NONE => NONE)
  /\
 (e_exec_acc' (e'_acc (e'_v (v_header boolv f_v_list)) f) =
  case ALOOKUP f_v_list f of
  | SOME v => SOME (e'_v v)
  | NONE => NONE)
  /\
 (e_exec_acc' _ = NONE)
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
 (e_exec_select' (e'_v v) s_l_x_l x =
  case v of
  | v_struct x_v_l =>
   (case match_all_first (SND $ UNZIP x_v_l) s_l_x_l of
    | SOME x' => SOME x'
    | NONE => SOME x)
  | _ => SOME x) /\
 (e_exec_select' _ _ _ = NONE)
End

Definition e_exec_concat'_def:
 (e_exec_concat' (e'_v (v_bit bitv1)) (e'_v (v_bit bitv2)) =
  SOME (v_bit (bitv_concat bitv1 bitv2)))
  /\
 (e_exec_concat' _ _ = NONE)
End

Definition e_exec_slice'_def:
 (e_exec_slice' (e'_v (v_bit bitv1)) (e'_v (v_bit bitv2)) (e'_v (v_bit bitv3)) =
  case slice' bitv1 bitv2 bitv3 of
  | SOME bitv => SOME $ v_bit bitv
  | NONE => NONE)
  /\
 (e_exec_slice' _ _ _ = NONE)
End

(********************************)
(* Statement-related shorthands *)

Definition is_empty'_def:
 (is_empty' stmt'_empty = T) /\
 (is_empty' _ = F)
End

Definition is_empty_singleton'_def:
 (is_empty_singleton' [stmt'_empty] = T) /\
 (is_empty_singleton' _ = F)
End

Definition get_ret_v'_def:
 (get_ret_v' (stmt'_ret (e'_v v)) = SOME v) /\
 (get_ret_v' (stmt'_seq (stmt'_ret (e'_v v)) stmt) = SOME v) /\
 (get_ret_v' _ = NONE)
End

Definition stmt_exec_ass'_def:
 (stmt_exec_ass' lval (e'_v v) ss =
  assign' ss v lval)
  /\
 (stmt_exec_ass' _ _ _ = NONE)
End

Definition stmt_exec_init'_def:
 (stmt_exec_init' varn (e'_v v) ss = initialise' ss varn v)
End

Definition stmt_exec_trans'_def:
 (stmt_exec_trans' (e'_v (v_str x)) = SOME (status_trans x))
  /\
 (stmt_exec_trans' _ = NONE)
End

Definition stmt_exec_cond'_def:
 (stmt_exec_cond' (e'_v (v_bool T)) =
  SOME T)
  /\
 (stmt_exec_cond' (e'_v (v_bool F)) =
  SOME F)
  /\
 (stmt_exec_cond' _ = NONE)
End

(************************)
(* Expression semantics *)

Definition e_state_size'_def:
 (e_state_size' ((ctx:'a e_ctx), (g_scope_list:g_scope_list'), (scope_list:scope_list'), (e:e')) = e'_size e)
End

Definition e_exec'_def:
 (********************)
 (* Variable look-up *)
 (e_exec' (ctx:'a e_ctx) (g_scope_list:g_scope_list') (scope_list:scope_list') (e'_var x) =
  case lookup_vexp2' scope_list g_scope_list x of
  | SOME v => SOME (e'_v v, [])
  | NONE => NONE)
  /\
 (******************************)
 (* Struct/header field access *)
 (e_exec' ctx g_scope_list scope_list (e'_acc e_v_struct x) =
  if is_v' e_v_struct
  then
   (case e_exec_acc' (e'_acc e_v_struct x) of
    | SOME v => SOME (v, [])
    | NONE => NONE)
   else
    (case e_exec' ctx g_scope_list scope_list e_v_struct of
     | SOME (e_v_struct', frame_list) =>
      SOME (e'_acc e_v_struct' x, frame_list)
     | NONE => NONE))
  /\
 (*********************************)
 (* Struct/header field reduction *)
 (e_exec' ctx g_scope_list scope_list (e'_struct x_e_l) =
  case unred_mem_index' (MAP_SND x_e_l) of
  | SOME i =>
   (case oEL i (MAP_SND x_e_l) of
    | SOME x_e =>
     (case e_exec' ctx g_scope_list scope_list x_e of
      | SOME (e', frame_list) => SOME (e'_struct (ZIP (MAP_FST x_e_l, (LUPDATE e' i (MAP_SND x_e_l)))), frame_list)
      | NONE => NONE)
    | NONE => NONE)
  | NONE =>
   (case vl_of_el' (MAP_SND x_e_l) of
    | SOME v_l => SOME (e'_v (v_struct (ZIP (MAP_FST x_e_l, v_l))), [])
    | NONE => NONE))
  /\
 (************************)
 (* Function/extern call *)
 (e_exec' (ext_map, func_map, b_func_map) g_scope_list scope_list (e'_call funn e_l) =
  (case lookup_funn_sig_body' funn func_map b_func_map ext_map of
    | SOME (stmt, x_d_l) =>
     if LENGTH x_d_l = LENGTH e_l
     then
      (case unred_arg_index' (MAP SND x_d_l) e_l of
       | SOME i =>
        (case oEL i e_l of
         | SOME elem =>
          (case e_exec' (ext_map, func_map, b_func_map) g_scope_list scope_list elem of
           | SOME (e', frame_list) => SOME (e'_call funn (LUPDATE e' i e_l), frame_list)
           | NONE => NONE)
         | NONE => NONE)
       | NONE =>
        (case copyin' (MAP FST x_d_l) (MAP SND x_d_l) e_l g_scope_list scope_list of
         | SOME scope => 
          SOME (e'_var (varn'_star funn), [(funn, [stmt], [scope])])
         | NONE => NONE))
     else NONE
    | NONE => NONE))
  /\
 (********)
 (* Cast *)
 (e_exec' ctx g_scope_list scope_list (e'_cast cast e) =
  if is_v' e
  then
   (case e_exec_cast' cast e of
    | SOME v => SOME (e'_v v, [])
    | NONE => NONE)
  else
   (case e_exec' ctx g_scope_list scope_list e of
    | SOME (e', frame_list) => SOME (e'_cast cast e', frame_list)
    | NONE => NONE))
  /\
 (********************)
 (* Unary arithmetic *)
 (e_exec' ctx g_scope_list scope_list (e'_unop unop e) =
  if is_v' e
  then 
   (case e_exec_unop' unop e of
    | SOME v => SOME (e'_v v, [])
    | NONE => NONE)
  else
   (case e_exec' ctx g_scope_list scope_list e of
    | SOME (e', frame_list) => SOME (e'_unop unop e', frame_list)
    | NONE => NONE))
  /\
 (*********************)
 (* Binary arithmetic *)
 (e_exec' ctx g_scope_list scope_list (e'_binop e1 binop e2) =
  (case e1 of
   | (e'_v v) =>
    if is_short_circuitable binop
    then
     (case e_exec_short_circuit' v binop e2 of
      | SOME e' => SOME (e', [])
      | NONE => NONE)
    else if is_v' e2
    then
     (case e_exec_binop' e1 binop e2 of
      | SOME v' => SOME (e'_v v', [])
      | NONE => NONE)
    else
     (case e_exec' ctx g_scope_list scope_list e2 of
      | SOME (e2', frame_list) => SOME (e'_binop e1 binop e2', frame_list)
      | NONE => NONE)
   | _ =>
    (case e_exec' ctx g_scope_list scope_list e1 of
     | SOME (e1', frame_list) => SOME (e'_binop e1' binop e2, frame_list)
     | NONE => NONE)))
  /\
 (**********)
 (* Select *)
 (e_exec' ctx g_scope_list scope_list (e'_select e s_l_x_l x) =
  if is_v' e
  then
   (case e_exec_select' e s_l_x_l x of
    | SOME x' => SOME (e'_v (v_str x'), [])
    | NONE => NONE)
  else
   (case e_exec' ctx g_scope_list scope_list e of
    | SOME (e', frame_list) => SOME (e'_select e' s_l_x_l x, frame_list)
    | NONE => NONE))
  /\
 (*****************)
 (* Concatenation *)
 (e_exec' ctx g_scope_list scope_list (e'_concat e1 e2) =
  if is_v_bit' e1
  then 
   (if is_v_bit' e2
    then 
     (case e_exec_concat' e1 e2 of
      | SOME v => SOME (e'_v v, [])
      | NONE => NONE)
    else
     (case e_exec' ctx g_scope_list scope_list e2 of
      | SOME (e2', frame_list) => SOME (e'_concat e1 e2', frame_list)
      | NONE => NONE))
  else
   (case e_exec' ctx g_scope_list scope_list e1 of
    | SOME (e1', frame_list) => SOME (e'_concat e1' e2, frame_list)
    | NONE => NONE))
  /\
 (***********)
 (* Slicing *)
 (e_exec' ctx g_scope_list scope_list (e'_slice e1 e2 e3) =
  if (is_v_bit' e2 /\ is_v_bit' e3)
  then
   (if is_v_bit' e1
    then 
     (case e_exec_slice' e1 e2 e3 of
      | SOME v => SOME (e'_v v, [])
      | NONE => NONE)
    else
     (case e_exec' ctx g_scope_list scope_list e1 of
      | SOME (e1', frame_list) => SOME (e'_slice e1' e2 e3, frame_list)
      | NONE => NONE))
   else NONE)
  /\
 (e_exec' _ _ _ _ = NONE)
Termination
cheat
(*
WF_REL_TAC `measure e_state_size'` \\
fs [e_state_size'_def, e'_size_def, MAP_SND_EQ, listTheory.oEL_EQ_EL] \\
REPEAT STRIP_TAC >| [
  IMP_RES_TAC unred_arg_index_in_range \\
  IMP_RES_TAC rich_listTheory.EL_MEM \\
  IMP_RES_TAC e3_size_mem \\
  fs [],

  IMP_RES_TAC unred_mem_index_in_range \\
  IMP_RES_TAC rich_listTheory.EL_MEM \\
  `e'_size (EL i (MAP SND x_e_l)) < e1_size x_e_l` suffices_by (
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
*)
End

(******************************************)
(* Statement-related function definitions *)


(* Same as regular state, but doesn't clash with state in semanticPrimitivesTheory *)
Type state' = “:('a # g_scope_list' # frame_list' # status)”

Definition get_e_ctx_def:
 get_e_ctx ((apply_table_f, ext_map, func_map, b_func_map, pars_map, tbl_map):'a ctx') = (ext_map, func_map, b_func_map)
End

Definition is_consts_exec'_def:
 (is_consts_exec' [] = T) /\
 (is_consts_exec' (h::t) = ((is_const' h) /\ (is_consts_exec' t)))
End

Definition stmt_exec'_def:
 (******************************************)
 (* Catch-all clauses for special statuses *)
 (stmt_exec' (ctx:'a ctx') ((ascope:'a, g_scope_list:g_scope_list', frame_list:frame_list', status_returnv v):'a state') = NONE)
  /\
 (stmt_exec' _ (_, _, _, status_trans x) = NONE)
  /\
 (* Empty frame list *)
 (stmt_exec' _ (_, _, [], _) = NONE)
  /\
 (* Empty scope stack *)
 (stmt_exec' _ (_, _, [(funn, stmt_stack, [])], _) = NONE)
  /\
 (**************)
 (* Assignment *)
 (stmt_exec' ctx (ascope, g_scope_list, [(funn, [stmt'_ass lval e], scope_list)], status_running) =
  if is_v' e
  then
   (case stmt_exec_ass' lval e (scope_list++g_scope_list) of
    | SOME scope_list'' =>
     (case separate scope_list'' of
      | (SOME g_scope_list', SOME scope_list') =>
       SOME (ascope, g_scope_list', [(funn, [stmt'_empty], scope_list')], status_running)
      | _ => NONE)
    | NONE => NONE)
  else
   (case e_exec' (get_e_ctx ctx) g_scope_list scope_list e of
    | SOME (e', frame_list) =>
     SOME (ascope, g_scope_list, frame_list++[(funn, [stmt'_ass lval e'], scope_list)], status_running)
    | _ => NONE))
  /\
 (**************)
 (* Transition *)
 (stmt_exec' ctx (ascope, g_scope_list, [(funn, [stmt'_trans e], scope_list)], status_running) =
  if is_v' e
  then
   if is_v_str' e
   then
    (case stmt_exec_trans' e of
     | SOME status' => SOME (ascope, g_scope_list, [(funn, [stmt'_empty], scope_list)], status')
     | NONE => NONE)
    else NONE
  else
   (case e_exec' (get_e_ctx ctx) g_scope_list scope_list e of
    | SOME (e', frame_list) =>
     SOME (ascope, g_scope_list, frame_list++[(funn, [stmt'_trans e'], scope_list)], status_running)
    | NONE => NONE))
  /\
 (***************)
 (* Conditional *)
 (stmt_exec' ctx (ascope, g_scope_list, [(funn, [stmt'_cond e stmt1 stmt2], scope_list)], status_running) =
  (* TODO: Make this more efficient by using a single get_v_bool e *)
  if is_v_bool' e
  then
   (case stmt_exec_cond' e of
    | SOME T => SOME (ascope, g_scope_list, [(funn, [stmt1], scope_list)], status_running)
    | SOME F => SOME (ascope, g_scope_list, [(funn, [stmt2], scope_list)], status_running)
    | NONE => NONE)
  else
   (case e_exec' (get_e_ctx ctx) g_scope_list scope_list e of
    | SOME (e', frame_list) =>
     SOME (ascope, g_scope_list, frame_list++[(funn, [stmt'_cond e' stmt1 stmt2], scope_list)], status_running)
    | NONE => NONE))
  /\
 (*********************)
 (* Table application *)
 (stmt_exec' (apply_table_f, ext_map, func_map, b_func_map, pars_map, tbl_map) (ascope, g_scope_list, [(funn, [stmt'_app t_name e_l], scope_list)], status_running) =
  (case index_not_const' e_l of
   | SOME i =>
    (case oEL i e_l of
     | SOME elem =>
      (case e_exec' (ext_map, func_map, b_func_map) g_scope_list scope_list elem of
       | SOME (e', frame_list) =>
        SOME (ascope, g_scope_list, frame_list++[(funn, [stmt'_app t_name (LUPDATE e' i e_l)], scope_list)], status_running)
       | NONE => NONE)
     | NONE => NONE)
   | NONE =>
    (case ALOOKUP tbl_map t_name of
     | SOME (mk_l, (default_f, default_f_args)) =>
      (if LENGTH mk_l = LENGTH e_l
       then
        (case apply_table_f (t_name, e_l, mk_l, (default_f, default_f_args), ascope) of
         | SOME (f, f_args) =>
          (if is_consts_exec' f_args
           then
            SOME (ascope, g_scope_list, [(funn, [stmt'_ass lval'_null (e'_call (funn_name f) f_args)], scope_list)], status_running)
           else NONE)
         | NONE => NONE)
       else NONE)
     | NONE => NONE)))
  /\
 (**********)
 (* Return *)
 (stmt_exec' ctx (ascope, g_scope_list, [(funn, [stmt'_ret e], scope_list)], status_running) =
  (case get_v' e of
   | SOME v => SOME (ascope, g_scope_list, [(funn, [stmt'_empty], scope_list)], status_returnv v)
   | NONE => 
    (case e_exec' (get_e_ctx ctx) g_scope_list scope_list e of
     | SOME (e', frame_list) =>
      SOME (ascope, g_scope_list, frame_list++[(funn, [stmt'_ret e'], scope_list)], status_running)
     | NONE => NONE)))
  /\
 (**********)
 (* Extern *)
 (stmt_exec' (apply_table_f, ext_map, func_map, b_func_map, pars_map, tbl_map) (ascope, g_scope_list, [(funn, [stmt'_ext], scope_list)], status_running) =
  (case lookup_ext_fun' funn ext_map of
   | SOME ext_fun =>
    (case ext_fun (ascope, g_scope_list, scope_list) of
     | SOME (ascope', scope_list', status') =>
      SOME (ascope', g_scope_list, [(funn, [stmt'_empty], scope_list')], status')
     | NONE => NONE)
   | NONE => NONE))
  /\
 (*********)
 (* Block *)
 (stmt_exec' ctx (ascope, g_scope_list, [(funn, [stmt'_block decl_list stmt], scope_list)], status_running) =
   SOME (ascope, g_scope_list, [(funn, [stmt]++[stmt'_empty], ((declare_list_in_fresh_scope' decl_list)::scope_list))], status_running))
  /\
 (************)
 (* Sequence *)
 (stmt_exec' ctx (ascope, g_scope_list, [(funn, [stmt'_seq stmt1 stmt2], scope_list)], status_running) =
  if is_empty' stmt1
  then SOME (ascope, g_scope_list, [(funn, [stmt2], scope_list)], status_running)
  else
   (* Note: this only allows for 0 or 1 frame being added, or (exclusively) 1 stmt element *)
   (case stmt_exec' ctx (ascope, g_scope_list, [(funn, [stmt1], scope_list)], status_running) of
    | SOME (ascope', g_scope_list', [(funn, [stmt1'], scope_list')], status') =>
     (case status' of 
      | status_running =>
       SOME (ascope', g_scope_list', [(funn, [stmt'_seq stmt1' stmt2], scope_list')], status_running)
      | _ =>
       SOME (ascope', g_scope_list', [(funn, [stmt1'], scope_list')], status'))
    | SOME (ascope', g_scope_list', [(funn, stmt1''::[stmt1'], scope_list')], status_running) =>
     SOME (ascope', g_scope_list', [(funn, [stmt1'']++[stmt'_seq stmt1' stmt2], scope_list')], status_running)
    | SOME (ascope', g_scope_list', (frame::[(funn, [stmt1'], scope_list')]), status_running) =>
     SOME (ascope', g_scope_list', (frame::[(funn, [stmt'_seq stmt1' stmt2], scope_list')]), status_running)
    | _ => NONE))
  /\
 (*********************)
 (* Stmt stack clause *)
 (*********************)
 (* TODO: Should the case statement be handled by better matching in the clause? *)
 (stmt_exec' ctx (ascope, g_scope_list, [(funn, stmt'_empty::stmt_stack, scope_list)], status) =
  case stmt_stack of
  | [] => NONE
  | _ =>
   (case scope_list of
    | [] => NONE
    | (h_scope::scope_list') => SOME (ascope, g_scope_list, [(funn, stmt_stack, TL (h_scope::scope_list'))], status)))
  /\
 (* TODO: This clause gets expanded into multiple clauses to account for all different
  *       statements. An alternative solution, which may be even more convoluted,
  *       could be to make mutually recursive functions *)
 (stmt_exec' ctx (ascope, g_scope_list, [(funn, stmt::stmt_stack, scope_list)], status) =
   (case stmt_exec' ctx (ascope, g_scope_list, [(funn, [stmt], scope_list)], status) of
   | SOME (ascope', g_scope_list', frame_list', status') =>
    (case frame_list' of
     (* Regular case *)
     | [(funn, [stmt'], scope_list')] =>
      SOME (ascope', g_scope_list', [(funn, stmt'::stmt_stack, scope_list')], status')
     (* Block entry *)
     | [(funn, stmt''::[stmt'], scope_list')] =>
      SOME (ascope', g_scope_list', [(funn, stmt''::(stmt'::stmt_stack), scope_list')], status')
     (* Function call *)
     | ((funn', [stmt'], scope_list')::[(funn, [stmt''], scope_list)]) =>
      SOME (ascope', g_scope_list', ((funn', [stmt'], scope_list')::[(funn, stmt''::stmt_stack, scope_list)]), status')
     (* TODO: What can happen here? *)
     | _ => NONE)
   | NONE => NONE))
  /\
 (stmt_exec' _ _ = NONE)
End

(**************************)
(*  Frame list semantics  *)
(**************************)

Definition frames_exec'_def:
 (******************************************)
 (* Catch-all clauses for special statuses *)
 (frames_exec' (ctx:'a ctx') ((ascope:'a, g_scope_list:g_scope_list', frame_list:frame_list', status_returnv v):'a state') = NONE)
  /\
 (frames_exec' _ (_, _, _, status_trans x) = NONE)
  /\
 (* Empty frame list *)
 (frames_exec' _ (_, _, [], _) = NONE)
  /\
 (*********)
 (* Comp2 + Comp1 case of multiple frames *)
 (frames_exec' (apply_table_f, ext_map, func_map, b_func_map, pars_map, tbl_map) (ascope, g_scope_list, ((funn, stmt_stack, scope_list)::((funn', stmt_stack', scope_list')::frame_list'')), status_running) =
  (case scopes_to_pass' funn func_map b_func_map g_scope_list of
   | SOME g_scope_list' =>
    (case map_to_pass' funn b_func_map of
     | SOME b_func_map' =>
      (case tbl_to_pass' funn b_func_map tbl_map of
       | SOME tbl_map' =>
        (case stmt_exec' (apply_table_f, ext_map, func_map, b_func_map', pars_map, tbl_map') (ascope, g_scope_list', [(funn, stmt_stack, scope_list)], status_running) of
         | SOME (ascope', g_scope_list'', frame_list', status') =>
          (case status' of
           | status_returnv v =>
            (* Comp2 *)
            (case frame_list' of
             | [(funn, stmt_stack'', scope_list'')] =>
              (case assign' g_scope_list'' v (lval'_varname (varn'_star funn)) of
               | SOME g_scope_list''' =>
                (case scopes_to_retrieve' funn func_map b_func_map g_scope_list g_scope_list''' of
                 | SOME g_scope_list'''' =>
                  (case lookup_funn_sig_body' funn func_map b_func_map ext_map of
                   | SOME (stmt'', x_d_l) =>
                    (case scopes_to_pass' funn' func_map b_func_map g_scope_list'''' of
                     | SOME g_scope_list''''' =>
                      (case copyout' (MAP FST x_d_l) (MAP SND x_d_l) g_scope_list''''' scope_list' scope_list'' of
                       | SOME (g_scope_list'''''', scope_list''') =>
                        (case scopes_to_retrieve' funn' func_map b_func_map g_scope_list'''' g_scope_list'''''' of
                         | SOME g_scope_list''''''' =>
                          SOME (ascope', g_scope_list''''''', ((funn', stmt_stack', scope_list''')::frame_list''), status_running)
                         | _ => NONE)
                       | _ => NONE)
                     | _ => NONE)
                   | _ => NONE)
                 | _ => NONE)
               | NONE => NONE)
             | _ => NONE)
           | _ => 
            (* Comp1 *)
            (case scopes_to_retrieve' funn func_map b_func_map g_scope_list g_scope_list'' of
             | SOME g_scope_list''' =>
              SOME (ascope', g_scope_list''', frame_list'++((funn', stmt_stack', scope_list')::frame_list''), status')
             | _ => NONE))
         | _ => NONE)
       | _ => NONE)
     | _ => NONE)
   | _ => NONE))
  /\
 (*********)
 (* Comp1, remaining cases *)
 (frames_exec' (apply_table_f, ext_map, func_map, b_func_map, pars_map, tbl_map) (ascope, g_scope_list, [(funn, stmt_stack, scope_list)], status_running) =
  (case scopes_to_pass' funn func_map b_func_map g_scope_list of
   | SOME g_scope_list' =>
    (case map_to_pass' funn b_func_map of
     | SOME b_func_map' =>
      (case tbl_to_pass' funn b_func_map tbl_map of
       | SOME tbl_map' =>
        (case stmt_exec' (apply_table_f, ext_map, func_map, b_func_map', pars_map, tbl_map') (ascope, g_scope_list', [(funn, stmt_stack, scope_list)], status_running) of
         | SOME (ascope', g_scope_list'', frame_list', status') =>
          (case scopes_to_retrieve' funn func_map b_func_map g_scope_list g_scope_list'' of
           | SOME g_scope_list''' =>
            SOME (ascope', g_scope_list''', frame_list', status')
           | _ => NONE)
         | _ => NONE)
       | _ => NONE)
     | _ => NONE)
   | _ => NONE))
 /\
 (frames_exec' _ _ = NONE)
End

(***********************************)
(*  Architectural-level semantics  *)
(***********************************)

Definition state_fin_exec_def:
 state_fin_exec status (frame_list:frame_list') =
  case frame_list of
  | [(funn, [stmt'_empty], scope_list)] =>
   (case status of
    | status_trans x =>
     if x = "accept" \/ x = "reject"
     then T
     else F
    | _ => T)
  | _ =>
   (case status of
    | status_returnv v => T
    | status_trans x =>
     if x = "accept" \/ x = "reject"
     then T
     else F
    | _ => F)
End

(* TODO: Outsource the stuff that causes too many case splits to other functions
 *       i.e. exec_arch_e, exec_arch_update_return_frame, exec_arch_assign, ... *)
Definition arch_exec'_def:
 (arch_exec' ((ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map):'a actx')
            (((i, in_out_list, in_out_list', scope):'a aenv), g_scope_list:g_scope_list', arch_frame_list'_regular frame_list, status:status) =
  (case oEL i ab_list of
   | SOME (arch_block'_pbl x e_l) =>
    (case ALOOKUP pblock_map x of
     | SOME (pbl_type, x_d_list, b_func_map, decl_list, pars_map, tbl_map) =>
      if state_fin_exec status frame_list
      then
       (case lookup_block_body' x b_func_map of
        | SOME stmt =>
         (* TODO: The below LENGTH check is only used for proofs (e.g. soundness proof) *)
         (if LENGTH e_l = LENGTH x_d_list
          then
           (* pbl_ret *)
           (* TODO: OK to only copy out from block-global scope here? *)
           (case copyout_pbl (g_scope_list, scope, MAP SND x_d_list, MAP FST x_d_list, set_fin_status pbl_type status) of
            | SOME scope' =>
             (case oLASTN 1 g_scope_list of
              | SOME g_scope_sing =>
               SOME ((i+1, in_out_list, in_out_list', scope'), g_scope_sing,
                     arch_frame_list'_empty, status_running)
              | NONE => NONE)
            | _ => NONE)
          else NONE)
        | NONE => NONE)
      else
       (case status of
        | status_trans x' =>
         (* parser_trans *)
         (case pbl_type of
          | pbl_type_parser =>
           (case ALOOKUP pars_map x' of
            | SOME stmt' =>
             SOME ((i, in_out_list, in_out_list', scope), g_scope_list, (arch_frame_list'_regular [(funn_name x', [stmt'], [ [] ])]), status_running)
            | _ => NONE)
          | _ => NONE)
        | status_running =>
         (* pbl_exec *)
         (case frames_exec' (apply_table_f, ext_map, func_map, b_func_map, pars_map, tbl_map) (scope, g_scope_list, frame_list, status) of
          | SOME (scope', g_scope_list', frame_list', status') =>
           SOME ((i, in_out_list, in_out_list', scope'), g_scope_list', (arch_frame_list'_regular frame_list'), status')
          | _ => NONE)
        | _ => NONE)
     | _ => NONE)
   | _ => NONE)
 )
 /\
 (arch_exec' (ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map)
            ((i, in_out_list, in_out_list', scope), g_scope_list,
             arch_frame_list'_empty, status_running) =
  (case oEL i ab_list of
   (* in *)
   | SOME arch_block'_inp =>
    (case input_f (in_out_list, scope) of
     | SOME (in_out_list'', scope') => 
      SOME ((i+1, in_out_list'', in_out_list', scope'), g_scope_list, arch_frame_list'_empty,
             status_running)
     | NONE => NONE)
   | SOME (arch_block'_pbl x e_l) =>
    (case ALOOKUP pblock_map x of
     (* pbl_init *)
     | SOME (pbl_type, x_d_list, b_func_map, decl_list, pars_map, tbl_map) =>
      (case lookup_block_body x b_func_map of
       | SOME stmt =>
        (* TODO: The below LENGTH check is only used for proofs (e.g. soundness proof) *)
        (if LENGTH e_l = LENGTH x_d_list
         then
          (case copyin_pbl ((MAP FST x_d_list), (MAP SND x_d_list), e_l, scope) of
           | SOME scope' =>
            (case oLASTN 1 g_scope_list of
             | SOME [g_scope] =>
              let g_scope_list' = ([declare_list_in_scope' (decl_list, scope')]++[g_scope]) in
               (case initialise_var_stars' func_map b_func_map ext_map g_scope_list' of
                | SOME g_scope_list'' =>
                 SOME ((i, in_out_list, in_out_list', scope), g_scope_list'',
                       arch_frame_list'_regular [(funn_name x, [stmt], [ [] ])], status_running)
                | NONE => NONE)
             | _ => NONE)
           | _ => NONE)
         else NONE)
       | NONE => NONE)
     | _ => NONE)
   (* ffbl *)
   | SOME (arch_block'_ffbl x) =>
    (case ALOOKUP ffblock_map x of
     | SOME (ffblock_ff ff) =>
      (case ff scope of
       | SOME scope' =>
        SOME ((i+1, in_out_list, in_out_list', scope'), g_scope_list, arch_frame_list'_empty, status_running)
       | NONE => NONE)
     | NONE => NONE)
   (* out *)
   | SOME arch_block'_out =>
    (case output_f (in_out_list', scope) of
     | SOME (in_out_list'', scope') =>
      SOME ((0, in_out_list, in_out_list'', scope'), g_scope_list, arch_frame_list'_empty,
            status_running)
     | NONE => NONE)
   | NONE => NONE
  )
 )
/\
(arch_exec' _ _ = NONE)
End

(* Fuel-powered multi-step architectural-level executable semantics *)
Definition arch_multi_exec'_def:
 (arch_multi_exec' actx ((aenv, g_scope_list, arch_frame_list, status):'a astate') 0 =
  SOME (aenv, g_scope_list, arch_frame_list, status))
  /\
 (arch_multi_exec' actx (aenv, g_scope_list, arch_frame_list, status) (SUC fuel) =
  case arch_exec' actx (aenv, g_scope_list, arch_frame_list, status) of
  | SOME (aenv', g_scope_list', arch_frame_list', status') =>
   arch_multi_exec' actx (aenv', g_scope_list', arch_frame_list', status') fuel
  | NONE => SOME (aenv, g_scope_list, arch_frame_list, status))
End

val _ = export_theory ();
