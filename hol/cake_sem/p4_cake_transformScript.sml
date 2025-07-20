open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_cake_transform";

open p4Syntax;
open bitstringSyntax numSyntax pairSyntax;
open p4Theory p4_auxTheory p4_cake_auxTheory p4_cake_exec_semTheory;
open p4_cake_auxLib;
open p4_coreTheory;
open p4_v1modelTheory;

open p4_cake_archTheory;
open p4_cake_arch_v1modelTheory;
open p4_cake_arch_ebpfTheory;

(* This file contains facilities to transform HOL4P4 programs from their regular representation to
 * a CakeML-friendly representation *)

Theorem e1_e3_size:
!xel el.
el = MAP SND xel ==>
e3_size el <= e1_size xel
Proof
Induct >- (
 gs[e_size_def]
) >>
rpt strip_tac >>
Cases_on ‘el’ >> (
 gs[e_size_def]
) >>
subgoal ‘?x e. h = (x,e)’ >- (
 Cases_on ‘h’ >>
 gs[]
) >>
gvs[] >>
ASSUME_TAC $ Q.SPECL [‘x’, ‘e’] e_e2_size_less >>
DECIDE_TAC
QED

(** Adding strings from an actx **)

(* TODO: How should this be handled? Needs the type operator from theory... *)
val new_dict_entry =
 if identifier = “:string”
 then “string:string”
 else if wordsSyntax.is_word_type identifier
 then “(n2w $ LENGTH (dict:(string # identifier) list)):identifier”
 else raise (mk_HOL_ERR "p4_cake_transformScript" "new_dict_entry" ("identifier type not supported:"^(type_to_string identifier)));

Definition add_string_def:
 add_string string (dict: (string, identifier) alist) =
  if IS_NONE $ ALOOKUP dict string
  then p4$AUPDATE dict (string, ^new_dict_entry)
  else dict
End

Definition add_varnames_funn_def:
 add_varnames_funn (dict: (string, identifier) alist) funn =
  case funn of
    funn_name name =>
   add_string name dict
  | funn_inst ext_name =>
   add_string ext_name dict
  | funn_ext ext_name extfun_name =>
   add_string ext_name $
   add_string extfun_name dict
End

Definition add_varnames_varn_def:
 add_varnames_varn (dict: (string, identifier) alist) varn =
  case varn of
    varn_name name =>
   add_string name dict
  | varn_star funn => add_varnames_funn dict funn
End

Definition add_varnames_v_def:
 add_varnames_v dict v =
  case v of
    v_bool boolv => dict
  | v_bit bitv => dict
  | v_str x => dict
  | v_struct x_v_list =>
   (case x_v_list of
    | ((x,v')::t) => add_varnames_v (add_string x $ add_varnames_v dict v') (v_struct t)
    | [] => dict)
  | v_header boolv x_v_list =>
   (case x_v_list of
    | ((x,v')::t) => add_varnames_v (add_string x $ add_varnames_v dict v') (v_header boolv t)
    | [] => dict)
  | v_ext_ref i => dict
  | v_bot => dict
End

Definition add_varnames_s_def:
 add_varnames_s s dict =
  case s of
    s_sing v => add_varnames_v dict v
  | s_range bitv bitv' => dict
  | s_mask bitv bitv' => dict
  | s_univ => dict
End

Definition add_varnames_s_list_def:
 (add_varnames_s_list [] dict = dict) /\
 (add_varnames_s_list (h::t) dict =
  add_varnames_s_list t (add_varnames_s h dict))
End

Definition add_varnames_e_def:
 add_varnames_e dict e =
  case e of
    e_v v => add_varnames_v dict v
  | e_var varn =>
   add_varnames_varn dict varn
  | e_list el =>
   (case el of
    | (h::t) =>
     add_varnames_e (add_varnames_e dict h) (e_list t)
    | [] => dict)
  | e_acc e x =>
   add_string x $ add_varnames_e dict e
  | e_unop unop e =>
   add_varnames_e dict e
  | e_cast cast e =>
   add_varnames_e dict e
  | e_binop e1 binop e2 =>
   add_varnames_e (add_varnames_e dict e1) e2
  | e_concat e1 e2 =>
   add_varnames_e (add_varnames_e dict e1) e2
  | e_slice e1 e2 e3 =>
   add_varnames_e (add_varnames_e (add_varnames_e dict e3) e2) e1
  | e_call funn el =>
   (case el of
    | (h::t) =>
     add_varnames_e (add_varnames_e dict h) (e_call funn t)
    | [] => add_varnames_funn dict funn)
  | e_select e s_list_x_list x =>
   (case s_list_x_list of
    | ((s_list, x')::t) =>
     add_varnames_e (add_string x' $ add_varnames_s_list s_list dict) (e_select e t x)
    | [] => add_string x $ add_varnames_e dict e)
  | e_struct x_e_list =>
   (case x_e_list of
    | ((x,e)::t) =>
     add_varnames_e (add_string x $ add_varnames_e dict e) (e_struct t)
    | [] => dict)
  | e_header validity x_e_list =>
   (case x_e_list of
    | ((x,e)::t) =>
     add_varnames_e (add_string x $ add_varnames_e dict e) (e_header validity t)
    | [] => dict)
End

Definition add_varnames_arch_block_def:
 add_varnames_arch_block arch_block dict =
  case arch_block of
    arch_block_inp => dict
  | arch_block_pbl x el =>
   add_string x $ add_varnames_e dict (e_list el)
  | arch_block_ffbl x => add_string x dict
  | arch_block_out => dict
End

Definition add_varnames_ab_list_def:
 add_varnames_ab_list ab_list dict =
  FOLDR add_varnames_arch_block dict ab_list
End

Definition add_varnames_arg_def:
 add_varnames_arg (string, d) dict =
  if IS_NONE $ ALOOKUP dict string
  then p4$AUPDATE dict (string, ^new_dict_entry)
  else dict
End

Definition add_varnames_args_def:
 add_varnames_args args dict =
  FOLDR add_varnames_arg dict args
End

Definition add_varnames_lval_def:
 add_varnames_lval lval dict =
  case lval of
    lval_varname varn =>
   add_varnames_varn dict varn
  | lval_null => dict
  | lval_field lval' x =>
   add_varnames_lval lval' (add_string x dict)
  | lval_slice lval' e1 e2 =>
   add_varnames_lval lval' $ add_varnames_e (add_varnames_e dict e1) e2
  | lval_paren lval' =>
   add_varnames_lval lval' dict
End

Definition add_varnames_tau_def:
 add_varnames_tau dict tau =
  case tau of
    tau_bool => dict
  | tau_bit num_exp => dict
  | tau_bot => dict
  | tau_xtl struct_ty x_tau_list =>
   (case x_tau_list of
    | ((x,tau')::t) => 
     add_varnames_tau (add_varnames_tau (add_string x dict) tau') (tau_xtl struct_ty t)
    | [] => dict)
  | tau_ext => dict
End

Definition add_varnames_t_scope_def:
 add_varnames_t_scope (varn, (tau, lval_opt)) dict =
  let dict' = add_varnames_varn dict varn in
  let dict'' = add_varnames_tau dict tau in
  (case lval_opt of
     SOME lval =>
    add_varnames_lval lval dict''
   | NONE => dict'')
End

Definition add_varnames_t_scope_list_def:
 add_varnames_t_scope_list (t_scope_list:t_scope) dict =
  FOLDR add_varnames_t_scope dict t_scope_list
End

Definition add_varnames_stmt_def:
 add_varnames_stmt stmt dict =
  case stmt of
    stmt_empty => dict
  | stmt_ass lval e =>
   add_varnames_lval lval $ add_varnames_e dict e
  | stmt_cond e stmt1 stmt2 =>
   add_varnames_stmt stmt1 $ add_varnames_stmt stmt2 $ add_varnames_e dict e
  | stmt_block t_scope stmt =>
   add_varnames_stmt stmt $ add_varnames_t_scope_list t_scope dict
  | stmt_ret e =>
   add_varnames_e dict e
  | stmt_seq stmt1 stmt2 =>
   add_varnames_stmt stmt1 $ add_varnames_stmt stmt2 dict
  | stmt_trans e =>
   add_varnames_e dict e
  | stmt_app x el =>
   add_string x $ add_varnames_e dict (e_list el)
  | stmt_ext => dict
End

Definition add_varnames_func_def:
 add_varnames_func (x, (body, args)) dict =
  add_string x $ add_varnames_stmt body $ add_varnames_args args dict
End

Definition add_varnames_func_map_def:
 add_varnames_func_map (func_map:func_map) dict =
  FOLDR add_varnames_func dict func_map
End

Definition add_varnames_tbl_def:
 add_varnames_tbl (x1, (mkl, (x2, el))) dict =
  add_string x1 $
  add_string x2 $
  add_varnames_e dict (e_list el)
End

Definition add_varnames_tbl_map_def:
 add_varnames_tbl_map (tbl_map:tbl_map) dict =
  FOLDR add_varnames_tbl dict tbl_map
End

Definition add_varnames_pars_state_def:
 add_varnames_pars_state (x, body) dict =
  add_string x $ add_varnames_stmt body dict
End

Definition add_varnames_pars_map_def:
 add_varnames_pars_map (pars_map:pars_map) dict =
  FOLDR add_varnames_pars_state dict pars_map
End

Definition add_varnames_pblock_def:
 add_varnames_pblock (x, (pbl_type, x_d_l, b_func_map, t_scope, pars_map, tbl_map):pblock) dict =
  add_string x $
  add_varnames_args x_d_l $
  add_varnames_func_map b_func_map $
  add_varnames_t_scope_list t_scope $
  add_varnames_pars_map pars_map $
  add_varnames_tbl_map tbl_map dict
End

Definition add_varnames_pblock_map_def:
 add_varnames_pblock_map (pblock_map:pblock_map) dict =
  FOLDR add_varnames_pblock dict pblock_map
End

Definition add_varnames_ffblock_def:
 add_varnames_ffblock (x, ffblock) dict =
  add_string x dict
End

Definition add_varnames_ffblock_map_def:
 add_varnames_ffblock_map (ffblock_map:'a ffblock_map) dict =
  FOLDR add_varnames_ffblock dict ffblock_map
End

Definition add_varnames_actx_def:
 add_varnames_actx dict ((ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map):'a actx) =
  add_varnames_ab_list ab_list $
  add_varnames_pblock_map pblock_map $
  add_varnames_ffblock_map ffblock_map $
  (* Note: Variable names from ext map should already be included in dict *)
  add_varnames_func_map func_map dict
End


(** Transforming an actx to an actx' **)

Definition transform_funn_def:
 transform_funn dict funn =
  case funn of
    funn_name name =>
   ALOOKUP dict name >>= \word. SOME $ funn'_name word
  | funn_inst ext_obj_name =>
   ALOOKUP dict ext_obj_name >>= \word. 
   SOME $ funn'_inst word
  | funn_ext ext_obj_name func_name =>
   ALOOKUP dict ext_obj_name >>= \word.
   ALOOKUP dict func_name >>= \word'. 
   SOME $ funn'_ext word word'
End

Definition transform_varn_def:
 transform_varn dict varn =
  case varn of
    varn_name name =>
   ALOOKUP dict name >>= \word. SOME $ varn'_name word
  | varn_star funn =>
   transform_funn dict funn >>=
   \funn'. SOME $ varn'_star funn'
End

(* TODO: oMAP??? Make better *)
Definition oFOLDR_def:
 (oFOLDR f []     = SOME []) /\
 (oFOLDR f (h::t) =
  f h >>=
  \res. oFOLDR f t >>=
  \res_list. SOME $ res::res_list)
End

Definition oFOLDL_def:
 (oFOLDL f e []     = SOME e) /\
 (oFOLDL f e (h::t) =
  f h >>=
  \res. oFOLDL f (res::e) t)
End

Definition transform_string_list_def:
 (transform_string_list dict []     acc = SOME acc) /\
 (transform_string_list dict (h::t) acc =
  let res_opt = ALOOKUP dict h in
  case res_opt of
    SOME w =>
   transform_string_list dict t (w::acc)
  | NONE => NONE)
End

Definition transform_v_def:
 (transform_v dict v =
  case v of
    v_bool boolv => SOME $ v'_bool boolv
  | v_bit bitv => SOME $ v'_bit bitv
  | v_str x =>
   ALOOKUP dict x >>= \word.
   SOME $ v'_str word
  | v_struct x_v_list =>
   (* Note: Recursing like this is infinitely faster than unzipping x_v_list and
    * transforming each list separately *)
   (case x_v_list of
    | ((x,v')::t) =>
     ALOOKUP dict x >>=
     \w. transform_v dict v' >>=
     \v''.
      (case transform_v dict (v_struct t) of
       | SOME $ v'_struct t' => SOME $ v'_struct ((w, v'')::t')
       | _ => NONE)
    | [] => SOME $ v'_struct [])
  | v_header boolv x_v_list =>
   (case x_v_list of
    | ((x,v')::t) =>
     ALOOKUP dict x >>=
     \w. transform_v dict v' >>=
     \v''.
      (case transform_v dict (v_struct t) of
       | SOME $ v'_struct t' => SOME $ v'_header boolv ((w, v'')::t')
       | _ => NONE)
    | [] => SOME $ v'_header boolv [])
  | v_ext_ref i => SOME $ v'_ext_ref i
  | v_bot => SOME $ v'_bot)
End

(* Note this only permits matching with up to 128 bits *)
(* TODO: Why the tupled width? *)
val transform_s_def = Define
 (if matching_optimization
  then
   ‘transform_s dict s =
    case s of
     s_sing v =>
    (case v of
     | v_bit (bl, n) =>
      if n <= 128
      then if n <= 64
      then SOME (s'_sing $ (0w, v2w bl), n)
      else SOME (s'_sing $ (v2w $ TAKE (n-64) bl, v2w $ DROP (n-64) bl), n)
      else NONE
     | _ => NONE)
   | s_range (bl1, n1) (bl2, n2) =>
    if n1 <= 128 /\ n2 <= 128
    then
     let w'1 = if n1 <= 64 then 0w else v2w $ TAKE (n1-64) bl1 in
     let w'2 = if n1 <= 64 then v2w bl1 else v2w $ DROP (n1-64) bl1 in
     let w''1 = if n2 <= 64 then 0w else v2w $ TAKE (n2-64) bl2 in
     let w''2 = if n2 <= 64 then v2w bl2 else v2w $ DROP (n2-64) bl2 in
      SOME (s'_range (w'1, w'2) (w''1, w''2), n1)
    else NONE
   | s_mask (bl1, n1) (bl2, n2) =>
    if n1 <= 128 /\ n2 <= 128
    then
     let w'1 = if n1 <= 64 then 0w else v2w $ TAKE (n1-64) bl1 in
     let w'2 = if n1 <= 64 then v2w bl1 else v2w $ DROP (n1-64) bl1 in
     let w''1 = if n2 <= 64 then 0w else v2w $ TAKE (n2-64) bl2 in
     let w''2 = if n2 <= 64 then v2w bl2 else v2w $ DROP (n2-64) bl2 in
      SOME (s'_mask (w'1, w'2) (w''1, w''2), n1)
    else NONE
   | s_univ => SOME (s'_univ, 0)’
  else
   ‘transform_s dict s =
    case s of
     s_sing v =>
    (case v of
     | v_bit (bl, n) =>
      transform_v dict v >>=
      \v'. SOME $ (s'_sing v', n)
     | _ => NONE)
   | s_range (bl1, n1) (bl2, n2) =>
    SOME $ (s'_range (bl1, n1) (bl2, n2), n1)
   | s_mask (bl1, n1) (bl2, n2) =>
    SOME $ (s'_mask (bl1, n1) (bl2, n2), n1)
   | s_univ => SOME $ (s'_univ, 0)’)
;

Definition transform_e_def:
 (transform_e dict e =
  case e of
    e_v v =>
   transform_v dict v >>=
   \v'. SOME $ e'_v v'
  | e_var varn =>
   transform_varn dict varn >>=
   \varn'. SOME $ e'_var varn'
  | e_list el =>
   (case el of
      (h::t) =>
     transform_e dict h >>=
     \e'. transform_e dict (e_list t) >>=
     \e''.
      (case e'' of
         e'_list t' => SOME $ e'_list (e'::t')
       | _ => NONE)
    | [] => SOME $ e'_list [])
  | e_acc e x =>
   transform_e dict e >>=
   \e'. ALOOKUP dict x >>= 
   \x'. SOME $ e'_acc e' x'
  | e_unop unop e =>
   transform_e dict e >>=
   \e'. SOME $ e'_unop unop e'
  | e_cast cast e =>
   transform_e dict e >>=
   \e'. SOME $ e'_cast cast e'
  | e_binop e1 binop e2 =>
   transform_e dict e1 >>=
   \e1'. transform_e dict e2 >>=
   \e2'. SOME $ e'_binop e1' binop e2'
  | e_concat e1 e2 =>
   transform_e dict e1 >>=
   \e1'. transform_e dict e2 >>=
   \e2'. SOME $ e'_concat e1' e2'
  | e_slice e1 e2 e3 =>
   transform_e dict e1 >>=
   \e1'. transform_e dict e2 >>=
   \e2'. transform_e dict e3 >>=
   \e3'. SOME $ e'_slice e1' e2' e3'
  | e_call funn el =>
    transform_funn dict funn >>= \funn'.
   (case el of
      (h::t) =>
     transform_e dict h >>=
     \e'. transform_e dict (e_list t) >>=
     \e''.
      (case e'' of
         e'_list t' => SOME $ e'_call funn' (e'::t')
       | _ => NONE)
    | [] => SOME $ e'_call funn' [])
  | e_select e s_list_x_list x =>
   let (s_list_list, x_list) = UNZIP s_list_x_list in
   transform_e dict e >>=
   \e'. (oFOLDR (oFOLDR (transform_s dict))) s_list_list >>=
   \s_n_list_list'. (oFOLDR (ALOOKUP dict)) x_list >>=
   \x_list'. ALOOKUP dict x >>=
   \x'. let (s_list_list', n_list_list) = UNZIP $ MAP UNZIP s_n_list_list' in
    SOME $ e'_select e' (ZIP (s_list_list', x_list')) x' n_list_list
  | e_struct x_e_list =>
   (case x_e_list of
      ((x,e)::t) =>
     ALOOKUP dict x >>=
     \x'. transform_e dict e >>=
     \e'. transform_e dict (e_struct t) >>=
     \e''.
      (case e'' of
         e'_struct t' => SOME $ e'_struct ((x', e')::t')
       | _ => NONE)
    | [] => SOME $ e'_struct [])
  | e_header validity x_e_list =>
   (case x_e_list of
      ((x,e)::t) =>
     ALOOKUP dict x >>=
     \x'. transform_e dict e >>=
     \e'. transform_e dict (e_header validity t) >>=
     \e''.
      (case e'' of
         e'_header validity' t' => SOME $ e'_header validity' ((x', e')::t')
       | _ => NONE)
    | [] => SOME $ e'_header validity []))
End

(* TODO: Is this the best way of handling lists of e in other dataytypes than e? *)
Definition transform_e_list_def:
 transform_e_list dict el =
  transform_e dict (e_list el) >>=
  \el'.
   case el' of
      e'_list el'' =>
     SOME el''
    | _ => NONE
End

Definition transform_arch_block_def:
 transform_arch_block dict arch_block =
  case arch_block of
    arch_block_inp => SOME arch_block'_inp
  | arch_block_pbl x el =>
   ALOOKUP dict x >>=
   \x'. transform_e_list dict el >>=
   \el'. SOME $ arch_block'_pbl x' el'
  | arch_block_ffbl x =>
   ALOOKUP dict x >>=
   \x'. SOME $ arch_block'_ffbl x'
  | arch_block_out =>
   SOME arch_block'_out
End

Definition transform_ab_list_def:
 transform_ab_list dict ab_list =
  oFOLDR (transform_arch_block dict) ab_list
End

Definition transform_lval_def:
 transform_lval dict lval =
  case lval of
    lval_varname varn =>
   transform_varn dict varn >>=
   \varn'. SOME $ lval'_varname varn'
  | lval_null => SOME $ lval'_null
  | lval_field lval' x =>
   transform_lval dict lval' >>=
   \lval''. ALOOKUP dict x >>=
   \word. SOME $ lval'_field lval'' word
  | lval_slice lval' e1 e2 =>
   transform_lval dict lval' >>=
   \lval''. transform_e dict e1 >>=
   \e1'. transform_e dict e2 >>=
   \e2'. SOME $ lval'_slice lval'' e1' e2'
  | lval_paren lval' =>
   transform_lval dict lval' >>=
   \lval''. SOME $ lval'_paren lval''
End

Definition transform_tau_def:
 (transform_tau dict tau =
  case tau of
     tau_bool => SOME $ tau'_bool 
   | tau_bit num_exp => SOME $ tau'_bit num_exp
   | tau_bot => SOME $ tau'_bot
   | tau_xtl struct_ty x_tau_list =>
    (case x_tau_list of
      ((x,tau')::t) =>
     ALOOKUP dict x >>=
     \x'. transform_tau dict tau' >>=
     \tau''.
      (case transform_tau dict (tau_xtl struct_ty t) of
         SOME $ tau'_xtl struct_ty' t' =>
         SOME $ tau'_xtl struct_ty' ((x', tau'')::t')
       | _ => NONE)
    | [] => SOME $ tau'_xtl struct_ty [])
   | tau_ext => SOME $ tau'_ext)
End

Definition transform_t_scope_def:
 transform_t_scope dict (varn, (tau, lval_opt)) =
  transform_varn dict varn >>=
  \varn'. transform_tau dict tau >>=
  \tau'.
  (case lval_opt of
     SOME lval =>
    transform_lval dict lval >>= 
    \lval'. SOME (varn', (tau', SOME lval'))
   | NONE =>
    SOME (varn', (tau', NONE)))
End

Definition transform_t_scope_list_def:
 (transform_t_scope_list dict (t_scope_list:t_scope) =
   oFOLDR (transform_t_scope dict) t_scope_list)
End

Definition transform_stmt_def:
 transform_stmt dict stmt =
  case stmt of
    stmt_empty => SOME $ stmt'_empty
  | stmt_ass lval e =>
   transform_lval dict lval >>=
   \lval'. transform_e dict e >>=
   \e'. SOME $ stmt'_ass lval' e'
  | stmt_cond e stmt1 stmt2 =>
   transform_e dict e >>=
   \e'. transform_stmt dict stmt1 >>=
   \stmt1'. transform_stmt dict stmt2 >>=
   \stmt2'. SOME $ stmt'_cond e' stmt1' stmt2'
  | stmt_block t_scope stmt =>
   transform_t_scope_list dict t_scope >>=
   \t_scope'. transform_stmt dict stmt >>=
   \stmt'. SOME $ stmt'_block t_scope' stmt'
  | stmt_ret e =>
   transform_e dict e >>=
   \e'. SOME $ stmt'_ret e'
  | stmt_seq stmt1 stmt2 =>
   transform_stmt dict stmt1 >>=
   \stmt1'. transform_stmt dict stmt2 >>=
   \stmt2'. SOME $ stmt'_seq stmt1' stmt2'
  | stmt_trans e =>
   transform_e dict e >>=
   \e'. SOME $ stmt'_trans e'
  | stmt_app x el =>
   ALOOKUP dict x >>=
   \w. transform_e_list dict el >>=
   \el'. SOME $ stmt'_app w el'
  | stmt_ext => SOME stmt'_ext
End

Definition transform_arg_def:
 transform_arg dict (x,d) =
  ALOOKUP dict x >>= \word. SOME (word, d)
End

Definition transform_args_def:
 (transform_args dict args =
   oFOLDR (transform_arg dict) args)
End

Definition transform_func_def:
 transform_func dict (x, (body, args)) =
  ALOOKUP dict x >>=
  \x'. transform_stmt dict body >>=
  \body'. transform_args dict args >>=
  \args. SOME (x', (body', args))
End

Definition transform_func_map_def:
 (transform_func_map dict (func_map:func_map) =
   (oFOLDR (transform_func dict) func_map):func_map' option)
End

Definition transform_tbl_def:
 transform_tbl dict (x1, (mkl, (x2, el))) =
  ALOOKUP dict x1 >>=
  \w. ALOOKUP dict x2 >>=
  \w'. transform_e_list dict el >>=
  \el'. SOME (w, (mkl, (w', el')))
End

Definition transform_tbl_map_def:
 (transform_tbl_map dict (tbl_map:tbl_map) =
  (oFOLDR (transform_tbl dict) tbl_map):tbl_map' option)
End

Definition transform_pars_state_def:
 transform_pars_state dict (x, body) =
  ALOOKUP dict x >>=
  \w. transform_stmt dict body >>=
  \body'. SOME (w, body')
End

Definition transform_pars_map_def:
 (transform_pars_map dict (pars_map:pars_map) =
  (oFOLDR (transform_pars_state dict) pars_map):pars_map' option)
End

Definition transform_pblock_def:
 transform_pblock dict (x, (pbl_type, x_d_l, b_func_map, t_scope, pars_map, tbl_map):pblock) =
  ALOOKUP dict x >>=
  \w. transform_args dict x_d_l >>=
  \args'. transform_func_map dict b_func_map >>=
  \b_func_map'. transform_t_scope_list dict t_scope >>=
  \t_scope'. transform_pars_map dict pars_map >>=
  \pars_map'. transform_tbl_map dict tbl_map >>=
  \tbl_map'. SOME (w, (pbl_type, args', b_func_map', t_scope', pars_map', tbl_map'))
End

Definition transform_pblock_map_def:
 (transform_pblock_map dict (pblock_map:pblock_map) =
  (oFOLDR (transform_pblock dict) pblock_map):pblock_map' option)
End

Definition transform_ffblock_def:
 transform_ffblock dict (x, ffblock) =
  ALOOKUP dict x >>=
  \w. SOME (w, ffblock)
End

Definition transform_ffblock_map_def:
 (transform_ffblock_map dict (ffblock_map:'a ffblock_map) =
  (oFOLDR (transform_ffblock dict) ffblock_map):'a ffblock_map' option)
End

Definition transform_ext_map_def:
 transform_ext_map dict (ext_map:v1model_ascope ext_map) =
   SOME ([(^(get_id "header"),NONE,
     [(^(get_id "isValid"),[(^(get_id "this"):identifier,d_in)],header_is_valid');
      (^(get_id "setValid"),[(^(get_id "this"),d_inout)],header_set_valid');
      (^(get_id "setInvalid"),[(^(get_id "this"),d_inout)],header_set_invalid')]);
    (^(get_id ""),NONE,
     [(^(get_id "mark_to_drop"),[(^(get_id "standard_metadata"),d_inout)],v1model_mark_to_drop');
      (^(get_id "verify"),[(^(get_id "condition"),d_in); (^(get_id "err"),d_in)],v1model_verify');

    (^(get_id "verify_checksum"),
     [(^(get_id "condition"),d_in); (^(get_id "data"),d_in); (^(get_id "checksum"),d_in); (^(get_id "algo"),d_none)],
     v1model_verify_checksum');
    (^(get_id "update_checksum"),
     [(^(get_id "condition"),d_in); (^(get_id "data"),d_in); (^(get_id "checksum"),d_inout);
      (^(get_id "algo"),d_none)],v1model_update_checksum');
    (^(get_id "assert"),[(^(get_id "check"),d_in)],v1model_assert');
    (^(get_id "assume"),[(^(get_id "check"),d_in)],v1model_assume')]);
      
    (^(get_id "packet_in"),NONE,
     [(^(get_id "extract"),[(^(get_id "this"),d_in); (^(get_id "headerLvalue"),d_out)],
       v1model_packet_in_extract');

    (^(get_id "lookahead"),[(^(get_id "this"),d_in); (^(get_id "targ1"),d_in)],v1model_packet_in_lookahead');
    (^(get_id "advance"),[(^(get_id "this"),d_in); (^(get_id "bits"),d_in)],v1model_packet_in_advance')

]);
    (^(get_id "packet_out"),NONE,
     [(^(get_id "emit"),[(^(get_id "this"),d_in); (^(get_id "data"),d_in)],v1model_packet_out_emit')]);

  (^(get_id "direct_counter"),
   SOME ([(^(get_id "this"),d_out); (^(get_id "type"),d_none)],v1model_direct_counter_construct'),
   [(^(get_id "count"),[(^(get_id "this"),d_out)],v1model_direct_counter_count')]);
  (^(get_id "direct_meter"),
   SOME ([(^(get_id "this"),d_out); (^(get_id "type"),d_none); (^(get_id "targ1"), d_in)],v1model_direct_meter_construct'),
   []);
  (^(get_id "action_selector"),
   SOME ([(^(get_id "this"),d_out); (^(get_id "algorithm"),d_none); (^(get_id "size"), d_none); (^(get_id "outputWidth"), d_none)],v1model_action_selector_construct'),
   [])
(*
    (^(get_id "register"),
     SOME
       ([(^(get_id "this"),d_out); (^(get_id "size"),d_none); (^(get_id "targ1"),d_in)],register_construct'),
     [(^(get_id "read"),[(^(get_id "this"),d_in); (^(get_id "result"),d_out); (^(get_id "index"),d_in)],register_read');
      (^(get_id "write"),[(^(get_id "this"),d_in); (^(get_id "index"),d_in); (^(get_id "value"),d_in)],register_write')
*) ]):v1model_ascope' ext_map' option
End

Definition transform_v_map_def:
 transform_v_map dict v_map =
  oFOLDR (\(x, v). case ALOOKUP dict x of SOME w => transform_v dict v >>= \v'. SOME (w, v') | NONE => NONE) v_map
End

val transform_core_v_ext_def =
 if io_optimization
 then Define
 ‘transform_core_v_ext core_ext_obj =
  case core_ext_obj of
  | core_v_ext_packet bl =>
   (case bool_list_to_byte_list bl of
     SOME byte_list =>
      SOME $ core_v_ext'_packet byte_list
    | NONE => NONE)’
 else Define
 ‘transform_core_v_ext core_ext_obj =
  case core_ext_obj of
  | core_v_ext_packet bl =>
   SOME $ core_v_ext'_packet bl’
;

Definition transform_ext_obj_map_def:
 transform_ext_obj_map ext_obj_map =
  oFOLDR (\(n, ext_obj).
          case ext_obj of
            INL core_ext_obj =>
           (case transform_core_v_ext core_ext_obj of
             SOME core_ext_obj' => SOME $ (n, INL core_ext_obj')
            | NONE => NONE)
          | INR arch_ext_obj => SOME $ (n, INR arch_ext_obj))
         ext_obj_map
End

(*

Definition transform_ctrl_def:
 transform_ctrl dict ctrl =
  oFOLDR (\(x, v). case ALOOKUP dict x of SOME word => SOME (word, v) | NONE => NONE) ctrl
End
(*
“a:v1model_ctrl”
*)

Definition transform_input_f_def:
 transform_input_f dict input_f =
  \arg:v1model_ascope'. (input_f $ transform_ascope' dict) arg >>=
  \(io_list, ascope'). transform_ascope dict ascope' >>=
  \ascope''. SOME (io_list, ascope'')
End
*)

Definition transform_tbl_regular_def:
 (transform_tbl_regular dict [] = SOME []) /\
 (transform_tbl_regular dict (((s_l, n:num), str, e_l)::t) =
  oFOLDR (\s. transform_s dict s >>= \s'_n. SOME (FST s'_n)) s_l >>=
  \s'_l. ALOOKUP dict str >>=
  \id. transform_e_list dict e_l >>=
  \e'_l. transform_tbl_regular dict t >>=
  \t'. SOME (((s'_l, n), id, e'_l)::t')
)
End

(* TODO: Do this better now *)
Definition transform_ctrl_empty_def:
 transform_ctrl_empty dict (ctrl:v1model_ctrl) =
  ((oFOLDR (\(x, tbl). ALOOKUP dict x >>= \w. SOME (w, (tbl'_regular []):tbl')) ctrl):v1model_ctrl' option)
(*
  (oFOLDR (\(x, v). case ALOOKUP dict x of SOME w => SOME (w, []:(((e_list' -> bool) # num), string # e_list') alist) | NONE => NONE) ctrl)
*)
End

Definition transform_ascope_def:
 transform_ascope dict (counter, ext_obj_map, v_map, ctrl) ctrl' =
  transform_ext_obj_map ext_obj_map >>=
  \ext_obj_map'. transform_v_map dict v_map >>=
  \v_map'.
  (* transform_ctrl dict ctrl >>=
  \ctrl'. *)
  SOME (counter, ext_obj_map', v_map', ctrl')
End

(* Given an alist of translations from strings to identifier, transforms an actx to an actx'. *)
(* TODO: Change the architectural representation so you can translate input_f and apply_table_f properly also *)
Definition transform_actx_def:
 transform_actx dict ((ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map):v1model_ascope actx) =
  transform_ab_list dict ab_list >>=
  \ab_list'. transform_pblock_map dict pblock_map >>=
  \pblock_map'. transform_ffblock_map dict ffblock_map >>=
  \ffblock_map'. transform_ext_map dict ext_map >>=
  \ext_map'. transform_func_map dict func_map >>=
  \func_map'. SOME (ab_list':ab_list', pblock_map':pblock_map', ext_map':v1model_ascope' ext_map', func_map':func_map')
End
(*
“transform_actx ^actx ^dict”
*)

val transform_io_list_def =
 if io_optimization
 then Define
 ‘transform_io_list io_list =
   oFOLDR (\(bl, p). case bool_list_to_byte_list bl of SOME w => SOME (w, p) | NONE => NONE) io_list’
 else Define
 ‘transform_io_list io_list = SOME io_list’
;

Definition transform_aenv_def:
 transform_aenv dict (i, io_list, io_list', ascope) ctrl' =
  transform_ascope dict ascope ctrl' >>=
  \ascope'. transform_io_list io_list >>=
  \io_list''. transform_io_list io_list' >>=
  \io_list'''. SOME (i, io_list'', io_list''', ascope')
End

Definition transform_scope_entry_def:
 transform_scope_entry dict (varn, (v, lval_opt)) =
  transform_varn dict varn >>=
  \varn'. transform_v dict v >>=
  \v'.
  (case lval_opt of
     SOME lval =>
    transform_lval dict lval >>= 
    \lval'. SOME (varn', (v', SOME lval'))
   | NONE =>
    SOME (varn', (v', NONE)))
End

Definition transform_scope_def:
 (transform_scope dict scope =
   (oFOLDR (transform_scope_entry dict) scope):scope' option)
End

Definition transform_scope_list_def:
 (transform_scope_list dict (scope_list:scope_list) =
  (oFOLDR (transform_scope dict) scope_list):scope_list' option)
End

Definition transform_status_def:
 transform_status dict status =
  case status of
    status_running => SOME $ status'_running
  | status_returnv v =>
   transform_v dict v >>=
   \v'. SOME $ status'_returnv v'
  | status_trans x =>
   ALOOKUP dict x >>=
   \w. SOME $ status'_trans w
End

Definition transform_astate_def:
 transform_astate dict ((aenv, g_scope_list, arch_frame_list, status):v1model_ascope astate) ctrl' =
  transform_aenv dict aenv ctrl' >>=
  \aenv'. transform_scope_list dict g_scope_list >>=
  (* TODO: arch_frame_list transformation hard-coded, for now *)
  \g_scope_list'. transform_status dict status >>=
  \status'. SOME ((aenv':v1model_ascope' aenv', g_scope_list':g_scope_list', arch_frame_list'_empty, status'):v1model_ascope' astate')
End

(********)
(* eBPF *)
(********)

Definition transform_ebpf_ext_map_def:
 transform_ebpf_ext_map dict (ext_map:ebpf_ascope ext_map) =
   SOME ([(^(get_id "header"),NONE,
     [(^(get_id "isValid"),[(^(get_id "this"):identifier,d_in)],header_is_valid');
      (^(get_id "setValid"),[(^(get_id "this"),d_inout)],header_set_valid');
      (^(get_id "setInvalid"),[(^(get_id "this"),d_inout)],header_set_invalid')]);
    (^(get_id ""),NONE,
     [(^(get_id "verify"),[(^(get_id "condition"),d_in); (^(get_id "err"),d_in)],ebpf_verify')]);      
    (^(get_id "packet_in"),NONE,
     [(^(get_id "extract"),[(^(get_id "this"),d_in); (^(get_id "headerLvalue"),d_out)],
       ebpf_packet_in_extract');
      (^(get_id "lookahead"),[(^(get_id "this"),d_in); (^(get_id "targ1"),d_in)],ebpf_packet_in_lookahead');
      (^(get_id "advance"),[(^(get_id "this"),d_in); (^(get_id "bits"),d_in)],ebpf_packet_in_advance')
     ]);
    (^(get_id "packet_out"),NONE,
     [(^(get_id "emit"),[(^(get_id "this"),d_in); (^(get_id "data"),d_in)],ebpf_packet_out_emit')]);
    (^(get_id "CounterArray"),
     SOME
       ([(^(get_id "this"),d_out); (^(get_id "max_index"),d_none); (^(get_id "sparse"),d_none)],
        CounterArray_construct'),
     [(^(get_id "increment"),[(^(get_id "this"),d_in); (^(get_id "index"),d_in)],CounterArray_increment');
      (^(get_id "add"),[(^(get_id "this"),d_in); (^(get_id "index"),d_in); (^(get_id "value"),d_in)],
       CounterArray_add')])
 ]):ebpf_ascope' ext_map' option
End

Definition transform_ebpf_actx_def:
 transform_ebpf_actx dict ((ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map):ebpf_ascope actx) =
  transform_ab_list dict ab_list >>=
  \ab_list'. transform_pblock_map dict pblock_map >>=
  \pblock_map'. transform_ffblock_map dict ffblock_map >>=
  \ffblock_map'. transform_ebpf_ext_map dict ext_map >>=
  \ext_map'. transform_func_map dict func_map >>=
  \func_map'. SOME (ab_list':ab_list', pblock_map':pblock_map', ext_map':ebpf_ascope' ext_map', func_map':func_map')
End

(*

val (aenv, g_scope_list, arch_frame_list, status) = dest_astate astate

val (i, io_list, io_list', ascope) = dest_aenv aenv
val (counter, ext_obj_map, v_map, ctrl) = dest_ascope ascope

EVAL “transform_aenv ^dict ^aenv ^ctrl'”
EVAL “(EL 4 ^v_map)”
*)
Definition transform_ebpf_astate_def:
 transform_ebpf_astate dict ((aenv, g_scope_list, arch_frame_list, status):ebpf_ascope astate) ctrl' =
  transform_aenv dict aenv ctrl' >>=
  \aenv'. transform_scope_list dict g_scope_list >>=
  (* TODO: arch_frame_list transformation hard-coded, for now *)
  \g_scope_list'. transform_status dict status >>=
  \status'. SOME ((aenv':ebpf_ascope' aenv', g_scope_list':g_scope_list', arch_frame_list'_empty, status'):ebpf_ascope' astate')
End

val _ = export_theory ();
