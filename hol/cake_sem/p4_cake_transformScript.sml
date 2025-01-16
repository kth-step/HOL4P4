open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_cake_transform";

open p4Syntax;
open bitstringSyntax numSyntax pairSyntax;
open p4Theory p4_auxTheory p4_exec_sem_cakeTheory;
open p4_coreTheory;
open p4_v1modelTheory;

open p4_arch_cakeTheory;

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

(** Adding varnames from an actx **)

Definition add_varnames_varn_def:
 add_varnames_varn (dict: (string, word64) alist) varn =
  case varn of
    varn_name name =>
   if IS_NONE $ ALOOKUP dict name
   then p4$AUPDATE dict (name, n2w $ LENGTH dict)
   else dict
  | varn_star funn => dict
End

Definition add_varnames_e_def:
 (add_varnames_e dict e =
  case e of
    e_v v => dict
  | e_var varn =>
   add_varnames_varn dict varn
  | e_list el =>
   add_varnames_e_list dict el
  | e_acc e x =>
   add_varnames_e dict e
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
   add_varnames_e_list dict el
  | e_select e s_list_x_list x =>
   add_varnames_e dict e
  | e_struct x_e_list =>
   let (x_list, e_list) = UNZIP x_e_list in
   add_varnames_e_list dict e_list
  | e_header validity x_e_list =>
   let (x_list, e_list) = UNZIP x_e_list in
   add_varnames_e_list dict e_list) /\
 (add_varnames_e_list dict [] = dict) /\
 (add_varnames_e_list dict (h::t) =
  add_varnames_e_list (add_varnames_e dict h) t)
Termination
WF_REL_TAC ‘measure $ (\a. case (a:(((string # word64) list) # e) + (((string # word64) list) # e list)) of INR d_el => e3_size $ SND d_el | INL d_e => e_size $ SND d_e)’ >>
rpt strip_tac >>
gs[e_size_def] >>
subgoal ‘e_list' = MAP SND x_e_list'’ >- (
 gs[listTheory.UNZIP_MAP]
) >>
imp_res_tac e1_e3_size >>
decide_tac
End

Definition add_varnames_arch_block_def:
 add_varnames_arch_block arch_block dict =
  case arch_block of
    arch_block_inp => dict
  | arch_block_pbl x el =>
   add_varnames_e_list dict el
  | arch_block_ffbl x => dict
  | arch_block_out => dict
End

Definition add_varnames_ab_list_def:
 add_varnames_ab_list ab_list dict =
  FOLDR add_varnames_arch_block dict ab_list
End

Definition add_varnames_arg_def:
 add_varnames_arg (x,d) dict =
  if IS_NONE $ ALOOKUP dict x
  then p4$AUPDATE dict (x, n2w $ LENGTH dict)
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
   add_varnames_lval lval' dict
  | lval_slice lval' e1 e2 =>
   add_varnames_lval lval' $ add_varnames_e (add_varnames_e dict e1) e2
  | lval_paren lval' =>
   add_varnames_lval lval' dict
End

Definition add_varnames_t_scope_def:
 add_varnames_t_scope (varn, (tau, lval_opt)) dict =
  let dict' = add_varnames_varn dict varn in
  (case lval_opt of
     SOME lval =>
    add_varnames_lval lval dict'
   | NONE => dict')
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
   add_varnames_e_list dict el
  | stmt_ext => dict
End

Definition add_varnames_func_def:
 add_varnames_func (x, (body, args)) dict =
  add_varnames_stmt body $ add_varnames_args args dict
End

Definition add_varnames_func_map_def:
 add_varnames_func_map (func_map:func_map) dict =
  FOLDR add_varnames_func dict func_map
End

Definition add_varnames_tbl_def:
 add_varnames_tbl (x1, (mkl, (x2, el))) dict =
  add_varnames_e_list dict el
End

Definition add_varnames_tbl_map_def:
 add_varnames_tbl_map (tbl_map:tbl_map) dict =
  FOLDR add_varnames_tbl dict tbl_map
End

Definition add_varnames_pars_state_def:
 add_varnames_pars_state (x, body) dict =
  add_varnames_stmt body dict
End

Definition add_varnames_pars_map_def:
 add_varnames_pars_map (pars_map:pars_map) dict =
  FOLDR add_varnames_pars_state dict pars_map
End

Definition add_varnames_pblock_def:
 add_varnames_pblock (x, (pbl_type, x_d_l, b_func_map, t_scope, pars_map, tbl_map):pblock) dict =
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

Definition add_varnames_actx_def:
 add_varnames_actx dict ((ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map):v1model_ascope actx) =
  add_varnames_ab_list ab_list $
  add_varnames_pblock_map pblock_map $
  (* Note: Variable names from ext map shoulc already be included in dict *)
  add_varnames_func_map func_map dict
End

(** Transforming an actx to an actx' *)

Definition transform_varn_def:
 transform_varn dict varn =
  case varn of
    varn_name name =>
   ALOOKUP dict name >>= \word. SOME $ varn'_name word
  | varn_star funn => SOME $ varn'_star funn
End

(* TODO: Make better *)
Definition oFOLDR_def:
 (oFOLDR f []     = SOME []) /\
 (oFOLDR f (h::t) =
  f h >>=
  \res. oFOLDR f t >>=
  \res_list. SOME $ res::res_list)
End

Definition transform_e_def:
 (transform_e dict e =
  case e of
    e_v v => SOME $ e'_v v
  | e_var varn =>
   transform_varn dict varn >>=
   \varn'. SOME $ e'_var varn'
  | e_list el =>
   transform_e_list dict el >>=
   \el'. SOME $ e'_list el'
  | e_acc e x =>
   transform_e dict e >>=
   \e'. SOME $ e'_acc e' x
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
   transform_e_list dict el >>=
   \el'. SOME $ e'_call funn el'
  | e_select e s_list_x_list x =>
   transform_e dict e >>=
   \e'. SOME $ e'_select e' s_list_x_list x
  | e_struct x_e_list =>
   let (x_list, e_list) = UNZIP x_e_list in
   transform_e_list dict e_list >>=
   \el'. SOME $ e'_struct $ ZIP (x_list, el')
  | e_header validity x_e_list =>
   let (x_list, e_list) = UNZIP x_e_list in
   transform_e_list dict e_list >>=
   \el'. SOME $ e'_header validity $ ZIP (x_list, el')) /\
 (transform_e_list dict [] = SOME []) /\
 (transform_e_list dict (h::t) =
  transform_e dict h >>=
  \e'. transform_e_list dict t >>=
  \el'. SOME $ e'::el')
Termination
WF_REL_TAC ‘measure $ (\a. case (a:(((string # word64) list) # e) + (((string # word64) list) # e list)) of INR d_el => e3_size $ SND d_el | INL d_e => e_size $ SND d_e)’ >>
rpt strip_tac >>
gs[e_size_def] >>
subgoal ‘e_list' = MAP SND x_e_list'’ >- (
 gs[listTheory.UNZIP_MAP]
) >>
imp_res_tac e1_e3_size >>
decide_tac
End

Definition transform_arch_block_def:
 transform_arch_block dict arch_block =
  case arch_block of
    arch_block_inp => SOME arch_block'_inp
  | arch_block_pbl x el =>
   transform_e_list dict el >>=
   \el'. SOME $ arch_block'_pbl x el'
  | arch_block_ffbl x =>
   SOME $ arch_block'_ffbl x
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
   \lval''. SOME $ lval'_field lval'' x
  | lval_slice lval' e1 e2 =>
   transform_lval dict lval' >>=
   \lval''. transform_e dict e1 >>=
   \e1'. transform_e dict e2 >>=
   \e2'. SOME $ lval'_slice lval'' e1' e2'
  | lval_paren lval' =>
   transform_lval dict lval' >>=
   \lval''. SOME $ lval'_paren lval''
End

Definition transform_t_scope_def:
 transform_t_scope dict (varn, (tau, lval_opt)) =
  transform_varn dict varn >>=
  \varn'.
  (case lval_opt of
     SOME lval =>
    transform_lval dict lval >>= 
    \lval'. SOME (varn', (tau, SOME lval'))
   | NONE =>
    SOME (varn', (tau, NONE)))
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
   transform_e_list dict el >>=
   \el'. SOME $ stmt'_app x el'
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
  transform_stmt dict body >>=
  \body'. transform_args dict args >>=
  \args. SOME (x, (body', args))
End

Definition transform_func_map_def:
 (transform_func_map dict (func_map:func_map) =
   (oFOLDR (transform_func dict) func_map):func_map' option)
End

Definition transform_tbl_def:
 transform_tbl dict (x1, (mkl, (x2, el))) =
  transform_e_list dict el >>=
  \el'. SOME (x1, (mkl, (x2, el')))
End

Definition transform_tbl_map_def:
 (transform_tbl_map dict (tbl_map:tbl_map) =
  (oFOLDR (transform_tbl dict) tbl_map):tbl_map' option)
End

Definition transform_pars_state_def:
 transform_pars_state dict (x, body) =
  transform_stmt dict body >>=
  \body'. SOME (x, body')
End

Definition transform_pars_map_def:
 (transform_pars_map dict (pars_map:pars_map) =
  (oFOLDR (transform_pars_state dict) pars_map):pars_map' option)
End

Definition transform_pblock_def:
 transform_pblock dict (x, (pbl_type, x_d_l, b_func_map, t_scope, pars_map, tbl_map):pblock) =
  transform_args dict x_d_l >>=
  \args'. transform_func_map dict b_func_map >>=
  \b_func_map'. transform_t_scope_list dict t_scope >>=
  \t_scope'. transform_pars_map dict pars_map >>=
  \pars_map'. transform_tbl_map dict tbl_map >>=
  \tbl_map'. SOME (x, (pbl_type, args', b_func_map', t_scope', pars_map', tbl_map'))
End

Definition transform_pblock_map_def:
 (transform_pblock_map dict (pblock_map:pblock_map) =
  (oFOLDR (transform_pblock dict) pblock_map):pblock_map' option)
End

(* TODO: Hard-coded, for now... *)
Definition transform_ext_map_def:
 transform_ext_map dict (ext_map:v1model_ascope ext_map) =
   SOME ([("header",NONE,
     [("isValid",[(3w:word64,d_in)],header_is_valid');
      ("setValid",[(3w,d_inout)],header_set_valid');
      ("setInvalid",[(3w,d_inout)],header_set_invalid')]);
    ("",NONE,
     [("mark_to_drop",[(10w,d_inout)],v1model_mark_to_drop');
      ("verify",[(2w,d_in); (1w,d_in)],v1model_verify');

    ("verify_checksum",
     [(2w,d_in); (7w,d_in); (15w,d_in); (16w,d_none)],
     v1model_verify_checksum');
    ("update_checksum",
     [(2w,d_in); (7w,d_in); (15w,d_inout);
      (16w,d_none)],v1model_update_checksum');
    ("assert",[(14w,d_in)],v1model_assert');
    ("assume",[(14w,d_in)],v1model_assume')]);
      
    ("packet_in",NONE,
     [("extract",[(3w,d_in); (4w,d_out)],
       v1model_packet_in_extract');

      ("lookahead",[(3w,d_in); (5w,d_in)],v1model_packet_in_lookahead');
    ("advance",[(3w,d_in); (6w,d_in)],v1model_packet_in_advance')

]);
    ("packet_out",NONE,
     [("emit",[(3w,d_in); (7w,d_in)],v1model_packet_out_emit')]);

  ("direct_counter",
   SOME ([(3w,d_out); (21w,d_none)],v1model_direct_counter_construct'),
   [("count",[(3w,d_out)],v1model_direct_counter_count')])
(*
    ("register",
     SOME
       ([(3w,d_out); (17w,d_none); (5w,d_in)],register_construct'),
     [("read",[(3w,d_in); (18w,d_out); (19w,d_in)],register_read');
      ("write",[(3w,d_in); (19w,d_in); (20w,d_in)],register_write')
*) ]):v1model_ascope' ext_map' option
End

(* TODO: Hard-coded for now, but that's probably alright for this function. *)
(*
Definition transform_ffblock_map_def:
 transform_ffblock_map dict ffblock_map =
  SOME [("postparser",ffblock_ff v1model_postparser')]
End
*)

Definition transform_v_map_def:
 transform_v_map dict v_map =
  oFOLDR (\(x, v). case ALOOKUP dict x of SOME w => SOME (w, v) | NONE => NONE) v_map
End


Definition transform_ascope_def:
 transform_ascope dict ((counter, ext_obj_map, v_map, ctrl):v1model_ascope) ctrl' =
  transform_v_map dict v_map >>=
  \v_map'. SOME (counter, ext_obj_map, v_map', ctrl')
End

(*

Definition transform_ctrl_entry_def:
 transform_ctrl_entry dict (tbl_name, ((matching_function, prio), default_action, default_args)) =
  let matching_function' = matching_function o in
  transform_e_list dict default_args >>=
  \default_args'. SOME (tbl_name, ((matching_function', prio), default_action, default_args'))
End

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

Definition transform_ctrl_empty_def:
 transform_ctrl_empty (ctrl:v1model_ctrl) =
  (oFOLDR (\(x, v). SOME (x, []:(((e_list' -> bool) # num), string # e_list') alist)) ctrl)
(*
  (oFOLDR (\(x, v). case ALOOKUP dict x of SOME w => SOME (w, []:(((e_list' -> bool) # num), string # e_list') alist) | NONE => NONE) ctrl)
*)
End

(* Given an alist of translations from strings to word64, transforms an actx to an actx'. *)
(* TODO: Change the architectural representation so you can translate input_f and apply_table_f properly also *)
Definition transform_actx_def:
 transform_actx dict ((ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map):v1model_ascope actx) =
  transform_ab_list dict ab_list >>=
  \ab_list'. transform_pblock_map dict pblock_map >>=
  \pblock_map'. transform_ext_map dict ext_map >>=
  \ext_map'. transform_func_map dict func_map >>=
  \func_map'. SOME (ab_list':ab_list', pblock_map':pblock_map', ext_map':v1model_ascope' ext_map', func_map':func_map')
End
(*
“transform_actx ^actx ^dict”
*)


Definition transform_aenv_def:
 transform_aenv dict (i, io_list, io_list', ascope) ctrl' =
  transform_ascope dict ascope ctrl' >>=
  \ascope'. SOME ((i, io_list, io_list', ascope'):v1model_ascope' aenv)
End

Definition transform_scope_entry_def:
 transform_scope_entry dict (varn, (v, lval_opt)) =
  transform_varn dict varn >>=
  \varn'.
  (case lval_opt of
     SOME lval =>
    transform_lval dict lval >>= 
    \lval'. SOME (varn', (v, SOME lval'))
   | NONE =>
    SOME (varn', (v, NONE)))
End

Definition transform_scope_def:
 (transform_scope dict scope =
   (oFOLDR (transform_scope_entry dict) scope):scope' option)
End

Definition transform_scope_list_def:
 (transform_scope_list dict (scope_list:scope_list) =
  (oFOLDR (transform_scope dict) scope_list):scope_list' option)
End

Definition transform_astate_def:
 transform_astate dict ((aenv, g_scope_list, arch_frame_list, status):v1model_ascope astate) ctrl' =
  transform_aenv dict aenv ctrl' >>=
  \aenv'. transform_scope_list dict g_scope_list >>=
  (* TODO: arch_frame_list transformation hard-coded, for now *)
  \g_scope_list'. SOME (aenv':v1model_ascope' aenv, g_scope_list':g_scope_list', arch_frame_list'_empty, status)
End

val _ = export_theory ();
