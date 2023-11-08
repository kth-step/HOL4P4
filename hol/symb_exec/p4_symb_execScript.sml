open HolKernel boolLib liteLib simpLib Parse bossLib;

open pairSyntax listSyntax optionSyntax;

open p4Theory p4_exec_semTheory p4Syntax p4_exec_semSyntax;

open evalwrapLib p4_testLib;

val _ = new_theory "p4_symb_exec";

val ERR = mk_HOL_ERR "p4_symb_exec"

(* Checking if a conditional statement is about to be reduced
 * to one of its two statement constituents *)

Definition stmt_get_cond_def:
 stmt_get_cond stmt =
  case stmt of
  | stmt_empty => NONE
  | stmt_ass lval e => NONE
  | stmt_cond e stmt' stmt'' =>
   (case e of
    | e_v cond => SOME cond
    | _ => NONE)
  | stmt_block t_scope stmt' =>
   stmt_get_cond stmt'
  | stmt_ret e => NONE
  | stmt_seq stmt' stmt'' =>
   stmt_get_cond stmt'
  | stmt_trans e => NONE
  | stmt_app x e_l => NONE
  | stmt_ext => NONE
End

Definition astate_get_cond_def:
 astate_get_cond ((aenv, g_scope_list, arch_frame_list, status):'a astate) =
  case arch_frame_list of
  | arch_frame_list_empty => NONE
  | arch_frame_list_regular frame_list =>
   (case frame_list of
    | [] => NONE
    | ((funn, stmt_stack, scope_list)::t) =>
     (case stmt_stack of
      | [] => NONE
      | (h'::t') => stmt_get_cond h'
     )
   )
End

Definition is_cond_red_next_def:
 is_cond_red_next stmt =
  case stmt_get_cond stmt of
  | SOME cond => T
  | NONE => F
End

(* Can use the SML function "free_vars" to check if expression to be
 * reduced contains any free variables. We should probably only perform
 * a branch if the next smallest subexpression to be reduced includes
 * a free variable. But even this subexpression reduction should be OK for
 * certain expressions: for example, bit slicing and casting if all
 * free variables involved are Booleans. *)
fun next_e_has_free_vars e =
 if is_e_v e
 then not $ null $ free_vars e
 else if is_e_var e
 then false
 else if is_e_acc e
 then
  let
   val (e', x) = dest_e_acc e
  in
   (* We can always allow field access to proceed *)
   if is_e_v e'
   then false
   else next_e_has_free_vars e'
  end
 else if is_e_unop e
 then
  let
   val (unop, e') = dest_e_unop e
  in
   next_e_has_free_vars e'
  end
 else if is_e_cast e
 then
  let
   val (cast, e') = dest_e_cast e
  in
   (* We can always allow cast to proceed *)
   if is_e_v e'
   then false
   else next_e_has_free_vars e'
  end
 else if is_e_binop e
 then
  let
   val (e', binop, e'') = dest_e_binop e
  in
   if is_e_v e'
   then next_e_has_free_vars e'
   else next_e_has_free_vars e''
  end
 else if is_e_concat e
 then
  let
   val (e', e'') = dest_e_concat e
  in
   (* We can always allow concat to proceed *)
   if is_e_v e'
   then
    if is_e_v e''
    then false
    else next_e_has_free_vars e''
   else next_e_has_free_vars e'
  end
 else if is_e_slice e
 then
  let
   val (e', e'', e''') = dest_e_slice e
  in
   (* We can allow slice to proceed if indices have no free variables *)
   if is_e_v e'
   then
    if is_e_v e''
    then
     if is_e_v e'''
     then next_e_has_free_vars e'' orelse next_e_has_free_vars e'''
     else next_e_has_free_vars e'''
    else next_e_has_free_vars e''
   else next_e_has_free_vars e'
  end
 else if is_e_call e
 then
  let
   val (funn, e_list) = dest_e_call e
  in
   next_e_has_free_vars_list (fst $ dest_list e_list)
  end
 else if is_e_select e
 then
  let
   val (e', v_x_list, x) = dest_e_select e
  in
   next_e_has_free_vars e'
  end
 else if is_e_struct e
 then
  let
   val x_e_list = dest_e_struct e
  in
   next_e_has_free_vars_list ((map (snd o dest_pair)) $ fst $ dest_list x_e_list)
  end
 else if is_e_header e
 then
  let
   val (boolv, x_e_list) = dest_e_header e
  in
   next_e_has_free_vars_list ((map (snd o dest_pair)) $ fst $ dest_list x_e_list)
  end
 (* Unsupported: e_list *)
 else raise (ERR "next_e_has_free_vars" ("Unsupported expression: "^(term_to_string e)))
and next_e_has_free_vars_list []     = false
  | next_e_has_free_vars_list (h::t) =
   if next_e_has_free_vars h
   then true
   else next_e_has_free_vars_list t
;


(* Symbolic executor should do similar things as eval_under_assum, but on every iteration
 * check if conditional is next to be reduced, then next_e_has_free_vars.
 *
 * Handler consists of:
 * get_branch_cond: Function that tells if to perform branch. Returns NONE if no, SOME cond
 * if yes, where cond is the condition (a term) to branch upon.
 *
 * new free variable introduction *)

(* eval_under_assum used like:
   eval_under_assum v1model_arch_ty ctx init_astate stop_consts_rewr stop_consts_never ctxt nsteps_max;
 * ctxt is a static evaluation context with theorems to rewrite with (use ASSUME on terms)
 * stop_consts_rewr and stop_consts_never are used for handling externs - telling the
 * evaluation when to halt
 * 
 * *)

local
(* TODO: The below two are also found in p4_testLib.sml - put elsewhere? *)
fun the_final_state_imp step_thm = dest_some $ snd $ dest_eq $ snd $ dest_imp $ concl step_thm
val simple_arith_ss = pure_ss++numSimps.REDUCE_ss

(* Symbolic execution with branching on if-then-else
 * Width-first scheduling (positive case first)
 * Note that branching consumes one step of fuel
 * Note that the static ctxt is shared between the branches, whereas the dynamic path
 * conditions are different and not shared *)
fun symb_exec' arch_ty ctx stop_consts_rewr stop_consts_never ctxt comp_thm [] finished_list =
 finished_list
  | symb_exec' arch_ty ctx stop_consts_rewr stop_consts_never ctxt comp_thm
               ((path_cond, step_thm, 0)::t) finished_list =
   symb_exec' arch_ty ctx stop_consts_rewr stop_consts_never ctxt comp_thm t
              (finished_list@[(path_cond, step_thm)])
  | symb_exec' arch_ty ctx stop_consts_rewr stop_consts_never ctxt comp_thm
               ((path_cond, step_thm, fuel)::t) finished_list =
 let
  val curr_state = the_final_state_imp step_thm
  (* Check if we should branch or take regular step *)
  (* TODO: Use separate handler for this - factor out the below into a separate function *)
  val branch_cond_opt = rhs $ concl $ EVAL “astate_get_cond curr_state”
 in
  if is_some branch_cond_opt
  (* Branch + prune *)
  then
   let
    (* Get branch condition term *)
    val branch_cond = dest_some branch_cond_opt
    (* Get new rewriting contexts for the positive and negative cases *)
    val path_cond_cond = CONJ path_cond (ASSUME branch_cond)
    val path_cond_neg_cond = CONJ path_cond (ASSUME $ mk_neg branch_cond)
    (* Check if the new rewriting contexts contradict themselves *)
    val is_path_cond_cond_F = Feq $ concl (SIMP_RULE std_ss [] path_cond_cond)
    val is_path_cond_neg_cond_F = Feq $ concl (SIMP_RULE std_ss [] path_cond_neg_cond)
    (* Prune away symbolic states with contradictory path_cond, otherwise add them to
     * end of procesing queue. Positive case goes before negative. *)
    val next_astate_cond =
     if is_path_cond_cond_F then [] else [(path_cond_cond, step_thm, fuel-1)]
    val next_astate_neg_cond =
     if is_path_cond_neg_cond_F then [] else [(path_cond_neg_cond, step_thm, fuel-1)]
   in
    symb_exec' arch_ty ctx stop_consts_rewr stop_consts_never ctxt comp_thm (t@(next_astate_cond@next_astate_neg_cond)) finished_list
   end
  (* Do not branch - compute one step *)
  else
   let
    val step_thm2 =
     eval_ctxt_gen (stop_consts_rewr@stop_consts_never) stop_consts_never ctxt (mk_arch_multi_exec (ctx, curr_state, 1));
    val comp_step_thm =
     SIMP_RULE simple_arith_ss []
      (MATCH_MP (MATCH_MP comp_thm step_thm) step_thm2);
   in
    symb_exec' arch_ty ctx stop_consts_rewr stop_consts_never ctxt comp_thm (t@[(path_cond, comp_step_thm, fuel-1)]) finished_list
   end
 end

in
fun symb_exec arch_ty ctx init_astate stop_consts_rewr stop_consts_never ctxt path_cond fuel =
 let
  (* TODO: Also branch check here *)
  val step_thm =
   eval_ctxt_gen (stop_consts_rewr@stop_consts_never) stop_consts_never ctxt (mk_arch_multi_exec (ctx, init_astate, 1));
  val comp_thm = INST_TYPE [Type.alpha |-> arch_ty] arch_multi_exec_comp_n_tl_assl;
 in
  if fuel = 1
  then [(path_cond, step_thm)]
  else symb_exec' arch_ty ctx stop_consts_rewr stop_consts_never ctxt comp_thm [(path_cond, step_thm, (fuel-1))] []
 end
end;

(* Test area *)

val symb_exec1_actx = ``([arch_block_inp;
  arch_block_pbl "p"
    [e_var (varn_name "b"); e_var (varn_name "parsedHdr");
     e_var (varn_name "meta"); e_var (varn_name "standard_metadata")];
  arch_block_ffbl "postparser";
  arch_block_pbl "vrfy" [e_var (varn_name "hdr"); e_var (varn_name "meta")];
  arch_block_pbl "ingress"
    [e_var (varn_name "hdr"); e_var (varn_name "meta");
     e_var (varn_name "standard_metadata")];
  arch_block_pbl "egress"
    [e_var (varn_name "hdr"); e_var (varn_name "meta");
     e_var (varn_name "standard_metadata")];
  arch_block_pbl "update" [e_var (varn_name "hdr"); e_var (varn_name "meta")];
  arch_block_pbl "deparser" [e_var (varn_name "b"); e_var (varn_name "hdr")];
  arch_block_out],
 [("p",
   pblock_regular pbl_type_parser
     [("p",stmt_seq stmt_empty (stmt_trans (e_v (v_str "start"))),
       [("b",d_none); ("h",d_out); ("m",d_inout); ("sm",d_inout)])] []
     [("start",
       stmt_seq
         (stmt_ass lval_null
            (e_call (funn_ext "packet_in" "extract")
               [e_var (varn_name "b"); e_acc (e_var (varn_name "h")) "h"]))
         (stmt_trans (e_v (v_str "accept"))))] []);
  ("vrfy",
   pblock_regular pbl_type_control
     [("vrfy",stmt_seq stmt_empty stmt_empty,[("h",d_inout); ("m",d_inout)])]
     [] [] []);
  ("update",
   pblock_regular pbl_type_control
     [("update",stmt_seq stmt_empty stmt_empty,[("h",d_inout); ("m",d_inout)])]
     [] [] []);
  ("egress",
   pblock_regular pbl_type_control
     [("egress",stmt_seq stmt_empty stmt_empty,
       [("h",d_inout); ("m",d_inout); ("sm",d_inout)])] [] [] []);
  ("deparser",
   pblock_regular pbl_type_control
     [("deparser",
       stmt_seq stmt_empty
         (stmt_ass lval_null
            (e_call (funn_ext "packet_out" "emit")
               [e_var (varn_name "b"); e_acc (e_var (varn_name "h")) "h"])),
       [("b",d_none); ("h",d_in)])] [] [] []);
  ("ingress",
   pblock_regular pbl_type_control
     [("ingress",
       stmt_seq stmt_empty
         (stmt_cond
            (e_binop
               (e_acc (e_acc (e_acc (e_var (varn_name "h")) "h") "row") "e")
               binop_lt (e_v (v_bit ([T; F; F; F; F; F; F; F],8))))
            (stmt_ass
               (lval_field (lval_varname (varn_name "standard_meta"))
                  "egress_spec")
               (e_v (v_bit ([F; F; F; F; F; F; F; F; T],9))))
            (stmt_ass
               (lval_field (lval_varname (varn_name "standard_meta"))
                  "egress_spec")
               (e_v (v_bit ([F; F; F; F; F; F; F; T; F],9))))),
       [("h",d_inout); ("m",d_inout); ("standard_meta",d_inout)])] [] [] [])],
 [("postparser",ffblock_ff v1model_postparser)],
 v1model_input_f
   (v_struct
      [("h",
        v_header ARB
          [("row",
            v_struct
              [("e",v_bit ([ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB],8));
               ("t",
                v_bit
                  ([ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
                    ARB; ARB; ARB; ARB; ARB],16));
               ("l",v_bit ([ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB],8));
               ("r",v_bit ([ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB],8));
               ("v",v_bit ([ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB],8))])])],
    v_struct []),v1model_output_f,v1model_copyin_pbl,v1model_copyout_pbl,
 v1model_apply_table_f,
 [("header",NONE,
   [("isValid",[("this",d_in)],header_is_valid);
    ("setValid",[("this",d_inout)],header_set_valid);
    ("setInvalid",[("this",d_inout)],header_set_invalid)]);
  ("",NONE,
   [("mark_to_drop",[("standard_metadata",d_inout)],v1model_mark_to_drop);
    ("verify",[("condition",d_in); ("err",d_in)],v1model_verify)]);
  ("packet_in",NONE,
   [("extract",[("this",d_in); ("headerLvalue",d_out)],
     v1model_packet_in_extract);
    ("lookahead",[("this",d_in); ("targ1",d_in)],v1model_packet_in_lookahead);
    ("advance",[("this",d_in); ("bits",d_in)],v1model_packet_in_advance)]);
  ("packet_out",NONE,
   [("emit",[("this",d_in); ("data",d_in)],v1model_packet_out_emit)]);
  ("register",
   SOME
     ([("this",d_out); ("size",d_none); ("targ1",d_in)],register_construct),
   [("read",[("this",d_in); ("result",d_out); ("index",d_in)],register_read);
    ("write",[("this",d_in); ("index",d_in); ("value",d_in)],register_write)])],
 [("NoAction",stmt_seq stmt_empty (stmt_ret (e_v v_bot)),[])]):v1model_ascope actx``;

val symb_exec1_astate = rhs $ concl $ EVAL “(p4_append_input_list [([F; F; F; F; F; F; F; T; F; F; F; T; F; F; F; T; F; F; F; T; F; F; F; T; F;
   F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; T; F; T; T; F; F; F; F],0);
 ([F; F; F; F; F; F; T; F; F; F; F; T; F; F; F; T; T; F; F; F; F; F; F; T; F;
   F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; T; F; T; T; F; F; F; F],0);
 ([T; T; T; T; F; F; T; T; F; F; F; T; F; F; F; F; F; F; F; F; F; F; F; F; F;
   F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; T; F; T; T; F; F; F; F],0);
 ([T; T; T; T; F; T; F; F; F; F; F; T; F; F; F; T; F; F; F; T; F; F; F; T; F;
   F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; T; F; T; T; F; F; F; F],0)] (((0,[],[],ARB,ARB,ARB,[]),[[]],arch_frame_list_empty,status_running):v1model_ascope astate))”;

(* eval_under_assum: *)
GEN_ALL $ eval_under_assum p4_v1modelLib.v1model_arch_ty symb_exec1_actx symb_exec1_astate [] [] (ASSUME T) 10;

val symb_exec1_astate_symb = rhs $ concl $ EVAL “(p4_append_input_list [([e1; e2; e3; e4; e5; e6; e7; e8; F; F; F; T; F; F; F; T; F; F; F; T; F; F; F; T; F;
   F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; T; F; T; T; F; F; F; F],0)] (((0,[],[],ARB,ARB,ARB,[]),[[]],arch_frame_list_empty,status_running):v1model_ascope astate))”;

(* symb_exec: *)
symb_exec p4_v1modelLib.v1model_arch_ty symb_exec1_actx symb_exec1_astate_symb [] [] (ASSUME T) (ASSUME T) 23

(* TODO: Something goes wrong here: *)
symb_exec p4_v1modelLib.v1model_arch_ty symb_exec1_actx symb_exec1_astate_symb [] [] (ASSUME T) (ASSUME T) 24

symb_exec p4_v1modelLib.v1model_arch_ty symb_exec1_actx symb_exec1_astate_symb [] [] (ASSUME T) (ASSUME T) 25

val _ = export_theory ();
