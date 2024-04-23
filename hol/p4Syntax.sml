structure p4Syntax :> p4Syntax =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open stringSyntax optionSyntax pairSyntax listSyntax
     wordsSyntax numSyntax bitstringSyntax;
open p4Theory;

val ERR = mk_HOL_ERR "p4Syntax"

fun dest_quinop c e tm =
   case with_exn strip_comb tm e of
      (t, [t1, t2, t3, t4, t5]) =>
         if same_const t c then (t1, t2, t3, t4, t5) else raise e
    | _ => raise e;
fun list_of_quintuple (a, b, c, d, e) = [a, b, c, d, e];
fun mk_quinop tm = HolKernel.list_mk_icomb tm o list_of_quintuple;
val syntax_fns5 = HolKernel.syntax_fns {n = 5, dest = dest_quinop, make = mk_quinop};

fun dest_sextop c e tm =
   case with_exn strip_comb tm e of
      (t, [t1, t2, t3, t4, t5, t6]) =>
         if same_const t c then (t1, t2, t3, t4, t5, t6) else raise e
    | _ => raise e;
fun list_of_sextuple (a, b, c, d, e, f) = [a, b, c, d, e, f];
fun mk_sextop tm = HolKernel.list_mk_icomb tm o list_of_sextuple;
val syntax_fns6 = HolKernel.syntax_fns {n = 6, dest = dest_sextop, make = mk_sextop};

fun dest_septop c e tm =
   case with_exn strip_comb tm e of
      (t, [t1, t2, t3, t4, t5, t6, t7]) =>
         if same_const t c then (t1, t2, t3, t4, t5, t6, t7) else raise e
    | _ => raise e;
fun list_of_septuple (a, b, c, d, e, f, g) = [a, b, c, d, e, f, g];
fun mk_septop tm = HolKernel.list_mk_icomb tm o list_of_septuple;
val syntax_fns7 = HolKernel.syntax_fns {n = 7, dest = dest_septop, make = mk_septop};

fun dest_octop c e tm =
   case with_exn strip_comb tm e of
      (t, [t1, t2, t3, t4, t5, t6, t7, t8]) =>
         if same_const t c then (t1, t2, t3, t4, t5, t6, t7, t8) else raise e
    | _ => raise e;
fun list_of_octuple (a, b, c, d, e, f, g, h) = [a, b, c, d, e, f, g, h];
fun mk_octop tm = HolKernel.list_mk_icomb tm o list_of_octuple;
val syntax_fns8 = HolKernel.syntax_fns {n = 8, dest = dest_octop, make = mk_octop};

fun dest_novop c e tm =
   case with_exn strip_comb tm e of
      (t, [t1, t2, t3, t4, t5, t6, t7, t8, t9]) =>
         if same_const t c then (t1, t2, t3, t4, t5, t6, t7, t8, t9) else raise e
    | _ => raise e;
fun list_of_novuple (a, b, c, d, e, f, g, h, i) = [a, b, c, d, e, f, g, h, i];
fun mk_novop tm = HolKernel.list_mk_icomb tm o list_of_novuple;
val syntax_fns9 = HolKernel.syntax_fns {n = 9, dest = dest_novop, make = mk_novop};

fun dest_decop c e tm =
   case with_exn strip_comb tm e of
      (t, [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10]) =>
         if same_const t c then (t1, t2, t3, t4, t5, t6, t7, t8, t9, t10) else raise e
    | _ => raise e;
fun list_of_decuple (a, b, c, d, e, f, g, h, i, j) = [a, b, c, d, e, f, g, h, i, j];
fun mk_decop tm = HolKernel.list_mk_icomb tm o list_of_decuple;
val syntax_fns10 = HolKernel.syntax_fns {n = 10, dest = dest_decop, make = mk_decop};

(* TODO: Move to ottSyntax *)
open ottTheory;
val (clause_name_tm,  mk_clause_name, dest_clause_name, is_clause_name) =
  syntax_fns1 "ott" "clause_name";

(********)
(* varn *)
(********)

val varn_ty = mk_type ("varn", []);

val (varn_name_tm,  mk_varn_name, dest_varn_name, is_varn_name) =
  syntax_fns1 "p4" "varn_name";

val varn_star_tm = prim_mk_const {Name="varn_star", Thy="p4"};
fun is_varn_star tm = term_eq tm varn_star_tm;


(*****)
(* v *)
(*****)

val v_ty = mk_type ("v", []);

val (e_v_tm,  mk_e_v, dest_e_v, is_e_v) =
  syntax_fns1 "p4" "e_v";

val (v_bit_tm, mk_v_bit, dest_v_bit, is_v_bit) =
  syntax_fns1 "p4" "v_bit";
fun mk_v_bitii (num, width) =
  mk_v_bit (mk_pair (mk_w2v $ mk_wordii (num, width), term_of_int width));
fun mk_v_biti_arb width =
  mk_v_bit (mk_pair (mk_list (List.tabulate (width, (fn w => (inst[Type.alpha |-> bool] arb))), bool), term_of_int width));

val (v_bool_tm, mk_v_bool, dest_v_bool, is_v_bool) =
  syntax_fns1 "p4" "v_bool";

val (v_str_tm, _, dest_v_str, is_v_str) =
  syntax_fns1 "p4" "v_str";
val mk_v_str = (#2 (syntax_fns1 "p4" "v_str")) o fromMLstring;

val (v_struct_tm, mk_v_struct, dest_v_struct, is_v_struct) =
  syntax_fns1 "p4" "v_struct";
fun mk_v_struct_list x_v_l =
  mk_v_struct (listSyntax.mk_list ((map (fn (a, b) => mk_pair (a, b)) x_v_l), ``:(string # v)``));

val (v_header_tm, mk_v_header, dest_v_header, is_v_header) =
  syntax_fns2 "p4" "v_header";
fun mk_v_header_list vbit x_v_l =
  mk_v_header (vbit, (listSyntax.mk_list ((map (fn (a, b) => mk_pair (a, b)) x_v_l), ``:(string # v) ``)));

val v_bot_tm = prim_mk_const {Name="v_bot", Thy="p4"};
fun is_v_bot tm = term_eq tm v_bot_tm;


(********)
(* lval *)
(********)

val lval_ty = mk_type ("lval", []);

val (lval_varname_tm, _, dest_lval_varname, is_lval_varname) =
  syntax_fns1 "p4" "lval_varname";
val mk_lval_varname = (#2 (syntax_fns1 "p4" "lval_varname")) o mk_varn_name o fromMLstring;

val (lval_field_tm, _, dest_lval_field, is_lval_field) =
  syntax_fns2 "p4" "lval_field";
val mk_lval_field = (fn (e, f) => (#2 (syntax_fns2 "p4" "lval_field")) (e, fromMLstring f));

val lval_null_tm = prim_mk_const {Name="lval_null", Thy="p4"};
fun is_lval_null tm = term_eq tm lval_null_tm;

(********)
(* funn *)
(********)

val (funn_name_tm, _, dest_funn_name, is_funn_name) =
  syntax_fns1 "p4" "funn_name";
val mk_funn_name = (#2 (syntax_fns1 "p4" "funn_name")) o fromMLstring;

val (funn_inst_tm, _, dest_funn_inst, is_funn_inst) =
  syntax_fns1 "p4" "funn_inst";
val mk_funn_inst = (#2 (syntax_fns1 "p4" "funn_inst")) o fromMLstring;

val (funn_ext_tm, _, dest_funn_ext, is_funn_ext) =
  syntax_fns2 "p4" "funn_ext";
val mk_funn_ext =
(#2 (syntax_fns2 "p4" "funn_ext")) o (fn (objname, metname) => (fromMLstring objname, fromMLstring metname));

(*****)
(* e *)
(*****)

val e_ty = mk_type ("e", []);

val (e_var_tm,  mk_e_var, dest_e_var, is_e_var) =
  syntax_fns1 "p4" "e_var";
val mk_e_var_name = (#2 (syntax_fns1 "p4" "e_var")) o mk_varn_name o fromMLstring;

val (e_list_tm,  mk_e_list, dest_e_list, is_e_list) =
  syntax_fns1 "p4" "e_list";

val (e_unop_tm,  mk_e_unop, dest_e_unop, is_e_unop) =
  syntax_fns2 "p4" "e_unop";
val (bitv_unop_tm, mk_bitv_unop, dest_bitv_unop, is_bitv_unop) =
  syntax_fns2 "p4" "bitv_unop";
val unop_neg_tm = prim_mk_const {Name="unop_neg", Thy="p4"};
val unop_compl_tm = prim_mk_const {Name="unop_compl", Thy="p4"};
val unop_neg_signed_tm = prim_mk_const {Name="unop_neg_signed", Thy="p4"};
val unop_un_plus_tm = prim_mk_const {Name="unop_un_plus", Thy="p4"};

val (e_cast_tm,  mk_e_cast, dest_e_cast, is_e_cast) =
  syntax_fns2 "p4" "e_cast";

val (e_binop_tm,  mk_e_binop, dest_e_binop, is_e_binop) =
  syntax_fns3 "p4"  "e_binop";
val (bitv_binop_tm, mk_bitv_binop, dest_bitv_binop, is_bitv_binop) =
  syntax_fns3 "p4"  "bitv_binop";
val binop_mul_tm = prim_mk_const {Name="binop_mul", Thy="p4"};
val binop_div_tm = prim_mk_const {Name="binop_div", Thy="p4"};
val binop_mod_tm = prim_mk_const {Name="binop_mod", Thy="p4"};
val binop_add_tm = prim_mk_const {Name="binop_add", Thy="p4"};
val binop_sub_tm = prim_mk_const {Name="binop_sub", Thy="p4"};
val binop_shl_tm = prim_mk_const {Name="binop_shl", Thy="p4"};
val binop_shr_tm = prim_mk_const {Name="binop_shr", Thy="p4"};
val binop_le_tm = prim_mk_const {Name="binop_le", Thy="p4"};
val binop_ge_tm = prim_mk_const {Name="binop_ge", Thy="p4"};
val binop_lt_tm = prim_mk_const {Name="binop_lt", Thy="p4"};
val binop_gt_tm = prim_mk_const {Name="binop_gt", Thy="p4"};
val binop_neq_tm = prim_mk_const {Name="binop_neq", Thy="p4"};
val binop_eq_tm = prim_mk_const {Name="binop_eq", Thy="p4"};
val binop_and_tm = prim_mk_const {Name="binop_and", Thy="p4"};
val binop_xor_tm = prim_mk_const {Name="binop_xor", Thy="p4"};
val binop_or_tm  = prim_mk_const {Name="binop_or",  Thy="p4"};
val binop_bin_and_tm = prim_mk_const {Name="binop_bin_and", Thy="p4"};
val binop_bin_or_tm  = prim_mk_const {Name="binop_bin_or",  Thy="p4"};

val (e_concat_tm,  mk_e_concat, dest_e_concat, is_e_concat) =
  syntax_fns2 "p4" "e_concat";

val (e_slice_tm,  mk_e_slice, dest_e_slice, is_e_slice) =
  syntax_fns3 "p4" "e_slice";

val (e_acc_tm, mk_e_acc_tmp, dest_e_acc, is_e_acc) =
  syntax_fns2 "p4" "e_acc";
val mk_e_acc =
  mk_e_acc_tmp o (fn (e_tm, fieldname) => (e_tm, fromMLstring fieldname));

val (e_call_tm, mk_e_call, dest_e_call, is_e_call) =
  syntax_fns2 "p4" "e_call";

val mk_e_ext_call_list =
  (fn (objname, metname, l) =>
   (#2 (syntax_fns2 "p4" "e_call")) (mk_funn_ext (objname, metname),
                                     listSyntax.mk_list (l, e_ty)));

val (e_select_tm,  mk_e_select, dest_e_select, is_e_select) =
  syntax_fns3 "p4" "e_select";

val (e_struct_tm,  mk_e_struct, dest_e_struct, is_e_struct) =
  syntax_fns1 "p4" "e_struct";

val (e_header_tm,  mk_e_header, dest_e_header, is_e_header) =
  syntax_fns2 "p4" "e_header";

val (s_sing_tm,  mk_s_sing, dest_s_sing, is_s_sing) =
  syntax_fns1 "p4" "s_sing";

val (s_range_tm,  mk_s_range, dest_s_range, is_s_range) =
  syntax_fns2 "p4" "s_range";

val (s_mask_tm,  mk_s_mask, dest_s_mask, is_s_mask) =
  syntax_fns2 "p4" "s_mask";

val s_univ_tm = prim_mk_const {Name="s_univ", Thy="p4"};
fun is_s_univ tm = term_eq tm s_univ_tm;

(*****)
(* d *)
(*****)

val d_in_tm = prim_mk_const {Name="d_in", Thy="p4"};
fun is_d_in tm = term_eq tm d_in_tm;

val d_out_tm = prim_mk_const {Name="d_out", Thy="p4"};
fun is_d_out tm = term_eq tm d_out_tm;

val d_inout_tm = prim_mk_const {Name="d_inout", Thy="p4"};
fun is_d_inout tm = term_eq tm d_inout_tm;

val d_none_tm = prim_mk_const {Name="d_none", Thy="p4"};
fun is_d_none tm = term_eq tm d_none_tm;


(*******)
(* tau *)
(*******)

val struct_ty_struct_tm = prim_mk_const {Name="struct_ty_struct", Thy="p4"};
fun is_struct_ty_struct tm = term_eq tm struct_ty_struct_tm;
val struct_ty_header_tm = prim_mk_const {Name="struct_ty_header", Thy="p4"};
fun is_struct_ty_header tm = term_eq tm struct_ty_header_tm;

val tau_ty = mk_type ("tau", []);

val tau_bool_tm = prim_mk_const {Name="tau_bool", Thy="p4"};
fun is_tau_bool tm = term_eq tm tau_bool_tm;

val (tau_bit_tm, mk_tau_bit_tmp, dest_tau_bit_tmp, is_tau_bit) =
  syntax_fns1 "p4" "tau_bit";
val mk_tau_bit =
  mk_tau_bit_tmp o (fn n => term_of_int n);
val dest_tau_bit =
  int_of_term o dest_tau_bit_tmp;

val (tau_xtl_tm, mk_tau_xtl_tmp, dest_tau_xtl, is_tau_xtl) =
  syntax_fns2 "p4" "tau_xtl";
fun mk_x_tau_l x_tau_l = mk_list (map mk_pair $ zip (map fromMLstring $ map fst x_tau_l) (map snd x_tau_l), “:(x # tau)”);
val mk_tau_struct =
  mk_tau_xtl_tmp o (fn x_tau_l => (struct_ty_struct_tm, mk_x_tau_l x_tau_l));
val mk_tau_header =
  mk_tau_xtl_tmp o (fn x_tau_l => (struct_ty_header_tm, mk_x_tau_l x_tau_l));


(********)
(* stmt *)
(********)

val stmt_empty_tm = prim_mk_const {Name="stmt_empty", Thy="p4"};
fun is_stmt_empty tm = term_eq tm stmt_empty_tm;
val (stmt_ass_tm, mk_stmt_ass, dest_stmt_ass, is_stmt_ass) =
  syntax_fns2 "p4"  "stmt_ass";
val (stmt_seq_tm, mk_stmt_seq, dest_stmt_seq, is_stmt_seq) =
  syntax_fns2 "p4"  "stmt_seq";
val (stmt_cond_tm, mk_stmt_cond, dest_stmt_cond, is_stmt_cond) =
  syntax_fns3 "p4"  "stmt_cond";
val (stmt_block_tm, mk_stmt_block, dest_stmt_block, is_stmt_block) =
  syntax_fns2 "p4"  "stmt_block";
val (stmt_ret_tm, mk_stmt_ret, dest_stmt_ret, is_stmt_ret) =
  syntax_fns1 "p4"  "stmt_ret";
val (stmt_trans_tm, mk_stmt_trans, dest_stmt_trans, is_stmt_trans) =
  syntax_fns1 "p4"  "stmt_trans";
val (stmt_app_tm, mk_stmt_app, dest_stmt_app, is_stmt_app) =
  syntax_fns2 "p4"  "stmt_app";
val stmt_ext_tm = prim_mk_const {Name="stmt_ext", Thy="p4"};
fun is_stmt_ext tm = term_eq tm stmt_ext_tm;

fun mk_stmt_seq_list' (h::[]) = h
  | mk_stmt_seq_list' (h::t) =
    mk_stmt_seq (h, mk_stmt_seq_list' t)
  | mk_stmt_seq_list' [] = stmt_empty_tm;
fun mk_stmt_seq_list [] = stmt_empty_tm
  | mk_stmt_seq_list [stmt] = stmt
  | mk_stmt_seq_list stmt_l = mk_stmt_seq_list' stmt_l;

val d_ty = mk_type ("d", []);

(*********)
(* State *)
(*********)

val scope_ty = mk_list_type $ mk_prod (varn_ty, mk_prod (v_ty, mk_option lval_ty));

val status_running_tm = prim_mk_const {Name="status_running", Thy="p4"};

fun dest_frame frame =
 case spine_pair frame of
    [funn, stmt_stack, scope_list] => (funn, stmt_stack, scope_list)
  | _ => raise (ERR "dest_frame" ("Unsupported frame shape: "^(term_to_string frame)))
;

(********)
(* Arch *)
(********)

val (arch_block_pbl_tm,  mk_arch_block_pbl, dest_arch_block_pbl, is_arch_block_pbl) =
  syntax_fns2 "p4" "arch_block_pbl";

val (arch_block_pbl_tm,  mk_arch_block_pbl, dest_arch_block_pbl, is_arch_block_pbl) =
  syntax_fns2 "p4" "arch_block_pbl";

val arch_frame_list_empty_tm = prim_mk_const {Name="arch_frame_list_empty", Thy="p4"};
fun is_arch_frame_list_empty tm = term_eq tm arch_frame_list_empty_tm;
val (arch_frame_list_regular_tm,  mk_arch_frame_list_regular, dest_arch_frame_list_regular, is_arch_frame_list_regular) =
  syntax_fns1 "p4" "arch_frame_list_regular";

fun dest_actx actx =
 case spine_pair actx of
    [ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_fun_map, func_map] => (ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_fun_map, func_map)
  | _ => raise (ERR "dest_actx" ("Unsupported actx shape: "^(term_to_string actx)))
;
fun dest_astate astate =
 case spine_pair astate of
    [aenv, g_scope_list, arch_frame_list, status] => (aenv, g_scope_list, arch_frame_list, status)
  | _ => raise (ERR "dest_astate" ("Unsupported astate shape: "^(term_to_string astate)))
;
(* TODO: Is this a hack? *)
fun dest_aenv aenv =
 let
  val (i, aenv') = dest_pair aenv
  val (io_list, aenv'') = dest_pair aenv'
  val (io_list', ascope) = dest_pair aenv''
 in
  (i, io_list, io_list', ascope)
 end
;

fun dest_pblock pblock =
 let
  val (pbl_type, pblock') = dest_pair pblock
  val (params, pblock'') = dest_pair pblock'
  val (b_func_map, pblock''') = dest_pair pblock''
  val (decl_list, pblock'''') = dest_pair pblock'''
  val (pars_map, tbl_map) = dest_pair pblock''''
 in
  (pbl_type, params, b_func_map, decl_list, pars_map, tbl_map)
 end
;


(**************)
(* Reductions *)
(**************)

val (e_red_tm,  mk_e_red, dest_e_red, is_e_red) =
  syntax_fns6 "p4" "e_red";

val (stmt_red_tm,  mk_stmt_red, dest_stmt_red, is_stmt_red) =
  syntax_fns3 "p4" "stmt_red";


(***********************)
(* Auxiliary functions *)
(***********************)

val (is_e_lval_tm, mk_is_e_lval, dest_is_e_lval, is_is_e_lval) =
  syntax_fns1 "p4" "is_e_lval";

val (lookup_vexp_tm, mk_lookup_vexp, dest_lookup_vexp, is_lookup_vexp) =
  syntax_fns2 "p4" "lookup_v";

val (lookup_funn_sig_tm, mk_lookup_funn_sig, dest_lookup_funn_sig, is_lookup_funn_sig) =
  syntax_fns4 "p4" "lookup_funn_sig";

val (assign_tm, mk_assign, dest_assign, is_assign) =
  syntax_fns3 "p4" "assign";

val (check_args_red_tm, mk_check_args_red, dest_check_args_red, is_check_args_red) =
  syntax_fns2 "p4" "check_args_red";

val (all_arg_update_for_newscope_tm, mk_all_arg_update_for_newscope, dest_all_arg_update_for_newscope, is_all_arg_update_for_newscope) =
  syntax_fns4 "p4" "all_arg_update_for_newscope";

val (unred_arg_index_tm, mk_unred_arg_index, dest_unred_arg_index, is_unred_arg_index) =
  syntax_fns2 "p4" "unred_arg_index";

val (match_all_tm,  mk_match_all, dest_match_all, is_match_all) =
  syntax_fns1 "p4" "match_all";

end
