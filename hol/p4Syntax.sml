structure p4Syntax :> p4Syntax =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open stringSyntax optionSyntax pairSyntax finite_mapSyntax
     wordsSyntax numSyntax bitstringSyntax;
open p4Theory;


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

val varn_ext_ret_tm = prim_mk_const {Name="varn_ext_ret", Thy="p4"};
fun is_varn_ext_ret tm = term_eq tm varn_ext_ret_tm;

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

val (v_bool_tm, mk_v_bool, dest_v_bool, is_v_bool) =
  syntax_fns1 "p4" "v_bool";

val (v_str_tm, _, dest_v_str, is_v_str) =
  syntax_fns1 "p4" "v_str";
val mk_v_str = (#2 (syntax_fns1 "p4" "v_str")) o fromMLstring;

val (v_struct_tm, mk_v_struct, dest_v_struct, is_v_struct) =
  syntax_fns1 "p4" "v_struct";
fun mk_v_struct_list x_v_l =
  mk_v_struct (listSyntax.mk_list ((map (fn (a, b) => mk_pair (a, b)) x_v_l), ``:(string # v) ``));

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

val (e_unop_tm,  mk_e_unop, dest_e_unop, is_e_unop) =
  syntax_fns2 "p4" "e_unop";
val (bitv_unop_tm, mk_bitv_unop, dest_bitv_unop, is_bitv_unop) =
  syntax_fns2 "p4" "bitv_unop";
val unop_neg_tm = prim_mk_const {Name="unop_neg", Thy="p4"};
val unop_compl_tm = prim_mk_const {Name="unop_compl", Thy="p4"};
val unop_neg_signed_tm = prim_mk_const {Name="unop_neg_signed", Thy="p4"};
val unop_un_plus_tm = prim_mk_const {Name="unop_un_plus", Thy="p4"};

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

val (e_acc_tm, mk_e_acc, dest_e_acc, is_e_acc) =
  syntax_fns2 "p4" "e_acc";

val (e_call_tm, mk_e_call, dest_e_call, is_e_call) =
  syntax_fns2 "p4" "e_call";

val mk_e_ext_call_list =
  (fn (objname, metname, l) =>
   (#2 (syntax_fns2 "p4" "e_call")) (mk_funn_ext (objname, metname),
                                     listSyntax.mk_list (l, e_ty)));

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
  syntax_fns1 "p4"  "stmt_block";
val (stmt_ret_tm, mk_stmt_ret, dest_stmt_ret, is_stmt_ret) =
  syntax_fns1 "p4"  "stmt_ret";
val (stmt_app_tm, mk_stmt_app, dest_stmt_app, is_stmt_app) =
  syntax_fns2 "p4"  "stmt_app";

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

val arch_frame_list_empty_tm = prim_mk_const {Name="arch_frame_list_empty", Thy="p4"};

val scope_ty = mk_fmap_ty (varn_ty, mk_prod (v_ty, mk_option lval_ty));

val status_running_tm = prim_mk_const {Name="status_running", Thy="p4"};

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

val (lookup_vexp_tm, mk_lookup_vexp, dest_lookup_vexp, is_lookup_vexp) =
  syntax_fns2 "p4" "lookup_vexp";

val (assign_tm, mk_assign, dest_assign, is_assign) =
  syntax_fns3 "p4" "assign";

val (check_args_red_tm, mk_check_args_red, dest_check_args_red, is_check_args_red) =
  syntax_fns2 "p4" "check_args_red";

val (all_arg_update_for_newscope_tm, mk_all_arg_update_for_newscope, dest_all_arg_update_for_newscope, is_all_arg_update_for_newscope) =
  syntax_fns4 "p4" "all_arg_update_for_newscope";

val (unred_arg_index_tm, mk_unred_arg_index, dest_unred_arg_index, is_unred_arg_index) =
  syntax_fns2 "p4" "unred_arg_index";

end
