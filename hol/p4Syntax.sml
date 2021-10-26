structure p4Syntax :> p4Syntax =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open stringSyntax optionSyntax pairSyntax finite_mapSyntax;
open p4Theory;


fun dest_septop c e tm =
   case with_exn strip_comb tm e of
      (t, [t1, t2, t3, t4, t5, t6, t7]) =>
         if same_const t c then (t1, t2, t3, t4, t5, t6, t7) else raise e
    | _ => raise e;
fun list_of_septuple (a, b, c, d, e, f, g) = [a, b, c, d, e, f, g];
fun mk_septop tm = HolKernel.list_mk_icomb tm o list_of_septuple;
val syntax_fns7 = HolKernel.syntax_fns {n = 7, dest = dest_septop, make = mk_septop};

fun dest_quinop c e tm =
   case with_exn strip_comb tm e of
      (t, [t1, t2, t3, t4, t5]) =>
         if same_const t c then (t1, t2, t3, t4, t5) else raise e
    | _ => raise e;
fun list_of_quintuple (a, b, c, d, e) = [a, b, c, d, e];
fun mk_quinop tm = HolKernel.list_mk_icomb tm o list_of_quintuple;
val syntax_fns5 = HolKernel.syntax_fns {n = 5, dest = dest_quinop, make = mk_quinop};

(* TODO: Move to ottSyntax *)
open ottTheory;
val (clause_name_tm,  mk_clause_name, dest_clause_name, is_clause_name) =
  syntax_fns1 "ott" "clause_name";

(*****)
(* v *)
(*****)

val v_ty = mk_type ("v", []);

val (e_v_tm,  mk_e_v, dest_e_v, is_e_v) =
  syntax_fns1 "p4" "e_v";

val (v_bit_tm, mk_v_bit, dest_v_bit, is_v_bit) =
  syntax_fns1 "p4" "v_bit";
val (v_bool_tm, mk_v_bool, dest_v_bool, is_v_bool) =
  syntax_fns1 "p4" "v_bool";

(********)
(* lval *)
(********)

val (lval_varname_tm, mk_lval_varname, dest_lval_varname, is_lval_varname) =
  syntax_fns1 "p4" "lval_varname";

val lval_null_tm = prim_mk_const {Name="lval_null", Thy="p4"};
fun is_lval_null tm = term_eq tm lval_null_tm;

(*****)
(* e *)
(*****)

val e_ty = mk_type ("e", []);

val (e_var_tm,  mk_e_var, dest_e_var, is_e_var) =
  syntax_fns1 "p4" "e_var";

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

val (e_func_call_tm, mk_e_func_call, dest_e_func_call, is_e_func_call) =
  syntax_fns2 "p4"  "e_func_call";

(********)
(* stmt *)
(********)

val stmt_empty_tm = prim_mk_const {Name="stmt_empty", Thy="p4"};
fun is_stmt_empty tm = term_eq tm stmt_empty_tm;
val (stmt_ass_tm, mk_stmt_ass, dest_stmt_ass, is_stmt_ass) =
  syntax_fns2 "p4"  "stmt_ass";
val (stmt_seq_tm, mk_stmt_seq, dest_stmt_seq, is_stmt_seq) =
  syntax_fns2 "p4"  "stmt_seq";

val d_ty = mk_type ("d", []);

(*********)
(* State *)
(*********)

val scope_ty = mk_fmap_ty (string_ty, mk_prod (v_ty, mk_option string_ty));

val (state_tup_tm, mk_state_tup, dest_state_tup, is_state_tup) =
  syntax_fns2 "p4" "state_tup";

val (called_function_name_function_name_tm, mk_called_function_name_function_name, dest_called_function_name_function_name, is_called_function_name_function_name) =
  syntax_fns1 "p4"  "called_function_name_function_name";

val (stacks_tup_tm, mk_stacks_tup, dest_stacks_tup, is_stacks_tup) =
  syntax_fns2 "p4" "stacks_tup";

(**************)
(* Reductions *)
(**************)

val (e_red_tm,  mk_e_red, dest_e_red, is_e_red) =
  syntax_fns7 "p4" "e_red";

val (stmt_red_tm,  mk_stmt_red, dest_stmt_red, is_stmt_red) =
  syntax_fns5 "p4" "stmt_red";

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
