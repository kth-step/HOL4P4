signature p4Syntax =
sig
  include Abbrev

val clause_name_tm : term
val dest_clause_name : term -> term
val is_clause_name : term -> bool
val mk_clause_name : term -> term

val dest_varn_name : term -> term
val is_varn_name : term -> bool
val mk_varn_name : term -> term
val varn_name_tm : term

val varn_star_tm : term
val is_varn_star : term -> bool

val varn_ext_ret_tm : term
val is_varn_ext_ret : term -> bool

val dest_e_v : term -> term
val e_v_tm : term
val is_e_v : term -> bool
val mk_e_v : term -> term

val dest_v_bit : term -> term
val is_v_bit : term -> bool
val mk_v_bit : term -> term
val v_bit_tm : term

val mk_v_bitii : int * int -> term

val dest_v_bool : term -> term
val is_v_bool : term -> bool
val mk_v_bool : term -> term
val v_bool_tm : term

val dest_v_str : term -> term
val is_v_str : term -> bool
val v_str_tm : term
val mk_v_str : string -> term

val dest_v_struct : term -> term
val is_v_struct : term -> bool
val mk_v_struct : term -> term
val v_struct_tm : term

val mk_v_struct_list : (term * term) list -> term

val dest_v_header : term -> term * term
val is_v_header : term -> bool
val mk_v_header : term * term -> term
val v_header_tm : term

val mk_v_header_list : term -> (term * term) list -> term

val v_bot_tm : term
val is_v_bot : term -> bool

val dest_lval_varname : term -> term
val is_lval_varname : term -> bool
val lval_varname_tm : term
val mk_lval_varname : string -> term

val dest_lval_field : term -> term * term
val is_lval_field : term -> bool
val lval_field_tm : term
val mk_lval_field : term * string -> term

val lval_null_tm : term
val is_lval_null : term -> bool


val dest_funn_name : term -> term
val funn_name_tm : term
val is_funn_name : term -> bool
val mk_funn_name : string -> term

val dest_funn_inst : term -> term
val funn_inst_tm : term
val is_funn_inst : term -> bool
val mk_funn_inst : string -> term

val dest_funn_ext : term -> term * term
val funn_ext_tm : term
val is_funn_ext : term -> bool
val mk_funn_ext : string * string -> term

val e_ty : hol_type

val dest_e_var : term -> term
val e_var_tm : term
val is_e_var : term -> bool
val mk_e_var : term -> term
val mk_e_var_name : string -> term

val dest_e_unop : term -> term * term
val e_unop_tm : term
val is_e_unop : term -> bool
val mk_e_unop : term * term -> term

val bitv_unop_tm : term
val dest_bitv_unop : term -> term * term
val is_bitv_unop : term -> bool
val mk_bitv_unop : term * term -> term

val unop_neg_tm : term
val unop_compl_tm : term
val unop_neg_signed_tm : term
val unop_un_plus_tm : term

val dest_e_binop : term -> term * term * term
val e_binop_tm : term
val is_e_binop : term -> bool
val mk_e_binop : term * term * term -> term

val bitv_binop_tm : term
val dest_bitv_binop : term -> term * term * term
val is_bitv_binop : term -> bool
val mk_bitv_binop : term * term * term -> term

val binop_mul_tm : term
val binop_div_tm : term
val binop_mod_tm : term
val binop_add_tm : term
val binop_sub_tm : term
val binop_shl_tm : term
val binop_shr_tm : term
val binop_le_tm : term
val binop_ge_tm : term
val binop_lt_tm : term
val binop_gt_tm : term
val binop_neq_tm : term
val binop_eq_tm : term
val binop_and_tm : term
val binop_xor_tm : term
val binop_or_tm : term
val binop_bin_and_tm : term
val binop_bin_or_tm : term

val dest_e_acc : term -> term * term
val e_acc_tm : term
val is_e_acc : term -> bool
val mk_e_acc : term * term -> term

val dest_e_call : term -> term * term
val e_call_tm : term
val is_e_call : term -> bool
val mk_e_call : term * term -> term

val mk_e_ext_call_list : string * string * term list -> term

val stmt_empty_tm : term
val is_stmt_empty : term -> bool

val dest_stmt_ass : term -> term * term
val is_stmt_ass : term -> bool
val mk_stmt_ass : term * term -> term
val stmt_ass_tm : term

val dest_stmt_seq : term -> term * term
val is_stmt_seq : term -> bool
val mk_stmt_seq : term * term -> term
val stmt_seq_tm : term

val dest_stmt_cond : term -> term * term * term
val is_stmt_cond : term -> bool
val mk_stmt_cond : term * term * term -> term
val stmt_cond_tm : term

val dest_stmt_block : term -> term
val is_stmt_block : term -> bool
val mk_stmt_block : term -> term
val stmt_block_tm : term

val dest_stmt_ret : term -> term
val is_stmt_ret : term -> bool
val mk_stmt_ret : term -> term
val stmt_ret_tm : term

val dest_stmt_app : term -> term * term
val is_stmt_app : term -> bool
val mk_stmt_app : term * term -> term
val stmt_app_tm : term

val mk_stmt_seq_list : term list -> term

val d_ty : hol_type


val arch_frame_list_empty_tm : term

val scope_ty : hol_type

val status_running_tm : term


val dest_e_red : term -> term * term * term * term * term * term
val e_red_tm : term
val is_e_red : term -> bool
val mk_e_red : term * term * term * term * term * term -> term

val dest_stmt_red : term -> term * term * term
val is_stmt_red : term -> bool
val mk_stmt_red : term * term * term -> term
val stmt_red_tm : term


val dest_lookup_vexp : term -> term * term
val is_lookup_vexp : term -> bool
val lookup_vexp_tm : term
val mk_lookup_vexp : term * term -> term

val dest_assign : term -> term * term * term
val is_assign : term -> bool
val assign_tm : term
val mk_assign : term * term * term -> term

val check_args_red_tm : term
val dest_check_args_red : term -> term * term
val is_check_args_red : term -> bool
val mk_check_args_red : term * term -> term

val all_arg_update_for_newscope_tm : term
val dest_all_arg_update_for_newscope : term -> term * term * term * term
val is_all_arg_update_for_newscope : term -> bool
val mk_all_arg_update_for_newscope : term * term * term * term -> term

val dest_unred_arg_index : term -> term * term
val is_unred_arg_index : term -> bool
val mk_unred_arg_index : term * term -> term
val unred_arg_index_tm : term

end
