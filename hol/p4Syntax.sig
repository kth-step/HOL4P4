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

val v_ty : hol_type

val dest_e_v : term -> term
val e_v_tm : term
val is_e_v : term -> bool
val mk_e_v : term -> term

val dest_v_bit : term -> term
val is_v_bit : term -> bool
val mk_v_bit : term -> term
val v_bit_tm : term

val mk_v_bitii : int * int -> term
val mk_v_biti_arb : int -> term

val dest_v_bool : term -> term
val is_v_bool : term -> bool
val mk_v_bool : term -> term
val v_bool_tm : term

val dest_v_ext_ref : term -> term
val ext_ref_tm : term
val is_v_ext_ref : term -> bool
val mk_v_ext_ref : term -> term

val dest_v_str : term -> term
val is_v_str : term -> bool
val v_str_tm : term
val mk_v_str : string -> term

val dest_v_struct : term -> term
val is_v_struct : term -> bool
val mk_v_struct : term -> term
val v_struct_tm : term

val mk_v_struct_list : (term * term) list -> term

val dest_v_struct_fields : term -> term list

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

val dest_e_list : term -> term
val e_list_tm : term
val is_e_list : term -> bool
val mk_e_list : term -> term

val dest_e_unop : term -> term * term
val e_unop_tm : term
val is_e_unop : term -> bool
val mk_e_unop : term * term -> term

val bitv_unop_tm : term
val dest_bitv_unop : term -> term * term
val is_bitv_unop : term -> bool
val mk_bitv_unop : term * term -> term

val dest_e_cast : term -> term * term
val e_cast_tm : term
val is_e_cast : term -> bool
val mk_e_cast : term * term -> term

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

val dest_e_concat : term -> term * term
val e_concat_tm : term
val is_e_concat : term -> bool
val mk_e_concat : term * term -> term

val dest_e_slice : term -> term * term * term
val e_slice_tm : term
val is_e_slice : term -> bool
val mk_e_slice : term * term * term -> term

val dest_e_acc : term -> term * term
val e_acc_tm : term
val is_e_acc : term -> bool
val mk_e_acc : term * string -> term

val dest_e_call : term -> term * term
val e_call_tm : term
val is_e_call : term -> bool
val mk_e_call : term * term -> term

val mk_e_ext_call_list : string * string * term list -> term

val dest_e_select : term -> term * term * term
val e_select_tm : term
val is_e_select : term -> bool
val mk_e_select : term * term * term -> term

val dest_e_struct : term -> term
val e_struct_tm : term
val is_e_struct : term -> bool
val mk_e_struct : term -> term

val dest_e_header : term -> term * term
val e_header_tm : term
val is_e_header : term -> bool
val mk_e_header : term * term -> term

val dest_s_sing : term -> term
val is_s_sing : term -> bool
val mk_s_sing : term -> term
val s_sing_tm : term
val dest_s_range : term -> term * term
val is_s_range : term -> bool
val mk_s_range : term * term -> term
val s_range_tm : term
val dest_s_mask : term -> term * term
val is_s_mask : term -> bool
val mk_s_mask : term * term -> term
val s_mask_tm : term
val s_univ_tm : term
val is_s_univ : term -> bool

val d_in_tm : term
val is_d_in : term -> bool
val d_out_tm : term
val is_d_out : term -> bool
val d_inout_tm : term
val is_d_inout : term -> bool
val d_none_tm : term
val is_d_none : term -> bool

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

val dest_stmt_trans : term -> term
val is_stmt_trans : term -> bool
val mk_stmt_trans : term -> term
val stmt_trans_tm : term

val dest_stmt_cond : term -> term * term * term
val is_stmt_cond : term -> bool
val mk_stmt_cond : term * term * term -> term
val stmt_cond_tm : term

val dest_stmt_block : term -> term * term
val is_stmt_block : term -> bool
val mk_stmt_block : term * term -> term
val stmt_block_tm : term

val dest_stmt_ret : term -> term
val is_stmt_ret : term -> bool
val mk_stmt_ret : term -> term
val stmt_ret_tm : term

val dest_stmt_app : term -> term * term
val is_stmt_app : term -> bool
val mk_stmt_app : term * term -> term
val stmt_app_tm : term

val stmt_ext_tm : term
val is_stmt_ext : term -> bool

val mk_stmt_seq_list : term list -> term

val d_ty : hol_type



val scope_ty : hol_type

val status_running_tm : term
val is_status_running : term -> bool

val dest_status_trans : term -> term
val is_status_trans : term -> bool
val mk_status_trans : term -> term
val status_trans_tm : term

val dest_status_returnv : term -> term
val is_status_returnv : term -> bool
val mk_status_returnv : term -> term
val status_returnv_tm : term

val frame_ty : hol_type

val dest_frame : term -> term * term * term
val mk_frame : term * term * term -> term

val arch_block_pbl_tm : term
val dest_arch_block_pbl : term -> term * term
val is_arch_block_pbl : term -> bool
val mk_arch_block_pbl : term * term -> term

val arch_frame_list_empty_tm : term
val is_arch_frame_list_empty : term -> bool

val arch_frame_list_regular_tm : term
val dest_arch_frame_list_regular : term -> term
val is_arch_frame_list_regular : term -> bool
val mk_arch_frame_list_regular : term -> term

val dest_actx :
   term ->
     term * term * term * term * term * term * term * term * term * term
val dest_astate : term -> term * term * term * term
val mk_astate : term * term * term * term -> term
val dest_aenv : term -> term * term * term * term
val mk_aenv : term * term * term * term -> term
val dest_pblock : term -> term * term * term * term * term * term

val dest_e_red : term -> term * term * term * term * term * term
val e_red_tm : term
val is_e_red : term -> bool
val mk_e_red : term * term * term * term * term * term -> term

val struct_ty_struct_tm : term
val is_struct_ty_struct : term -> bool
val struct_ty_header_tm : term
val is_struct_ty_header : term  -> bool

val tau_ty : hol_type

val is_tau_bool : term -> bool
val tau_bool_tm : term

val is_tau_ext : term -> bool
val tau_ext_tm : term

val dest_tau_bit : term -> int
val is_tau_bit : term -> bool
val mk_tau_bit : int -> term
val tau_bit_tm : term

val dest_tau_xtl : term -> term * term
val is_tau_xtl : term -> bool
val tau_xtl_tm : term
val mk_tau_struct : (string * term) list -> term
val mk_tau_header : (string * term) list -> term

val dest_stmt_red : term -> term * term * term
val is_stmt_red : term -> bool
val mk_stmt_red : term * term * term -> term
val stmt_red_tm : term


val dest_is_e_lval : term -> term
val is_e_lval_tm : term
val is_is_e_lval : term -> bool
val mk_is_e_lval : term -> term

val dest_lookup_lval : term -> term * term
val is_lookup_lval : term -> bool
val lookup_lval_tm : term
val mk_lookup_lval : term * term -> term

val dest_lookup_funn_sig : term -> term * term * term * term
val is_lookup_funn_sig : term -> bool
val lookup_funn_sig_tm : term
val mk_lookup_funn_sig : term * term * term * term -> term

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

val dest_match_all : term -> term
val is_match_all : term -> bool
val match_all_tm : term
val mk_match_all : term -> term

end
