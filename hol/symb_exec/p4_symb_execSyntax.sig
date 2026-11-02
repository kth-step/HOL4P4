signature p4_symb_execSyntax =
sig
  include Abbrev

val p4_contract_list_tm : term
val mk_p4_contract_list : term * term * term * term * term -> term
val dest_p4_contract_list : term -> term * term * term * term * term
val is_p4_contract_list : term -> bool

val p4_contract_tm : term
val mk_p4_contract : term * term * term * term -> term
val dest_p4_contract : term -> term * term * term * term
val is_p4_contract : term -> bool

val p4_contract'_tm : term
val mk_p4_contract' : term * term * term -> term
val dest_p4_contract' : term -> term * term * term
val is_p4_contract' : term -> bool

val p4_contract_at_tm : term
val mk_p4_contract_at : term * term * term * term -> term
val dest_p4_contract_at : term -> term * term * term * term
val is_p4_contract_at : term -> bool

val p4_finished_tm : term
val mk_p4_finished : term -> term
val dest_p4_finished : term -> term
val is_p4_finished : term -> bool

val v1model_tbl_is_well_formed_tm : term
val mk_v1model_tbl_is_well_formed : term * term * term -> term
val dest_v1model_tbl_is_well_formed : term -> term * term * term
val is_v1model_tbl_is_well_formed : term -> bool

val wellformed_register_array_tm : term
val mk_wellformed_register_array : term * term -> term
val dest_wellformed_register_array : term -> term * term
val is_wellformed_register_array : term -> bool

val p4_assumption_tm : term
val mk_p4_assumption : term -> term
val dest_p4_assumption : term -> term
val is_p4_assumption : term -> bool

end
