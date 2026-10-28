structure p4_symb_execSyntax :> p4_symb_execSyntax =
struct

open HolKernel Abbrev;

open p4Syntax;
local open p4_symb_execTheory in end;

val (p4_contract_list_tm, mk_p4_contract_list, dest_p4_contract_list, is_p4_contract_list) =
 syntax_fns5 "p4_symb_exec" "p4_contract_list";

val (p4_contract_tm, mk_p4_contract, dest_p4_contract, is_p4_contract) =
 syntax_fns4 "p4_symb_exec" "p4_contract";

val (p4_contract'_tm, mk_p4_contract', dest_p4_contract', is_p4_contract') =
 syntax_fns3 "p4_symb_exec" "p4_contract'";

val (p4_contract_at_tm, mk_p4_contract_at, dest_p4_contract_at, is_p4_contract_at) =
 syntax_fns4 "p4_symb_exec" "p4_contract_at";

val (p4_finished_tm, mk_p4_finished, dest_p4_finished, is_p4_finished) =
 syntax_fns1 "p4_symb_exec" "p4_finished";

val (v1model_tbl_is_well_formed_tm, mk_v1model_tbl_is_well_formed, dest_v1model_tbl_is_well_formed, is_v1model_tbl_is_well_formed) =
 syntax_fns3 "p4_symb_exec" "v1model_tbl_is_well_formed";

val (wellformed_register_array_tm, mk_wellformed_register_array, dest_wellformed_register_array, is_wellformed_register_array) =
  syntax_fns2 "p4_symb_exec" "wellformed_register_array";

val (p4_assumption_tm, mk_p4_assumption, dest_p4_assumption, is_p4_assumption) =
  syntax_fns1 "p4_symb_exec" "p4_assumption";

end
