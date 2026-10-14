structure p4_symb_execSyntax :> p4_symb_execSyntax =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open p4Syntax;
open p4_symb_execTheory;

val (p4_contract_list_tm, mk_p4_contract_list, dest_p4_contract_list, is_p4_contract_list) =
 syntax_fns5 "p4_symb_exec" "p4_contract_list";

val (p4_contract_tm, mk_p4_contract, dest_p4_contract, is_p4_contract) =
 syntax_fns4 "p4_symb_exec" "p4_contract";

val (p4_contract'_tm, mk_p4_contract', dest_p4_contract', is_p4_contract') =
 syntax_fns3 "p4_symb_exec" "p4_contract'";

val (wellformed_register_array_tm, mk_wellformed_register_array, dest_wellformed_register_array, is_wellformed_register_array) =
  syntax_fns2 "p4_symb_exec" "wellformed_register_array";

end
