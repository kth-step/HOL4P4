open HolKernel boolLib liteLib simpLib Parse bossLib;

open policy_arith_to_varTheory;

open bdd_utilsLib;
open fwd_proofLib;   


val _ = new_theory "internet_firewall_template";

val _ = type_abbrev("single_rule", “:((string# num list) action_expr) arith_rule”);
 
val test_pd_type = “[("h", type_record [("srcPort", type_length 16);
                                        ("dstPort", type_length 16);
                                        ("srcNAT", type_length 16);
                                        ("dstNAT", type_length 16)])]”;

(************************************************)
(***********************************************)

(*val final_thm_res =
fwd_proofLib.convert_arith_policy_to_interval_tables (arith_policy, policy_me, test_pd_type, policy_full_order, policy_order);
*)
                      
val _ = export_theory ();
