open HolKernel boolLib liteLib simpLib Parse bossLib;

open policy_arith_to_varTheory;

val _ = load "bdd_utils";   
val _ = load "fwd_proof";   


val _ = new_theory "auto_test1";


val _ = type_abbrev("single_rule", “:((string# num list) action_expr) arith_rule”);

 
val test_pd_type1 = “[("ip", type_record [("ttl", type_length 6)])]”;

val is_le_than_10 = “(arithm_le (lv_acc (lv_x "ip") "ttl") ^(BDDUtils.make_bv 10 6))”;
val is_ge_than_10 = “(arithm_ge (lv_acc (lv_x "ip") "ttl") ^(BDDUtils.make_bv 10 6))”;

val is_ge_than_30 = “(arithm_ge (lv_acc (lv_x "ip") "ttl") ^(BDDUtils.make_bv 30 6))”;
val is_le_than_9  = “(arithm_le (lv_acc (lv_x "ip") "ttl") ^(BDDUtils.make_bv 9 6))”;


val policy_me1 =   “[("x", ^is_le_than_10)]”;

val policy_full_order1 = “[("a",["x"])]”;

val policy_order1 = “["x"]”;

(* Rule 1: ttl <= 10 : accept *)
val arith_policy_rule1 = “((arith_a ^is_le_than_10),
                           action ("accept",[])):single_rule”;

(* Default forward rule *)
val arith_policy_default = “(arith_a a_True,
                           action ("reject",[])):single_rule”;

val arith_policy1 =   “[^arith_policy_rule1;
                       ^arith_policy_default]:single_rule list”;



val final_thm_res1 =
mk_fwd_proof.convert_arith_policy_to_interval_tables (arith_policy1, policy_me1, test_pd_type1, policy_full_order1, policy_order1);

(*********************************)

val arith_policy_rule2 = “((arith_a ^is_ge_than_30),
                           action ("accept",[])):single_rule”;


val arith_policy2 =   “[^arith_policy_rule2;
                       ^arith_policy_default]:single_rule list”;

val policy_me2 =   “[("x", ^is_ge_than_30)]”;


val final_thm_res2 =
mk_fwd_proof.convert_arith_policy_to_interval_tables (arith_policy2, policy_me2, test_pd_type1, policy_full_order1, policy_order1);

(***********************)

val arith_policy_rule3 = “(arith_or (arith_a ^is_ge_than_10) (arith_a ^is_le_than_9),
                           action ("reject",[])):single_rule”;



val arith_policy3 =   “[^arith_policy_default;
                       ^arith_policy_rule3]:single_rule list”;

val policy_me3 =   “[("x", ^is_ge_than_10);("y", ^is_le_than_9)]”;

val policy_full_order3 = “[("a",["x";"y"])]”;

val policy_order3 = “["x";"y"]”;


val final_thm_res3 =
mk_fwd_proof.convert_arith_policy_to_interval_tables (arith_policy3, policy_me3, test_pd_type1, policy_full_order3, policy_order3);







                      
val _ = export_theory ();





             
