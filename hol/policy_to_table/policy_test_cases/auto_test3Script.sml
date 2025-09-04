open HolKernel boolLib liteLib simpLib Parse bossLib;

open policy_arith_to_varTheory;

open bdd_utilsLib;
open fwd_proofLib;   


val _ = new_theory "auto_test3";

val _ = type_abbrev("single_rule", “:((string# num list) action_expr) arith_rule”);
 
val test_pd_type = “[("ip", type_record [("priority", type_length 3);
                                         ("size", type_length 16);
                                         ("age", type_length 8);
                                         ("type", type_length 4)])]”;

val is_high_priority = “(arithm_le (lv_acc (lv_x "ip") "priority") ^(bdd_utilsLib.make_bv 2 3))”;
val is_medium_priority = “(arithm_ge (lv_acc (lv_x "ip") "priority") ^(bdd_utilsLib.make_bv 4 3))”;

val is_size_packet1 = “(arithm_ge (lv_acc (lv_x "ip") "size") ^(bdd_utilsLib.make_bv 30000 16))”;
val is_size_packet2 = “(arithm_ge (lv_acc (lv_x "ip") "size") ^(bdd_utilsLib.make_bv 27000 16))”;
val is_size_packet3 = “(arithm_ge (lv_acc (lv_x "ip") "size") ^(bdd_utilsLib.make_bv 25000 16))”;
val is_size_packet4 = “(arithm_ge (lv_acc (lv_x "ip") "size") ^(bdd_utilsLib.make_bv 23000 16))”;


val is_young_packet = “(arithm_ge (lv_acc (lv_x "ip") "age") ^(bdd_utilsLib.make_bv 200 8))”;

val is_control_type = “(arithm_le (lv_acc (lv_x "ip") "type") ^(bdd_utilsLib.make_bv 3 4))”;
val is_data_type = “(arithm_ge (lv_acc (lv_x "ip") "type") ^(bdd_utilsLib.make_bv 8 4))”;



val policy_me =   “[("x1", ^is_high_priority);
                    ("x2", ^is_medium_priority);

                    ("z1", ^is_size_packet1);
                    ("z2", ^is_size_packet2);
                    ("z3", ^is_size_packet3);
                    ("z4", ^is_size_packet4);

                    ("q1", ^is_control_type);
                    ("q2", ^is_data_type)]”;

val policy_full_order = “[("a",["x1";"x2"]);
                          ("b",["z1";"z2";"z3";"z4"]);
                          ("d",["q1";"q2"])]”;

val policy_order = “["x1";"x2";"z1";"z2";"z3";"z4";"q1";"q2"]”;

val arith_policy_rule1 = “(arith_and (arith_a ^is_high_priority) 
                                     (arith_and (arith_a ^is_size_packet1) (arith_a ^is_control_type)),
                           action ("fwd_priority",[1; 255])):single_rule”;

val arith_policy_rule2 = “(arith_and (arith_a ^is_high_priority) (arith_a ^is_size_packet2),
                           action ("fwd",[1])):single_rule”;

val arith_policy_rule3 = “(arith_and (arith_a ^is_high_priority) (arith_a ^is_size_packet3),
                           action ("fwd",[2])):single_rule”;

val arith_policy_rule4 = “(arith_and (arith_a ^is_high_priority) (arith_a ^is_size_packet4),
                           action ("fwd",[3])):single_rule”;

val arith_policy_rule5 = “(arith_and (arith_a ^is_medium_priority) 
                                     (arith_and (arith_a ^is_size_packet1) (arith_a ^is_data_type)),
                           action ("fwd_priority",[1; 4])):single_rule”;




(* Default forward rule *)
val arith_policy_rule_default = “(arith_a a_True,
                           action ("fwd",[5])):single_rule”;

val arith_policy =   “[^arith_policy_rule1;
                       ^arith_policy_rule2;
                       ^arith_policy_rule3;
                       ^arith_policy_rule4;
                       ^arith_policy_rule5;
                       ^arith_policy_rule_default]:single_rule list”;



val final_thm_res =
fwd_proofLib.convert_arith_policy_to_interval_tables (arith_policy, policy_me, test_pd_type, policy_full_order, policy_order);




                      
val _ = export_theory ();





             
