open HolKernel boolLib liteLib simpLib Parse bossLib;

open policy_arith_to_varTheory;

val _ = load "bdd_utils";   
val _ = load "fwd_proof";   


val _ = new_theory "auto_test_pipeline";


val _ = type_abbrev("single_rule", “:((string# num list) action_expr) arith_rule”);

 
val test_pd_type = “[("ip", type_record [("priority", type_length 3);
                                         ("size", type_length 16);
                                         ("age", type_length 8);
                                         ("type", type_length 4)])]”;

val is_high_priority = “(arithm_le (lv_acc (lv_x "ip") "priority") ^(BDDUtils.make_bv 2 3))”;
val is_medium_priority = “(arithm_ge (lv_acc (lv_x "ip") "priority") ^(BDDUtils.make_bv 4 3))”;
val is_small_packet = “(arithm_le (lv_acc (lv_x "ip") "size") ^(BDDUtils.make_bv 500 16))”;
val is_young_packet = “(arithm_ge (lv_acc (lv_x "ip") "age") ^(BDDUtils.make_bv 200 8))”;
val is_control_type = “(arithm_le (lv_acc (lv_x "ip") "type") ^(BDDUtils.make_bv 3 4))”;
val is_data_type = “(arithm_ge (lv_acc (lv_x "ip") "type") ^(BDDUtils.make_bv 8 4))”;

val policy_me =   “[("x", ^is_high_priority);
                    ("y", ^is_medium_priority);
                    ("z", ^is_small_packet);
                    ("w", ^is_young_packet);
                    ("q", ^is_control_type);
                    ("r", ^is_data_type)]”;

val policy_full_order = “[("a",["x";"y"]);
                          ("b",["z"]);
                          ("c",["w"]);
                          ("d",["q";"r"])]”;

val policy_order = “["x";"y";"z";"w";"q";"r"]”;

(* Rule 1: High priority small control packets - expedited forwarding *)
val arith_policy_rule1 = “(arith_and (arith_a ^is_high_priority) 
                                     (arith_and (arith_a ^is_small_packet) (arith_a ^is_control_type)),
                           action ("fwd_priority",[1; 255])):single_rule”;

(* Rule 2: High priority data packets *)
val arith_policy_rule2 = “(arith_and (arith_a ^is_high_priority) (arith_a ^is_data_type),
                           action ("fwd",[1])):single_rule”;

(* Rule 3: Medium priority young packets *)
val arith_policy_rule3 = “(arith_and (arith_a ^is_medium_priority) (arith_a ^is_young_packet),
                           action ("fwd",[2])):single_rule”;

(* Rule 7: Default forward rule *)
val arith_policy_rule7 = “(arith_a a_True,
                           action ("fwd",[5])):single_rule”;

val arith_policy =   “[^arith_policy_rule1;
                       ^arith_policy_rule2;
                       ^arith_policy_rule3;
                       ^arith_policy_rule7]:single_rule list”;



val final_thm_res =
mk_fwd_proof.convert_arith_policy_to_interval_tables (arith_policy, policy_me, test_pd_type, policy_full_order, policy_order);

                      
val _ = export_theory ();





             
