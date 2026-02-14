open HolKernel boolLib liteLib simpLib Parse bossLib;
open policy_arith_to_varTheory;
open bdd_utilsLib;

val _ = new_theory "test_poly_eq";



val _ = type_abbrev("single_rule", “:((string# num list) action_expr) arith_rule”);



val test_pd_type = “[("h", type_record [("srcPort", type_length 16)])]”;

(************************************************)

(* rule 1 *)

val is_srcPort_le_57222 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 57222 16))”;
val is_srcPort_ge_57222 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 57222 16))”;


val arith_policy_rule1 = “((arith_and (arith_a ^is_srcPort_le_57222)
                           (arith_a ^is_srcPort_ge_57222)) ,
                           action ("allow",[1])):single_rule”;

(* Default policy rule *)
val arith_policy_rule_default = “(arith_a a_True, action ("drop", [])):single_rule”;

(* Combined arith policy list *)
val arith_policy1 = “[
    ^arith_policy_rule1;
    ^arith_policy_rule_default
]:single_rule list”;


val arith_policy2 = “[
    ^arith_policy_rule1;
    ^arith_policy_rule1;
    ^arith_policy_rule_default
]:single_rule list”;



(* Combined policy mapping *)
val policy_me =   “[
    ("is_srcPort_le_57222", ^is_srcPort_le_57222);
    ("is_srcPort_ge_57222", ^is_srcPort_ge_57222)
]”;


(******************************)
(*   Best output table order  *)
(******************************)

(* Grouped policy ordering *)
val policy_full_order = “[
  ("srcPortGrp",["is_srcPort_le_57222";"is_srcPort_ge_57222"])
]”;

(* Flat policy order (grouped) *)
val policy_order = “["is_srcPort_le_57222"; "is_srcPort_ge_57222"]”;

val policy_eq_thm = fwd_proof_polcies_cakeLib.check_two_polcies_eq (arith_policy1, arith_policy2, policy_me, test_pd_type, policy_full_order, policy_order, "internet_firewall_1");

val _ = export_theory ();
