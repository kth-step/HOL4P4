open HolKernel boolLib liteLib simpLib Parse bossLib;
open policy_arith_to_varTheory;
open bdd_utilsLib;

val _ = new_theory "policy_min_example";


(* ---------------------------------------------------------------------------
   Policy Minimization Example 
 
   This script demonstrates PolyGram's policy minimization on a
   policy defined over three predicates:
 
     y1: tcp.dstport <= 1023   (standard service ports)
     y2: tcp.dstport >= 49152  (dynamic/ephemeral ports)
     z:  ip.ttl >= 2           (packet has enough hops left)
 
   
   The input policy has 9 rules with several issues:
     - Rules that are unreachable due to match-first semantics
     - Rules with unsatisfiable conditions (e.g. y1 AND y2, which is empty)
     - Rules that are subsumed by earlier rules
     - Redundant conditions within a single rule
 
   PolyGram generates a minimized policy and produces a certified proof
   that the minimized policy is semantically equivalent to the original.
   --------------------------------------------------------------------------- *)



Type single_rule = “:((string# num list) action_expr) arith_rule”;



(* Packet type descriptor: encodes the bit-vector width of each header field
   Used by trans-back to compute interval complements (Section IV-D) *)
val test_pd_type = “["h", type_record [("ip", type_record [ ("ttl", type_length 8);]);
                                       ("tcp", type_record [("dstPort", type_length 16)])]]”;



(* tcp.dstport <= 1023  (standard-service traffic) *)
val y1 = “(arithm_le (lv_acc (lv_acc (lv_x "h") "tcp") "dstPort") ^(bdd_utilsLib.make_bv 1023 16))”;

(* tcp.dstport >= 49152 (dynamic-port traffic) *)
val y2 = “(arithm_ge (lv_acc (lv_acc (lv_x "h") "tcp") "dstPort") ^(bdd_utilsLib.make_bv 49152 16))”;

(* ip.ttl >= 2 *)
val z = “(arithm_ge (lv_acc (lv_acc (lv_x "h") "ip") "ttl") ^(bdd_utilsLib.make_bv 2 8))”;


(* Lifted predicates *)

val a_y1 = “arith_a ^y1”;
val a_y2 = “arith_a ^y2”;
val a_z = “arith_a ^z”;


(* -----------------------------------------------------------------------
   Bloated input policy (9 rules)
 
   Rule 1: y1 AND z     : fwd(1)   standard ports, good TTL
   Rule 2: y1 AND z AND y2 ; fwd(1)   UNSATISFIABLE: y1 AND y2 is empty
                                          (disjoint port ranges)
   Rule 3: y2 AND z     : fwd(1)   dynamic ports, good TTL
   Rule 4: y1 AND NOT y1: fwd(2)   UNSATISFIABLE: always false
   Rule 5: y1           : fwd(1)   subsumes Rule 1 (no z needed)
                                          but comes AFTER Rule 1 in match-first!
   Rule 6: NOT y1 AND NOT y2 AND z ; fwd(1)  middle ports, good TTL
   Rule 7: y2 AND z AND NOT z ; fwd(1)  UNSATISFIABLE: z AND NOT z is empty
   Rule 8: NOT z        : fwd(2)   bad TTL -> fwd(2)
   Rule 9: y1 AND NOT z : fwd(1)   standard ports, bad TTL
                                          UNREACHABLE: Rule 8 fires first
   Default: drop
   ----------------------------------------------------------------------- *)




(* Rule 1: y1 AND z -> fwd(1) *)
val rule1 = “(arith_and ^a_y1 ^a_z,
              action ("fwd",[1])):single_rule”;
 
(* Rule 2: y1 AND z AND y2 -> fwd(1)  [UNSATISFIABLE: y1 AND y2 = empty] *)
val rule2 = “(arith_and ^a_y1 (arith_and ^a_z ^a_y2),
              action ("fwd",[1])):single_rule”;
 
(* Rule 3: y2 AND z -> fwd(1) *)
val rule3 = “(arith_and ^a_y2 ^a_z,
              action ("fwd",[1])):single_rule”;
 
(* Rule 4: y1 AND NOT y1 -> fwd(2)  [UNSATISFIABLE: always false] *)
val rule4 = “(arith_and ^a_y1 (arith_not ^a_y1),
              action ("fwd",[2])):single_rule”;
 
(* Rule 5: y1 -> fwd(1)  [comes after Rule 1, partially subsumed] *)
val rule5 = “(^a_y1,
              action ("fwd",[1])):single_rule”;
 
(* Rule 6: NOT y1 AND NOT y2 AND z -> fwd(1)  middle ports, good TTL *)
val rule6 = “(arith_and (arith_not ^a_y1) (arith_and (arith_not ^a_y2) ^a_z),
              action ("fwd",[1])):single_rule”;
 
(* Rule 7: y2 AND z AND NOT z -> fwd(1)  [UNSATISFIABLE: z AND NOT z = empty] *)
val rule7 = “(arith_and ^a_y2 (arith_and ^a_z (arith_not ^a_z)),
              action ("fwd",[1])):single_rule”;
 
(* Rule 8: NOT z -> fwd(2)  bad TTL *)
val rule8 = “(arith_not ^a_z,
              action ("fwd",[2])):single_rule”;
 
(* Rule 9: y1 AND NOT z -> fwd(1)  [UNREACHABLE: Rule 8 fires first] *)
val rule9 = “(arith_and ^a_y1 (arith_not ^a_z),
              action ("fwd",[1])):single_rule”;
 
val arith_policy_default = “(arith_a a_True, action ("drop",[])):single_rule”;
 
val arith_policy = “[
    ^rule1;
    ^rule2;
    ^rule3;
    ^rule4;
    ^rule5;
    ^rule6;
    ^rule7;
    ^rule8;
    ^rule9;
    ^arith_policy_default
]:single_rule list”;
 
(* -----------------------------------------------------------------------
   Mapping m
   ----------------------------------------------------------------------- *)
 
val policy_me = “[
    ("y1", ^y1);
    ("y2", ^y2);
    ("z",  ^z)
]”;
 
(* Variable order *)
val policy_order = “["y1"; "y2"; "z"]”;
 
(* -----------------------------------------------------------------------
   Policy minimization
   PolyGram generates a minimized policy and proves it equivalent to the
   bloated input policy above.
   ----------------------------------------------------------------------- *)
 
val final_thm_res_eq_cake = fwd_proof_gen_eq_cake.gen_eq_policy_and_prove
    (arith_policy, policy_me, test_pd_type, policy_order,
    "policy_min_example");
 


val _ = export_theory ();
