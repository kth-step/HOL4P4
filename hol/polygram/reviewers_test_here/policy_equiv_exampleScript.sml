open HolKernel boolLib liteLib simpLib Parse bossLib;
open policy_arith_to_varTheory;
open bdd_utilsLib;

val _ = new_theory "policy_equiv_example";


(* ---------------------------------------------------------------------------
   Policy Equivalence Example 
 
   This script shows PolyGram's policy equivalence checking using
   match-first semantics. Two policies are defined over three predicates:
 
     y1: tcp.dstport <= 1023   (standard service ports)
     y2: tcp.dstport >= 49152  (dynamic/ephemeral ports)
     z:  ip.ttl >= 2           (packet has enough hops left)
 
 
   Both policies forward a packet (fwd(1)) when:
     - it is a standard-service packet (y1), OR
     - it is not standard-service but has sufficient TTL (NOT y1 AND z)
 
   Otherwise they use fwd(2).
 
   Policy 1 has a redundant Rule 4 (y2 is a subset of NOT y1, so
   Rule 2 always fires first for y2 packets with z).
 
   Policy 2 has a redundant Rule 4 (NOT z AND NOT y1 already covers
   y2 AND NOT z in Rule 3, so Rule 4 never fires).
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
   POLICY 1
   Rule 1: y1               : fwd(1)  standard ports -> forward
   Rule 2: NOT y1 AND z     : fwd(1)  non-standard, good TTL -> forward
   Rule 3: NOT y1 AND NOT z : fwd(2)  non-standard, bad TTL -> fwd(2)
   Rule 4: y2 AND z         : fwd(1)  REDUNDANT: y2 subset of NOT y1,
                                       Rule 2 always fires first for y2 AND z
   Default: drop
   ----------------------------------------------------------------------- *)
 
val p1_rule1 = “(^a_y1,
                action ("fwd",[1])):single_rule”;
 
val p1_rule2 = “(arith_and (arith_not ^a_y1) ^a_z,
                action ("fwd",[1])):single_rule”;
 
val p1_rule3 = “(arith_and (arith_not ^a_y1) (arith_not ^a_z),
                action ("fwd",[2])):single_rule”;
 
(* This rule is redundant: y2 implies NOT y1, so Rule 2 catches y2 AND z first *)
val p1_rule4 = “(arith_and ^a_y2 ^a_z,
                action ("fwd",[1])):single_rule”;
 
val p1_default = “(arith_a a_True, action ("drop",[])):single_rule”;
 
val arith_policy1 = “[
    ^p1_rule1;
    ^p1_rule2;
    ^p1_rule3;
    ^p1_rule4;
    ^p1_default
]:single_rule list”;
 
(* -----------------------------------------------------------------------
   POLICY 2
   Rule 1: z                : fwd(1)  good TTL -> forward
   Rule 2: NOT z AND y1     : fwd(1)  bad TTL but standard ports -> forward
   Rule 3: NOT z AND NOT y1 : fwd(2)  bad TTL, non-standard -> fwd(2)
   Rule 4: y2 AND NOT z     : fwd(2)  REDUNDANT: y2 AND NOT z is a subset
                                       of NOT z AND NOT y1, Rule 3 fires first
   Default: drop
   ----------------------------------------------------------------------- *)
 
val p2_rule1 = “(^a_z,
                action ("fwd",[1])):single_rule”;
 
val p2_rule2 = “(arith_and (arith_not ^a_z) ^a_y1,
                action ("fwd",[1])):single_rule”;
 
val p2_rule3 = “(arith_and (arith_not ^a_z) (arith_not ^a_y1),
                action ("fwd",[2])):single_rule”;
 
(* This rule is redundant: y2 AND NOT z is already covered by Rule 3 *)
val p2_rule4 = “(arith_and ^a_y2 (arith_not ^a_z),
                action ("fwd",[2])):single_rule”;
 
val p2_default = “(arith_a a_True, action ("drop",[])):single_rule”;
 
val arith_policy2 = “[
    ^p2_rule1;
    ^p2_rule2;
    ^p2_rule3;
    ^p2_rule4;
    ^p2_default
]:single_rule list”;
 
(* -----------------------------------------------------------------------
   Mapping m — shared across both policies
   ----------------------------------------------------------------------- *)
 
val policy_me = “[
    ("y1", ^y1);
    ("y2", ^y2);
    ("z",  ^z)
]”;
 
(* Variable order *)
val policy_order = “["y1"; "y2"; "z"]”;
 
(* -----------------------------------------------------------------------
   Equivalence check
   ----------------------------------------------------------------------- *)
 
val eq_thm = fwd_proof_polcies_cakeLib.check_two_polcies_eq
    (arith_policy1, arith_policy2, policy_me, test_pd_type, policy_order,
    "policy_equiv_example");
 
val _ = export_theory ();
