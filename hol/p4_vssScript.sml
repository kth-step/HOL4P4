open HolKernel boolLib Parse bossLib ottLib;

open p4Theory;

val _ = new_theory "p4_vss";


(**********************)
(* Checksum16 methods *)
(**********************)

(*********)
(* clear *)

Definition clear:
 (clear (ext_obj_name, e_l, (state_tup (stacks_tup frame call_stack) status)) =
  case e_l of
  | [] =>
   (case assign frame (v_ext (ext_obj_ck 0w)) (lval_varname ext_obj_name) of
    | SOME frame' =>
     SOME (v_bot, state_tup (stacks_tup frame' call_stack) status)
    | NONE => NONE)
  | _ => NONE
 )
End


(**********)
(* update *)

Definition lookup_ipv4_checksum:
 (lookup_ipv4_checksum frame ext_obj_name =
  case lookup_v frame ext_obj_name of
  | (v_ext (ext_obj_ck ipv4_checksum)) => SOME ipv4_checksum
  | _ => NONE
 )
End

(* TODO: Add recursive cases *)
Definition header_entry2v:
 (header_entry2v (x, v) =
  case v of
  | (v_bit (bl, n)) => SOME bl
  | _ => NONE
 )
End

Definition header_entries2v:
 (header_entries2v [] = SOME []) /\
 (header_entries2v (h::t) =
  case header_entry2v h of
  | SOME bl =>
  (case header_entries2v t of
   | SOME bl2 => SOME (bl++bl2)
   | NONE => NONE)
  | NONE => NONE
 )
End

TotalDefn.tDefine "v2w16s'" `
 (v2w16s' [] = []) /\
 (v2w16s' v =
  ((v2w (TAKE 16 v)):word16)::(v2w16s' (DROP 16 v))
 )`
(WF_REL_TAC `measure LENGTH` >>
 fs []);

Definition v2w16s:
 (v2w16s v = if (LENGTH v) MOD 16 = 0 then SOME (v2w16s' v) else NONE)
End

Definition get_checksum_incr:
 (get_checksum_incr frame e_l =
  case e_l of
  | [e_v v] =>
   (case v of
    | (v_bit (bl, n)) => if n = 16 then SOME ((v2w bl):word16) else NONE
    | (v_header vbit h_list) =>
     (case header_entries2v h_list of
      | SOME bl =>
       (case v2w16s bl of
	| SOME w16s => SOME (FOLDL word_add (0w) w16s)
	| NONE => NONE)
      | NONE => NONE)
    | _ => NONE)
  | _ => NONE
 )
End

Definition update:
 (update (ext_obj_name, e_l, (state_tup (stacks_tup frame call_stack) status)) =
  case lookup_ipv4_checksum frame ext_obj_name of
  | SOME ipv4_checksum =>
  (case get_checksum_incr frame e_l of
   | SOME checksum_incr =>
    (case assign frame (v_ext (ext_obj_ck (ipv4_checksum + checksum_incr))) (lval_varname ext_obj_name) of
     | SOME frame' =>
      SOME (v_bot, state_tup (stacks_tup frame' call_stack) status)
     | NONE => NONE)
   | NONE => NONE)
  | NONE => NONE
 )
End

(*******)
(* get *)

Definition get:
 (get (ext_obj_name, e_l, (state_tup (stacks_tup frame call_stack) status)) =
  case lookup_ipv4_checksum frame ext_obj_name of
  | SOME ipv4_checksum =>
      SOME (v_bit (fixwidth 16 (w2v ipv4_checksum), 16), state_tup (stacks_tup frame call_stack) status)
  | NONE => NONE
 )
End

val _ = export_theory ();
