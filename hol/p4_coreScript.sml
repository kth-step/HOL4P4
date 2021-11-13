open HolKernel boolLib Parse bossLib ottLib;

open p4Theory;

val _ = new_theory "p4_core";

(******************)
(* Header methods *)
(******************)

(* We might want this to take a header argument to agree with minSizeInBits() *)
Definition min_size_in_bits:
 (min_size_in_bits (v_header valid_bit []) = SOME 0) /\
 (min_size_in_bits (v_header valid_bit (h::t)) =
  case SND h of
  | (v_bit (bl, num)) => 
   (case min_size_in_bits (v_header valid_bit t) of
    | SOME num' => SOME (num + num')
    | NONE => NONE
   )
  | (v_bool _) => 
   (case min_size_in_bits (v_header valid_bit t) of
    | SOME num' => SOME (1 + num')
    | NONE => NONE
   )
  | _ => NONE
 )
End

Definition min_size_in_bytes:
 (min_size_in_bytes (v_header valid_bit x_v_l) =
  case min_size_in_bits (v_header valid_bit x_v_l) of
  | SOME num => SOME ((num+7) DIV 8)
  | NONE => NONE
 )
End

(* TODO: isValid *)

(* TODO: setValid *)
(* TODO: setInvalid *)

(*********************)
(* packet_in methods *)
(*********************)

Definition lookup_packet_in:
 (lookup_packet_in frame ext_obj_name =
  case lookup_v frame ext_obj_name of
  | (v_ext (ext_obj_in packet_in)) => SOME packet_in
  | _ => NONE
 )
End

Definition lookup_lval_header:
 (lookup_lval_header frame header_lval =
  case lookup_lval frame header_lval of
   | (v_header valid_bit x_v_l) => SOME (valid_bit, x_v_l)
   | _ => NONE
 )
End

(* Helper function to extract *)
Definition get_header_lval':
 (get_header_lval' e =
  case e of
  | (e_acc e (e_var x)) => 
   (case get_header_lval' e of
    | SOME lval => SOME (lval_field lval x)
    | NONE => NONE)
  | (e_var x) => SOME (lval_varname x)
  | _ => NONE
 )
End
Definition get_header_lval:
 (get_header_lval e_l =
  case e_l of
  | [e] => get_header_lval' e
  | _ => NONE
 )
End

(* Helper function to extract *)
Definition set_header_fields':
 (set_header_fields' []     acc _ = SOME acc) /\
 (set_header_fields' (h::t) acc packet_in =
  case h of
  | (x, (v_bool b)) => set_header_fields' t ((x, (v_bool (HD packet_in)))::acc) (DROP 1 packet_in)
  | (x, (v_bit (bv, l))) => set_header_fields' t ((x, (v_bit (TAKE l packet_in, l)))::acc) (DROP l packet_in)
  | _ => NONE
 )
End
Definition set_header_fields:
 (set_header_fields x_v_l packet_in = set_header_fields' x_v_l [] packet_in)
End

(* See https://p4.org/p4-spec/docs/P4-16-v1.2.2.html#sec-packet-extract-one *)
(* TODO: Extend to cover stuff related to header stacks *)
(* TODO: Extend to allow e.g. header field accesses in place of variables in e_l *)
Definition extract:
 (extract (ext_obj_name, e_l, (state_tup (stacks_tup frame call_stack) status)) =
  case lookup_packet_in frame ext_obj_name of
  | SOME packet_in =>
   (case get_header_lval e_l of
    | SOME header_lval =>
     (case lookup_lval_header frame header_lval of
      | SOME (valid_bit, x_v_l) =>
       (case min_size_in_bits (v_header valid_bit x_v_l) of
        | SOME size =>
         if size <= LENGTH packet_in
         then
          (case set_header_fields x_v_l packet_in of
           | SOME x_v_l' =>
	    (case assign frame (v_header T x_v_l') header_lval of
	     | SOME frame' =>
             (case assign frame' (v_ext (ext_obj_in (DROP size packet_in))) (lval_varname ext_obj_name) of
	      | SOME frame'' =>             
	       SOME (v_bot, state_tup (stacks_tup frame'' call_stack) status)
              | NONE => NONE)
             | NONE => NONE)
           | NONE => NONE)
         else
	  (case assign frame (v_err "PacketTooShort") (lval_varname "parseError") of
	   | SOME frame' => SOME (v_bot, state_tup (stacks_tup frame' call_stack) status)
           | NONE => NONE)
        | NONE => NONE)
      | NONE => NONE)
    | NONE => NONE)
  | NONE => NONE
 )
End


val _ = export_theory ();
