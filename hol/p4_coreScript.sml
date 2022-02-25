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

Definition is_valid:
 (is_valid (header_name, (e_l:e list), ((ctrl, (frame, call_stack), status):state)) =
  case lookup_lval frame header_name of
  | (v_header valid_bit x_v_l) =>
   SOME (v_bool valid_bit, (ctrl, (frame, call_stack), status))
  | _ => NONE
 )
End

Definition set_valid:
 (set_valid (header_name, (e_l:e list), ((ctrl, (frame, call_stack), status):state)) =
  case lookup_lval frame header_name of
  | (v_header valid_bit x_v_l) =>
   (case assign frame (v_header T x_v_l) header_name of
    | SOME frame' =>             
     SOME (v_bot, (ctrl, (frame', call_stack), status))
    | NONE => NONE)
  | _ => NONE
 )
End

Definition set_invalid:
 (set_invalid (header_name, (e_l:e list), ((ctrl, (frame, call_stack), status):state)) =
  case lookup_lval frame header_name of
  | (v_header valid_bit x_v_l) =>
   (case assign frame (v_header F x_v_l) header_name of
    | SOME frame' =>             
     SOME (v_bot, (ctrl, (frame', call_stack), status))
    | NONE => NONE)
  | _ => NONE
 )
End

(*********************)
(* packet_in methods *)
(*********************)

Definition lookup_packet_in:
 (lookup_packet_in frame ext_obj_name =
  case lookup_lval frame ext_obj_name of
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
  | (e_acc e (e_v (v_str x))) => 
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
  | (x:x, (v_bool b)) => set_header_fields' t ((x, (v_bool (HD packet_in)))::acc) (DROP 1 packet_in)
  | (x, (v_bit (bv, l))) => set_header_fields' t ((x, (v_bit (TAKE l packet_in, l)))::acc) (DROP l packet_in)
  | _ => NONE
 )
End
Definition set_header_fields:
 (set_header_fields x_v_l packet_in = set_header_fields' x_v_l [] packet_in)
End

(* See https://p4.org/p4-spec/docs/P4-16-v1.2.2.html#sec-packet-extract-one *)
(* TODO: Extend to cover extraction to header stacks *)
Definition extract:
 (extract (ext_obj_name, e_l, ((ctrl, (frame, call_stack), status):state)) =
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
             (case assign frame' (v_ext (ext_obj_in (DROP size packet_in))) ext_obj_name of
	      | SOME frame'' =>             
	       SOME (v_bot, (ctrl, (frame'', call_stack), status))
              | NONE => NONE)
             | NONE => NONE)
           | NONE => NONE)
         else
	  (case assign frame (v_err "PacketTooShort") (lval_varname "parseError") of
	   | SOME frame' => SOME (v_bot, (ctrl, (frame', call_stack), status))
           | NONE => NONE)
        | NONE => NONE)
      | NONE => NONE)
    | NONE => NONE)
  | NONE => NONE
 )
End

(**********************)
(* packet_out methods *)
(**********************)

Definition lookup_packet_out:
 (lookup_packet_out frame ext_obj_name =
  case lookup_lval frame ext_obj_name of
  | (v_ext (ext_obj_in packet_out)) => SOME packet_out
  | _ => NONE
 )
End

Definition get_e_l_v:
 (get_e_l_v e =
  case e of
  | [e_v v] =>
   SOME v
  | _ => NONE
 )
End

Definition flatten_v_l:
 (flatten_v_l [] = SOME []) /\
 (flatten_v_l (h::t) =
  case h of
  | v_struct [] => SOME []
  | v_struct (h'::t') =>
   (case flatten_v_l [SND h'] of
    | SOME l =>
     (case flatten_v_l ((v_struct t')::t) of
      | SOME l' => SOME (l++l')
      | NONE => NONE)
    | NONE => NONE)
  | v_bit (bl, n) => SOME bl
  | v_bool b => SOME [b]
  | _ => NONE
 )
End

(* TODO: Should also support emission from: header stack and header union *)
(* Note: Nested headers are not allowed, so this is only checked at top level *)
Definition emit:
 (emit (ext_obj_name, e_l, ((ctrl, (frame, call_stack), status):state)) =
  case lookup_packet_out frame ext_obj_name of
  | SOME packet_out =>
   (case get_e_l_v e_l of
    | SOME (v_header F x_v_l) => SOME (v_bot, (ctrl, (frame, call_stack), status))
    | SOME (v_header T x_v_l) =>
     (case flatten_v_l (MAP SND x_v_l) of
      | SOME bl =>
       (case assign frame (v_ext (ext_obj_out (packet_out++bl))) ext_obj_name of
	| SOME frame' =>             
	 SOME (v_bot, (ctrl, (frame', call_stack), status))
	| NONE => NONE)
      | NONE => NONE)
    | SOME (v_struct x_v_l) =>
     (case flatten_v_l (MAP SND x_v_l) of
      | SOME bl =>
       (case assign frame (v_ext (ext_obj_out (packet_out++bl))) ext_obj_name of
	| SOME frame' =>             
	 SOME (v_bot, (ctrl, (frame', call_stack), status))
	| NONE => NONE)
      | NONE => NONE)
    | SOME _ => NONE
    | NONE => NONE)
  | NONE => NONE)
End

val _ = export_theory ();
