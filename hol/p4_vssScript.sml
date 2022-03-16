open HolKernel boolLib Parse bossLib ottLib;

open p4Theory;

val _ = new_theory "p4_vss";
    
(**********************************************************)
(*                     EXTERN OBJECTS                     *)
(**********************************************************)

(**********************)
(* Checksum16 methods *)
(**********************)
(* TODO: Prefix function definitions with ck_? *)

(*************)
(* construct *)

(* TODO: Use ARB instead of 0w? *)
Definition construct:
 (construct (ext_obj_name, (e_l:e list), ((ctrl, (frame, call_stack), status):state)) =
  case e_l of
  | [] =>
   (case ext_obj_name of
    | lval_varname x =>
     (let frame' = (LUPDATE (FUPDATE (HD (REVERSE frame)) (x, (v_ext (ext_obj_ck 0w), NONE))) (LENGTH frame - 1) frame) in
      SOME (v_bot, (ctrl, (frame', call_stack), status))
     )
    | _ => NONE
   )
  | _ => NONE
 )
End
   
(*********)
(* clear *)

Definition clear:
 (clear (ext_obj_name, (e_l:e list), ((ctrl, (frame, call_stack), status):state)) =
  case e_l of
  | [] =>
   (case assign frame (v_ext (ext_obj_ck 0w)) ext_obj_name of
    | SOME frame' =>
     SOME (v_bot, (ctrl, (frame', call_stack), status))
    | NONE => NONE)
  | _ => NONE
 )
End


(**********)
(* update *)

Definition lookup_ipv4_checksum:
 (lookup_ipv4_checksum frame ext_obj_name =
  case lookup_lval frame ext_obj_name of
  | (v_ext (ext_obj_ck ipv4_checksum)) => SOME ipv4_checksum
  | _ => NONE
 )
End

(* TODO: Add recursive cases *)
Definition header_entry2v:
 (header_entry2v (x:x, v) =
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
 (get_checksum_incr e_l =
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

(* Note that this assumes the order of fields in the header is correct *)
(* TODO: Check for overflow, compensate according to IPv4 checksum algorithm  *)
Definition update:
 (update (ext_obj_name, e_l, ((ctrl, (frame, call_stack), status):state)) =
  case lookup_ipv4_checksum frame ext_obj_name of
  | SOME ipv4_checksum =>
  (case get_checksum_incr e_l of
   | SOME checksum_incr =>
    (case assign frame (v_ext (ext_obj_ck (word_1comp (ipv4_checksum + checksum_incr)))) ext_obj_name of
     | SOME frame' =>
      SOME (v_bot, (ctrl, (frame', call_stack), status))
     | NONE => NONE)
   | NONE => NONE)
  | NONE => NONE
 )
End

(*******)
(* get *)

Definition get:
 (get (ext_obj_name, (e_l:e list), ((ctrl, (frame, call_stack), status):state)) =
   case e_l of
   | [] =>
    (case lookup_ipv4_checksum frame ext_obj_name of
     | SOME ipv4_checksum =>
        SOME (v_bit (fixwidth 16 (w2v ipv4_checksum), 16), (ctrl, (frame, call_stack), status))
     | NONE => NONE)
   | _ => NONE
 )
End

(**********************************************************)
(*                     MODEL-SPECIFIC                     *)
(**********************************************************)

(* TODO: This should arbitrate between different ports, taking a list of lists of input *)
(* NOTE: the model starts out at the data link layer *)
(* https://en.wikipedia.org/wiki/Ethernet_frame#Frame_%E2%80%93_data_link_layer *)
(* 1. Read into header to determine size of packet *)
(*    Technically, you would look into EtherType first, to determine
 *    whether it is used for payload size or protocol ID.
 *    We always have IPv4, so need to look into IPv4 header.
 *    Also, no 802.1Q tag is assumed. This would have been known
 *    from the bits normally forming the EtherType field having the
 *    value 0x8100 instead of 0x8000 (IPv4). *)
(* 2. Remove data + Ethernet CRC *)
(* 3. Put the rest of the header into the input extern object *)
(* TODO: Also take different values of IHL into account *)
(* Length of both headers 112+160=272 (IHL=5 assumed) *)
(* TODO: Make smarter extract function for getting total_length *)
(* let total_length = (v2n (REVERSE (TAKE 16 (REVERSE (TAKE 144 h)))))*8 in *)
val vss_input_f_def = Define `
  (vss_input_f (io_list:in_out_list, scope) =
   case io_list of
   | [] => NONE
   | ((bl,p)::t) =>
    let header = TAKE 272 bl in
    let data_crc = REVERSE (DROP 272 (REVERSE bl)) in
    (case assign [scope] (v_ext (ext_obj_in header)) (lval_varname "b") of
     | SOME [scope'] =>
      (case assign [scope'] (v_ext (ext_obj_out data_crc)) (lval_varname "data_crc") of
       | SOME [scope''] =>
        (case assign [scope''] (v_bit (fixwidth 4 (n2v p), 4)) (lval_field (lval_varname "inCtrl") "inputPort") of
         | SOME [scope'''] => SOME (t, scope''')
         | _ => NONE)
       | _ => NONE)
     | _ => NONE)
  )
`;

val vss_parser_runtime_def = Define `
  vss_parser_runtime ((e_l:e list), scope:scope, curr_stack_frame:curr_stack_frame) =
   case e_l of
   | [] =>
    (case lookup_lval [scope] (lval_varname "parsedHeaders") of
     | (v_struct hdrs) =>
        (case assign [scope] (v_struct hdrs) (lval_varname "headers") of
         | SOME [scope'] => SOME (scope', curr_stack_frame)
         | _ => NONE)
     | _ => NONE)
   | _ => NONE
`;

val vss_pre_deparser_def = Define `
  vss_pre_deparser ((e_l:e list), scope:scope, curr_stack_frame:curr_stack_frame) =
   case e_l of
   | [] =>
    (case lookup_lval [scope] (lval_varname "headers") of
     | (v_struct hdrs) =>
        (case assign [scope] (v_struct hdrs) (lval_varname "outputHeaders") of
         | SOME [scope'] => SOME (scope', curr_stack_frame)
         | _ => NONE)
     | _ => NONE)
   | _ => NONE
`;

(* Add new header + data + Ethernet CRC as a tuple with new output port to output list *)
(* Add data + Ethernet CRC *)
(* TODO: Outsource obtaining the output port to an external function? *)
val vss_output_f_def = Define `
 vss_output_f (in_out_list:in_out_list, scope:scope) =
  (case lookup_lval [scope] (lval_varname "b") of
   | (v_ext (ext_obj_in headers)) =>
    (case lookup_lval [scope] (lval_varname "data_crc") of
     | (v_ext (ext_obj_out data_crc)) =>
      (case lookup_lval [scope] (lval_varname "outCtrl") of
       | (v_struct [(fldname, v_bit (bl, n))]) =>
        SOME (in_out_list++[(headers++data_crc, v2n bl)], scope)
       | _ => NONE
      )
     | _ => NONE
    )
   | _ => NONE
  )
`;

val _ = export_theory ();
