open HolKernel boolLib Parse bossLib ottLib;

open p4Theory p4_auxTheory;

val _ = new_theory "p4_vss";
    
(**********************************************************)
(*                     EXTERN OBJECTS                     *)
(**********************************************************)

(**********************)
(* Checksum16 methods *)
(**********************)

(*************)
(* construct *)

(* TODO: Fix this. It should now initialise a new object in the ascope. *)
Definition Checksum16_construct:
 (Checksum16_construct (vss_arch_scope, g_scope_list, scope_stack) =
(*
  (let scope_stack' = initialise (g_scope_list++scope_stack) varn_ext_ret (v_ext (ext_obj_ck ARB)) in
   SOME (vss_arch_scope, TAKE 2 scope_stack', DROP 2 scope_stack', ctrl)
  )
*)
  SOME (vss_arch_scope, g_scope_list, scope_stack)
 )
End


(*********)
(* clear *)

(* TODO: Fix this. *)
Definition Checksum16_clear:
 (Checksum16_clear (vss_arch_scope, g_scope_list:g_scope_list, scope_stack) =
(*
   (case assign scope_stack (v_ext (ext_obj_ck 0w)) (lval_varname (varn_name "this")) of
    | SOME scope_stack' =>
     SOME (g_scope_list, scope_stack', ctrl)
    | NONE => NONE)
*)
   SOME (vss_arch_scope, g_scope_list, scope_stack)
 )
End


(**********)
(* update *)
(* OLD
Definition lookup_ipv4_checksum:
 (lookup_ipv4_checksum ss ext_obj_name =
  case lookup_lval ss ext_obj_name of
  | SOME (v_ext (ext_obj_ck ipv4_checksum)) => SOME ipv4_checksum
  | _ => NONE
 )
End
*)

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
 (get_checksum_incr ss ext_data_name =
   (case lookup_lval ss ext_data_name of
    | SOME (v_bit (bl, n)) => if n = 16 then SOME ((v2w bl):word16) else NONE
    | SOME (v_header vbit h_list) =>
     (case header_entries2v h_list of
      | SOME bl =>
       (case v2w16s bl of
	| SOME w16s => SOME (FOLDL word_add (0w) w16s)
	| NONE => NONE)
      | NONE => NONE)
    | _ => NONE)
 )
End

(* Note that this assumes the order of fields in the header is correct *)
(* TODO: Check for overflow, compensate according to IPv4 checksum algorithm *)
(* TODO: Fix this. *)
Definition Checksum16_update:
 (Checksum16_update (vss_arch_scope, g_scope_list:g_scope_list, scope_stack) =
(*
  case lookup_ipv4_checksum scope_stack (lval_varname (varn_name "this")) of
  | SOME ipv4_checksum =>
  (case get_checksum_incr scope_stack (lval_varname (varn_name "data")) of
   | SOME checksum_incr =>
    (case assign scope_stack (v_ext (ext_obj_ck (word_1comp (ipv4_checksum + checksum_incr)))) (lval_varname (varn_name "this")) of
     | SOME scope_stack' =>
      SOME (g_scope_list, scope_stack', ctrl)
     | NONE => NONE)
   | NONE => NONE)
  | NONE => NONE
*)
  SOME (vss_arch_scope, g_scope_list, scope_stack)
 )
End

(*******)
(* get *)

(* TODO: Fix this. *)
Definition Checksum16_get:
 (Checksum16_get (vss_arch_scope, g_scope_list:g_scope_list, scope_stack) =
(*
  (case lookup_ipv4_checksum scope_stack (lval_varname (varn_name "this")) of
   | SOME ipv4_checksum =>
    (let scope_stack' = initialise scope_stack varn_ext_ret (v_bit (fixwidth 16 (w2v ipv4_checksum), 16)) in
      SOME (g_scope_list, scope_stack', ctrl))
   | NONE => NONE)
*)
  SOME (vss_arch_scope, g_scope_list, scope_stack)
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
(* TODO: Fix this. *)
val vss_input_f_def = Define `
  (vss_input_f (io_list:in_out_list, scope:scope) =
(*
   case io_list of
   | [] => NONE
   | ((bl,p)::t) =>
    let header = TAKE 272 bl in
    let data_crc = REVERSE (DROP 272 (REVERSE bl)) in
    (case assign [scope] (v_ext (ext_obj_in header)) (lval_varname (varn_name "b")) of
     | SOME [scope'] =>
      (case assign [scope'] (v_ext (ext_obj_out data_crc)) (lval_varname (varn_name "data_crc")) of
       | SOME [scope''] =>
        (case assign [scope''] (v_bit (fixwidth 4 (n2v p), 4)) (lval_field (lval_varname (varn_name "inCtrl")) "inputPort") of
         | SOME [scope'''] => SOME (t, scope''')
         | _ => NONE)
       | _ => NONE)
     | _ => NONE)
*)
  SOME (io_list:in_out_list, scope)
  )
`;

(* TODO: Write copyout_pbl and copyin_pbl *)
val vss_reduce_nonout_def = Define `
 (vss_reduce_nonout ([], elist, vss_arch_scope) =
  SOME []
 ) /\
 (vss_reduce_nonout (d::dlist, e::elist, vss_arch_scope) =
  if is_d_out d
  then oCONS (e, vss_reduce_nonout (dlist, elist, vss_arch_scope))
  else
   (case e of
    | (e_var x) =>
     (case lookup_vexp2 [ [] ] [vss_arch_scope] x of
      | SOME v => oCONS (e_v v, vss_reduce_nonout (dlist, elist, vss_arch_scope))
      | NONE => NONE)
    | _ => NONE) 
 )
`;

(* TODO: Should also initialise parseError. Since this should be initialised
 *       for all architectures, maybe it should be outsourced to a
 *       architecture-generic function? *)
val vss_copyin_pbl_def = Define `
  vss_copyin_pbl (xlist, dlist, elist, vss_arch_scope, pbl_type) =
    case vss_reduce_nonout (dlist, elist, vss_arch_scope) of
    | SOME elist' =>
      (case copyin xlist dlist elist' [vss_arch_scope] [ [] ] of
       | SOME scope =>
         if pbl_type = pbl_type_parser
         then
           SOME (initialise_parse_error scope)
         else
           SOME scope
       | NONE => NONE)
    | NONE => NONE
`;

(* TODO: Does anything need to be looked up for this function? *)
(* TODO: pbl_type-dependent behaviour *)
(* Note that this re-uses the copyout function intended for P4 functions *)
val vss_copyout_pbl_def = Define `
  vss_copyout_pbl (ss, vss_arch_scope, dlist, xlist, pbl_type, (status:status)) =
    case copyout xlist dlist [ [] ; [] ] [vss_arch_scope] ss of
    | SOME (g_scope_list, [vss_arch_scope']) =>
      if pbl_type = pbl_type_parser
      then
        (case lookup_lval ss (lval_varname (varn_name "parseError")) of
         | SOME v =>
           (case assign [vss_arch_scope'] v (lval_varname (varn_name "parseError")) of
            | SOME [vss_arch_scope''] => SOME vss_arch_scope''
            | NONE => NONE)
         | _ => NONE)
      else
       SOME vss_arch_scope'
    | _ => NONE
`;


val vss_parser_runtime_def = Define `
  vss_parser_runtime (scope:scope) =
   (case lookup_lval [scope] (lval_varname (varn_name "parsedHeaders")) of
    | SOME (v_struct hdrs) =>
       (case assign [scope] (v_struct hdrs) (lval_varname (varn_name "headers")) of
        | SOME [scope'] => SOME scope'
        | _ => NONE)
    | _ => NONE)
`;

val vss_pre_deparser_def = Define `
  vss_pre_deparser (scope:scope) =
   (case lookup_lval [scope] (lval_varname (varn_name "headers")) of
    | SOME (v_struct hdrs) =>
      (case assign [scope] (v_struct hdrs) (lval_varname (varn_name "outputHeaders")) of
       | SOME [scope'] => SOME scope'
       | _ => NONE)
    | _ => NONE)
`;

(* Add new header + data + Ethernet CRC as a tuple with new output port to output list *)
(* Add data + Ethernet CRC *)
(* TODO: Outsource obtaining the output port to an external function? *)
(* TODO: Fix this *)
val vss_output_f_def = Define `
 vss_output_f (in_out_list:in_out_list, scope:scope) =
(*
  (case lookup_lval [scope] (lval_varname (varn_name "b")) of
   | SOME (v_ext (ext_obj_in headers)) =>
    (case lookup_lval [scope] (lval_varname (varn_name "data_crc")) of
     | SOME (v_ext (ext_obj_out data_crc)) =>
      (case lookup_lval [scope] (lval_varname (varn_name "outCtrl")) of
       | SOME (v_struct [(fldname, v_bit (bl, n))]) =>
        SOME (in_out_list++[(headers++data_crc, v2n bl)], scope)
       | _ => NONE
      )
     | _ => NONE
    )
   | _ => NONE
  )
*)
  SOME (in_out_list:in_out_list, scope:scope)
`;

(*

val copyin_pbl_def = Define `
  copyin_pbl xlist dlist elist gsl ss_curr =
    let
     (* MAP if_is_red*)
    in
      all_arg_update_for_newscope xlist dlist elist' (gsl++ss_curr)
    end
`;

*)

val _ = export_theory ();
