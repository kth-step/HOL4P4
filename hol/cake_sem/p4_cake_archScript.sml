open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_cake_arch";

open p4Syntax;
open bitstringSyntax numSyntax pairSyntax;
open p4Theory p4_auxTheory p4_cake_auxLib p4_cake_auxTheory p4_cake_exec_semTheory;
open p4_coreTheory p4_v1modelTheory;

(* Note that the below have been manually translated using the dictionary mapping strings to words64
 * created using p4_transform_cakeLib *)

(*********************)
(* Core architecture *)

Datatype:
 core_v_ext' =
  core_v_ext'_packet io_type
End

(* OLD
Datatype:
tbl' =
   (* Any regular table *)
   tbl'_regular ((s' list # num, (identifier # e_list')) alist)
   (* A table with a custom implementation *)
 | tbl'_impl (((word64 # word64) list -> (identifier # e_list')))
End
*)
val _ = Datatype
 (if matching_optimization
  then
   ‘tbl' =
      (* Any regular table *)
      tbl'_regular ((s' list # num, (identifier # e_list')) alist)
      (* A table with a custom implementation *)
    | tbl'_impl (((word64 # word64) list -> (identifier # e_list')))’
  else
   ‘tbl' =
      (* Any regular table *)
      tbl'_regular ((s' list # num, (identifier # e_list')) alist)
      (* A table with a custom implementation *)
    | tbl'_impl ((v' list -> (identifier # e_list')))’);

Definition header_entries2v'_def:
 (header_entries2v' (INL []) = SOME []) /\
 (header_entries2v' (INL (h::t)) =
  case header_entries2v' (INR h) of
  | SOME bl =>
  (case header_entries2v' (INL t) of
   | SOME bl2 => SOME (bl++bl2)
   | NONE => NONE)
  | NONE => NONE
 ) /\
 (header_entries2v' (INR (x, v)) =
  case v of
  | (v'_bit (bl, n)) => SOME bl
  | (v'_struct x_v_l) => header_entries2v' (INL x_v_l)
  | (v'_header validity x_v_l) => header_entries2v' (INL x_v_l)
  | _ => NONE
 )
End

Definition get_checksum_incr''_def:
 (get_checksum_incr'' (scope_list:scope_list') ext_data_name =
   (case lookup_lval'' scope_list ext_data_name of
    | SOME (v'_bit (bl, n)) =>
     if n MOD 16 = 0 then (v2w16s''' bl) else NONE
    | SOME (v'_header vbit f_list) =>
     (case header_entries2v' (INL f_list) of
      | SOME bl => v2w16s'' bl
      | NONE => NONE)
    | SOME (v'_struct f_list) =>
     (case header_entries2v' (INL f_list) of
      | SOME bl => v2w16s'' bl
      | NONE => NONE)
    | _ => NONE)
 )
End

(** Some new architectural functions **)

Definition v_map_to_scope'_def:
 (v_map_to_scope' [] = []) /\
 (v_map_to_scope' (((k, v)::t)) =
  ((varn'_name k, (v:v', NONE:lval' option))::v_map_to_scope' t))
End

Definition scope_to_vmap'_def:
 (scope_to_vmap' [] = SOME []) /\
 (scope_to_vmap' ((vn, (v:v', lval_opt:lval' option))::t) =
  case vn of
   | (varn'_name k) => oCONS ((k, v), scope_to_vmap' t)
   | _ => NONE)
End

Definition copyout_pbl_gen'_def:
 copyout_pbl_gen' xlist dlist g_scope_list v_map =
  let v_map_scope = v_map_to_scope' v_map in
   update_return_frame' xlist dlist [v_map_scope] g_scope_list
End

(** Generic implementations **)
Definition verify_gen'_def:
 (verify_gen' ascope_update_v_map (ascope:'a, g_scope_list:g_scope_list', scope_list) =
  case lookup_lval'' scope_list (lval'_varname (varn'_name ^(get_id "condition"))) of
  | SOME (v'_bool T) =>
   SOME (ascope, scope_list, status'_returnv v'_bot)
  | SOME (v'_bool F) =>
   (case lookup_lval'' scope_list (lval'_varname (varn'_name ^(get_id "err"))) of
    | SOME (v'_bit bitv) =>
     SOME (ascope_update_v_map ascope ^(get_id "parseError") (v'_bit bitv), scope_list, status'_trans ^(get_id "reject"))
    | _ => NONE)
  | _ => NONE
 )
End

Definition lookup_lval_header'_def:
 (lookup_lval_header' ss header_lval =
  case lookup_lval'' ss header_lval of
   | SOME (v'_header valid_bit x_v_l) => SOME (valid_bit, x_v_l)
   | _ => NONE
 )
End

Definition size_in_bits'_def:
 (size_in_bits' (v'_bool b) = SOME 1) /\
 (size_in_bits' (v'_bit (bl, n)) = SOME n) /\
 (size_in_bits' (v'_header valid_bit []) = SOME 0) /\
 (size_in_bits' (v'_struct []) = SOME 0) /\
 (size_in_bits' (v'_header valid_bit (h::t)) =
  case SND h of
  | (v'_bit (bl, num)) =>
   (case size_in_bits' (v'_header valid_bit t) of
    | SOME num' => SOME (num + num')
    | NONE => NONE
   )
  | (v'_bool _) =>
   (case size_in_bits' (v'_header valid_bit t) of
    | SOME num' => SOME (1 + num')
    | NONE => NONE
   )
  | (v'_struct fields) =>
   (case size_in_bits' (v'_header valid_bit t) of
    | SOME num' =>
     (case size_in_bits' (v'_struct fields) of
      | SOME num'' =>
       SOME (num'' + num')
      | NONE => NONE
     )
    | NONE => NONE
   )
  | _ => NONE
 ) /\
 (size_in_bits' (v'_struct (h::t)) =
  case SND h of
  | (v'_bit (bl, num)) => 
   (case size_in_bits' (v'_struct t) of
    | SOME num' => SOME (num + num')
    | NONE => NONE
   )
  | (v'_bool _) =>
   (case size_in_bits' (v'_struct t) of
    | SOME num' => SOME (1 + num')
    | NONE => NONE
   )
  | _ => NONE
 ) /\
 (size_in_bits' _ = NONE)
End

Definition set_bool'_def:
 (set_bool' [] = NONE) /\
 (set_bool' packet_in = SOME (v'_bool (HD packet_in), TL packet_in))
End
Definition set_bit'_def:
 (set_bit' n packet_in =
  case oTAKE n packet_in of
  | SOME res => SOME (v'_bit (res, n), DROP n packet_in)
  | NONE => NONE)
End

Definition set_fields'_def:
 (set_fields' []     acc _ = SOME acc) /\
 (set_fields' (h::t) acc packet_in =
  case h of
  | (x:identifier, (v'_bool b)) =>
   (case set_bool' packet_in of
    | SOME (res, t') => set_fields' t (acc++[(x, res)]) t'
    | NONE => NONE)
  | (x, (v'_bit (bv, l))) =>
   (case set_bit' l packet_in of
    | SOME (res, t') => set_fields' t (acc++[(x, res)]) t'
    | NONE => NONE)
  | (x, (v'_struct x_v_l)) =>
   (case size_in_bits' (v'_struct x_v_l) of
    | SOME n =>
     (case oTAKE_DROP n packet_in of
      | SOME (res, t') =>
       (case set_fields' x_v_l [] res of
        | SOME acc' =>
         set_fields' t (acc++[(x, v'_struct acc')]) t'
        | NONE => NONE)
      | NONE => NONE)
    | NONE => NONE)
  | _ => NONE)
End

Definition set_header'_def:
 (set_header' x_v_l packet_in =
  case set_fields' x_v_l [] packet_in of
  | SOME x_v_l' => SOME (v'_header T x_v_l')
  | NONE => NONE)
End

Definition set_struct'_def:
 (set_struct' x_v_l packet_in =
  case set_fields' x_v_l [] packet_in of
  | SOME x_v_l' => SOME (v'_struct x_v_l')
  | NONE => NONE)
End

Definition set_v'_def:
 (set_v' (v'_bit (bitv, n)) packet_in =
  case set_bit' n packet_in of
  | SOME (res, t') => SOME res
  | NONE => NONE) /\
 (set_v' (v'_bool b)        packet_in =
  case set_bool' packet_in of
  | SOME (res, t') => SOME res
  | NONE => NONE) /\
 (set_v' (v'_struct x_v_l) packet_in = (set_struct' x_v_l packet_in)) /\
 (set_v' (v'_header validity x_v_l) packet_in = (set_header' x_v_l packet_in)) /\
 (set_v' _ packet_in = NONE)
End

Definition w8_to_v_def:
w8_to_v (w:word8) =
 [128w && w ≠ 0w; 64w && w ≠ 0w; 32w && w ≠ 0w; 16w && w ≠ 0w;
  8w && w ≠ 0w; 4w && w ≠ 0w; 2w && w ≠ 0w; 1w && w ≠ 0w]
End
Theorem w8_to_v_equiv_def:
!w. w8_to_v w = w2v w
Proof
fs[w8_to_v_def, bitstringTheory.w2v_def, wordsTheory.word_bit_test, wordsTheory.word_bit_def, wordsTheory.word_bit]
QED

Definition byte_list_to_bool_list_take_def:
(byte_list_to_bool_list_take l 0 = SOME []) /\ 
(byte_list_to_bool_list_take ((h:word8)::t) (SUC n) =
 case byte_list_to_bool_list_take t n of
   SOME res =>
  SOME (w8_to_v h::res)
  | NONE => NONE) /\
(byte_list_to_bool_list_take [] n = NONE)
End

val packet_in_extract_gen'_def =
 if io_optimization
 then Define
  ‘(packet_in_extract_gen' ascope_lookup ascope_update ascope_update_v_map (ascope:'a, g_scope_list:g_scope_list', scope_list) =
    case lookup_lval'' scope_list (lval'_varname (varn'_name ^(get_id "this"))) of
    | SOME (v'_ext_ref i) =>
     (case lookup_lval_header' scope_list (lval'_varname (varn'_name ^(get_id "headerLvalue"))) of
      | SOME (valid_bit, x_v_l) =>
       (case lookup_ascope_gen ascope_lookup ascope i of
        | SOME ((INL (core_v_ext'_packet packet_in_bl)):(core_v_ext', 'b) sum) =>
         (case size_in_bits' (v'_header valid_bit x_v_l) of
          | SOME size =>
           (* TODO: Handle non-mod 8 case properly *)
           if size MOD 8 = 0
           then
             if size <= (LENGTH packet_in_bl) * 8
             then
              case byte_list_to_bool_list_take packet_in_bl (size DIV 8) of
               SOME bool_list_list =>
               (case set_header' x_v_l (FLAT bool_list_list) of
                | SOME header =>
                 (case assign' scope_list header (lval'_varname (varn'_name ^(get_id "headerLvalue"))) of
                  | SOME scope_list' =>
                   SOME (update_ascope_gen ascope_update ascope i ((INL (core_v_ext'_packet (DROP (size DIV 8) packet_in_bl))):(core_v_ext', 'b) sum), scope_list', status'_returnv v'_bot)
                  | NONE => NONE)
                | NONE => NONE)
              | NONE => NONE
             else
              (* NOTE: Specific serialisation of errors is assumed here - "PacketTooShort" -> 1 *)
              SOME (ascope_update_v_map (update_ascope_gen ascope_update ascope i ((INL (core_v_ext'_packet [])):(core_v_ext', 'b) sum)) ^(get_id "parseError") (v'_bit (fixwidth 32 (n2v 1), 32)), scope_list, status'_trans ^(get_id "reject"))
           else NONE
          | NONE => NONE)
         | _ => NONE)
      | NONE => NONE)
    | _ => NONE
   )’
 else Define
  ‘(packet_in_extract_gen' ascope_lookup ascope_update ascope_update_v_map (ascope:'a, g_scope_list:g_scope_list', scope_list) =
    case lookup_lval'' scope_list (lval'_varname (varn'_name ^(get_id "this"))) of
    | SOME (v'_ext_ref i) =>
     (case lookup_lval_header' scope_list (lval'_varname (varn'_name ^(get_id "headerLvalue"))) of
      | SOME (valid_bit, x_v_l) =>
       (case lookup_ascope_gen ascope_lookup ascope i of
        | SOME ((INL (core_v_ext'_packet packet_in_bl)):(core_v_ext', 'b) sum) =>
         (case size_in_bits' (v'_header valid_bit x_v_l) of
          | SOME size =>
           if size <= LENGTH packet_in_bl
           then
             (case set_header' x_v_l packet_in_bl of
              | SOME header =>
               (case assign' scope_list header (lval'_varname (varn'_name ^(get_id "headerLvalue"))) of
                | SOME scope_list' =>
                 SOME (update_ascope_gen ascope_update ascope i ((INL (core_v_ext'_packet (DROP size packet_in_bl))):(core_v_ext', 'b) sum), scope_list', status'_returnv v'_bot)
                | NONE => NONE)
              | NONE => NONE)
           else
            (* NOTE: Specific serialisation of errors is assumed here - "PacketTooShort" -> 1 *)
            SOME (ascope_update_v_map (update_ascope_gen ascope_update ascope i ((INL (core_v_ext'_packet [])):(core_v_ext', 'b) sum)) ^(get_id "parseError") (v'_bit (fixwidth 32 (n2v 1), 32)), scope_list, status'_trans ^(get_id "reject"))
          | NONE => NONE)
         | _ => NONE)
      | NONE => NONE)
    | _ => NONE
   )’
;

val packet_in_lookahead_gen'_def =
 if io_optimization
 then Define
  ‘(packet_in_lookahead_gen' ascope_lookup ascope_update_v_map (ascope:'a, g_scope_list:g_scope_list', scope_list) =
    case lookup_lval'' scope_list (lval'_varname (varn'_name ^(get_id "this"))) of
    | SOME (v'_ext_ref i) =>
     (case lookup_lval'' scope_list (lval'_varname (varn'_name ^(get_id "targ1"))) of
      | SOME dummy_v =>
       (case lookup_ascope_gen ascope_lookup ascope i of
        | SOME ((INL (core_v_ext'_packet packet_in_bl)):(core_v_ext', 'b) sum) =>
         (case size_in_bits' dummy_v of
          | SOME size =>
           (* TODO: Handle non-mod 8 case properly *)
           if size MOD 8 = 0
           then
            if size <= (LENGTH packet_in_bl) * 8
            then
             case byte_list_to_bool_list_take packet_in_bl (size DIV 8) of
              SOME bool_list_list =>
               (case set_v' dummy_v (FLAT bool_list_list) of
                | SOME v =>
                 SOME (ascope, scope_list, status'_returnv v)
                | NONE => NONE)
              | NONE => NONE
            else
             (* NOTE: Specific serialisation of errors is assumed here - "PacketTooShort" -> 1 *)
             SOME (ascope_update_v_map ascope ^(get_id "parseError") (v'_bit (fixwidth 32 (n2v 1), 32)), scope_list, status'_trans ^(get_id "reject"))
           else NONE
          | NONE => NONE)
         | _ => NONE)
      | NONE => NONE)
    | _ => NONE
   )’
 else Define
  ‘(packet_in_lookahead_gen' ascope_lookup ascope_update_v_map (ascope:'a, g_scope_list:g_scope_list', scope_list) =
    case lookup_lval'' scope_list (lval'_varname (varn'_name ^(get_id "this"))) of
    | SOME (v'_ext_ref i) =>
     (case lookup_lval'' scope_list (lval'_varname (varn'_name ^(get_id "targ1"))) of
      | SOME dummy_v =>
       (case lookup_ascope_gen ascope_lookup ascope i of
        | SOME ((INL (core_v_ext'_packet packet_in_bl)):(core_v_ext', 'b) sum) =>
         (case size_in_bits' dummy_v of
          | SOME size =>
           if size <= LENGTH packet_in_bl
           then
            (case set_v' dummy_v packet_in_bl of
             | SOME v =>
              SOME (ascope, scope_list, status'_returnv v)
             | NONE => NONE)
           else
            (* NOTE: Specific serialisation of errors is assumed here - "PacketTooShort" -> 1 *)
            SOME (ascope_update_v_map ascope ^(get_id "parseError") (v'_bit (fixwidth 32 (n2v 1), 32)), scope_list, status'_trans ^(get_id "reject"))
          | NONE => NONE)
         | _ => NONE)
      | NONE => NONE)
    | _ => NONE
   )’
;

Definition lookup_lval_bit32'_def:
 (lookup_lval_bit32' ss bit32_lval =
  case lookup_lval'' ss bit32_lval of
   | SOME (v'_bit (bitv, 32)) => SOME (v2n bitv)
   | _ => NONE
 )
End

val packet_in_advance_gen'_def =
 if io_optimization
 then Define
  ‘(packet_in_advance_gen' ascope_lookup ascope_update ascope_update_v_map (ascope:'a, g_scope_list:g_scope_list', scope_list) =
    case lookup_lval'' scope_list (lval'_varname (varn'_name ^(get_id "this"))) of
    | SOME (v'_ext_ref i) =>
     (case lookup_lval_bit32' scope_list (lval'_varname (varn'_name ^(get_id "bits"))) of
      | SOME n_bits =>
       (case lookup_ascope_gen ascope_lookup ascope i of
        | SOME ((INL (core_v_ext'_packet packet_in_bl)):(core_v_ext', 'b) sum) =>
         (* TODO: Handle non-mod 8 case properly *)
         if n_bits MOD 8 = 0
         then
          if n_bits <= (LENGTH packet_in_bl) * 8
          then
           SOME (update_ascope_gen ascope_update ascope i ((INL (core_v_ext'_packet (DROP (n_bits DIV 8) packet_in_bl))):(core_v_ext', 'b) sum), scope_list, status'_returnv v'_bot)
          else
           (* NOTE: Serialisation of errors is assumed here - "PacketTooShort" -> 1 *)
           SOME (ascope_update_v_map ascope ^(get_id "parseError") (v'_bit (fixwidth 32 (n2v 1), 32)), scope_list, status'_trans ^(get_id "reject"))
         else NONE
         | _ => NONE)
      | NONE => NONE)
    | _ => NONE
   )’
 else Define
  ‘(packet_in_advance_gen' ascope_lookup ascope_update ascope_update_v_map (ascope:'a, g_scope_list:g_scope_list', scope_list) =
    case lookup_lval'' scope_list (lval'_varname (varn'_name ^(get_id "this"))) of
    | SOME (v'_ext_ref i) =>
     (case lookup_lval_bit32' scope_list (lval'_varname (varn'_name ^(get_id "bits"))) of
      | SOME n_bits =>
       (case lookup_ascope_gen ascope_lookup ascope i of
        | SOME ((INL (core_v_ext'_packet packet_in_bl)):(core_v_ext', 'b) sum) =>
         if n_bits <= LENGTH packet_in_bl
         then
          SOME (update_ascope_gen ascope_update ascope i ((INL (core_v_ext'_packet (DROP n_bits packet_in_bl))):(core_v_ext', 'b) sum), scope_list, status'_returnv v'_bot)
         else
          (* NOTE: Serialisation of errors is assumed here - "PacketTooShort" -> 1 *)
          SOME (ascope_update_v_map ascope ^(get_id "parseError") (v'_bit (fixwidth 32 (n2v 1), 32)), scope_list, status'_trans ^(get_id "reject"))
         | _ => NONE)
      | NONE => NONE)
    | _ => NONE
   )’
;

Definition flatten_v_l'_def:
 (flatten_v_l' [] = SOME []) /\
 (flatten_v_l' (h::t) =
  case h of
  | v'_struct [] =>
   (case flatten_v_l' t of
    | SOME l => SOME l
    | NONE => NONE)
  | v'_struct (h'::t') =>
   (case flatten_v_l' [SND h'] of
    | SOME l =>
     (case flatten_v_l' ((v'_struct t')::t) of
      | SOME l' => SOME (l++l')
      | NONE => NONE)
    | NONE => NONE)
  | v'_header validity [] =>
   (case flatten_v_l' t of
    | SOME l => SOME l
    | NONE => NONE)
  | v'_header validity (h'::t') =>
   (case flatten_v_l' [SND h'] of
    | SOME l =>
     (case flatten_v_l' ((v'_struct t')::t) of
      | SOME l' => SOME (l++l')
      | NONE => NONE)
    | NONE => NONE)
  | v'_bit (bl, n) =>
   (case flatten_v_l' t of
    | SOME l => SOME (bl++l)
    | NONE => NONE)
  | v'_bool b =>
   (case flatten_v_l' t of
    | SOME l => SOME (b::l)
    | NONE => NONE)
  | _ => NONE
 )
End

val packet_out_emit_gen'_def =
 if io_optimization
 then Define
  ‘(packet_out_emit_gen' (ascope_lookup:'a -> num -> (core_v_ext' + 'b) option) ascope_update (ascope:'a, g_scope_list:g_scope_list', scope_list) =
    case lookup_lval'' scope_list (lval'_varname (varn'_name ^(get_id "this"))) of
    | SOME (v'_ext_ref i) =>
     (case lookup_ascope_gen ascope_lookup ascope i of
      | SOME (INL (core_v_ext'_packet packet_out_bl)) =>
       (case lookup_lval'' scope_list (lval'_varname (varn'_name ^(get_id "data"))) of
        | SOME (v'_header F x_v_l) => SOME (ascope, scope_list, status'_returnv v'_bot)
        | SOME (v'_header T x_v_l) =>
         (case flatten_v_l' (MAP SND x_v_l) of
          | SOME bl =>
           (case bool_list_to_byte_list bl of
            | SOME byte_list =>
             SOME (update_ascope_gen ascope_update ascope i ((INL (core_v_ext'_packet (packet_out_bl++ byte_list))):(core_v_ext', 'b) sum), scope_list, status'_returnv v'_bot)
            | NONE => NONE)
          | NONE => NONE)
        | SOME (v'_struct x_v_l) =>
         (case flatten_v_l' (MAP SND x_v_l) of
          | SOME bl =>
           (case bool_list_to_byte_list bl of
            | SOME byte_list =>
             SOME (update_ascope_gen ascope_update ascope i ((INL (core_v_ext'_packet (packet_out_bl++byte_list))):(core_v_ext', 'b) sum), scope_list, status'_returnv v'_bot)
            | NONE => NONE)
          | NONE => NONE)
        | SOME _ => NONE
        | NONE => NONE)
      | _ => NONE)
    | _ => NONE
   )’
 else Define
  ‘(packet_out_emit_gen' (ascope_lookup:'a -> num -> (core_v_ext' + 'b) option) ascope_update (ascope:'a, g_scope_list:g_scope_list', scope_list) =
    case lookup_lval'' scope_list (lval'_varname (varn'_name ^(get_id "this"))) of
    | SOME (v'_ext_ref i) =>
     (case lookup_ascope_gen ascope_lookup ascope i of
      | SOME (INL (core_v_ext'_packet packet_out_bl)) =>
       (case lookup_lval'' scope_list (lval'_varname (varn'_name ^(get_id "data"))) of
        | SOME (v'_header F x_v_l) => SOME (ascope, scope_list, status'_returnv v'_bot)
        | SOME (v'_header T x_v_l) =>
         (case flatten_v_l' (MAP SND x_v_l) of
          | SOME bl =>
           SOME (update_ascope_gen ascope_update ascope i ((INL (core_v_ext'_packet (packet_out_bl++ bl))):(core_v_ext', 'b) sum), scope_list, status'_returnv v'_bot)
          | NONE => NONE)
        | SOME (v'_struct x_v_l) =>
         (case flatten_v_l' (MAP SND x_v_l) of
          | SOME bl =>
            SOME (update_ascope_gen ascope_update ascope i ((INL (core_v_ext'_packet (packet_out_bl++bl))):(core_v_ext', 'b) sum), scope_list, status'_returnv v'_bot)
          | NONE => NONE)
        | SOME _ => NONE
        | NONE => NONE)
      | _ => NONE)
    | _ => NONE
   )’
;

(** Implementations **)

Definition header_is_valid'_def:
 (header_is_valid' (ascope:'a, g_scope_list:g_scope_list', scope_list) =
  case lookup_lval'' scope_list (lval'_varname (varn'_name ^(get_id "this"))) of
  | SOME (v'_header valid_bit x_v_l) =>
   SOME (ascope, scope_list, status'_returnv (v'_bool valid_bit))
  | _ => NONE
 )
End

Definition header_set_valid'_def:
 (header_set_valid' (ascope:'a, g_scope_list:g_scope_list', scope_list) =
  case lookup_lval'' scope_list (lval'_varname (varn'_name ^(get_id "this"))) of
  | SOME (v'_header valid_bit x_v_l) =>
   (case assign' scope_list (v'_header T x_v_l) (lval'_varname (varn'_name ^(get_id "this"))) of
    | SOME scope_list' =>
     SOME (ascope, scope_list', status'_returnv v'_bot)
    | NONE => NONE)
  | _ => NONE
 )
End

Definition header_set_invalid'_def:
 (header_set_invalid' (ascope:'a, g_scope_list:g_scope_list', scope_list) =
  case lookup_lval'' scope_list (lval'_varname (varn'_name ^(get_id "this"))) of
  | SOME (v'_header valid_bit x_v_l) =>
   (case assign' scope_list (v'_header F x_v_l) (lval'_varname (varn'_name ^(get_id "this"))) of
    | SOME scope_list' =>             
     SOME (ascope, scope_list', status'_returnv v'_bot)
    | NONE => NONE)
  | _ => NONE
 )
End

(* Without matching optimization *)
(* TODO: Dummy definitions required for translation file... *)
val (FOLDL_MATCH'_def, FOLDL_MATCH_alt'_def) = 
 if matching_optimization
 then (Define ‘FOLDL_MATCH' = T’, Define ‘FOLDL_MATCH_alt' = T’)
 else
  (Define
   ‘(FOLDL_MATCH' v_l res [] = res) /\
    (FOLDL_MATCH' (v_l:v' list) (res_act:identifier # e' list, res_prio_opt:num option) (((s_l,prio),v)::t) =
     if match_all' (ZIP(v_l, s_l))
     then
      (* TODO: Largest priority wins (like for P4Runtime API) is hard-coded *)
      case res_prio_opt of
      | SOME res_prio =>
       if prio > res_prio
       then
        FOLDL_MATCH' v_l (v, SOME prio) t
       else FOLDL_MATCH' v_l (res_act, res_prio_opt) t
      | NONE => FOLDL_MATCH' v_l (v, SOME prio) t
     else FOLDL_MATCH' v_l (res_act, res_prio_opt) t)’,
   Define
    ‘(FOLDL_MATCH_alt' v_l res acc [] = res) /\
     (FOLDL_MATCH_alt' v_l (res_act, res_prio_opt:num option) acc (((s_l,prio),v)::t) =
      if match_all' (ZIP(v_l, s_l))
      then
       (* TODO: Smallest priority wins (like for TDI) is hard-coded,
        *       other than priority zero. *)
       case res_prio_opt of
       | SOME res_prio =>
        let prio' = if (prio = 0) then acc else prio in
        if (prio' < res_prio)
        then
         FOLDL_MATCH_alt' v_l (v, SOME prio') (acc+1) t
        else FOLDL_MATCH_alt' v_l (res_act, res_prio_opt) (acc+1) t
       | NONE => FOLDL_MATCH_alt' v_l (v, SOME prio) (acc+1) t
      else FOLDL_MATCH_alt' v_l (res_act, res_prio_opt) (acc+1) t)’
  )
;

(* With matching optimization *)
val (FOLDL_MATCH''_def, FOLDL_MATCH_alt''_def) = 
 if matching_optimization
 then
  (Define
   ‘(FOLDL_MATCH'' w_l res [] = res) /\
    (FOLDL_MATCH'' (w_l:(word64 # word64) list) (res_act:identifier # e' list, res_prio_opt:num option) (((s_l,prio),v)::t) =
     if match_all'' (ZIP(w_l, s_l))
     then
      (* TODO: Largest priority wins (like for P4Runtime API) is hard-coded *)
      case res_prio_opt of
      | SOME res_prio =>
       if prio > res_prio
       then
        FOLDL_MATCH'' w_l (v, SOME prio) t
       else FOLDL_MATCH'' w_l (res_act, res_prio_opt) t
      | NONE => FOLDL_MATCH'' w_l (v, SOME prio) t
     else FOLDL_MATCH'' w_l (res_act, res_prio_opt) t)’,
   Define
   ‘(FOLDL_MATCH_alt'' w_l res acc [] = res) /\
    (FOLDL_MATCH_alt'' w_l (res_act, res_prio_opt:num option) acc (((s_l,prio),v)::t) =
     if match_all'' (ZIP(w_l, s_l))
     then
      (* TODO: Smallest priority wins (like for TDI) is hard-coded,
       *       other than priority zero. *)
      case res_prio_opt of
      | SOME res_prio =>
       let prio' = if (prio = 0) then acc else prio in
       if (prio' < res_prio)
       then
        FOLDL_MATCH_alt'' w_l (v, SOME prio') (acc+1) t
       else FOLDL_MATCH_alt'' w_l (res_act, res_prio_opt) (acc+1) t
      | NONE => FOLDL_MATCH_alt'' w_l (v, SOME prio) (acc+1) t
     else FOLDL_MATCH_alt'' w_l (res_act, res_prio_opt) (acc+1) t)’)
 else (Define ‘FOLDL_MATCH'' = T’, Define ‘FOLDL_MATCH_alt'' = T’)
;

val _ = export_theory ();
