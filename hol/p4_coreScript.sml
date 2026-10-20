Theory p4_core
Ancestors
  p4 p4_aux

(*****************)
(* core ext type *)
(*****************)

(* TODO: Separate packet_in and packet_out?  *)

(* packet_in:
     https://p4.org/p4-spec/docs/P4-16-v1.2.4.html#sec-packet-data-extraction
*)
Datatype:
 core_v_ext =
  core_v_ext_packet (bool list)
End

(* NOTE: Definitions with _gen get specialised later by the different architectures *)

(**********************)
(* Objectless methods *)
(**********************)

Definition verify_gen_def:
 (verify_gen ascope_update_v_map (ascope:'a, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "condition")) of
  | SOME (v_bool T) =>
   SOME (ascope, scope_list, status_returnv v_bot)
  | SOME (v_bool F) =>
   (case lookup_lval scope_list (lval_varname (varn_name "err")) of
    | SOME (v_bit bitv) =>
     SOME (ascope_update_v_map ascope "parseError" (v_bit bitv), scope_list, status_trans "reject")
    | _ => NONE)
  | _ => NONE
 )
End

(******************)
(* Header methods *)
(******************)

(* TODO: Perform this on list only? *)
(* NOTE: This features more types that we can actually extract to, to facilitate re-use *)
Definition size_in_bits_def:
 (size_in_bits (v_bool b) = SOME 1) /\
 (size_in_bits (v_bit (bl, n)) = SOME n) /\
 (size_in_bits (v_struct x_v_l) = fields_size_in_bits x_v_l) /\
 (size_in_bits (v_header valid_bit x_v_l) = fields_size_in_bits x_v_l) /\
 (size_in_bits _ = NONE) /\
 (fields_size_in_bits [] = SOME 0) /\
 (fields_size_in_bits ((x:x, v)::t) =
  case size_in_bits v of
  | SOME num =>
   (case fields_size_in_bits t of
    | SOME num' => SOME (num + num')
    | NONE => NONE)
  | NONE => NONE)
End

(* TODO: Perform this on list only? *)
Definition size_in_bytes_def:
 (size_in_bytes (v_header valid_bit x_v_l) =
  case size_in_bits (v_header valid_bit x_v_l) of
  | SOME num => SOME ((num+7) DIV 8)
  | NONE => NONE
 )
End

Definition header_is_valid_def:
 (header_is_valid (ascope:'a, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "this")) of
  | SOME (v_header valid_bit x_v_l) =>
   SOME (ascope, scope_list, status_returnv (v_bool valid_bit))
  | _ => NONE
 )
End

Definition header_set_valid_def:
 (header_set_valid (ascope:'a, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "this")) of
  | SOME (v_header valid_bit x_v_l) =>
   (case assign scope_list (v_header T x_v_l) (lval_varname (varn_name "this")) of
    | SOME scope_list' =>
     SOME (ascope, scope_list', status_returnv v_bot)
    | NONE => NONE)
  | _ => NONE
 )
End

Definition header_set_invalid_def:
 (header_set_invalid (ascope:'a, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "this")) of
  | SOME (v_header valid_bit x_v_l) =>
   (case assign scope_list (v_header F x_v_l) (lval_varname (varn_name "this")) of
    | SOME scope_list' =>             
     SOME (ascope, scope_list', status_returnv v_bot)
    | NONE => NONE)
  | _ => NONE
 )
End


(*********************)
(* packet_in methods *)
(*********************)

Definition lookup_ascope_gen_def:
 (lookup_ascope_gen ascope_lookup (ascope:'a) (ext_ref:num) =
  case ascope_lookup ascope ext_ref of
  | SOME v_ext => SOME (v_ext:(core_v_ext, 'b) sum)
  | _ => NONE
 )
End

(* TODO: Is this really needed as a separate function? *)
Definition update_ascope_gen_def:
 (update_ascope_gen ascope_update (ascope:'a) (ext_ref:num) (v_ext:(core_v_ext, 'b) sum) =
  (ascope_update ascope ext_ref v_ext):'a
 )
End

Definition lookup_lval_header_def:
 (lookup_lval_header ss header_lval =
  case lookup_lval ss header_lval of
   | SOME (v_header valid_bit x_v_l) => SOME (valid_bit, x_v_l)
   | _ => NONE
 )
End

(* Partial, but does the job where it is used *)
Definition set_bool_def:
 (set_bool packet_in = v_bool (HD packet_in))
End
Definition set_bit_def:
 (set_bit n packet_in = v_bit (TAKE n packet_in, n))
End

Definition set_fields_def:
 (set_fields []     acc _ = SOME acc) /\
 (set_fields (h::t) acc packet_in =
  case h of
  | (x:x, (v_bool b)) => set_fields t (acc++[(x, set_bool packet_in)]) (DROP 1 packet_in)
  | (x, (v_bit (bv, l))) => set_fields t (acc++[(x, set_bit l packet_in)]) (DROP l packet_in)
  | (x, (v_struct x_v_l)) =>
   (case size_in_bits (v_struct x_v_l) of
    | SOME n =>
     (case set_fields x_v_l [] (TAKE n packet_in) of
      | SOME acc' =>
       set_fields t (acc++[(x, v_struct acc')]) (DROP n packet_in)
      | NONE => NONE)
    | NONE => NONE)
  | (x, (v_header validity x_v_l)) =>
   (case size_in_bits (v_header validity x_v_l) of
    | SOME n =>
     (case set_fields x_v_l [] (TAKE n packet_in) of
      | SOME acc' =>
       set_fields t (acc++[(x, v_header T acc')]) (DROP n packet_in)
      | NONE => NONE)
    | NONE => NONE)
  | _ => NONE)
End

Definition set_header_def:
 (set_header x_v_l packet_in =
  case set_fields x_v_l [] packet_in of
  | SOME x_v_l' => SOME (v_header T x_v_l')
  | NONE => NONE)
End

Definition set_struct_def:
 (set_struct x_v_l packet_in =
  case set_fields x_v_l [] packet_in of
  | SOME x_v_l' => SOME (v_struct x_v_l')
  | NONE => NONE)
End

Definition set_v_def:
 (set_v (v_bit (bitv, n)) packet_in = SOME (set_bit n packet_in)) /\
 (set_v (v_bool b)        packet_in = SOME (set_bool packet_in)) /\
 (set_v (v_struct x_v_l)  packet_in = (set_struct x_v_l packet_in)) /\
 (set_v (v_header validity x_v_l) packet_in = (set_header x_v_l packet_in))
End

(* The symbolic executor stops evaluation at this function and branches *)
Definition packet_in_take_def:
 packet_in_take size packet_in_bl =
  if size <= LENGTH packet_in_bl
  then SOME (TAKE size packet_in_bl, DROP size packet_in_bl)
  else NONE
End

(* See https://p4.org/p4-spec/docs/P4-16-v1.2.2.html#sec-packet-extract-one *)
(* TODO: Extend to cover extraction to header stacks *)
Definition packet_in_extract_gen_def:
 (packet_in_extract_gen ascope_lookup ascope_update ascope_update_v_map (ascope:'a, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "this")) of
  | SOME (v_ext_ref i) =>
   (case lookup_lval_header scope_list (lval_varname (varn_name "headerLvalue")) of
    | SOME (valid_bit, x_v_l) =>
     (case lookup_ascope_gen ascope_lookup ascope i of
      | SOME ((INL (core_v_ext_packet packet_in_bl)):(core_v_ext, 'b) sum) =>
       (case size_in_bits (v_header valid_bit x_v_l) of
        | SOME size =>
         (case packet_in_take size packet_in_bl of
          | SOME (header_bl, packet_in_bl') =>
           (case set_header x_v_l header_bl of
            | SOME header =>
             (case assign scope_list header (lval_varname (varn_name "headerLvalue")) of
              | SOME scope_list' =>
               SOME (update_ascope_gen ascope_update ascope i ((INL (core_v_ext_packet packet_in_bl')):(core_v_ext, 'b) sum), scope_list', status_returnv v_bot)
              | NONE => NONE)
            | NONE => NONE)
          | NONE =>
           (* NOTE: Specific serialisation of errors is assumed here - "PacketTooShort" -> 1 *)
           SOME (ascope_update_v_map ascope "parseError" (v_bit (fixwidth 32 (n2v 1), 32)), scope_list, status_trans "reject"))
        | NONE => NONE)
       | _ => NONE)
    | NONE => NONE)
  | _ => NONE
 )
End

(* See https://p4.org/p4-spec/docs/P4-16-v1.2.4.html#sec-packet-lookahead *)
Definition packet_in_lookahead_gen_def:
 (packet_in_lookahead_gen ascope_lookup ascope_update_v_map (ascope:'a, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "this")) of
  | SOME (v_ext_ref i) =>
   (case lookup_lval scope_list (lval_varname (varn_name "targ1")) of
    | SOME dummy_v =>
     (case lookup_ascope_gen ascope_lookup ascope i of
      | SOME ((INL (core_v_ext_packet packet_in_bl)):(core_v_ext, 'b) sum) =>
       (case size_in_bits dummy_v of
        | SOME size =>
         (case packet_in_take size packet_in_bl of
          | SOME (v_bl, _) =>
           (case set_v dummy_v v_bl of
            | SOME v =>
             SOME (ascope, scope_list, status_returnv v)
            | NONE => NONE)
          | NONE =>
           (* NOTE: Specific serialisation of errors is assumed here - "PacketTooShort" -> 1 *)
           SOME (ascope_update_v_map ascope "parseError" (v_bit (fixwidth 32 (n2v 1), 32)), scope_list, status_trans "reject"))
        | NONE => NONE)
       | _ => NONE)
    | NONE => NONE)
  | _ => NONE
 )
End

(* Advance
   https://p4.org/p4-spec/docs/P4-16-v1.2.4.html#sec-skip-bits
*)

Definition lookup_lval_bit32_def:
 (lookup_lval_bit32 ss bit32_lval =
  case lookup_lval ss bit32_lval of
   | SOME (v_bit (bitv, 32)) => SOME (v2n bitv)
   | _ => NONE
 )
End

Definition packet_in_advance_gen_def:
 (packet_in_advance_gen ascope_lookup ascope_update ascope_update_v_map (ascope:'a, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "this")) of
  | SOME (v_ext_ref i) =>
   (case lookup_lval_bit32 scope_list (lval_varname (varn_name "bits")) of
    | SOME n_bits =>
     (case lookup_ascope_gen ascope_lookup ascope i of
      | SOME ((INL (core_v_ext_packet packet_in_bl)):(core_v_ext, 'b) sum) =>
       (case packet_in_take n_bits packet_in_bl of
        | SOME (_, packet_in_bl') =>
         SOME (update_ascope_gen ascope_update ascope i ((INL (core_v_ext_packet packet_in_bl')):(core_v_ext, 'b) sum), scope_list, status_returnv v_bot)
        | NONE =>
         (* NOTE: Serialisation of errors is assumed here - "PacketTooShort" -> 1 *)
         SOME (ascope_update_v_map ascope "parseError" (v_bit (fixwidth 32 (n2v 1), 32)), scope_list, status_trans "reject"))
       | _ => NONE)
    | NONE => NONE)
  | _ => NONE
 )
End


Theorem packet_in_take_NONE:
!size bl. packet_in_take size bl = NONE <=> LENGTH bl < size
Proof
simp[packet_in_take_def]
QED

Theorem set_fields_TAKE:
!x_v_l size acc bl m.
 fields_size_in_bits x_v_l = SOME size /\ size <= m ==>
 set_fields x_v_l acc (TAKE m bl) = set_fields x_v_l acc bl
Proof
Induct_on ‘x_v_l’ >> rpt strip_tac >- (
 simp[set_fields_def]
) >>
PairCases_on ‘h’ >>
Cases_on ‘h1’ >- (
 gvs[size_in_bits_def, AllCaseEqs()] >>
 asm_simp_tac (srw_ss()++numSimps.ARITH_ss) [set_fields_def, set_bool_def, listTheory.HD_TAKE, listTheory.DROP_TAKE]
) >- (
 PairCases_on ‘p’ >>
 gvs[size_in_bits_def, AllCaseEqs()] >>
 asm_simp_tac (srw_ss()++numSimps.ARITH_ss) [set_fields_def, set_bit_def, listTheory.DROP_TAKE, rich_listTheory.TAKE_TAKE_T]
) >> (
 gvs[size_in_bits_def, AllCaseEqs()] >>
 asm_simp_tac (srw_ss()++numSimps.ARITH_ss) [set_fields_def, size_in_bits_def, listTheory.DROP_TAKE, rich_listTheory.TAKE_TAKE_T]
)
QED

Theorem set_header_TAKE:
!b x_v_l size bl.
 size_in_bits (v_header b x_v_l) = SOME size ==>
 set_header x_v_l (TAKE size bl) = set_header x_v_l bl
Proof
rpt strip_tac >>
gvs[size_in_bits_def, set_header_def] >>
drule_then (qspecl_then [‘[]’, ‘bl’, ‘size’] mp_tac) set_fields_TAKE >>
simp[]
QED

Theorem set_v_TAKE:
!v size bl.
 size_in_bits v = SOME size ==>
 set_v v (TAKE size bl) = set_v v bl
Proof
Cases_on ‘v’ >> (
 rpt strip_tac >>
 TRY (rename1 ‘v_bit bvn’ >> Cases_on ‘bvn’) >>
 gvs[size_in_bits_def, set_v_def, set_bit_def, set_bool_def, set_struct_def, set_header_def, listTheory.HD_TAKE, rich_listTheory.TAKE_TAKE_T] >>
 TRY (drule_then (qspecl_then [‘[]’, ‘bl’, ‘size’] mp_tac) set_fields_TAKE >> simp[])
)
QED


(**********************)
(* packet_out methods *)
(**********************)

Definition header_fields_bits_def:
 (header_fields_bits [] = SOME []) /\
 (header_fields_bits (h::t) =
  case header_field_bits h of
  | SOME bl =>
   (case header_fields_bits t of
    | SOME bl' => SOME (bl++bl')
    | NONE => NONE)
  | NONE => NONE
 ) /\
 (header_field_bits (x:x, v) =
  case v of
  | v_bit (bl, n) => SOME bl
  | v_bool b => SOME [b]
  | v_struct x_v_l => header_fields_bits x_v_l
  | _ => NONE
 )
End

(* Emitting a struct emits its valid headers; other member types are not allowed *)
Definition struct_members_bits_def:
 (struct_members_bits [] = SOME []) /\
 (struct_members_bits (h::t) =
  case struct_member_bits h of
  | SOME bl =>
   (case struct_members_bits t of
    | SOME bl' => SOME (bl++bl')
    | NONE => NONE)
  | NONE => NONE
 ) /\
 (struct_member_bits (x:x, v) =
  case v of
  | v_header validity x_v_l => if validity then header_fields_bits x_v_l else SOME []
  | v_struct x_v_l => struct_members_bits x_v_l
  | _ => NONE
 )
End

(* TODO: Should also support emission from: header stack and header union *)
Definition packet_out_emit_gen_def:
 (packet_out_emit_gen (ascope_lookup:'a -> num -> (core_v_ext + 'b) option) ascope_update (ascope:'a, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "this")) of
  | SOME (v_ext_ref i) =>
   (case lookup_ascope_gen ascope_lookup ascope i of
    | SOME (INL (core_v_ext_packet packet_out_bl)) =>
     (case lookup_lval scope_list (lval_varname (varn_name "data")) of
      | SOME (v_header F x_v_l) => SOME (ascope, scope_list, status_returnv v_bot)
      | SOME (v_header T x_v_l) =>
       (case header_fields_bits x_v_l of
        | SOME bl =>
         SOME (update_ascope_gen ascope_update ascope i ((INL (core_v_ext_packet (packet_out_bl++bl))):(core_v_ext, 'b) sum), scope_list, status_returnv v_bot)
        | NONE => NONE)
      | SOME (v_struct x_v_l) =>
       (case struct_members_bits x_v_l of
        | SOME bl =>
         SOME (update_ascope_gen ascope_update ascope i ((INL (core_v_ext_packet (packet_out_bl++bl))):(core_v_ext, 'b) sum), scope_list, status_returnv v_bot)
        | NONE => NONE)
      | SOME _ => NONE
      | NONE => NONE)
    | _ => NONE)
  | _ => NONE
 )
End

(************)
(* Checksum *)
(************)

(* Bits of checksum and hash data *)
Definition header_entries2v_def:
 (header_entries2v [] = SOME []) /\
 (header_entries2v ((x:x, v)::t) =
  case data_bits v of
  | SOME bl =>
  (case header_entries2v t of
   | SOME bl2 => SOME (bl++bl2)
   | NONE => NONE)
  | NONE => NONE
 ) /\
 (data_bits v =
  case v of
  | (v_bit (bl, n)) => SOME bl
  | (v_bool b) => SOME [b]
  | (v_struct x_v_l) => header_entries2v x_v_l
  (* Invalid headers contribute no bits, as in bmv2 *)
  | (v_header validity x_v_l) => if validity then header_entries2v x_v_l else SOME []
  | _ => NONE
 )
End


Definition v2w16s'_def:
 (v2w16s' [] = []) /\
 (v2w16s' v =
  ((v2w (TAKE 16 v)):word16)::(v2w16s' (DROP 16 v))
 )
Termination
WF_REL_TAC `measure LENGTH` >>
fs []
End

Definition v2w16s_def:
 (v2w16s v = if (LENGTH v) MOD 16 = 0 then SOME (v2w16s' v) else NONE)
End

Definition get_checksum_incr_def:
 (get_checksum_incr scope_list ext_data_name =
   (case lookup_lval scope_list ext_data_name of
    | SOME v =>
     (case data_bits v of
      | SOME bl => v2w16s bl
      | NONE => NONE)
    | NONE => NONE)
 )
End

(* Alternative version tailored for symbolic execution *)
Definition get_checksum_incr'_def:
 (get_checksum_incr' scope_list ext_data_name =
   (case lookup_lval scope_list ext_data_name of
    | SOME (v_bit (bl, n)) =>
     if n MOD 16 = 0 then SOME bl else NONE
    | SOME (v_header vbit f_list) =>
     (case header_entries2v f_list of
      | SOME bl =>
       if (LENGTH bl) MOD 16 = 0 then SOME bl else NONE
      | NONE => NONE)
    | SOME (v_struct f_list) =>
     (case header_entries2v f_list of
      | SOME bl =>
       if (LENGTH bl) MOD 16 = 0 then SOME bl else NONE
      | NONE => NONE)
    | _ => NONE)
 )
End

Definition add_ones_complement_def:
 add_ones_complement (x, y) = 
  let
   (result,carry_out,overflow) = add_with_carry(x,y,F)
  in
   if carry_out
   then result + 1w
   else result
End

Definition sub_ones_complement_def:
 sub_ones_complement (x, y) = add_ones_complement (x, word_1comp y)
End

Definition compute_checksum16_def:
 compute_checksum16 (w16_list:word16 list) = 
  word_1comp (FOLDR (CURRY add_ones_complement) (0w:word16) w16_list)
End

Definition get_bitlist_def:
 get_bitlist scope_list ext_data_name =
  case lookup_lval scope_list ext_data_name of
   | SOME (v_bit (bl, n)) => SOME bl
   | SOME (v_header vbit f_list) =>
    (case header_entries2v f_list of
     | SOME bl => SOME bl
     | NONE => NONE)
   | SOME (v_struct f_list) =>
    (case header_entries2v f_list of
     | SOME bl => SOME bl
     | NONE => NONE)
   | _ => NONE
End


(*****************)
(* Architectural *)
(*****************)

Definition ascope_lookup_gen_def:
 ascope_lookup_gen ascope ext_ref =
  let ext_obj_map = FST $ SND ascope in
   ALOOKUP ext_obj_map ext_ref
End

Definition ascope_update_gen_def:
 ascope_update_gen (counter, ext_obj_map, v_map, ctrl, oracle_index:num) ext_ref v_ext =
  (counter, AUPDATE ext_obj_map (ext_ref, v_ext), v_map, ctrl, oracle_index)
End

Definition ascope_update_v_map_gen_def:
 ascope_update_v_map_gen (counter, ext_obj_map, v_map, ctrl, oracle_index:num) str (v:v) =
  (counter, ext_obj_map, AUPDATE v_map (str, v), ctrl, oracle_index)
End

(* Keeps the n persistent extern objects, discards the rest *)
Definition reset_ext_obj_map_gen_def:
 reset_ext_obj_map_gen (n:num) ((counter, ext_obj_map, v_map, ctrl, oracle_index):(num # ((num, (core_v_ext, 'a) sum) alist) # ((string, v) alist) # 'b # num)) =
  (n, FILTER (\ (k, v_ext). k < n) ext_obj_map, v_map, ctrl, oracle_index)
End

Theorem reset_ext_obj_map_gen_ALOOKUP:
!n counter ext_obj_map v_map ctrl oracle_index k.
 ALOOKUP (FST $ SND (reset_ext_obj_map_gen n ((counter, ext_obj_map, v_map, ctrl, oracle_index):(num # ((num, (core_v_ext, 'a) sum) alist) # ((string, v) alist) # 'b # num)))) k =
  if k < n then ALOOKUP ext_obj_map k else NONE
Proof
rpt strip_tac >>
simp[reset_ext_obj_map_gen_def, alistTheory.ALOOKUP_FILTER]
QED

(* TODO: Remove these and keep "v_map" as just a regular scope? *)
Definition v_map_to_scope_def:
 (v_map_to_scope [] = []) /\
 (v_map_to_scope (((k, v)::t):(string, v) alist) =
  ((varn_name k, (v, NONE:lval option))::v_map_to_scope t)
 )
End

Definition scope_to_vmap_def:
 (scope_to_vmap [] = SOME []) /\
 (scope_to_vmap ((vn, (v:v, lval_opt:lval option))::t) =
  case vn of
   | (varn_name k) => oCONS ((k, v), scope_to_vmap t)
   | _ => NONE
 )
End

(* Looks up the non-out arguments of a programmable block in v_map before copy-in *)
Definition reduce_nonout_def:
 (reduce_nonout ([], elist, v_map) = SOME []) /\
 (reduce_nonout (d::dlist, e::elist, v_map) =
  if is_d_out d
  then oCONS (e, reduce_nonout (dlist, elist, v_map))
  else
   (case e of
    | (e_var (varn_name x)) =>
     (case ALOOKUP v_map x of
      | SOME v =>
       (* NOTE: Only externs can be passed as directionless arguments here *)
       oCONS (e_v v, reduce_nonout (dlist, elist, v_map))
      | _ => NONE)
    | _ => NONE)) /\
 (reduce_nonout (_, _, v_map) = NONE)
End

(* TODO: Don't reduce all arguments at once? *)
Definition copyin_pbl_gen_def:
 copyin_pbl_gen (xlist, dlist, elist, (counter, ext_obj_map, v_map, ctrl, oracle_index), random_oracle) =
  case reduce_nonout (dlist, elist, v_map) of
  | SOME elist' =>
   copyin xlist dlist elist' [v_map_to_scope v_map] [ [] ] oracle_index random_oracle
  | NONE => NONE
End

(* Re-uses the copy-out of P4 functions *)
Definition copyout_pbl_gen_def:
 copyout_pbl_gen (g_scope_list, (counter, ext_obj_map, v_map, ctrl, oracle_index), dlist, xlist, (status:status)) =
  case update_return_frame xlist dlist [v_map_to_scope v_map] g_scope_list of
  | SOME [v_map_scope] =>
   (case scope_to_vmap v_map_scope of
    | SOME v_map' => SOME (counter, ext_obj_map, v_map', ctrl, oracle_index)
    | NONE => NONE)
  | _ => NONE
End

Definition get_oracle_index_gen_def:
 get_oracle_index_gen (counter, ext_obj_map, v_map, ctrl, oracle_index:num) =
  oracle_index
End

Definition set_oracle_index_gen_def:
 set_oracle_index_gen i_opt (counter, ext_obj_map, v_map, ctrl, oracle_index:num) =
  (counter, ext_obj_map, v_map, ctrl, case i_opt of NONE => oracle_index | SOME i => i)
End

(* Looks up the extern object a v_map entry refers to *)
Definition lookup_obj_def:
 lookup_obj ext_obj_map v_map k =
  case ALOOKUP v_map k of
  | SOME (v_ext_ref i) =>
   ALOOKUP ext_obj_map i
  | _ => NONE
End

(* A separate definition so that symbolic execution can choose to not evaluate it
 * and rewrite with assumptions instead *)
Definition get_port_number_def:
 get_port_number bl = v2n bl
End

(************************************)
(* Miscellaneous common definitions *)
(************************************)

(* TODO: Are match_kinds needed at all in the dynamic semantics? *)
Definition FOLDL_MATCH_def:
 (FOLDL_MATCH e_l res [] = res) /\
 (FOLDL_MATCH e_l (res_act, res_prio_opt:num option) (((k,prio),v)::t) =
  if k e_l
  then
   (* TODO: Largest priority wins (like for P4Runtime API) is hard-coded *)
   case res_prio_opt of
   | SOME res_prio =>
    if prio > res_prio
    then
     FOLDL_MATCH e_l (v, SOME prio) t
    else FOLDL_MATCH e_l (res_act, res_prio_opt) t
   | NONE => FOLDL_MATCH e_l (v, SOME prio) t
  else FOLDL_MATCH e_l (res_act, res_prio_opt) t)
End

(* Alternative version, which uses smallest priority *)
Definition FOLDL_MATCH_alt_def:
 (FOLDL_MATCH_alt e_l res acc [] = res) /\
 (FOLDL_MATCH_alt e_l (res_act, res_prio_opt:num option) acc (((k,prio),v)::t) =
  if k e_l
  then
   (* TODO: Smallest priority wins (like for TDI) is hard-coded,
    *       other than priority zero. *)
   case res_prio_opt of
   | SOME res_prio =>
    let prio' = if (prio = 0) then acc else prio in
    if (prio' < res_prio)
    then
     FOLDL_MATCH_alt e_l (v, SOME prio') (acc+1) t
    else FOLDL_MATCH_alt e_l (res_act, res_prio_opt) (acc+1) t
   | NONE => FOLDL_MATCH_alt e_l (v, SOME prio) (acc+1) t
  else FOLDL_MATCH_alt e_l (res_act, res_prio_opt) (acc+1) t)
End

(* largest_wins mk_list picks FOLDL_MATCH (largest priority wins) over FOLDL_MATCH_alt *)
Definition apply_table_f_gen_def:
 apply_table_f_gen largest_wins (x, e_l, mk_list:mk_list, (x', e_l'), (counter, ext_obj_map, v_map, ctrl, oracle_index:num)) =
  case ALOOKUP ctrl x of
  | SOME table =>
   if largest_wins mk_list
   then SOME (FST $ FOLDL_MATCH e_l ((x', e_l'), NONE) table)
   else SOME (FST $ FOLDL_MATCH_alt e_l ((x', e_l'), NONE) (1:num) table)
  | NONE => NONE
End
