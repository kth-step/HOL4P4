Theory p4_v1model
Ancestors
  p4 p4_aux p4_core
Libs
  p4Syntax

(* Useful documentation and reference links:
   https://github.com/p4lang/behavioral-model/blob/main/docs/simple_switch.md
   https://github.com/p4lang/behavioral-model/blob/main/targets/simple_switch/simple_switch.cpp
*)

(* NOTE ON CONTROL PLANE APIS
 * By default, this model is set up to work with TDI-style tables, where priority annotation
 * leads to smallest priority winning out in case of multiple matches (for ternary match kinds).
 * Change this by setting the value of CONTROL_PLANE_API to correspond with the control plane
 * API you want to model.
 *
 * TDI (default): 0
 * P4Runtime API: 1
 *
 * *)

val CONTROL_PLANE_API = 0;

(* TODO: v1model uses a checksum in the verify_checksum and update_checksum externs *)
Datatype:
 v1model_v_ext =
   v1model_v_ext_ipv4_checksum (word16 list)
 | v1model_v_ext_counter (num # num # (num, num # num) alist)
 | v1model_v_ext_direct_counter
 | v1model_v_ext_meter
 | v1model_v_ext_direct_meter
 | v1model_v_ext_register ((bool list # num) list)
 (* From IPSec example *)
 | v1model_v_ext_ipsec_crypt
End
Type v1model_sum_v_ext = “:(core_v_ext, v1model_v_ext) sum”

(* The control plane representation:

   (* the table name *)
   (string, 
     (* the key of a table entry: first element is a predicate for matching, second is priority *)
    ((e_list -> bool, num),
     (* the action of a table entry: string is action name, e_list is arguments *)
     string # e_list) alist) alist``)
*)
Type v1model_ctrl = “:(string, (((e_list -> bool) # num), string # e_list) alist) alist”

(* The architectural state type of the V1Model architecture model *)
Type v1model_ascope = “:(num # ((num, v1model_sum_v_ext) alist) # ((string, v) alist) # v1model_ctrl # num)”

(**********************************************************)
(*               SPECIALISED CORE METHODS                 *)
(**********************************************************)

(* TODO: Remove unused arguments from these? *)

Definition v1model_ascope_lookup_def:
 v1model_ascope_lookup (ascope:v1model_ascope) ext_ref = 
  let ext_obj_map = FST $ SND ascope in
   ALOOKUP ext_obj_map ext_ref
End

Definition v1model_ascope_update_def:
 v1model_ascope_update ((counter, ext_obj_map, v_map, ctrl, oracle_index):v1model_ascope) ext_ref v_ext =
   (counter, AUPDATE ext_obj_map (ext_ref, v_ext), v_map, ctrl, oracle_index)
End

Definition v1model_ascope_update_v_map_def:
 v1model_ascope_update_v_map ((counter, ext_obj_map, v_map, ctrl, oracle_index):v1model_ascope) str v =
   (counter, ext_obj_map, AUPDATE v_map (str, v), ctrl, oracle_index)
End

Definition v1model_packet_in_extract_def:
 v1model_packet_in_extract = packet_in_extract_gen v1model_ascope_lookup v1model_ascope_update v1model_ascope_update_v_map
End

Definition v1model_packet_in_lookahead_def:
 v1model_packet_in_lookahead = packet_in_lookahead_gen v1model_ascope_lookup v1model_ascope_update_v_map
End

Definition v1model_packet_in_advance_def:
 v1model_packet_in_advance = packet_in_advance_gen v1model_ascope_lookup v1model_ascope_update v1model_ascope_update_v_map
End

Definition v1model_packet_out_emit_def:
 v1model_packet_out_emit = packet_out_emit_gen v1model_ascope_lookup v1model_ascope_update
End

Definition v1model_verify_def:
 (v1model_verify (ascope:v1model_ascope, g_scope_list:g_scope_list, scope_list) =
  verify_gen v1model_ascope_update_v_map (ascope, g_scope_list, scope_list))
End

(**********************************************)
(*             HELPER FUNCTIONS               *)
(**********************************************)

Definition v1model_ascope_read_ext_obj_def:
 v1model_ascope_read_ext_obj ((counter, ext_obj_map, v_map, ctrl, oracle_index):v1model_ascope) vname =
  case ALOOKUP v_map vname of
  | SOME (v_ext_ref n) =>
   ALOOKUP ext_obj_map n
  | _ => NONE
End

Definition v1model_ascope_of_conc_state_def:
 v1model_ascope_of_conc_state (io1,io2,(ascope:v1model_ascope)) =
  ascope
End
    
(**********************************************************)
(*             EXTERN OBJECTS AND FUNCTIONS               *)
(**********************************************************)

(* NOTE: 511 is the default drop port *)
Definition v1model_mark_to_drop_def:
 v1model_mark_to_drop (v1model_ascope:v1model_ascope, g_scope_list:g_scope_list, scope_list) =
  case assign scope_list (v_bit (fixwidth 9 (n2v 511), 9)) (lval_field (lval_varname (varn_name "standard_metadata")) "egress_spec") of
   | SOME scope_list' =>
    (case assign scope_list' (v_bit (fixwidth 16 (n2v 0), 16)) (lval_field (lval_varname (varn_name "standard_metadata")) "mcast_grp") of
     | SOME scope_list'' =>
      SOME (v1model_ascope, scope_list'', status_returnv v_bot)
     | NONE => NONE)
   | NONE => NONE
End

(**********************)
(* Checksum methods   *)
(**********************)

(* Reflected CRCs as in bmv2 (behavioral-model/src/bm_sim/calculations.cpp) *)
Definition crc_byte_def:
 crc_byte (poly:'a word) (crc:'a word) (b:word8) =
  FUNPOW (\c. if word_lsb c then (c >>> 1) ?? poly else c >>> 1) 8 (crc ?? w2w b)
End

Definition crc16_def:
 crc16 (bytes:word8 list) = FOLDL (crc_byte (0xA001w:word16)) 0w bytes
End

Definition crc32_def:
 crc32 (bytes:word8 list) = word_1comp (FOLDL (crc_byte (0xEDB88320w:word32)) 0xFFFFFFFFw bytes)
End

Definition v2w8s'_def:
 (v2w8s' [] = []) /\
 (v2w8s' v =
  ((v2w (TAKE 8 v)):word8)::(v2w8s' (DROP 8 v))
 )
Termination
WF_REL_TAC `measure LENGTH` >>
fs []
End

(* Zero-pads at the end to a multiple of n bits *)
Definition pad_bits_def:
 pad_bits n bl = bl ++ REPLICATE ((n - LENGTH bl MOD n) MOD n) F
End


(********)
(* hash *)

Definition v1model_hash_bits_def:
 v1model_hash_bits v =
  case v of
  | v_bit (bl, n) => SOME bl
  | v_struct x_v_l => header_entries2v x_v_l
  | v_header validity x_v_l => if validity then header_entries2v x_v_l else SOME []
  | _ => NONE
End

(* HashAlgorithm members in declaration order; the custom CRCs are the unconfigured crc32/crc16 of bmv2 *)
Definition v1model_hash_det_def:
 v1model_hash_det (algo:num) bl =
  if algo = 0 \/ algo = 1 then SOME (w2n (crc32 (v2w8s' (pad_bits 8 bl))))
  else if algo = 2 \/ algo = 3 then SOME (w2n (crc16 (v2w8s' (pad_bits 8 bl))))
  else if algo = 5 then SOME (v2n (TAKE 64 (pad_bits 8 bl)))
  else if algo = 6 then SOME (w2n (compute_checksum16 (v2w16s' (pad_bits 16 bl))))
  else if algo = 7 then SOME (w2n (FOLDL word_xor (0w:word16) (v2w16s' (pad_bits 16 bl))))
  else NONE
End

(* random draws width oracle bits *)
Definition v1model_hash_inner_def:
 v1model_hash_inner (algo:num) width oracle_index random_oracle bl =
  if algo = 4 then SOME (v2n (get_oracle_calls width oracle_index random_oracle), oracle_index + width)
  else OPTION_MAP (\h. (h, oracle_index)) (v1model_hash_det algo bl)
End

(* As bmv2: 64-bit operands and arithmetic, the caller truncates to the result width *)
Definition v1model_hash_range_def:
 v1model_hash_range base max h =
  let base' = base MOD 2 ** 64 in
  let max' = max MOD 2 ** 64 in
   if max' = 0 then base' else (base' + h MOD max') MOD 2 ** 64
End

(* The width of the result is that of the out parameter, as in register_read *)
Definition v1model_hash_def:
 v1model_hash random_oracle ((counter, ext_obj_map, v_map, ctrl, oracle_index):v1model_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "result")) of
  | SOME (v_bit (bl_res, width)) =>
   (case lookup_lval scope_list (lval_varname (varn_name "algo")) of
    | SOME (v_bit (bl_algo, n_algo)) =>
     (case lookup_lval scope_list (lval_varname (varn_name "base")) of
      | SOME (v_bit (bl_base, n_base)) =>
       (case lookup_lval scope_list (lval_varname (varn_name "max")) of
        | SOME (v_bit (bl_max, n_max)) =>
         (case lookup_lval scope_list (lval_varname (varn_name "data")) of
          | SOME data =>
           (case v1model_hash_bits data of
            | SOME bl =>
             (case v1model_hash_inner (v2n bl_algo) width oracle_index random_oracle bl of
              | SOME (h, oracle_index') =>
               (case assign scope_list (v_bit (fixwidth width (n2v (v1model_hash_range (v2n bl_base) (v2n bl_max) h)), width)) (lval_varname (varn_name "result")) of
                | SOME scope_list' =>
                 SOME ((counter, ext_obj_map, v_map, ctrl, oracle_index'), scope_list', status_returnv v_bot)
                | NONE => NONE)
              | NONE => NONE)
            | NONE => NONE)
          | NONE => NONE)
        | _ => NONE)
      | _ => NONE)
    | _ => NONE)
  | _ => NONE
End

(*******************)
(* verify_checksum *)

(* Any algorithm, data length and checksum width; the comparison is numeric, as in bmv2 *)
Definition v1model_verify_checksum_def:
 (v1model_verify_checksum ((counter, ext_obj_map, v_map, ctrl, oracle_index):v1model_ascope, g_scope_list:g_scope_list, scope_list) =
  (case lookup_lval scope_list (lval_varname (varn_name "condition")) of
   | SOME $ v_bool b =>
    if b
    then
     (case lookup_lval scope_list (lval_varname (varn_name "algo")) of
      | SOME $ v_bit (bl, n) =>
       (case lookup_lval scope_list (lval_varname (varn_name "data")) of
        | SOME data =>
         (case v1model_hash_bits data of
          | SOME bl_data =>
           (case v1model_hash_det (v2n bl) bl_data of
            | SOME h =>
             (case lookup_lval scope_list (lval_varname (varn_name "checksum")) of
              | SOME $ v_bit (bl', n') =>
               (if v2n bl' = h
                then SOME ((counter, ext_obj_map, v_map, ctrl, oracle_index), scope_list, status_returnv v_bot)
                else
                 (case assign [v_map_to_scope v_map] (v_bit ([T], 1)) (lval_field (lval_varname (varn_name "standard_metadata")) "checksum_error") of
                  | SOME [v_map_scope] =>
                   (case scope_to_vmap v_map_scope of
                    | SOME v_map' =>
                     SOME ((counter, ext_obj_map, v_map', ctrl, oracle_index), scope_list, status_returnv v_bot)
                    | NONE => NONE)
                  | _ => NONE))
              | _ => NONE)
            | NONE => NONE)
          | NONE => NONE)
        | NONE => NONE)
      | _ => NONE)
    else SOME ((counter, ext_obj_map, v_map, ctrl, oracle_index), scope_list, status_returnv v_bot)
   | _ => NONE)
 )
End

(*******************)
(* update_checksum *)

Definition v1model_update_checksum_inner_def:
 v1model_update_checksum_inner bitlist =
  v_bit $ w16 $ compute_checksum16 $ v2w16s' bitlist
End

(* csum16 into a 16-bit field stays the folded v1model_update_checksum_inner for symbolic execution *)
Definition v1model_update_checksum_def:
 (v1model_update_checksum ((counter, ext_obj_map, v_map, ctrl, oracle_index):v1model_ascope, g_scope_list:g_scope_list, scope_list) =
  (case lookup_lval scope_list (lval_varname (varn_name "condition")) of
   | SOME $ v_bool b =>
    if b
    then
     (case lookup_lval scope_list (lval_varname (varn_name "algo")) of
      | SOME $ v_bit (bl, n) =>
       (case lookup_lval scope_list (lval_varname (varn_name "data")) of
        | SOME data =>
         (case v1model_hash_bits data of
          | SOME bl_data =>
           (case lookup_lval scope_list (lval_varname (varn_name "checksum")) of
            | SOME $ v_bit (bl', n') =>
             if v2n bl = 6 /\ n' = 16
             then
              (case assign scope_list (v1model_update_checksum_inner (pad_bits 16 bl_data)) (lval_varname (varn_name "checksum")) of
               | SOME scope_list' =>
                SOME ((counter, ext_obj_map, v_map, ctrl, oracle_index), scope_list', status_returnv v_bot)
               | NONE => NONE)
             else
              (case v1model_hash_det (v2n bl) bl_data of
               | SOME h =>
                (case assign scope_list (v_bit (fixwidth n' (n2v h), n')) (lval_varname (varn_name "checksum")) of
                 | SOME scope_list' =>
                  SOME ((counter, ext_obj_map, v_map, ctrl, oracle_index), scope_list', status_returnv v_bot)
                 | NONE => NONE)
               | NONE => NONE)
            | _ => NONE)
          | NONE => NONE)
        | NONE => NONE)
      | _ => NONE)
    else SOME ((counter, ext_obj_map, v_map, ctrl, oracle_index), scope_list, status_returnv v_bot)
   | _ => NONE)
 )
End

(**************)
(* Register   *)
(**************)
(*
Definition replicate_arb_def:
 replicate_arb length width =
  REPLICATE length ((REPLICATE width (ARB:bool)), width)
End


*)
Definition get_oracle_calls_array_def:
 (get_oracle_calls_array width oracle_index random_oracle 0 = []) /\
 (get_oracle_calls_array width oracle_index random_oracle (SUC amount) =
  (get_oracle_calls width oracle_index random_oracle, width)::(get_oracle_calls_array width (oracle_index + width) random_oracle amount))
End

Definition v1model_register_construct_inner_def:
 v1model_register_construct_inner size width oracle_index random_oracle =
  get_oracle_calls_array width oracle_index random_oracle size
End
        
Definition register_construct_def:
 (register_construct random_oracle ((counter, ext_obj_map, v_map, ctrl, oracle_index):v1model_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "size")) of
  | SOME (v_bit (bl, n)) =>
   (case lookup_lval scope_list (lval_varname (varn_name "targ1")) of
    | SOME (v_bit (bl', n')) =>
     let size = v2n bl in
     let width = n' in
     let ext_obj_map' = AUPDATE ext_obj_map (counter, INR (v1model_v_ext_register (v1model_register_construct_inner size width oracle_index random_oracle))) in
     (case assign scope_list (v_ext_ref counter) (lval_varname (varn_name "this")) of
      | SOME scope_list' =>
       SOME ((counter + 1, ext_obj_map', v_map, ctrl, oracle_index + (size*width)), scope_list', status_returnv v_bot)
      | NONE => NONE)
    | _ => NONE)
  | _ => NONE
 )
End

(* OLD:
Definition register_read_def:
 (register_read ((counter, ext_obj_map, v_map, ctrl):v1model_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "index")) of
  | SOME (v_bit (bl, n)) =>
   (case lookup_lval scope_list (lval_varname (varn_name "this")) of
    | SOME (v_ext_ref i) =>
     (case ALOOKUP ext_obj_map i of
      | SOME (INR (v1model_v_ext_register array)) =>
       (case oEL (v2n bl) array of
        | SOME (bl', n') =>
         (case assign scope_list (v_bit (bl', n')) (lval_varname (varn_name "result")) of
          | SOME scope_list' =>
           SOME ((counter, ext_obj_map, v_map, ctrl), scope_list', status_returnv v_bot)
          | NONE => NONE)
        | NONE => NONE)
      | _ => NONE)
    | _ => NONE)
  | _ => NONE
 )
End
*)

(* Simply replaces the oEL of a v2n index *)
Definition v1model_register_read_inner_def:
 (v1model_register_read_inner n'' array_index_v array oracle_index random_oracle =
  case oEL (v2n array_index_v) array of
  | SOME res => res
  | NONE => (get_oracle_calls n'' oracle_index random_oracle, n'')
 )
End

(* Note that register_read always has a result, according to v1model.p4. *)
Definition register_read_def:
 (register_read random_oracle ((counter, ext_obj_map, v_map, ctrl, oracle_index):v1model_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "index")) of
  | SOME (v_bit (bl, n)) =>
   (case lookup_lval scope_list (lval_varname (varn_name "this")) of
    | SOME (v_ext_ref i) =>
     (case ALOOKUP ext_obj_map i of
      | SOME (INR (v1model_v_ext_register array)) =>
       (* TODO: HACK, looking up the result variable to get the result width. *)
       (case lookup_lval scope_list (lval_varname (varn_name "result")) of
        | SOME (v_bit (bl'', n'')) =>
         let (bl', n') = v1model_register_read_inner n'' bl array oracle_index random_oracle in
           (case assign scope_list (v_bit (bl', n')) (lval_varname (varn_name "result")) of
            | SOME scope_list' =>
             SOME ((counter, ext_obj_map, v_map, ctrl, oracle_index), scope_list', status_returnv v_bot)
            | NONE => NONE)
        | _ => NONE)
      | _ => NONE)
    | _ => NONE)
  | _ => NONE
 )
End

Definition v1model_register_write_inner_def:
 (v1model_register_write_inner update array_index_v (array:(bool list # num) list) =
  LUPDATE update (v2n array_index_v) array
 )
End

Definition register_write_def:
 (register_write ((counter, ext_obj_map, v_map, ctrl, oracle_index):v1model_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "index")) of
  | SOME (v_bit (bl, n)) =>
   (case lookup_lval scope_list (lval_varname (varn_name "value")) of
    | SOME (v_bit (bl', n')) =>
     (case lookup_lval scope_list (lval_varname (varn_name "this")) of
      | SOME (v_ext_ref i) =>
       (case ALOOKUP ext_obj_map i of
        | SOME (INR (v1model_v_ext_register array)) =>
         let array' = v1model_register_write_inner (bl', n') bl array in
         let ext_obj_map' = AUPDATE ext_obj_map (i, INR (v1model_v_ext_register array')) in
          SOME ((counter, ext_obj_map', v_map, ctrl, oracle_index), scope_list, status_returnv v_bot)
        | _ => NONE)
      | _ => NONE)
    | _ => NONE)
  | _ => NONE
 )
End

(**************)
(* Counter    *)
(**************)

(* Counter state: CounterType, size and the (packets, bytes) of the touched indices *)
Definition counter_construct_def:
 (counter_construct ((counter, ext_obj_map, v_map, ctrl, oracle_index):v1model_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "size")) of
  | SOME (v_bit (bl, n)) =>
   (case lookup_lval scope_list (lval_varname (varn_name "type")) of
    | SOME (v_bit (bl', n')) =>
     let ext_obj_map' = AUPDATE ext_obj_map (counter, INR (v1model_v_ext_counter (v2n bl', v2n bl, []))) in
     (case assign scope_list (v_ext_ref counter) (lval_varname (varn_name "this")) of
      | SOME scope_list' =>
       SOME ((counter + 1, ext_obj_map', v_map, ctrl, oracle_index), scope_list', status_returnv v_bot)
      | NONE => NONE)
    | _ => NONE)
  | _ => NONE
 )
End

(* Indices at or above the size are ignored, as specified by v1model.p4 *)
Definition v1model_counter_count_inner_def:
 v1model_counter_count_inner ((ty:num), (size:num), counts) (index:num) (len:num) =
  if index < size
  then
   let (packets, bytes) = (case ALOOKUP counts index of SOME pb => pb | NONE => (0, 0)) in
    (ty, size, AUPDATE counts (index, (packets + 1, bytes + len)))
  else (ty, size, counts)
End

Definition counter_count_def:
 (counter_count ((counter, ext_obj_map, v_map, ctrl, oracle_index):v1model_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "index")) of
  | SOME (v_bit (bl, n)) =>
   (case lookup_lval scope_list (lval_varname (varn_name "this")) of
    | SOME (v_ext_ref i) =>
     (case ALOOKUP ext_obj_map i of
      | SOME (INR (v1model_v_ext_counter counter_state)) =>
       (case ALOOKUP v_map "standard_metadata" of
        | SOME (v_struct fields) =>
         (case ALOOKUP fields "packet_length" of
          | SOME (v_bit (bl', n')) =>
           let ext_obj_map' = AUPDATE ext_obj_map (i, INR (v1model_v_ext_counter (v1model_counter_count_inner counter_state (v2n bl) (v2n bl')))) in
            SOME ((counter, ext_obj_map', v_map, ctrl, oracle_index), scope_list, status_returnv v_bot)
          | _ => NONE)
        | _ => NONE)
      | _ => NONE)
    | _ => NONE)
  | _ => NONE
 )
End

(*******************)
(* IPSec methods   *)
(*******************)

(* TODO: Initialises nothing, for now... *)
Definition ipsec_crypt_construct_def:
 (ipsec_crypt_construct ((counter, ext_obj_map, v_map, ctrl, oracle_index):v1model_ascope, g_scope_list:g_scope_list, scope_list) =
   let ext_obj_map' = AUPDATE ext_obj_map (counter, INR (v1model_v_ext_ipsec_crypt)) in
   (case assign scope_list (v_ext_ref counter) (lval_varname (varn_name "this")) of
    | SOME scope_list' =>
     SOME ((counter + 1, ext_obj_map', v_map, ctrl, oracle_index), scope_list', status_returnv v_bot)
    | NONE => NONE)
 )
End

Definition set_validity_def:
  (set_validity validity (v_struct ((x,v)::t)) = v_struct (((x, set_validity validity v))::(MAP (\(x',v'). (x', set_validity validity v')) t))) /\
  (set_validity validity (v_struct []) = v_struct []) /\
  (set_validity validity (v_header boolv ((x,v)::t)) =
    v_header validity (( (x, set_validity validity v) )::(MAP (\(x',v'). (x', set_validity validity v')) t))) /\
  (set_validity validity (v_header boolv []) = v_header validity []) /\
  (set_validity _ (v:v) = v)
Termination
 WF_REL_TAC `measure (\ (validity,v). v_size v)` >>
 fs [v_size_def] >>
 REPEAT STRIP_TAC >>
 `v_size v' < v1_size t` suffices_by (
  fs []
 ) >>
 METIS_TAC [v1_size_mem]
End

Definition ipsec_crypt_decrypt_aes_ctr_def:
 (ipsec_crypt_decrypt_aes_ctr random_oracle ((counter, ext_obj_map, v_map, ctrl, oracle_index):v1model_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "ipv4")) of
  | SOME ipv4_header =>
   (case lookup_lval scope_list (lval_varname (varn_name "esp")) of
    | SOME esp_header =>
     (case lookup_lval scope_list (lval_varname (varn_name "standard_metadata")) of
      | SOME standard_metadata =>
       let (v1, oracle_index') = init_out_v random_oracle oracle_index ipv4_header in
       (case assign scope_list (set_validity T v1) (lval_varname (varn_name "ipv4")) of
        | SOME scope_list' =>
         let (v2, oracle_index'') = init_out_v random_oracle oracle_index esp_header in
         (case assign scope_list' (set_validity T v2) (lval_varname (varn_name "esp")) of
          | SOME scope_list'' =>
         let (v3, oracle_index''') = init_out_v random_oracle oracle_index standard_metadata in
           (case assign scope_list'' (set_validity T v3) (lval_varname (varn_name "standard_metadata")) of
            | SOME scope_list''' =>
             SOME ((counter, ext_obj_map, v_map, ctrl, oracle_index'''), scope_list''', status_returnv v_bot)
            | _ => NONE)
          | _ => NONE)
        | _ => NONE)
      | _ => NONE)
    | _ => NONE)
  | _ => NONE
 )
End

Definition ipsec_crypt_encrypt_aes_ctr_def:
 (ipsec_crypt_encrypt_aes_ctr random_oracle ((counter, ext_obj_map, v_map, ctrl, oracle_index):v1model_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "ipv4")) of
  | SOME ipv4_header =>
   (case lookup_lval scope_list (lval_varname (varn_name "esp")) of
    | SOME esp_header =>
     let (v1, oracle_index') = init_out_v random_oracle oracle_index ipv4_header in
     (case assign scope_list (set_validity T v1) (lval_varname (varn_name "ipv4")) of
      | SOME scope_list' =>
       let (v2, oracle_index'') = init_out_v random_oracle oracle_index esp_header in
       (case assign scope_list' (set_validity T v2) (lval_varname (varn_name "esp")) of
        | SOME scope_list'' =>
         SOME ((counter, ext_obj_map, v_map, ctrl, oracle_index), scope_list'', status_returnv v_bot)
        | _ => NONE)
      | _ => NONE)
    | _ => NONE)
  | _ => NONE
 )
End

Definition ipsec_crypt_encrypt_null_def:
 (ipsec_crypt_encrypt_null random_oracle ((counter, ext_obj_map, v_map, ctrl, oracle_index):v1model_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "ipv4")) of
  | SOME ipv4_header =>
   (case lookup_lval scope_list (lval_varname (varn_name "esp")) of
    | SOME esp_header =>
     let (v1, oracle_index') = init_out_v random_oracle oracle_index ipv4_header in
     (case assign scope_list (set_validity T v1) (lval_varname (varn_name "ipv4")) of
      | SOME scope_list' =>
       let (v2, oracle_index'') = init_out_v random_oracle oracle_index esp_header in
       (case assign scope_list' (set_validity T v2) (lval_varname (varn_name "esp")) of
        | SOME scope_list'' =>
         SOME ((counter, ext_obj_map, v_map, ctrl, oracle_index''), scope_list'', status_returnv v_bot)
        | _ => NONE)
      | _ => NONE)
    | _ => NONE)
  | _ => NONE
 )
End

Definition ipsec_crypt_decrypt_null_def:
 (ipsec_crypt_decrypt_null random_oracle ((counter, ext_obj_map, v_map, ctrl, oracle_index):v1model_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "ipv4")) of
  | SOME ipv4_header =>
   (case lookup_lval scope_list (lval_varname (varn_name "esp")) of
    | SOME esp_header =>
     (case lookup_lval scope_list (lval_varname (varn_name "standard_metadata")) of
      | SOME standard_metadata =>
       let (v1, oracle_index') = init_out_v random_oracle oracle_index ipv4_header in
       (case assign scope_list (set_validity T v1) (lval_varname (varn_name "ipv4")) of
        | SOME scope_list' =>
         let (v2, oracle_index'') = init_out_v random_oracle oracle_index esp_header in
         (case assign scope_list' (set_validity T v2) (lval_varname (varn_name "esp")) of
          | SOME scope_list'' =>
           let (v3, oracle_index''') = init_out_v random_oracle oracle_index standard_metadata in
           (case assign scope_list'' (set_validity T v3) (lval_varname (varn_name "standard_metadata")) of
            | SOME scope_list''' =>
             SOME ((counter, ext_obj_map, v_map, ctrl, oracle_index'''), scope_list''', status_returnv v_bot)
            | _ => NONE)
          | _ => NONE)
        | _ => NONE)
      | _ => NONE)
    | _ => NONE)
  | _ => NONE
 )
End

(**********************************************************)
(*                     MODEL-SPECIFIC                     *)
(**********************************************************)

(* TODO: The reset values of standard metadata *)
val v1model_standard_metadata_zeroed =
 listSyntax.mk_list
  (map pairSyntax.mk_pair
   [(``"ingress_port"``, mk_v_bitii (0, 9)),
    (``"egress_spec"``, mk_v_bitii (0, 9)),
    (``"egress_port"``, mk_v_bitii (0, 9)),
    (``"instance_type"``, mk_v_bitii (0, 32)),
    (``"packet_length"``, mk_v_bitii (0, 32)),
    (``"enq_timestamp"``, mk_v_bitii (0, 32)),
    (``"enq_qdepth"``, mk_v_bitii (0, 19)),
    (``"deq_timedelta"``, mk_v_bitii (0, 32)),
    (``"deq_qdepth"``, mk_v_bitii (0, 19)),
    (``"ingress_global_timestamp"``, mk_v_bitii (0, 48)),
    (``"egress_global_timestamp"``, mk_v_bitii (0, 48)),
    (``"mcast_grp"``, mk_v_bitii (0, 16)),
    (``"egress_rid"``, mk_v_bitii (0, 16)),
    (``"checksum_error"``, mk_v_bitii (0, 1)),
    (``"parser_error"``, mk_v_bitii (0, 32)),
    (``"priority"``, mk_v_bitii (0, 3))],
   “:(string # v)”);

(*
val v1model_standard_metadata_uninit =
 mk_v_struct_list [(``"ingress_port"``, mk_v_biti_arb 9),
                   (``"egress_spec"``, mk_v_biti_arb 9),
                   (``"egress_port"``, mk_v_biti_arb 9),
                   (``"instance_type"``, mk_v_biti_arb 32),
                   (``"packet_length"``, mk_v_biti_arb 32),
                   (``"enq_timestamp"``, mk_v_biti_arb 32),
                   (``"enq_qdepth"``, mk_v_biti_arb 19),
                   (``"deq_timedelta"``, mk_v_biti_arb 32),
                   (``"deq_qdepth"``, mk_v_biti_arb 19),
                   (``"ingress_global_timestamp"``, mk_v_biti_arb 48),
                   (``"egress_global_timestamp"``, mk_v_biti_arb 48),
                   (``"mcast_grp"``, mk_v_biti_arb 16),
                   (``"egress_rid"``, mk_v_biti_arb 16),
                   (``"checksum_error"``, mk_v_biti_arb 1),
                   (``"parser_error"``, mk_v_biti_arb 32),
                   (``"priority"``, mk_v_biti_arb 3)];
*)
(*
val v1model_meta_uninit =
 mk_v_struct_list [];

val v1model_row_uninit =
 mk_v_struct_list [(``"e"``, mk_v_biti_arb 8),
                   (``"t"``, mk_v_biti_arb 16),
                   (``"l"``, mk_v_biti_arb 8),
                   (``"r"``, mk_v_biti_arb 8),
                   (``"v"``, mk_v_biti_arb 8)];

val v1model_hdr_uninit =
 mk_v_header_list F [(``"row"``, v1model_row_uninit)];

val v1model_header_uninit =
 mk_v_struct_list [(``"h"``, v1model_hdr_uninit)];
*)

(* TODO: This should also arbitrate between different ports, taking a list of lists of input *)
Definition v1model_input_f_def:
 (v1model_input_f n (tau1_uninit_v,tau2_uninit_v) (io_list:in_out_list, ascope:v1model_ascope) =
  case io_list of
  | [] => NONE
  | ((bl,p)::t) =>
   let (counter, ext_obj_map, v_map, ctrl, oracle_index) = reset_ext_obj_map_gen n ascope in
   let ext_obj_map' = AUPDATE_LIST ext_obj_map [(counter, INL (core_v_ext_packet bl));
                                                (counter+1, INL (core_v_ext_packet []))] in
   let counter' = counter + 2 in
   (* TODO: Currently, no garbage collection in v_map is done *)
   let v_map' = AUPDATE_LIST v_map [("b", v_ext_ref counter);
                                    ("b_temp", v_ext_ref (counter+1));
                                    ("standard_metadata", v_struct (AUPDATE_LIST (^v1model_standard_metadata_zeroed) [("ingress_port", v_bit (w9 (n2w p))); ("packet_length", v_bit (fixwidth 32 (n2v (LENGTH bl DIV 8)), 32))]));
                                    ("parsedHdr", tau1_uninit_v);
                                    ("hdr", tau1_uninit_v);
                                    ("meta", tau2_uninit_v)] in
    SOME (t, (counter', ext_obj_map', v_map', ctrl, oracle_index):v1model_ascope))
End

(* TODO: Generalise and move to core? Duplicated in all three architectures... *)
Definition v1model_reduce_nonout_def:
 (v1model_reduce_nonout ([], elist, v_map) =
  SOME []
 ) /\
 (v1model_reduce_nonout (d::dlist, e::elist, v_map) =
  if is_d_out d
  then oCONS (e, v1model_reduce_nonout (dlist, elist, v_map))
  else
   (case e of
    | (e_var (varn_name x)) =>
     (case ALOOKUP v_map x of
      | SOME v =>
       (* NOTE: Only externs can be passed as directionless arguments here *)
       oCONS (e_v v, v1model_reduce_nonout (dlist, elist, v_map))
      | _ => NONE)
    | _ => NONE)) /\
 (v1model_reduce_nonout (_, _, v_map) = NONE)
End

(* TODO: Since the same thing should be initialised
 *       for all known architectures, maybe it should be made a
 *       architecture-generic (core) function? *)
(* TODO: Don't reduce all arguments at once? *)
Definition v1model_copyin_pbl_def:
 v1model_copyin_pbl (xlist, dlist, elist, (counter, ext_obj_map, v_map, ctrl, oracle_index):v1model_ascope, random_oracle) =
  case v1model_reduce_nonout (dlist, elist, v_map) of
  | SOME elist' =>
   copyin xlist dlist elist' [v_map_to_scope v_map] [ [] ] oracle_index random_oracle
  | NONE => NONE
End

(* Note that this re-uses the copyout function intended for P4 functions *)
Definition v1model_copyout_pbl_def:
 v1model_copyout_pbl (g_scope_list, (counter, ext_obj_map, v_map, ctrl, oracle_index):v1model_ascope, dlist, xlist, (status:status)) =
  case copyout_pbl_gen xlist dlist g_scope_list v_map of
  | SOME [v_map_scope] =>
   (case scope_to_vmap v_map_scope of
    | SOME v_map' => SOME ((counter, ext_obj_map, v_map', ctrl, oracle_index):v1model_ascope)
    | NONE => NONE)
  | _ => NONE
End

(* TODO: Make generic *)
Definition v1model_lookup_obj_def:
 v1model_lookup_obj ext_obj_map v_map k =
  case ALOOKUP v_map k of
  | SOME (v_ext_ref i) =>
   ALOOKUP ext_obj_map i
  | _ => NONE
End

(* Transfers the value of parsedHdr to hdr and the parserError value to standard_metadata,
 * then resets the shared packet "b" (TODO: Fix that hack) and saves its content in "b_temp" *)
(* TODO: Note that this also resets parseError to 0 *)
Definition v1model_postparser_def:
 v1model_postparser ((i, io_list, io_list', (counter, ext_obj_map, v_map, ctrl, oracle_index)):v1model_ascope aenv) =
  (case ALOOKUP v_map "b" of
   | SOME (v_ext_ref j) =>
    (case ALOOKUP ext_obj_map j of
     | SOME (INL (core_v_ext_packet bl)) =>
      (case ALOOKUP v_map "b_temp" of
       | SOME (v_ext_ref j') =>
        (case ALOOKUP v_map "parsedHdr" of
         | SOME v =>
          let v_map' = AUPDATE v_map ("hdr", v) in
           (case ALOOKUP v_map "parseError" of
            | SOME v' =>
             (case assign [v_map_to_scope v_map'] v' (lval_field (lval_varname (varn_name "standard_metadata")) "parser_error") of
              | SOME [v_map_scope] =>
               (case scope_to_vmap v_map_scope of
                | SOME v_map'' =>
                 let v_map''' = AUPDATE v_map'' ("parseError", v_bit (fixwidth 32 (n2v 0), 32)) in
                 let (counter', ext_obj_map', v_map'''', ctrl', oracle_index') = (v1model_ascope_update (counter, ext_obj_map, v_map''', ctrl, oracle_index) j' (INL (core_v_ext_packet bl))) in
   SOME (i+1, io_list, io_list', (v1model_ascope_update (counter', ext_obj_map', v_map'''', ctrl', oracle_index') j (INL (core_v_ext_packet []))))
                | NONE => NONE)
              | _ => NONE)
            | NONE => NONE)
         | _ => NONE)
       | _ => NONE)
     | _ => NONE)
   | _ => NONE)
End

(* Note that this split-up of functions is so that the symbolic execution
 * can handle symbolic branch on output port.
 * TODO: Use the v directly (and not the port_bl) in order to
 * make sense to also use as a control plane assumption, specifically on
 * the argument of an action. *)
Definition v1model_is_drop_port_def:
 v1model_is_drop_port port_bl =
  if v2n port_bl = 511
  then T
  else F
End

(* TODO: Outsource obtaining the output port to an external function? *)
(* NOTE: "b" renamed to "b_out" *)
(* A little clumsy with the double v2n, but that makes things easier *)
Definition v1model_output_f_def:
 v1model_output_f (in_out_list:in_out_list, (counter, ext_obj_map, v_map, ctrl, oracle_index):v1model_ascope) =
  (case v1model_lookup_obj ext_obj_map v_map "b" of
   | SOME (INL (core_v_ext_packet bl)) =>
    (case v1model_lookup_obj ext_obj_map v_map "b_temp" of
     | SOME (INL (core_v_ext_packet bl')) =>
      (case ALOOKUP v_map "standard_metadata" of
       | SOME (v_struct struct) =>
        (case ALOOKUP struct "egress_spec" of
         | SOME (v_bit (port_bl, n)) =>
          SOME (in_out_list++(if v1model_is_drop_port port_bl then [] else [(bl++bl', v2n port_bl)]), (counter, ext_obj_map, v_map, ctrl, oracle_index))
         | _ => NONE)
       | _ => NONE)
     | _ => NONE)
   | _ => NONE)
End

(* This assumes that tables contains at most one LPM key,
 * with other keys being exact if one LPM key is present.
 * Note that table priority is runtime-dependent, with only partial P4 language
 * support. *)
val v1model_apply_table_f_def =
 if CONTROL_PLANE_API = 0
 then xDefine "v1model_apply_table_f"
  ‘v1model_apply_table_f (x, e_l, mk_list:mk_list, (x', e_l'), (counter, ext_obj_map, v_map, ctrl, oracle_index):v1model_ascope) =
    (* TODO: Note that this function could do other stuff here depending on table name.
     *       Ideally, one could make a general, not hard-coded, solution for this *)
    case ALOOKUP ctrl x of
     | SOME table =>
      if (MEM mk_lpm mk_list)
      then
       (* Largest priority wins (like for P4Runtime API - should be equivalent to TDI
        * for tables that contain at most one LPM key, with others exact) *)
       SOME (FST $ FOLDL_MATCH e_l ((x', e_l'), NONE) table)
      else
       (* Smallest priority wins (like for TDI) *)
       SOME (FST $ FOLDL_MATCH_alt e_l ((x', e_l'), NONE) (1:num) table)
     | NONE => NONE’
 else xDefine "v1model_apply_table_f"
  ‘v1model_apply_table_f (x, e_l, mk_list:mk_list, (x', e_l'), (counter, ext_obj_map, v_map, ctrl, oracle_index):v1model_ascope) =
    (* TODO: Note that this function could do other stuff here depending on table name.
     *       Ideally, one could make a general, not hard-coded, solution for this *)
    case ALOOKUP ctrl x of
     | SOME table =>
      (* Largest priority wins *)
      SOME (FST $ FOLDL_MATCH e_l ((x', e_l'), NONE) table)
     | NONE => NONE’;

(* TODO: Generalise the below as needed *)

Definition v1model_get_oracle_index_def:
 v1model_get_oracle_index ((counter, ext_obj_map, v_map, ctrl, oracle_index):v1model_ascope) =
  oracle_index
End

Definition v1model_set_oracle_index_def:
 v1model_set_oracle_index i_opt ((counter, ext_obj_map, v_map, ctrl, oracle_index):v1model_ascope) =
  (counter, ext_obj_map, v_map, ctrl, case i_opt of NONE => oracle_index | SOME i => i):v1model_ascope
End
