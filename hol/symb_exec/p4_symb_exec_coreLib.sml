structure p4_symb_exec_coreLib :> p4_symb_exec_coreLib = struct

open HolKernel boolLib liteLib simpLib bossLib;

open bitstringSyntax listSyntax numSyntax optionSyntax pairSyntax;

open symb_execTheory p4_coreTheory p4_symb_execTheory;

open p4Syntax auxLib symb_execSyntax p4_convLib;

(*****************************************************)
(* Approximation functions for the packet_in externs *)

(* The packet is a term of one of three shapes: a literal list (possibly with free Boolean variables
 * as bits), a variable p, or DROP n p with n a numeral (p after n consumed bits). The three
 * methods take their bits from the packet with packet_in_take, whose result on a symbolic
 * packet is expressed with EL terms over p (see packet_slice in p4_symb_execTheory), so no
 * fresh variables are introduced and the methods then interpret an explicit list of bits by
 * evaluation. *)

val ERR = mk_HOL_ERR "p4_symb_exec_coreLib";

(* TODO: Move to syntax file *)
val (packet_in_take_tm, mk_packet_in_take, dest_packet_in_take, is_packet_in_take) =
 syntax_fns2 "p4_core" "packet_in_take";
val (size_in_bits_tm, mk_size_in_bits, dest_size_in_bits, is_size_in_bits) =
 syntax_fns1 "p4_core" "size_in_bits";
val (packet_slice_tm, mk_packet_slice, dest_packet_slice, is_packet_slice) =
 syntax_fns3 "p4_symb_exec" "packet_slice";

val packet_in_inner_consts = [packet_in_take_tm];

fun add_packet_in_stop_consts stop_consts =
 stop_consts@(filter (fn c => not (exists (same_const c) stop_consts)) packet_in_inner_consts)
;

fun lookup_var varname scope_list =
 let
  val lookup_res = rhs $ concl $ HOL4P4_CONV (mk_lookup_lval (scope_list, (mk_lval_varname varname)))
 in
  if is_some lookup_res
  then dest_some lookup_res
  else raise (ERR "lookup_var" ("Could not find variable in local scope: "^varname))
 end
;

(* TODO: Hack *)
fun ascope_ext_obj_map ascope =
 el 2 $ strip_pair ascope
;

fun lookup_packet scope_list ascope =
 let
  val ext_ref = dest_v_ext_ref $ lookup_var "this" scope_list
  val obj = rhs $ concl $ HOL4P4_CONV (mk_alookup (ascope_ext_obj_map ascope, ext_ref))
  val (packet_constr, pkt) = dest_comb $ fst $ sumSyntax.dest_inl $ dest_some obj
 in
  if fst (dest_const packet_constr) = "core_v_ext_packet"
  then pkt
  else raise (ERR "lookup_packet" "this does not refer to a packet")
 end
 handle HOL_ERR _ => raise (ERR "lookup_packet" "Could not find the packet that this refers to")
;

datatype packet_shape =
   literal
 | suffix of term * int;

fun packet_shape pkt =
 if is_list pkt
 then literal
 else if is_var pkt
 then suffix (pkt, 0)
 else if is_drop pkt
 then
  let
   val (n, p) = dest_drop pkt
  in
   if is_numeral n andalso is_var p
   then suffix (p, int_of_term n)
   else raise (ERR "packet_shape" ("Unsupported packet term: "^(term_to_string pkt)))
  end
 else raise (ERR "packet_shape" ("Unsupported packet term: "^(term_to_string pkt)))
;

fun is_num_comparison tm =
 let
  val tm' = if is_neg tm then dest_neg tm else tm
 in
  (is_eq tm' andalso type_of (lhs tm') = num) orelse
  is_leq tm' orelse is_less tm' orelse is_geq tm' orelse is_greater tm'
 end
 handle HOL_ERR _ => false
;

fun path_cond_num_facts path_cond_tm =
 filter is_num_comparison (strip_conj path_cond_tm)
;

fun prove_num_fact facts tm =
 let
  val thm = SIMP_CONV (bool_ss ++ numSimps.ARITH_ss) (map ASSUME facts) tm
 in
  if Teq $ rhs $ concl thm
  then SOME (EQT_ELIM thm)
  else NONE
 end
 handle UNCHANGED => NONE
      | HOL_ERR _ => NONE
;

fun prove_num_fact_or_fail facts tm =
 case prove_num_fact facts tm of
   SOME thm => thm
 | NONE => raise (ERR "prove_num_fact" ("Could not prove "^((term_to_string tm)^" from the path condition")))
;

(* Turns (h1, ..., hn |- tm) into |- (h1 /\ ... /\ hn) ==> tm *)
fun disch_hyps_conj thm =
 case hyp thm of
   [] => thm
 | hyps =>
  let
   val conj_tm = list_mk_conj hyps
   val thm' = foldl (fn (h, th) => PROVE_HYP h th) thm (CONJUNCTS (ASSUME conj_tm))
  in
   DISCH conj_tm thm'
  end
;

fun mk_disj_list_thm disjs thm =
 let
  val disj_tm = mk_disj_list disjs
 in
  EQ_MP (SYM (PURE_REWRITE_CONV [disj_list_def, boolTheory.OR_CLAUSES] disj_tm)) thm
 end
;

(* Builds the branch theorem from
 *  conjs: the numerical conjuncts of the path condition,
 *  cond: the statement that enough bits remain, and ncond: its negation,
 *  some_thm: |- ante_some ==> tm1 = rhs, and none_thm: |- ante_none ==> tm1 = NONE,
 * as a theorem with hypotheses among the conjs:
 *  disj_list [tm1 = rhs] when ante_some follows from the conjs,
 *  disj_list [tm1 = NONE] when ante_none follows,
 *  disj_list [cond /\ tm1 = rhs; ncond /\ tm1 = NONE] otherwise. *)
fun packet_in_branch_thm fv_index conjs (cond, ncond) some_thm none_thm =
 let
  val (some_ante, some_eq) = dest_imp $ concl some_thm
  val (none_ante, none_eq) = dest_imp $ concl none_thm
 in
  case prove_num_fact conjs some_ante of
    SOME ante_thm => (mk_disj_list_thm [some_eq] (MP some_thm ante_thm), [fv_index])
  | NONE =>
   (case prove_num_fact conjs none_ante of
      SOME ante_thm => (mk_disj_list_thm [none_eq] (MP none_thm ante_thm), [fv_index])
    | NONE =>
     let
      val d1_tm = mk_conj (cond, some_eq)
      val d2_tm = mk_conj (ncond, none_eq)
      (* Case 1: enough bits remain *)
      val cond_thm = ASSUME cond
      val some_ante_thm = prove_num_fact_or_fail (cond::conjs) some_ante
      val d1 = DISJ1 (CONJ cond_thm (MP some_thm some_ante_thm)) d2_tm
      (* Case 2: the packet is too short *)
      val ncond_thm = prove_num_fact_or_fail [mk_neg cond] ncond
      val none_ante_thm = prove_num_fact_or_fail (ncond::conjs) none_ante
      val d2 = DISJ2 d1_tm (CONJ ncond_thm (PROVE_HYP ncond_thm (MP none_thm none_ante_thm)))
      val cases_thm = DISJ_CASES (SPEC cond EXCLUDED_MIDDLE) d1 d2
     in
      (mk_disj_list_thm [d1_tm, d2_tm] cases_thm, [fv_index, fv_index])
     end)
 end
;

fun approx_packet_in_gen fv_index path_cond_tm pkt tm1 size mk_thms =
 case packet_shape pkt of
   literal =>
  (mk_disj_list_thm [concl $ EVAL tm1] (EVAL tm1), [fv_index])
 | suffix (p, n) =>
  let
   val n_tm = term_of_int n
   val k_tm = term_of_int (n + size)
   val len_tm = mk_length p
   val cond = mk_leq (k_tm, len_tm)
   val ncond = mk_less (len_tm, k_tm)
   val facts = path_cond_num_facts path_cond_tm
   val (some_thm, none_thm) = mk_thms (n_tm, p)
   (* DROP 0 p is p, and the numerals in the offsets are added up *)
   fun norm thm = CONV_RULE numLib.REDUCE_CONV (REWRITE_RULE [listTheory.DROP_0] thm)
   val (disj_thm, fv_indices) =
    packet_in_branch_thm fv_index facts (cond, ncond) (norm some_thm) (norm none_thm)
  in
   (disch_hyps_conj disj_thm, fv_indices)
  end
;

fun get_size name v =
 let
  val size_opt = rhs $ concl $ EVAL (mk_size_in_bits v)
 in
  if is_some size_opt
  then dest_some size_opt
  else raise (ERR name ("The value has no size in bits: "^(term_to_string v)))
 end
;

fun approx_packet_in_take fv_index path_cond_tm pkt size_tm =
 let
  val tm1 = mk_packet_in_take (size_tm, pkt)
  fun mk_thms (n_tm, p) =
   let
    (* Built with syntax functions, not parsed: the grammar of the script that runs the
     * symbolic execution need not know packet_slice *)
    val slice_thm = EVAL (mk_packet_slice (n_tm, size_tm, p))
   in
    (REWRITE_RULE [slice_thm] (ISPECL [size_tm, n_tm, p] packet_in_take_slice),
     ISPECL [size_tm, n_tm, p] packet_in_take_too_short)
   end
 in
  approx_packet_in_gen fv_index path_cond_tm pkt tm1 (int_of_term size_tm) mk_thms
 end
;

fun approx_packet_in_extract fv_index path_cond_tm scope_list ascope =
 approx_packet_in_take fv_index path_cond_tm (lookup_packet scope_list ascope)
  (get_size "approx_packet_in_extract" (lookup_var "headerLvalue" scope_list))
;

fun approx_packet_in_lookahead fv_index path_cond_tm scope_list ascope =
 approx_packet_in_take fv_index path_cond_tm (lookup_packet scope_list ascope)
  (get_size "approx_packet_in_lookahead" (lookup_var "targ1" scope_list))
;

fun approx_packet_in_advance fv_index path_cond_tm scope_list ascope =
 let
  val (bits, _) = dest_pair $ dest_v_bit $ lookup_var "bits" scope_list
  val k_tm = rhs $ concl $ EVAL (mk_v2n bits)
  val _ = if is_numeral k_tm then () else raise (ERR "approx_packet_in_advance" "The number of bits to advance is not concrete")
 in
  approx_packet_in_take fv_index path_cond_tm (lookup_packet scope_list ascope) k_tm
 end
;

end
