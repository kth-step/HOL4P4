structure testLib :> testLib = struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open p4Syntax;

(******************)
(* Test functions *)

(* Simpset fragment containing a conversion keyed on bitvectors that will
 * rewrite bool lists as the v2w of the corresponding word *)
local
fun to_bitv_word_form bitv =
  let
    val (vector, width) = pairSyntax.dest_pair bitv
    val word = wordsSyntax.mk_wordi (bitstringSyntax.num_of_term vector, numSyntax.int_of_term width)
    val bitv_word = bitstringSyntax.mk_w2v word
    val bitv' = pairSyntax.mk_pair (bitv_word, width)
  in
    bitv'
  end
;

fun to_bitv_word_form_conv bitv =
  let
    val bitv_word = to_bitv_word_form bitv
    val bitv_word_thm = GSYM (EVAL bitv_word)
  in
    bitv_word_thm
  end
;
in
val p4_v2w_ss =
  SSFRAG {ac = [],
          congs = [],
          convs = [{conv = K (K to_bitv_word_form_conv),
                    key= SOME ([], ``(v:bool list, 32)``),
                    name = "BITV_TO_WORD_FORM",
                    trace = 2}],
                    dprocs = [],
          filter = NONE,
          name = SOME "p4_v2w_ss",
          rewrs = []};
end;

(* Obtains result and evaluation theorem of expression *)
fun eval_e e_tm =
  let
    val res_thm = EVAL (``e_exec ctx (^e_tm) stacks status_running``) (* TODO: Alternatively, use a tailor-made eval_e_conv *)
    val res_canon_thm = SIMP_RULE (pure_ss++p4_v2w_ss) [] res_thm
    val res_canon_tm = rhs $ concl res_canon_thm
  in
    (* Present bool lists as w2v function on words *)
    (res_canon_tm, res_canon_thm)
  end
;

fun is_v_bool_well_formed res_opt =
  let
    (* Result is syntactically a SOME *)
    val res = optionSyntax.dest_some res_opt
    (* TODO: Hack, replace with syntactic functions *)
    val res_bs = dest_v_bool $ dest_e_v $ snd $ dest_comb $ fst $ dest_comb res
  in
    ((term_eq res_bs T) orelse (term_eq res_bs F))
  end
;

fun is_v_bit_word_well_formed width res_opt =
  let
    (* Result is syntactically a SOME *)
    val res = optionSyntax.dest_some res_opt
    (* TODO: Hack, replace with syntactic functions *)
    (* TODO: Check status and stacks? *)
    val res_bs = dest_v_bit $ dest_e_v $ snd $ dest_comb $ fst $ dest_comb res
    (* Bit-string is syntactically a pair *)
    val (res_w2v, res_width) = pairSyntax.dest_pair res_bs
    (* Width of result matches expected width *)
    val width_ok = (term_eq res_width width)
 
    (* Result w2v word is syntactically a word literal *)
    val res_w = bitstringSyntax.dest_w2v res_w2v
    val literal_ok = wordsSyntax.is_word_literal res_w

    (* Result w2v word has expected size *)
    val size_ok = ((wordsSyntax.size_of res_w) = (numSyntax.dest_numeral width))
  in
    (width_ok andalso literal_ok andalso size_ok)
  end
;

(* This tests all test cases in a provided list using antecedent-evaluation function f
 * and well-formedness function wf *)
fun test_red _ _ [] = ()
  | test_red (f_name, f) (wf_name, wf) ((e_tm, exp_res)::t) =
  let
    val _ = print ((term_to_string e_tm)^ ":\n");
    val _ = print "===============================\n";
    val res = f e_tm
    val _ = (Hol_pp.print_thm (snd res); print "\n");
    val _ = if wf (fst res) then () else
            raise Fail ("test_red::the result is not well-formed according to "^(wf_name))
    val res_e = fst $ pairSyntax.dest_pair $ optionSyntax.dest_some $ fst res
    val _ = if isSome exp_res
            then
              if optionSyntax.is_some res_e
              then
                if identical (optionSyntax.mk_some res_e) (valOf exp_res) then () else
                raise Fail "test_red::reduction does not have expected result"
              else
                if identical res_e (valOf exp_res) then () else
                raise Fail "test_red::reduction does not have expected result"
            else ()
    val _ = print "\n\n";
  in
    (test_red (f_name, f) (wf_name, wf) t)
  end;

end
