open HolKernel boolLib Parse bossLib;

val _ = new_theory "cake_vss_v1model";

open p4Syntax;
open bitstringSyntax numSyntax pairSyntax;
open p4Theory p4_auxTheory p4_cake_exec_semTheory;
open p4_coreTheory;
open p4_v1modelTheory;

(* CakeML: *)
open preamble ml_translatorLib ml_progLib;

intLib.deprecate_int();
val _ = (max_print_depth := 1000);

open p4_cake_exec_semProgTheory;
open p4_cake_transformLib p4_cake_auxLib;
open p4_cake_arch_v1modelProgTheory;

(*
open realLib;

realLib.prefer_real;

map (fn (a,b) => (a, (Real.fromInt b) / 3.0))

       [
        (1, 5696),
        (2, 4736),
        (3, 4928),
        (4, 5056),
        (5, 4288),
        (6, 4608),
        (7, 4480)
        ]

*)

(*********************)

fun get_keys [] = []
  | get_keys (h::t) =
 let
  val matching = fst $ dest_pair h
  val (s_list_tm, prio) = dest_pair matching
  val s_list = fst $ dest_list $ s_list_tm
 in
  if length s_list = 1
  then
   let
    val s = el 1 s_list
   in
    if is_s_sing s
    then
     let
      val (bool_list_tm, width_tm) = dest_pair $ dest_v_bit $ dest_s_sing s
      val value = int_of_term $ rhs $ concl $ EVAL “v2n ^bool_list_tm”
      val width = int_of_term width_tm
     in
      ((value, width), int_of_term prio)::(get_keys t)
     end
    else raise Fail "get_keys only supports s_sing"
   end
  else raise Fail "get_keys only supports single matching keys (got multiple entries)"
 end
;

(* Populate a table with singleton keys, outside of existing entries.
 * Used for creating dummy entries for benchmarking table matching *)
(* TODO: How to best handle priority? Best make new entries the prioritized ones... *)
fun populate_table' tbl rand_gen n_additional_entries =
 let
  val (name, entries) = dest_pair tbl
  val entries_list_tm = p4_coreLib.dest_tbl_regular entries
  val entries_list = fst $ dest_list $ entries_list_tm
  val (keys, prios) = unzip $ get_keys entries_list
  (* TODO: Hack. Warn if widths disagree. *)
  val width = el 1 $ map snd keys

  val max_prio = fst $ mlibUseful.max (fn (a,b) => Int.compare (a, b)) prios

  fun get_rand_range width rand_gen existing_keys =
   let
    val range_value1 = Random.range (0, (funpow width (fn a => a*2) 1)) rand_gen;
    val range_value2 = Random.range (0, (funpow width (fn a => a*2) 1)) rand_gen;
    val (lo, hi) =
     if range_value1 < range_value2
     then (range_value1, range_value2)
     else (range_value2, range_value1)
    val lo' = rhs $ concl $ EVAL $ “(fixwidth ^(numSyntax.term_of_int width) $ n2v ^(numSyntax.term_of_int lo), ^(numSyntax.term_of_int width))”
    val hi' = rhs $ concl $ EVAL $ “(fixwidth ^(numSyntax.term_of_int width) $ n2v ^(numSyntax.term_of_int hi), ^(numSyntax.term_of_int width))”
   in
    if not $ exists (fn a => a >= lo) existing_keys
    then
     mk_s_range (lo', hi')
    else get_rand_range width rand_gen existing_keys
   end
  ;

  (* TODO: Chance for doubles now very low *)
  fun add_entries existing_keys width rand_gen 0 = []
    | add_entries existing_keys width rand_gen n_additional_entries =
   let
    val new_entry = get_rand_range width rand_gen existing_keys
   in
    new_entry::(add_entries existing_keys width rand_gen (n_additional_entries-1))
   end
  ;

  (* TODO: Take action as an argument *)
  val action =
   “("NoAction",
      [e_v (v_bool T); e_v (v_bool T)])”
  val new_entries = add_entries (map fst keys) width rand_gen n_additional_entries
  val new_entries' = map (fn a => mk_pair (mk_list ([a], “:s”), term_of_int (max_prio+1))) new_entries
  val new_entries_tm = mk_list (map (fn a => mk_pair (a, action)) new_entries', “:(s list # num) # string # e list”)

  val entries_list_tm' = rhs $ concl $ EVAL “^new_entries_tm ++ ^entries_list_tm”
  
 in
  mk_pair (name, p4_coreLib.mk_tbl_regular entries_list_tm')
 end
;

(*********************)

val _ = translation_extends "p4_cake_arch_v1modelProg";

val ipv4_match_tbl =
 “("ipv4_match",
   tbl_regular
   [((
           [s_mask (* 00001010.00000000.00000000.00000010 *)
              ([F; F; F; F; T; F; T; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; T; F],32)
              ([T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T;
                T; T; T; T; T; T; T; T],32)],4),
     "Set_nhop",
     [e_v (v_bool T); e_v (v_bool T);
      (* 00001010.00000000.00000000.00000010 *)
      e_v (v_bit ([F; F; F; F; T; F; T; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                   F; F; F; F; F; F; T; F],32));
      (* port *)
      e_v (v_bit ([F; F; F; F; F; F; F; T; F],9))]);
    ((
           [s_mask (* 00001010.00000000.00000000.00000001 *)
              ([F; F; F; F; T; F; T; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; T],32)
              ([T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T;
                T; T; T; T; T; T; T; T],32)],4),
     "Set_nhop",
     [e_v (v_bool T); e_v (v_bool T);
      (* 00001010.00000000.00000000.00000001 *)
      e_v (v_bit ([F; F; F; F; T; F; T; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                   F; F; F; F; F; F; F; T],32));
      (* port *)
      e_v (v_bit ([F; F; F; F; F; F; F; F; T],9))]);
   ]):(string # tbl)”;

val dmac_tbl =
  “("dmac",
   tbl_regular
    [((
             (* 00001010.00000000.00000000.00000010 *)
            [s_sing $ v_bit ([F; F; F; F; T; F; T; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                              F; F; F; F; F; F; T; F],32)],4),
      "Set_dmac",
      (* 00000010:00010001:00100010:00110011:01000100:00000010 *)
      [e_v (v_bool T); e_v (v_bool T);
       e_v (v_bit ([F; F; F; F; F; F; T; F; F; F; F; T; F; F; F; T; F; F; T; F; F; F; T; F;
                    F; F; T; T; F; F; T; T; F; T; F; F; F; T; F; F; F; F; F; F; F; F; T; F],48))]);
     ((
             (* 00001010.00000000.00000000.00000001 *)
            [s_sing $ v_bit ([F; F; F; F; T; F; T; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                              F; F; F; F; F; F; F; T],32)],4),
      "Set_dmac",
      (* 00000010:00010001:00100010:00110011:01000100:00000001 *)
      [e_v (v_bool T); e_v (v_bool T);
       e_v (v_bit ([F; F; F; F; F; F; T; F; F; F; F; T; F; F; F; T; F; F; T; F; F; F; T; F;
                    F; F; T; T; F; F; T; T; F; T; F; F; F; T; F; F; F; F; F; F; F; F; F; T],48))])
    ]):(string # tbl)”;

val smac_tbl =
  “("smac",
   tbl_regular
    [((
            [s_sing $ v_bit ([F; F; F; F; F; F; F; T; F],9)],4),
      "Set_smac",
      (* 00000010:00010001:00100010:00110011:01000100:00000100 *)
      [e_v (v_bool T); e_v (v_bool T);
       e_v (v_bit ([F; F; F; F; F; F; T; F; F; F; F; T; F; F; F; T; F; F; T; F; F; F; T; F;
                               F; F; T; T; F; F; T; T; F; T; F; F; F; T; F; F; F; F; F; F; F; T; F; F],48))]);
     ((
            [s_sing $ v_bit ([F; F; F; F; F; F; F; F; T],9)],4),
      "Set_smac",
      (* 00000010:00010001:00100010:00110011:01000100:00000011 *)
      [e_v (v_bool T); e_v (v_bool T);
       e_v (v_bit ([F; F; F; F; F; F; T; F; F; F; F; T; F; F; F; T; F; F; T; F; F; F; T; F;
     F; F; T; T; F; F; T; T; F; T; F; F; F; T; F; F; F; F; F; F; F; F; T; T],48))])
    ]):(string # tbl)”;

val rand_gen = Random.newgen ();

val n_additional_entries = 1000;

val dmac_tbl' = populate_table' dmac_tbl rand_gen n_additional_entries;

val vss_v1model_actx = “([arch_block_inp;
  arch_block_pbl "TopParser"
    [e_var (varn_name "b"); e_var (varn_name "parsedHdr");
     e_var (varn_name "meta"); e_var (varn_name "standard_metadata")];
  arch_block_ffbl "postparser";
  arch_block_pbl "TopVerifyChecksum"
    [e_var (varn_name "hdr"); e_var (varn_name "meta")];
  arch_block_ffbl "preingress";
  arch_block_pbl "TopIngress"
    [e_var (varn_name "hdr"); e_var (varn_name "meta");
     e_var (varn_name "standard_metadata")];
  arch_block_pbl "TopPipe"
    [e_var (varn_name "hdr"); e_var (varn_name "meta");
     e_var (varn_name "standard_metadata")];
  arch_block_pbl "TopComputeChecksum"
    [e_var (varn_name "hdr"); e_var (varn_name "meta")];
  arch_block_pbl "TopDeparser"
    [e_var (varn_name "b"); e_var (varn_name "hdr")]; arch_block_out],
 [("TopParser",pbl_type_parser,
   [("b",d_none); ("p",d_out); ("meta",d_inout);
    ("standard_metadata",d_inout)],
   [("TopParser",stmt_seq stmt_empty (stmt_trans (e_v (v_str "start"))),[])],
   [],
   [("start",
     stmt_seq
       (stmt_ass lval_null
          (e_call (funn_ext "packet_in" "extract")
             [e_var (varn_name "b");
              e_acc (e_var (varn_name "p")) "ethernet"]))
       (stmt_trans
          (e_select
             (e_struct
                [("",
                  e_acc (e_acc (e_var (varn_name "p")) "ethernet")
                    "etherType")])
             [([s_sing
                  (v_bit
                     ([F; F; F; F; T; F; F; F; F; F; F; F; F; F; F; F],16))],
               "parse_ipv4")] "set_no_match")));
    ("parse_ipv4",
     stmt_seq
       (stmt_seq
          (stmt_ass lval_null
             (e_call (funn_ext "packet_in" "extract")
                [e_var (varn_name "b"); e_acc (e_var (varn_name "p")) "ip"]))
          (stmt_seq
             (stmt_ass lval_null
                (e_call (funn_ext "" "verify")
                   [e_binop
                      (e_acc (e_acc (e_var (varn_name "p")) "ip") "version")
                      binop_eq (e_v (v_bit ([F; T; F; F],4)));
                    e_v
                      (v_bit
                         ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                           F; F; F; F; F; F; F; F; F; F; F; T; F; F; F],32))]))
             (stmt_ass lval_null
                (e_call (funn_ext "" "verify")
                   [e_binop
                      (e_acc (e_acc (e_var (varn_name "p")) "ip") "ihl")
                      binop_eq (e_v (v_bit ([F; T; F; T],4)));
                    e_v
                      (v_bit
                         ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                           F; F; F; F; F; F; F; F; F; F; F; F; T; T; T],32))]))))
       (stmt_trans (e_v (v_str "accept"))));
    ("set_no_match",
     stmt_ass lval_null
       (e_call (funn_ext "" "verify")
          [e_v (v_bool F);
           e_v
             (v_bit
                ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                  F; F; F; F; F; F; F; F; F; F; T; F],32))]))],[]);
  ("TopVerifyChecksum",pbl_type_control,
   [("headers",d_inout); ("meta",d_inout)],
   [("TopVerifyChecksum",
     stmt_seq stmt_empty
       (stmt_ass lval_null
          (e_call (funn_ext "" "verify_checksum")
             [e_v (v_bool T);
              e_struct
                [("1",
                  e_acc (e_acc (e_var (varn_name "headers")) "ip") "version");
                 ("2",e_acc (e_acc (e_var (varn_name "headers")) "ip") "ihl");
                 ("3",
                  e_acc (e_acc (e_var (varn_name "headers")) "ip") "diffserv");
                 ("4",
                  e_acc (e_acc (e_var (varn_name "headers")) "ip") "totalLen");
                 ("5",
                  e_acc (e_acc (e_var (varn_name "headers")) "ip")
                    "identification");
                 ("6",
                  e_acc (e_acc (e_var (varn_name "headers")) "ip") "flags");
                 ("7",
                  e_acc (e_acc (e_var (varn_name "headers")) "ip")
                    "fragOffset");
                 ("8",e_acc (e_acc (e_var (varn_name "headers")) "ip") "ttl");
                 ("9",
                  e_acc (e_acc (e_var (varn_name "headers")) "ip") "protocol");
                 ("10",
                  e_acc (e_acc (e_var (varn_name "headers")) "ip") "srcAddr");
                 ("11",
                  e_acc (e_acc (e_var (varn_name "headers")) "ip") "dstAddr")];
              e_acc (e_acc (e_var (varn_name "headers")) "ip") "hdrChecksum";
              e_v
                (v_bit
                   ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                     F; F; F; F; F; F; F; F; F; F; T; T; F],32))])),[])],[],
   [],[]);
  ("TopIngress",pbl_type_control,
   [("headers",d_inout); ("meta",d_inout); ("standard_metadata",d_inout)],
   [("TopIngress",stmt_seq stmt_empty stmt_empty,[])],[],[],[]);
  ("TopPipe",pbl_type_control,
   [("headers",d_inout); ("meta",d_inout); ("standard_metadata",d_inout)],
   [("TopPipe",
     stmt_seq stmt_empty
       (stmt_seq
          (stmt_cond
             (e_binop
                (e_acc (e_var (varn_name "standard_metadata")) "parser_error")
                binop_neq
                (e_v
                   (v_bit
                      ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                        F; F; F; F; F; F; F; F; F; F; F; F; F; F],32))))
             (stmt_block []
                (stmt_seq
                   (stmt_ass lval_null
                      (e_call (funn_name "Drop_action")
                         [e_v (v_bool F); e_v (v_bool F)]))
                   (stmt_ret (e_v v_bot)))) stmt_empty)
          (stmt_seq
             (stmt_app "ipv4_match"
                [e_acc (e_acc (e_var (varn_name "headers")) "ip") "dstAddr"])
             (stmt_seq
                (stmt_cond
                   (e_binop
                      (e_acc (e_var (varn_name "standard_metadata"))
                         "egress_spec") binop_eq
                      (e_v (v_bit ([T; T; T; T; T; T; T; T; T],9))))
                   (stmt_ret (e_v v_bot)) stmt_empty)
                (stmt_seq
                   (stmt_app "check_ttl"
                      [e_acc (e_acc (e_var (varn_name "headers")) "ip") "ttl"])
                   (stmt_seq
                      (stmt_cond
                         (e_binop
                            (e_acc (e_var (varn_name "standard_metadata"))
                               "egress_spec") binop_eq
                            (e_v (v_bit ([T; T; T; T; T; T; T; T; F],9))))
                         (stmt_ret (e_v v_bot)) stmt_empty)
                      (stmt_seq
                         (stmt_app "dmac" [e_var (varn_name "nextHop")])
                         (stmt_seq
                            (stmt_cond
                               (e_binop
                                  (e_acc
                                     (e_var (varn_name "standard_metadata"))
                                     "egress_spec") binop_eq
                                  (e_v
                                     (v_bit ([T; T; T; T; T; T; T; T; T],9))))
                               (stmt_ret (e_v v_bot)) stmt_empty)
                            (stmt_app "smac"
                               [e_acc (e_var (varn_name "standard_metadata"))
                                  "egress_spec"])))))))),[]);
    ("Set_smac",
     stmt_seq
       (stmt_cond (e_var (varn_name "from_table"))
          (stmt_ass (lval_varname (varn_name "gen_apply_result"))
             (e_struct
                [("hit",e_var (varn_name "hit"));
                 ("miss",e_unop unop_neg (e_var (varn_name "hit")));
                 ("action_run",
                  e_v
                    (v_bit
                       ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                         F; F; F; F; F; F; F; F; F; F; F; F; T; F; T],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_ass
             (lval_field
                (lval_field (lval_varname (varn_name "headers")) "ethernet")
                "srcAddr") (e_var (varn_name "smac"))) (stmt_ret (e_v v_bot))),
     [("from_table",d_in); ("hit",d_in); ("smac",d_none)]);
    ("Set_dmac",
     stmt_seq
       (stmt_cond (e_var (varn_name "from_table"))
          (stmt_ass (lval_varname (varn_name "gen_apply_result"))
             (e_struct
                [("hit",e_var (varn_name "hit"));
                 ("miss",e_unop unop_neg (e_var (varn_name "hit")));
                 ("action_run",
                  e_v
                    (v_bit
                       ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                         F; F; F; F; F; F; F; F; F; F; F; F; T; F; F],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_ass
             (lval_field
                (lval_field (lval_varname (varn_name "headers")) "ethernet")
                "dstAddr") (e_var (varn_name "dmac"))) (stmt_ret (e_v v_bot))),
     [("from_table",d_in); ("hit",d_in); ("dmac",d_none)]);
    ("Send_to_cpu",
     stmt_seq
       (stmt_cond (e_var (varn_name "from_table"))
          (stmt_ass (lval_varname (varn_name "gen_apply_result"))
             (e_struct
                [("hit",e_var (varn_name "hit"));
                 ("miss",e_unop unop_neg (e_var (varn_name "hit")));
                 ("action_run",
                  e_v
                    (v_bit
                       ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                         F; F; F; F; F; F; F; F; F; F; F; F; F; T; T],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_ass
             (lval_field (lval_varname (varn_name "standard_metadata"))
                "egress_spec") (e_v (v_bit ([T; T; T; T; T; T; T; T; F],9))))
          (stmt_ret (e_v v_bot))),[("from_table",d_in); ("hit",d_in)]);
    ("Set_nhop",
     stmt_seq
       (stmt_cond (e_var (varn_name "from_table"))
          (stmt_ass (lval_varname (varn_name "gen_apply_result"))
             (e_struct
                [("hit",e_var (varn_name "hit"));
                 ("miss",e_unop unop_neg (e_var (varn_name "hit")));
                 ("action_run",
                  e_v
                    (v_bit
                       ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                         F; F; F; F; F; F; F; F; F; F; F; F; F; T; F],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_seq
             (stmt_ass (lval_varname (varn_name "nextHop"))
                (e_var (varn_name "ipv4_dest")))
             (stmt_seq
                (stmt_ass
                   (lval_field
                      (lval_field (lval_varname (varn_name "headers")) "ip")
                      "ttl")
                   (e_binop
                      (e_acc (e_acc (e_var (varn_name "headers")) "ip") "ttl")
                      binop_sub (e_v (v_bit ([F; F; F; F; F; F; F; T],8)))))
                (stmt_ass
                   (lval_field (lval_varname (varn_name "standard_metadata"))
                      "egress_spec") (e_var (varn_name "port")))))
          (stmt_ret (e_v v_bot))),
     [("from_table",d_in); ("hit",d_in); ("ipv4_dest",d_none);
      ("port",d_none)]);
    ("Drop_action",
     stmt_seq
       (stmt_cond (e_var (varn_name "from_table"))
          (stmt_ass (lval_varname (varn_name "gen_apply_result"))
             (e_struct
                [("hit",e_var (varn_name "hit"));
                 ("miss",e_unop unop_neg (e_var (varn_name "hit")));
                 ("action_run",
                  e_v
                    (v_bit
                       ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                         F; F; F; F; F; F; F; F; F; F; F; F; F; F; T],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_ass
             (lval_field (lval_varname (varn_name "standard_metadata"))
                "egress_spec") (e_v (v_bit ([T; T; T; T; T; T; T; T; T],9))))
          (stmt_ret (e_v v_bot))),[("from_table",d_in); ("hit",d_in)])],
   [(varn_name "nextHop",tau_bit 32,NONE)],[],
   [("smac",[mk_exact],"Drop_action",[e_v (v_bool T); e_v (v_bool F)]);
    ("dmac",[mk_exact],"Drop_action",[e_v (v_bool T); e_v (v_bool F)]);
    ("check_ttl",[mk_exact],"NoAction",[e_v (v_bool T); e_v (v_bool F)]);
    ("ipv4_match",[mk_lpm],"Drop_action",[e_v (v_bool T); e_v (v_bool F)])]);
  ("TopComputeChecksum",pbl_type_control,[("p",d_inout); ("meta",d_inout)],
   [("TopComputeChecksum",
     stmt_seq stmt_empty
       (stmt_cond
          (e_call (funn_ext "header" "isValid")
             [e_acc (e_var (varn_name "p")) "ip"])
          (stmt_block []
             (stmt_ass lval_null
                (e_call (funn_ext "" "update_checksum")
                   [e_v (v_bool T);
                    e_struct
                      [("1",
                        e_acc (e_acc (e_var (varn_name "p")) "ip") "version");
                       ("2",e_acc (e_acc (e_var (varn_name "p")) "ip") "ihl");
                       ("3",
                        e_acc (e_acc (e_var (varn_name "p")) "ip") "diffserv");
                       ("4",
                        e_acc (e_acc (e_var (varn_name "p")) "ip") "totalLen");
                       ("5",
                        e_acc (e_acc (e_var (varn_name "p")) "ip")
                          "identification");
                       ("6",
                        e_acc (e_acc (e_var (varn_name "p")) "ip") "flags");
                       ("7",
                        e_acc (e_acc (e_var (varn_name "p")) "ip")
                          "fragOffset");
                       ("8",e_acc (e_acc (e_var (varn_name "p")) "ip") "ttl");
                       ("9",
                        e_acc (e_acc (e_var (varn_name "p")) "ip") "protocol");
                       ("10",
                        e_acc (e_acc (e_var (varn_name "p")) "ip") "srcAddr");
                       ("11",
                        e_acc (e_acc (e_var (varn_name "p")) "ip") "dstAddr")];
                    e_acc (e_acc (e_var (varn_name "p")) "ip") "hdrChecksum";
                    e_v
                      (v_bit
                         ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                           F; F; F; F; F; F; F; F; F; F; F; F; T; T; F],32))])))
          stmt_empty),[])],[],[],[]);
  ("TopDeparser",pbl_type_control,[("b",d_none); ("p",d_in)],
   [("TopDeparser",
     stmt_seq stmt_empty
       (stmt_seq
          (stmt_ass lval_null
             (e_call (funn_ext "packet_out" "emit")
                [e_var (varn_name "b");
                 e_acc (e_var (varn_name "p")) "ethernet"]))
          (stmt_ass lval_null
             (e_call (funn_ext "packet_out" "emit")
                [e_var (varn_name "b"); e_acc (e_var (varn_name "p")) "ip"]))),
     [])],[],[],[])],
 [("postparser",ffblock_ff v1model_postparser);
  ("preingress",ffblock_ff v1model_preingress)],
 v1model_input_f
   (v_struct
      [("ethernet",
        v_header F
          [("dstAddr",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F],
               48));
           ("srcAddr",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F],
               48));
           ("etherType",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16))]);
       ("ip",
        v_header F
          [("version",v_bit ([F; F; F; F],4));
           ("ihl",v_bit ([F; F; F; F],4));
           ("diffserv",v_bit ([F; F; F; F; F; F; F; F],8));
           ("totalLen",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16));
           ("identification",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16));
           ("flags",v_bit ([F; F; F],3));
           ("fragOffset",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F],13));
           ("ttl",v_bit ([F; F; F; F; F; F; F; F],8));
           ("protocol",v_bit ([F; F; F; F; F; F; F; F],8));
           ("hdrChecksum",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16));
           ("srcAddr",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F],32));
           ("dstAddr",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F],32))])],v_struct []),
 v1model_output_f,v1model_copyin_pbl,v1model_copyout_pbl,
 v1model_apply_table_f'',
 [("header",NONE,
   [("isValid",[("this",d_in)],header_is_valid);
    ("setValid",[("this",d_inout)],header_set_valid);
    ("setInvalid",[("this",d_inout)],header_set_invalid)]);
  ("",NONE,
   [("mark_to_drop",[("standard_metadata",d_inout)],v1model_mark_to_drop);
    ("verify",[("condition",d_in); ("err",d_in)],v1model_verify);
    ("verify_checksum",
     [("condition",d_in); ("data",d_in); ("checksum",d_in); ("algo",d_none)],
     v1model_verify_checksum);
    ("update_checksum",
     [("condition",d_in); ("data",d_in); ("checksum",d_inout);
      ("algo",d_none)],v1model_update_checksum);
    ("assert",[("check",d_in)],v1model_assert);
    ("assume",[("check",d_in)],v1model_assume)]);
  ("packet_in",NONE,
   [("extract",[("this",d_in); ("headerLvalue",d_out)],
     v1model_packet_in_extract);
    ("lookahead",[("this",d_in); ("targ1",d_in)],v1model_packet_in_lookahead);
    ("advance",[("this",d_in); ("bits",d_in)],v1model_packet_in_advance)]);
  ("packet_out",NONE,
   [("emit",[("this",d_in); ("data",d_in)],v1model_packet_out_emit)]);
  ("direct_counter",
   SOME ([("this",d_out); ("type",d_none)],v1model_direct_counter_construct),
   [("count",[("this",d_out)],v1model_direct_counter_count)]);
  ("direct_meter",
   SOME
     ([("this",d_out); ("type",d_none); ("targ1",d_in)],
      v1model_direct_meter_construct),[]);
  ("action_selector",
   SOME
     ([("this",d_out); ("algorithm",d_none); ("size",d_none);
       ("outputWidth",d_none)],v1model_action_selector_construct),[]);
  ("register",
   SOME
     ([("this",d_out); ("size",d_none); ("targ1",d_in)],register_construct),
   [("read",[("this",d_in); ("result",d_out); ("index",d_in)],register_read);
    ("write",[("this",d_in); ("index",d_in); ("value",d_in)],register_write)]);
  ("ipsec_crypt",SOME ([("this",d_out)],ipsec_crypt_construct),
   [("decrypt_aes_ctr",
     [("this",d_in); ("ipv4",d_inout); ("esp",d_inout);
      ("standard_metadata",d_inout); ("key",d_in); ("key_hmac",d_in)],
     ipsec_crypt_decrypt_aes_ctr);
    ("encrypt_aes_ctr",
     [("this",d_in); ("ipv4",d_inout); ("esp",d_inout); ("key",d_in);
      ("key_hmac",d_in)],ipsec_crypt_encrypt_aes_ctr);
    ("encrypt_null",[("this",d_in); ("ipv4",d_inout); ("esp",d_inout)],
     ipsec_crypt_encrypt_null);
    ("decrypt_null",
     [("this",d_in); ("ipv4",d_inout); ("esp",d_inout);
      ("standard_metadata",d_inout)],ipsec_crypt_decrypt_null)])],
 [("NoAction",
   stmt_seq
     (stmt_cond (e_var (varn_name "from_table"))
        (stmt_ass (lval_varname (varn_name "gen_apply_result"))
           (e_struct
              [("hit",e_var (varn_name "hit"));
               ("miss",e_unop unop_neg (e_var (varn_name "hit")));
               ("action_run",
                e_v
                  (v_bit
                     ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                       F; F; F; F; F; F; F; F; F; F; F; F; F; F],32)))]))
        stmt_empty) (stmt_seq stmt_empty (stmt_ret (e_v v_bot))),
   [("from_table",d_in); ("hit",d_in)])]):v1model_ascope actx”;

val vss_v1model_astate = “((0,[],[],0,[],[("parseError",v_bit (fixwidth 32 (n2v 0),32))],
  [^smac_tbl; ^dmac_tbl'; ("check_ttl", tbl_regular []); ^ipv4_match_tbl]),
 [[(varn_name "gen_apply_result",
    v_struct
      [("hit",v_bool F); ("miss",v_bool F);
       ("action_run",v_bit (REPLICATE 32 F,32))],NONE)]],
 arch_frame_list_empty,status_running):v1model_ascope astate”;

(* Use hex_to_bool_list to debug from simulator print-out.

val packet_in = hex_to_bool_list "01 00 5E 00 00 16 02 11 22 33 44 01 08 00 46 C0 00 28 00 00 40 00 01 02 F9 F8 0A 00 00 01 E0 00 00 16 94 04 00 00 22 00 F9 02 00 00 00 01 04 00 00 00 E0 00 00 FB"
val input = mk_pair (packet_in, “1:num”)

EVAL “arch_multi_exec ^vss_v1model_actx (p4_append_input_list [^input] ^vss_v1model_astate) 267”

EVAL “arch_multi_exec ^vss_v1model_actx (p4_append_input_list [^input] ^vss_v1model_astate) 167”
val astate2 = dest_some $ rhs $ concl $ EVAL “arch_multi_exec ^vss_v1model_actx (p4_append_input_list [^input] ^vss_v1model_astate) 176”
EVAL “arch_multi_exec ^vss_v1model_actx (p4_append_input_list [^input] ^astate2) 175”

val res = dest_some $ rhs $ concl $ EVAL “arch_multi_exec ^vss_v1model_actx (p4_append_input_list [^input] ^vss_v1model_astate) 267”

bool_list_to_hex “[F; F; F; F; F; F; T; F; F; F; F; T; F; F; F; T; F; F; T; F; F; F;
            T; F; F; F; T; T; F; F; T; T; F; T; F; F; F; T; F; F; F; F; F; F;
            F; F; T; F; F; F; F; F; F; F; T; F; F; F; F; T; F; F; F; T; F; F;
            T; F; F; F; T; F; F; F; T; T; F; F; T; T; F; T; F; F; F; T; F; F;
            F; F; F; F; F; T; F; F; F; F; F; F; T; F; F; F; F; F; F; F; F; F;
            F; F; F; T; F; F; F; T; F; T; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; T; T; F; F; T; F; T; F; F; T; F; T; T; T; F; T;
            F; T; T; T; T; T; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; T; T; T; T; T; T; F; F; F; T; F; F; F; T; T; T; F; T; F; F;
            F; F; F; T; F; T; T; F; F; T; F; F; F; F; T; F; T; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; T; F; F;
            F; F; T; F; T; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; T; F; F; F; F; F; F; T; F; F; T; T; F; T; F; F;
            T; F; F; F; F; F; F; T; F; F; F; F; F; F; F; T; F; F; F; F; F; F;
            F; F; F; F; F; F; F; T; T; T; T; F; T; F; F; T; T; T; T; F; T; T;
            F; T; F; T; F; F; F; T; T; F; T; F; T; T; F; T; T; F; T; T; F; F;
            F; T; T; F; T; T; F; T; F; T; T; F; T; T; T; F; F; T; T; F; T; T;
            T; T; F; T; T; T; F; F; F; F; T; T; T; T; T; T; T; F; T; T; F; F;
            T; F; T; F; F; F; F; F; T; T; F; T; T; T; T; T; F; F; F; F; F; F;
            F; F; F; F; F; T; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F; F; F; F; F; F; T; F; F; F; F; F; T; T;
            T; T; F; F; F; F; F; T; F; T; T; T; F; T; T; T; T; T; T; T; T; F;
            F; T; T; F; F; F; F; T; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F]”

EVAL “arch_multi_exec ^vss_v1model_actx (p4_append_input_list [^input] ^vss_v1model_astate) 50”
            
EVAL “arch_multi_exec ^vss_v1model_actx (p4_append_input_list [^input] ^vss_v1model_astate) 51”

*)
(*
val actx = vss_v1model_actx
val astate = vss_v1model_astate
*)
val (dict', actx', astate') =
 transform_program cake_dict_tm "v1model" vss_v1model_actx vss_v1model_astate;

(*

val astate'2_opt = rhs $ concl $ EVAL “arch_multi_exec' ^actx' (THE $ p4_append_input_bool_list' [^input] ^astate') 267”

val astate'2 = dest_some astate'2_opt

val astate'2_opt = rhs $ concl $ EVAL “arch_multi_exec' ^actx' (THE $ p4_append_input_bool_list' [^input] ^astate'2) 267”

val res =
 bool_list_to_hex $ rhs $ concl $ EVAL “FLAT $ MAP w2v ([2w; 17w; 34w; 51w; 68w; 2w; 2w; 17w; 34w; 51w; 68w; 4w; 8w; 0w;
           69w; 0w; 0w; 50w; 151w; 95w; 0w; 0w; 63w; 17w; 208w; 89w; 10w; 0w;
           0w; 1w; 10w; 0w; 0w; 2w; 4w; 210w; 4w; 4w; 0w; 30w; 158w; 212w;
           107w; 108w; 109w; 110w; 111w; 112w; 254w; 202w; 13w; 240w; 1w; 0w;
           0w; 0w; 2w; 15w; 5w; 223w; 230w; 16w; 0w; 0w]:word8 list)”;

*)

val dict'' = invert_dict dict';

val progname = Theory.current_theory();
val dict = dict'';
val actx = actx';
val astate = astate';
val n_max = “1000:num”;
val debug_mode = false;
val inlogic = false;

p4_cake_wrapper_ffiLib.translate_p4 progname dict actx astate n_max debug_mode inlogic;

val _ = export_theory ();
