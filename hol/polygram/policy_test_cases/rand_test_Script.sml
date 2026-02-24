open HolKernel boolLib liteLib simpLib Parse bossLib;
open policy_arith_to_varTheory;


val _ = new_theory "test_rand";



Type action_policy_type = :((string# num list) action_expr) policy
Type action_table_type = :((string# num list) var_table_list # num)

(*

open HolKernel boolLib bossLib Parse;
open listTheory pairTheory optionTheory;
open pairSyntax numSyntax listSyntax stringSyntax optionSyntax;

fun term_of_num n = mk_numeral (Arbnum.fromInt n);
fun num_of_term t = Arbnum.toInt (dest_numeral t);

fun mk_action_expr (cmd, args) =
    “action (^(fromMLstring cmd), ^(mk_list (map term_of_num args, ”:num“)))
     : (string # num list) action_expr”;

fun mk_state_expr n =
    “state ^(term_of_num n) : (string # num list) action_expr”;

fun extract_bdd bdd_term =
    let val (start_state_term, rest) = dest_pair bdd_term
        val (edges_term, labelings_term) = dest_pair rest
        val edges_list = fst (dest_list edges_term)
        val labelings_list = fst (dest_list labelings_term)
        val edges = map (fn edge_term =>
                let val (parent, rest) = dest_pair edge_term
                    val (left_child, right_child) = dest_pair rest
                in (num_of_term parent, num_of_term left_child, num_of_term right_child)
                end) edges_list
        val labelings = map (fn label_term =>
                let val (id_term, label) = dest_pair label_term
                in (num_of_term id_term, label)
                end) labelings_list
    in (num_of_term start_state_term, edges, labelings)
    end;

fun extract_groupings groupings_term =
    let val groupings_list = fst (dest_list groupings_term)
    in map (fn group_term =>
            let val (name_term, vars_term) = dest_pair group_term
                val name = fromHOLstring name_term
                val vars_list = fst (dest_list vars_term)
                val vars = map fromHOLstring vars_list
            in (name, vars)
            end) groupings_list
    end;

fun get_children edges node_id =
    case List.find (fn (parent, _, _) => parent = node_id) edges of
        SOME (_, left, right) => (left, right) | NONE => (~1, ~1);

fun get_node_label labelings node_id =
    case List.find (fn (id, _) => id = node_id) labelings of
        SOME (_, label) => label | NONE => “dummy”;

fun get_node_variable labelings node_id =
    let val label = get_node_label labelings node_id
        val (constructor, args) = dest_comb label
    in if same_const constructor “non_termn” then
            let val (opt_term, _) = dest_pair args
            in case (dest_some opt_term) of var_name_term => SOME (fromHOLstring var_name_term)
            end handle HOL_ERR _ => NONE
        else NONE
    end handle HOL_ERR _ => NONE;

fun in_group labelings group_vars node_id =
    case get_node_variable labelings node_id of
        SOME var_name => List.exists (fn v => v = var_name) group_vars | NONE => false;

fun is_terminal_node labelings node_id =
    case List.find (fn (id, label) => id = node_id) labelings of
        SOME (_, label) =>
            let val (constructor, _) = dest_comb label
            in same_const constructor “termn” end
      | NONE => false;

fun find_main_path edges labelings group_vars entry_node =
    let fun traverse current path =
            if not (in_group labelings group_vars current) then (current, path)
            else case get_node_variable labelings current of
                    SOME var_name =>
                        let val (left_child, _) = get_children edges current
                        in if left_child >= 0 then
                             traverse left_child (path @ [(var_name, true)])
                           else (current, path @ [(var_name, true)])
                        end
                  | NONE => (current, path)
    in traverse entry_node []
    end;

fun collect_main_path_nodes edges labelings group_vars entry_node main_path_vars =
    let fun collect current remaining acc idx =
            case remaining of
                [] => rev acc
              | (var, _)::rest =>
                    let val (left_child, _) = get_children edges current
                    in if left_child >= 0 then
                         collect left_child rest ((current, var, idx)::acc) (idx + 1)
                       else
                         rev ((current, var, idx)::acc)
                    end
    in collect entry_node main_path_vars [] 0
    end;

fun find_shared_right_child edges main_path_nodes idx =
    if idx >= length main_path_nodes then
        ([], ~1)
    else
        let val (node1, _, _) = List.nth (main_path_nodes, idx)
            val (_, right1) = get_children edges node1
        in
            if right1 < 0 then ([], ~1)
            else
                let fun collect_sharing i acc =
                        if i >= length main_path_nodes then rev acc
                        else
                            let val (node_i, _, _) = List.nth (main_path_nodes, i)
                                val (_, right_i) = get_children edges node_i
                            in
                                if right_i = right1 then
                                    collect_sharing (i + 1) (i :: acc)
                                else
                                    rev acc
                            end
                in
                    (collect_sharing idx [], right1)
                end
        end;

fun find_default_exit edges labelings group_vars entry_node =
    let
        fun explore current =
            if is_terminal_node labelings current orelse not (in_group labelings group_vars current) then
                current
            else
                let val (_, right_child) = get_children edges current
                in if right_child >= 0 then explore right_child else current
                end
    in explore entry_node
    end;

(* Restricted exploration: Pattern 1, 2, and 3 *)
fun explore_restricted edges labelings group_vars node : ((string * bool) list * int) list =
    let
        val (main_exit, main_path_vars) = find_main_path edges labelings group_vars node
        val main_path_nodes = collect_main_path_nodes edges labelings group_vars node main_path_vars

        val main_rule = (main_path_vars, main_exit)

        fun process_positions idx acc =
            if idx < 0 then
                acc
            else
                let val (shared_indices, shared_right) = find_shared_right_child edges main_path_nodes idx
                in
                    if length shared_indices > 1 andalso shared_right >= 0 then
                        if in_group labelings group_vars shared_right then
                            (* Shared child is IN GROUP - could be Pattern 1 or 2 *)
                            let
                                fun is_entry_at_start () =
                                    case shared_indices of
                                        [] => false
                                      | (first::_) =>
                                            let val (first_node, _, _) = List.nth (main_path_nodes, first)
                                            in first_node = node
                                            end
                            in
                                if is_entry_at_start () then
                                    (* Pattern 2: CUTOFF - recursive cutoff *)
                                    let val cutoff_rules = explore_restricted edges labelings group_vars shared_right
                                    in
                                        process_positions (idx - 1) (acc @ cutoff_rules)
                                    end
                                else
                                    (* Pattern 1: NOT at entry - restricted exploration only *)
                                    let
                                        fun append_restricted_exploration idx_in_seq =
                                            let val (_, var, _) = List.nth (main_path_nodes, idx_in_seq)
                                                val before_ss = List.take (main_path_vars, idx_in_seq)
                                                val negation_prefix = before_ss @ [(var, false)]
                                                val restricted_rules = explore_restricted edges labelings group_vars shared_right
                                                fun add_prefix (path, exit) = (negation_prefix @ path, exit)
                                            in
                                                map add_prefix restricted_rules
                                            end

                                        val all_restricted = List.concat (map append_restricted_exploration shared_indices)
                                    in
                                        process_positions (idx - 1) (acc @ all_restricted)
                                    end
                            end
                        else
                            (* OUT OF GROUP - Pattern 3: negation only *)
                            let
                                fun create_negation_rule idx_in_seq =
                                    let val (_, var, _) = List.nth (main_path_nodes, idx_in_seq)
                                        val before_ss = List.take (main_path_vars, idx_in_seq)
                                    in (before_ss @ [(var, false)], shared_right)
                                    end

                                val negation_rules = map create_negation_rule shared_indices
                            in
                                process_positions (idx - 1) (acc @ negation_rules)
                            end
                    else
                        process_positions (idx - 1) acc
                end

        val path_rules = process_positions (length main_path_nodes - 1) []

        val default_exit = find_default_exit edges labelings group_vars node

        val all_rules = main_rule :: path_rules @ [([], default_exit)]
    in
        all_rules
    end;

(* Main processing with Pattern 2 at entry level *)
fun process_entry_rec edges labelings group_vars entry_node parent_entry is_original =
    let
        val (main_exit, main_path_vars) = find_main_path edges labelings group_vars entry_node
        val main_path_nodes = collect_main_path_nodes edges labelings group_vars entry_node main_path_vars

        val main_rule = (main_path_vars, main_exit)

        (* Track which indices have been processed via shared sequences *)
        val processed_indices = ref []

        fun mark_processed idx = processed_indices := idx :: !processed_indices

        fun process_positions idx acc =
            if idx < 0 then
                acc
            else
                let val (shared_indices, shared_right) = find_shared_right_child edges main_path_nodes idx
                in
                    if length shared_indices > 1 andalso shared_right >= 0 then
                        (* Mark all these indices as processed *)
                        (app mark_processed shared_indices;

                         if in_group labelings group_vars shared_right then
                             (* Shared child is IN GROUP - could be Pattern 1 or 2 *)
                             let
                                 fun is_entry_at_start () =
                                     case shared_indices of
                                         [] => false
                                       | (first::_) =>
                                             let val (first_node, _, _) = List.nth (main_path_nodes, first)
                                             in first_node = entry_node
                                             end
                             in
                                 if is_entry_at_start () then
                                     (* Pattern 2: CUTOFF - generate fresh rules from cutoff node *)
                                     let
                                         val cutoff_triples =
                                             process_entry_point_rec edges labelings group_vars shared_right parent_entry false
                                         (* Extract just (path, exit) from (entry, path, exit) triples *)
                                         val cutoff_rules = map (fn (_, path, exit) => (path, exit)) cutoff_triples
                                     in
                                         process_positions (idx - 1) (acc @ cutoff_rules)
                                     end
                                 else
                                     (* Pattern 1: NOT at entry - restricted exploration ONLY *)
                                     let
                                         fun append_restricted_exploration idx_in_seq =
                                             let val (_, var, _) = List.nth (main_path_nodes, idx_in_seq)
                                                 val prefix_vars = List.take (main_path_vars, idx_in_seq)
                                                 val negation_prefix = prefix_vars @ [(var, false)]
                                                 val restricted_rules = explore_restricted edges labelings group_vars shared_right
                                                 fun add_prefix (path, exit) = (negation_prefix @ path, exit)
                                             in
                                                 map add_prefix restricted_rules
                                             end

                                         val all_restricted = List.concat (map append_restricted_exploration shared_indices)
                                     in
                                         process_positions (idx - 1) (acc @ all_restricted)
                                     end
                             end
                         else
                             (* OUT OF GROUP - Pattern 3: negation only *)
                             let
                                 fun create_negation_rule idx_in_seq =
                                     let val (_, var, _) = List.nth (main_path_nodes, idx_in_seq)
                                         val prefix_vars = List.take (main_path_vars, idx_in_seq)
                                     in (prefix_vars @ [(var, false)], shared_right)
                                     end

                                 val negation_rules = map create_negation_rule shared_indices
                             in
                                 process_positions (idx - 1) (acc @ negation_rules)
                             end)
                    else
                        process_positions (idx - 1) acc
                end

        val path_rules = process_positions (length main_path_nodes - 1) []

        (* Process individual unshared right children *)
        fun process_individual_nodes idx acc =
            if idx < 0 then
                acc
            else if List.exists (fn i => i = idx) (!processed_indices) then
                process_individual_nodes (idx - 1) acc
            else
                let
                    val (node_id, var, _) = List.nth (main_path_nodes, idx)
                    val (_, right_child) = get_children edges node_id
                    val prefix_vars = List.take (main_path_vars, idx)
                in
                    if right_child >= 0 then
                        if in_group labelings group_vars right_child then
                            (* Right child is in group - treat as cutoff (like Pattern 2) *)
                            let
                                val cutoff_triples =
                                    process_entry_point_rec edges labelings group_vars right_child parent_entry false
                                (* Extract just (path, exit) from (entry, path, exit) triples *)
                                val cutoff_rules = map (fn (_, path, exit) => (path, exit)) cutoff_triples
                            in
                                process_individual_nodes (idx - 1) (acc @ cutoff_rules)
                            end
                        else
                            (* Right child is out of group - just create negation rule *)
                            let val rule = (prefix_vars @ [(var, false)], right_child)
                            in
                                process_individual_nodes (idx - 1) (rule :: acc)
                            end
                    else
                        process_individual_nodes (idx - 1) acc
                end

        val individual_rules = process_individual_nodes (length main_path_nodes - 1) []

        (* Special case: Handle entry node's right child as cutoff even if not processed yet *)
        val entry_cutoff_rules =
            if is_original andalso not (List.exists (fn i => i = 0) (!processed_indices)) then
                let
                    val (_, right_child) = get_children edges entry_node
                in
                    if right_child >= 0 andalso in_group labelings group_vars right_child then
                        (* Entry node's right child is in group - treat as cutoff *)
                        let
                            val cutoff_triples =
                                process_entry_point_rec edges labelings group_vars right_child parent_entry false
                            (* Extract just (path, exit) from (entry, path, exit) triples *)
                            val cutoff_rules = map (fn (_, path, exit) => (path, exit)) cutoff_triples
                        in
                            cutoff_rules
                        end
                    else
                        []
                end
            else []

        val default_exit = find_default_exit edges labelings group_vars entry_node

        val all_rules = main_rule :: path_rules @ individual_rules @ entry_cutoff_rules @ [([], default_exit)]

        val rules_with_entry = map (fn (path, exit) => (parent_entry, path, exit)) all_rules
    in
        rules_with_entry
    end

and process_entry_point_rec edges labelings group_vars entry_node parent_entry is_original =
    process_entry_rec edges labelings group_vars entry_node parent_entry is_original;

fun find_paths_for_group bdd_term groupings_term group_name input_states =
    let val (_, edges, labelings) = extract_bdd bdd_term
        val groupings = extract_groupings groupings_term
        val group_vars = case List.find (fn (name, _) => name = group_name) groupings of SOME (_, vars) => vars | NONE => []

        fun process_states [] acc = rev acc
          | process_states (state::states) acc =
                process_states states (process_entry_point_rec edges labelings group_vars state state true :: acc)

        val all_rules = List.concat (process_states input_states [])

        fun deduplicate rules =
            let fun dedup [] seen acc = rev acc
                  | dedup (rule::rest) seen acc =
                        let val (inp, path, exit) = rule
                            val rule_key = (inp, path, exit)
                        in
                            if List.exists (fn k => k = rule_key) seen then
                                dedup rest seen acc
                            else
                                dedup rest (rule_key::seen) (rule::acc)
                        end
            in
                rev (dedup (rev rules) [] [])
            end

        val deduped_rules = deduplicate all_rules

        (* ==== ADD THE OPTIMIZATION HERE ==== *)
        (* NEW: Optimize by removing rules made redundant by true rules *)
        fun optimize_with_true_rules rules =
            let
                (* Process the entire list, looking for true rules and optimizing before them *)
                fun process_remaining [] acc = rev acc
                  | process_remaining (current_rule::rest) acc =
                        let
                            val (entry, path, exit) = current_rule
                        in
                            if path = [] then  (* This is a true rule *)
                                (* Look back at accumulated rules to find consecutive ones with same entry and exit *)
                                let
                                    fun find_consecutive_to_remove [] to_remove = to_remove
                                      | find_consecutive_to_remove ((prev_entry, prev_path, prev_exit)::prev_rules) to_remove =
                                            if prev_entry = entry andalso prev_exit = exit then
                                                find_consecutive_to_remove prev_rules ((prev_entry, prev_path, prev_exit)::to_remove)
                                            else
                                                to_remove  (* Stop when exit is different *)

                                    val to_remove = find_consecutive_to_remove (rev acc) []

                                    (* Filter out the rules to remove from acc *)
                                    val new_acc =
                                        List.filter (fn rule => not (List.exists (fn r => r = rule) to_remove)) acc
                                in
                                    (* Keep the true rule and continue *)
                                    process_remaining rest (current_rule :: new_acc)
                                end
                            else
                                (* Not a true rule, just accumulate *)
                                process_remaining rest (current_rule :: acc)
                        end
            in
                process_remaining rules []
            end

        val optimized_rules = optimize_with_true_rules deduped_rules
        (* ==== END OF OPTIMIZATION ==== *)


        (* DEBUG: Print rules before optimization *)
        val _ = print ("\n=== DEBUG: Rules before optimization ===\n")
        val _ = app (fn (entry, path, exit) =>
                       print ("(" ^ Int.toString entry ^ ", " ^
                              (if null path then "TRUE" else "PATH") ^ ", " ^
                              Int.toString exit ^ ")\n")) deduped_rules

        val optimized_rules = optimize_with_true_rules deduped_rules

        (* DEBUG: Print rules after optimization *)
        val _ = print ("\n=== DEBUG: Rules after optimization ===\n")
        val _ = app (fn (entry, path, exit) =>
                       print ("(" ^ Int.toString entry ^ ", " ^
                              (if null path then "TRUE" else "PATH") ^ ", " ^
                              Int.toString exit ^ ")\n")) optimized_rules




        fun rule_to_term (inp, path, exit) =
            let val atom_vars = map (fn (var, value) => if value then “Var ^(fromMLstring var)” else “Not ^(fromMLstring var)”) path
                val atom_list = if null atom_vars then [“True”] else atom_vars
            in “(^(mk_list (atom_list, ”:atom_var“)), ^(term_of_num inp), ^(mk_state_expr exit))”
            end
    in map rule_to_term optimized_rules  (* Changed from deduped_rules to optimized_rules *)
    end handle e => (print ("ERROR in find_paths_for_group: " ^ exnMessage e ^ "\n"); []);

fun generate_action_table bdd_term =
    let val (_, _, labelings) = extract_bdd bdd_term
        fun process_labeling (node_id, label) =
            let val (constructor, args) = dest_comb label
            in if same_const constructor “termn” then
                    let val (action_term, _) = dest_pair args
                    in SOME “([True], ^(term_of_num node_id), ^action_term)”
                    end
                else NONE
            end handle HOL_ERR _ => NONE
    in List.mapPartial process_labeling labelings
    end;

fun extract_exit_states raw_table =
    let fun get_exit_state term =
            let val (_, state_pair) = dest_pair term
                val (_, state_expr) = dest_pair state_pair
                val (_, num_term) = dest_comb state_expr
            in num_of_term num_term
            end
        fun uniq [] = [] | uniq (x::xs) = if List.exists (fn y => y = x) xs then uniq xs else x :: uniq xs
    in uniq (map get_exit_state raw_table)
    end;

fun bdd_to_tables_iterative bdd_term groupings_term =
    let val groupings = extract_groupings groupings_term
        fun iterate inputs groups acc =
            case groups of
                [] =>
                    let val group_tables = rev acc
                        val action_table = generate_action_table bdd_term
                    in group_tables @ [action_table]
                    end
              | (group_name, _)::gs =>
                    let val raw_table = find_paths_for_group bdd_term groupings_term group_name inputs
                        val next_states = extract_exit_states raw_table
                    in iterate next_states gs (raw_table::acc)
                    end

        val tables = iterate [0] groupings []

        fun mk_table_list [] = “[] : (atom_var list # num # (string # num list) action_expr) list list”
          | mk_table_list tables =
                let val table_terms = map (fn t => mk_list (t, “:(atom_var list # num # (string # num list) action_expr)”)) tables
                in mk_list (table_terms, “:(atom_var list # num # (string # num list) action_expr) list”)
                end
    in “(^(mk_table_list tables), ^(term_of_num 0))”
    end
    handle e => (print ("ERROR in bdd_to_tables_iterative: " ^ exnMessage e ^ "\n"); “([], ^(term_of_num 0))”);








(************************************************)

val var_policy_1 =
“
 [(And (Var "a1")
       (And (Var "b1")
            (And (Var "c1")
                 (And (Var "d1")
                      (And (Var "e1")
                           ( (Var "f1")))))),
    action ("allow",[1]));
   (And (Var "a2")
        (And (Var "b2")
             (And (Var "c2")
                  (And (Var "d2")
                       (And (Var "e2")
                            ( (Var "f2")))))),
    action ("allow",[2]));
   (True,action ("drop",[]))]:action_policy_type
”;




val policy_order_1 = “["a1";"b1";"a2";"b2";
                       "c1";"d1";"c2";"d2";
                       "e1";"f1";"e2";"f2";]”;

val policy_full_order_1 = “[
  ("grp_ab_1" ,["a1";"b1";"a2";"b2"]);
  ("grp_cd_2" ,["c1";"d1";"c2";"d2"]);
  ("grp_ef_3" ,["e1";"f1";"e2";"f2"])
                          ]”;

val eval_policy_full_opt1 = EVAL “mk_BDDPred_opt policy_structure (0,[],[(0, non_termn (NONE, ^var_policy_1))]) [] ^policy_order_1 1”;

val eval_policy_full_opt_rhs1 = optionSyntax.dest_some (rhs (concl eval_policy_full_opt1));

val test_groupings_1 = rhs(concl(EVAL policy_full_order_1));


val old_gen_var_table_auto1 = bdd_utilsLib.bdd_to_tables_iterative_old eval_policy_full_opt_rhs1 test_groupings_1;


val new_gen_var_table_auto1 = bdd_to_tables_iterative eval_policy_full_opt_rhs1 test_groupings_1;



val old_tbl_bdd = optionSyntax.dest_some (rhs(concl(EVAL
“mk_BDDPred_opt table_structure (0,[],[(0, non_termn (NONE, ^old_gen_var_table_auto1))]) [] ^policy_order_1 1”)));

val new_tbl_bdd = optionSyntax.dest_some (rhs(concl(EVAL
“mk_BDDPred_opt table_structure (0,[],[(0, non_termn (NONE, ^new_gen_var_table_auto1))]) [] ^policy_order_1 1”)));



(*
([[([Var "a1"; Var "b1"; Var "a2"; Var "b2"],0,state 11);
       ([Var "a1"; Var "b1"; Var "a2"; Not "b2"],0,state 12);
       ([Var "a1"; Var "b1"; Not "a2"],0,state 12);
       ([Var "a2"; Var "b2"],0,state 24); ([True],0,state 10)];
      [([Var "c1"; Var "d1"; Var "c2"; Var "d2"],11,state 35);
       ([Var "c1"; Var "d1"; Var "c2"; Not "d2"],11,state 36);
       ([Var "c1"; Var "d1"; Not "c2"],11,state 36);
       ([Var "c2"; Var "d2"],11,state 48); ([True],11,state 10);
       ([Var "c1"; Var "d1"],12,state 36);
       ([Var "c1"; Not "d1"],12,state 10); ([Not "c1"],12,state 10);
       ([True],12,state 10); ([Var "c2"; Var "d2"],24,state 48);
       ([Var "c2"; Not "d2"],24,state 10); ([Not "c2"],24,state 10);
       ([True],24,state 10); ([True],10,state 10)];
      [([Var "e1"; Var "f1"],35,state 47);
       ([Var "e2"; Var "f2"],35,state 55); ([True],35,state 10);
       ([Var "e1"; Var "f1"],36,state 47);
       ([Var "e1"; Not "f1"],36,state 10); ([Not "e1"],36,state 10);
       ([True],36,state 10); ([Var "e2"; Var "f2"],48,state 55);
       ([Var "e2"; Not "f2"],48,state 10); ([Not "e2"],48,state 10);
       ([True],48,state 10); ([True],10,state 10)];
      [([True],10,action ("drop",[])); ([True],47,action ("allow",[1]));
       ([True],55,action ("allow",[2]))]],0)

*)





(************************************************)




val bdd_policy_10_2 =  (* removed too large *)

val test_order_10_2 = “
 ["is_srcPort_le_57222"; "is_srcPort_ge_57222"; "is_srcPort_le_56258";
 "is_srcPort_ge_56258"; "is_srcPort_le_6881"; "is_srcPort_ge_6881";
 "is_srcPort_le_50553"; "is_srcPort_ge_50553"; "is_srcPort_le_50002";
 "is_srcPort_ge_50002"; "is_srcPort_le_51465"; "is_srcPort_ge_51465";
 "is_srcPort_le_60513"; "is_srcPort_ge_60513"; "is_srcPort_le_50049";
 "is_srcPort_ge_50049"; "is_srcPort_le_52244"; "is_srcPort_ge_52244";
 "is_srcPort_le_50627"; "is_srcPort_ge_50627"]”



val test_grouping_10_2 = “[
  ("srcPortGrp",["is_srcPort_le_57222";"is_srcPort_ge_57222";"is_srcPort_le_56258";"is_srcPort_ge_56258";"is_srcPort_le_6881";"is_srcPort_ge_6881";"is_srcPort_le_50553";"is_srcPort_ge_50553";"is_srcPort_le_50002";"is_srcPort_ge_50002";"is_srcPort_le_51465";"is_srcPort_ge_51465";"is_srcPort_le_60513";"is_srcPort_ge_60513";"is_srcPort_le_50049";"is_srcPort_ge_50049";"is_srcPort_le_52244";"is_srcPort_ge_52244";"is_srcPort_le_50627";"is_srcPort_ge_50627"])
]”;


val gen_tbl_new2 = bdd_to_tables_iterative bdd_policy_10_2 test_grouping_10_2;

EVAL “mk_BDDPred_opt table_structure (0,[],[(0, non_termn (NONE, ^gen_tbl_new2 ))]) [] ^test_order_10_2 1”;


(*
([[([Var "is_srcPort_ge_57222"],0,state 1);
   ([Var "is_srcPort_ge_56258"],0,state 3);
   ([Var "is_srcPort_ge_6881"],0,state 5);
   ([Var "is_srcPort_ge_50553"],0,state 7);
   ([Var "is_srcPort_ge_50002"],0,state 9);
   ([Var "is_srcPort_ge_51465"],0,state 11);
   ([Var "is_srcPort_ge_60513"],0,state 13);
   ([Var "is_srcPort_ge_50049"],0,state 15);
   ([Var "is_srcPort_ge_52244"],0,state 17);
   ([Var "is_srcPort_ge_50627"],0,state 19); ([True],0,state 20)];
  [([True],1,action ("allow",[1])); ([True],3,action ("allow",[2]));
   ([True],5,action ("allow",[3])); ([True],7,action ("allow",[4]));
   ([True],9,action ("allow",[5])); ([True],11,action ("allow",[6]));
   ([True],13,action ("allow",[7])); ([True],15,action ("allow",[8]));
   ([True],17,action ("allow",[9])); ([True],19,action ("allow",[10]));
   ([True],20,action ("drop",[]))]],0)

*)




(********************************************)








val var_policy_2_6 =
“
 [(And (Var "a1")
       (And (Var "b1")
            (And (Var "c1")
                 (And (Var "d1")
                      (And (Var "e1")
                           ( (Var "f1")))))),
    action ("allow",[1]));
   (And (Var "a2")
        (And (Var "b2")
             (And (Var "c2")
                  (And (Var "d2")
                       (And (Var "e2")
                            ( (Var "f2")))))),
    action ("allow",[2]));
   (And (Var "a3")
        ( (Var "b3")),
    action ("allow",[3]));
   (True,action ("drop",[]))]:action_policy_type
”;






val policy_order_2_6 = “["a1";"b1";"a2";"b2";"a3";"b3";
                        "c1";"d1";"c2";"d2";
                        "e1";"f1";"e2";"f2";]”;

val policy_full_order_2_6 = “[
  ("grp_ab" ,["a1";"b1";"a2";"b2";"a3";"b3";]);
  ("grp_cd" ,["c1";"d1";"c2";"d2";]);
  ("grp_ef" ,["e1";"f1";"e2";"f2";])
                          ]”;




val eval_policy_full_opt2_6 = EVAL “mk_BDDPred_opt policy_structure (0,[],[(0, non_termn (NONE, ^var_policy_2_6))]) [] ^policy_order_2_6 1”;





val test_groupings_2_6 = rhs(concl(EVAL policy_full_order_2_6));
val old_gen_var_table_auto2_6 = bdd_utilsLib.bdd_to_tables_iterative_old eval_policy_full_opt_rhs2_6 test_groupings_2_6;
val old_tbl_bdd = optionSyntax.dest_some (rhs(concl(EVAL
   “mk_BDDPred_opt table_structure (0,[],[(0, non_termn (NONE, ^old_gen_var_table_auto2_6))]) [] ^policy_order_2_6 1”)));


bdd_utilsLib.bdd_to_tables_iterative_old eval_policy_full_opt_rhs2_6 test_groupings_2_6;



val new_gen_var_table_auto2_6 = bdd_to_tables_iterative eval_policy_full_opt_rhs2_6 test_groupings_2_6;



val new_tbl_bdd = optionSyntax.dest_some (rhs(concl(EVAL
“mk_BDDPred_opt table_structure (0,[],[(0, non_termn (NONE, ^new_gen_var_table_auto2_6))]) [] ^policy_order_2_6 1”)));

(*


val best_tbl = “([[([Var "a1"; Var "b1"; Var "a2"; Var "b2"; Var "a3"; Var "b3"],0,state 27);
               ([Var "a1"; Var "b1"; Var "a2"; Var "b2"; Not "a3"],0,state 28);
               ([Var "a1"; Var "b1"; Var "a2"; Var "b2"; Not "b3"],0,state 28);

               ([Var "a1"; Var "b1"; Var "a2"; Not "b2"; Var "a3"; Var "b3"],0,state 31);
               ([Var "a1"; Var "b1"; Var "a2"; Not "b2"; Not "b3"],0,state 32);
               ([Var "a1"; Var "b1"; Var "a2"; Not "b2"; Not "a3"],0,state 32);

               ([Var "a1"; Var "b1"; Not "a2"; Var "a3"; Var "b3"],0,state 31);
               ([Var "a1"; Var "b1"; Not "a2"; Not "b3"],0,state 32);
               ([Var "a1"; Var "b1"; Not "a2"; Not "a3"],0,state 32);

               (* cutt off*)
               ([Var "a2"; Var "b2"; Var "a3"; Var "b3"],0,state 54);
               ([Var "a2"; Var "b2"; Not "a3"],0,state 58);
               ([Var "a2"; Var "b2"; Not "b3"],0,state 58);

               ([Var "a3"; Var "b3"],0,state 39);
               ([Not "a3"],0,state 26);
               ([Not "b3"],0,state 26)];


              [([Var "c1"; Var "d1"; Var "c2"; Var "d2"],27,state 77);
               ([Var "c1"; Var "d1"; Not "c2"],27,state 78);
               ([Var "c1"; Var "d1"; Not "d2"],27,state 78);

               ([Var "c2"; Var "d2"],27,state 102);
               ([Not "d2"],27,state 39);
               ([Not "c2"],27,state 39);

               ([Var "c1"; Var "d1"; Var "c2"; Var "d2"],28,state 83);
               ([Var "c1"; Var "d1"; Not "c2"],28,state 84);
               ([Var "c1"; Var "d1"; Not "d2"],28,state 84);

               ([Var "c2"; Var "d2"],28,state 108);
               ([Not "c2"],28,state 26);
               ([Not "d2"],28,state 26);

               ([Var "c1"; Var "d1"],31,state 78);
               ([Not "c1"],31,state 39);
               ([Not "d1"],31,state 39);

               ([Var "c1"; Var "d1"],32,state 84);
               ([Not "c1"],32,state 26);
               ([Not "d1"],32,state 26);

               ([Var "c2"; Var "d2"],54,state 102);
               ([Not "c2"],54,state 39);
               ([Not "d2"],54,state 39);

               ([Var "c2"; Var "d2"],58,state 108);
               ([Not "c2"],58,state 26);
               ([Not "d2"],58,state 26);

               ([True],39,state 39); ([True],26,state 26)];
              [([Var "e1"; Var "f1"],77,state 101);
               ([Var "e2"; Var "f2"],77,state 117);
               ([Not "e2"],77,state 39);
               ([Not "f2"],77,state 39);

               ([Var "e1"; Var "f1"],83,state 101);
               ([Var "e2"; Var "f2"],83,state 117);
               ([Not "e2"],83,state 26);
               ([Not "f2"],83,state 26);

               ([Var "e1"; Var "f1"],78,state 101);
               ([Not "e1"],78,state 39);
               ([Not "f1"],78,state 39);

               ([Var "e1"; Var "f1"],84,state 101);
               ([Not "e1"],84,state 26);
               ([Not "f1"],84,state 26);

               ([Var "e2"; Var "f2"],102,state 117);
               ([Not "e2"],102,state 39);
               ([Not "f2"],102,state 39);

               ([Var "e2"; Var "f2"],108,state 117);
               ([Not "e2"],108,state 26);
               ([Not "f2"],108,state 26); ([True],39,state 39);
               ([True],26,state 26)];
              [([True],26,action ("drop",[]));
               ([True],39,action ("allow",[3]));
               ([True],101,action ("allow",[1]));
               ([True],117,action ("allow",[2]))]],0)

:action_table_type”






EVAL
“mk_BDDPred_opt table_structure (0,[],[(0, non_termn (NONE, ^best_tbl))]) [] ^policy_order_2_6 1”

*)

(********************************)




val new_gen_var_table_auto2_6 = bdd_to_tables_iterative eval_policy_full_opt_rhs2_6 test_groupings_2_6;


EVAL
“mk_BDDPred_opt table_structure (0,[],[(0, non_termn (NONE, ^new_gen_var_table_auto2_6))]) [] ^policy_order_2_6 1”

(*******************************)

*)



val _ = export_theory ();
