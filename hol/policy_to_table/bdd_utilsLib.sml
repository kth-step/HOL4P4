structure bdd_utilsLib :> bdd_utilsLib = struct

open HolKernel boolLib bossLib Parse;
open listTheory pairTheory optionTheory;
open pairSyntax numSyntax listSyntax stringSyntax optionSyntax;


  fun make_bv n len = let
    val n_term = numSyntax.mk_numeral (Arbnum.fromInt n)
    val len_term = numSyntax.mk_numeral (Arbnum.fromInt len)
  in
    ``(fixwidth ^(len_term) (n2v ^(n_term)), ^(len_term))``
  end



  fun make_interval a b len = let
      val a_term = make_bv a len
      val b_term = make_bv b len
    in
      ``Single ^a_term ^b_term``
  end



  fun pairBDDs (bdd1: term, bdd2: term) =
      let
        open pairSyntax numSyntax listSyntax;
    


        fun num_to_arbnum num_term = 
            if is_numeral num_term then
              dest_numeral num_term
            else raise Fail "Not a numeral";
    
        fun convert_edges edges_term =
            let
              val (list_items, _) = dest_list edges_term
              fun convert_item item_term =
                  let
                    val (node, children) = dest_pair item_term
                    val (left, right) = dest_pair children
                  in
                    (num_to_arbnum node, (num_to_arbnum left, num_to_arbnum right))
                  end
            in
              map convert_item list_items
            end;



    
        val (root1_t, rest1) = dest_pair bdd1
        val (edges1_t, labels1_t) = dest_pair rest1
        val (root2_t, rest2) = dest_pair bdd2
        val (edges2_t, labels2_t) = dest_pair rest2
    
        val root1 = num_to_arbnum root1_t
        val root2 = num_to_arbnum root2_t
        val edges1 = convert_edges edges1_t
        val edges2 = convert_edges edges2_t
    


        fun lookupChildren node edges =
            case List.find (fn (n, _) => Arbnum.compare(n, node) = EQUAL) edges of
              SOME (_, (l, r)) => (SOME l, SOME r)
            | NONE => (NONE, NONE)





    
        val queue = ref [(root1, root2)]
        val visited = ref []
    



        fun processQueue () =
            case !queue of
              [] => rev (!visited)
            | (n1, n2)::rest =>
              let
                fun isVisited pair = List.exists (fn p => p = pair) (!visited)
                val _ = queue := rest
                val newPair = (n1, n2)
                val _ = visited := newPair :: (!visited)
                val (l1, r1) = lookupChildren n1 edges1
                val (l2, r2) = lookupChildren n2 edges2
                val newLeft = 
                  case (l1, l2) of
                    (SOME left1, SOME left2) => [(left1, left2)]
                  | _ => []
                val newRight = 
                  case (r1, r2) of
                    (SOME right1, SOME right2) => [(right1, right2)]
                  | _ => []
                val newPairs = newLeft @ newRight
                val notVisited = List.filter (fn pair => not (isVisited pair)) newPairs
              in
                queue := !queue @ notVisited;
                processQueue ()
              end

        (* Convert result to HOL term *)
        fun to_hol_pair (a, b) = 
            mk_pair(mk_numeral a, mk_numeral b)
        val arbnum_pairs = processQueue ()
      in
        mk_list(map to_hol_pair arbnum_pairs, 
          mk_prod(num, num))
      end





  
(* 1. numeric conversion helpers *)
fun term_of_num n = mk_numeral (Arbnum.fromInt n);
fun num_of_term t = Arbnum.toInt (dest_numeral t);

(* 2. typed term constructors *)
fun mk_action_expr (cmd, args) =
    ``action (^(fromMLstring cmd), ^(mk_list (map term_of_num args, ``:num``))) 
     : (string # num list) action_expr``;

fun mk_state_expr n =
    ``state ^(term_of_num n) : (string # num list) action_expr``;



fun generate_combinations vars =
    let
      fun make_var_term v = ``Var ^(fromMLstring v)``
      fun make_not_var_term v = ``Not (Var ^(fromMLstring v))``
  
      fun combinations [] = [[]]
        | combinations (v::vs) = 
          let 
            val rest = combinations vs
            val var_term = make_var_term v
            val not_var_term = make_not_var_term v
          in 
            (map (fn combo => var_term::combo) rest) @ 
            (map (fn combo => not_var_term::combo) rest)
          end
    in 
      combinations vars
    end;

(* Helper function to get all variables in a group *)
fun get_all_vars_in_group groupings group_name =
    case List.find (fn (name, _) => name = group_name) groupings of
      SOME (_, vars) => vars
    | NONE => [];

(* Generate action table for terminal nodes *)
(*fun generate_action_table bdd_term =
    let
      val (start_state_term, rest) = dest_pair bdd_term
      val (edges_term, labelings_term) = dest_pair rest
  
      val labelings_list = fst (dest_list labelings_term)
      val labelings = map (fn label_term => 
            let val (id_term, label) = dest_pair label_term
            in (num_of_term id_term, label)
            end) labelings_list
  
      val terminal_entries = List.mapPartial (fn (node_id, label) =>
            let
              val (constructor, args) = dest_comb label
            in
              if same_const constructor ``termn`` then
                let 
                  val (action_term, _) = dest_pair args
                  val (cmd_term, args_term) = dest_pair action_term
                  val cmd = fromHOLstring cmd_term
                  val args_list = fst (dest_list args_term)
                  val args = map num_of_term args_list
                in
                  SOME ``([True], ^(term_of_num node_id), ^(mk_action_expr (cmd, args)))``
                end
              else NONE
            end handle HOL_ERR _ => NONE
        ) labelings
    in
      terminal_entries
    end;
*)


(* Enhanced find_paths_for_group that handles input states *)
fun find_paths_for_group_with_inputs_old bdd_term groupings_term group_name input_states =
    let
      (* Extract components from the BDD term *)
      val (start_state_term, rest) = dest_pair bdd_term
      val (edges_term, labelings_term) = dest_pair rest

      (* Extract edges and labelings *)
      val edges_list = fst (dest_list edges_term)
      val edges = map (fn edge_term => 
            let 
              val (parent, rest) = dest_pair edge_term
              val (left_child, right_child) = dest_pair rest
            in 
              (num_of_term parent, num_of_term left_child, num_of_term right_child)
            end) edges_list

      val labelings_list = fst (dest_list labelings_term)
      val labelings = map (fn label_term => 
            let val (id_term, label) = dest_pair label_term
            in (num_of_term id_term, label)
            end) labelings_list

      (* Extract groupings *)
      val groupings_list = fst (dest_list groupings_term)
      val groupings = map (fn group_term =>
            let 
              val (name_term, vars_term) = dest_pair group_term
              val name = fromHOLstring name_term
              val vars_list = fst (dest_list vars_term)
              val vars = map fromHOLstring vars_list
            in
              (name, vars)
            end) groupings_list
            
      val group_vars = get_all_vars_in_group groupings group_name
      (*val _ = print ("Group vars for " ^ group_name ^ ": [" ^ String.concatWith ", " group_vars ^ "]\n")
      val _ = print ("Input states: [" ^ String.concatWith ", " (map Int.toString input_states) ^ "]\n")
*)
      (* Helper functions *)
      fun get_children node_id =
          case List.find (fn (parent, _, _) => parent = node_id) edges of
            SOME (_, left, right) => (SOME left, SOME right)
          | NONE => (NONE, NONE)

      fun get_node_variable node_id =
          case List.find (fn (id, _) => id = node_id) labelings of
            SOME (_, label) => 
              (let
                  val (constructor, args) = dest_comb label
                in
                  if same_const constructor ``non_termn`` then
                    let val (opt_term, _) = dest_pair args
                    in
                      case dest_some opt_term of
                        var_name_term => SOME (fromHOLstring var_name_term)
                    end
                  else NONE
                end handle HOL_ERR _ => NONE)
          | NONE => NONE

      fun node_in_group node_id =
          case get_node_variable node_id of
            SOME var_name => List.exists (fn v => v = var_name) group_vars
          | NONE => false

      (* Traverse from a given starting node *)
      fun traverse_group current_node path =
          if node_in_group current_node then
            let
              val (left_child, right_child) = get_children current_node
              val var_name = get_node_variable current_node
            in
              case (var_name, left_child, right_child) of
                (SOME v, SOME l, SOME r) =>
                  (traverse_group l (path @ [(v, true)])) @
                  (traverse_group r (path @ [(v, false)]))
              | _ => [(path, current_node)]
            end
          else
            [(path, current_node)]

      (* Generate paths from all input states *)
      val all_paths = List.concat (map (fn input_state => 
              let 
                val paths = traverse_group input_state []
               (*) val _ = print ("From input state " ^ Int.toString input_state ^ 
                    ": " ^ Int.toString (length paths) ^ " paths\n") *)
              in
                map (fn (path, exit_state) => (input_state, path, exit_state)) paths
              end) input_states)

      (* Convert to table entries *)
      fun path_to_entry (input_state, path, exit_state) =
          let
            val atom_vars = map (fn (var, value) =>
                  if value then ``Var ^(fromMLstring var)``
                  else ``Not (^(fromMLstring var))``
              ) path
    
            val simplified_atoms = 
              if null path then [``True``]
              else atom_vars
          in
            ``(^(mk_list (simplified_atoms, ``:atom_var``)), 
              ^(term_of_num input_state), 
              ^(mk_state_expr exit_state))``
          end

      val table_entries = map path_to_entry all_paths
    in
      table_entries
    end;


fun bdd_to_tables_iterative_old bdd_term groupings_term =
    let

        val groupings = map (fn t => 
            let val (n,v) = dest_pair t
            in (fromHOLstring n, map fromHOLstring (fst (dest_list v)))
            end) (fst (dest_list groupings_term));

        (* 2. Fixed generate action table-------don't destructure the action term *)
        fun generate_action_table bdd =
            let
                val (_, bdd_rest) = dest_pair bdd
                val (edges_term, labelings_term) = dest_pair bdd_rest
                val labelings = fst (dest_list labelings_term)
                
                fun process_labeling label_term =
                    let 
                        val (id_term, label) = dest_pair label_term
                        val (constructor, args) = dest_comb label
                    in
                        if same_const constructor ``termn`` then
                            let 
                                val (action_term, _) = dest_pair args
                                (* action_term is already the complete action, don't destructure it *)
                            in
                                SOME ``([True], ^(term_of_num (num_of_term id_term)), ^action_term)``
                            end
                        else NONE
                    end handle HOL_ERR _ => NONE
            in
                List.mapPartial process_labeling labelings
            end;

        (* 3. Process group tables with [True] entries last *)
        fun process_group_table table =
            let
                val (true_entries, other_entries) = 
                    List.partition (fn t => 
                        let val (atoms_term, _) = dest_pair t
                            val atoms_list = fst (dest_list atoms_term)
                        in length atoms_list = 1 andalso 
                           same_const (hd atoms_list) ``True``
                        end handle HOL_ERR _ => false) table
            in
                other_entries @ true_entries
            end;

        (* 4. Main iteration *)
        fun iterate inputs groups acc = 
            case groups of
              [] => 
                let 
                    val group_tables = rev acc
                    val action_table = generate_action_table bdd_term
                in
                    group_tables @ [action_table]
                end
            | g::gs =>
                let
                    val raw_table = find_paths_for_group_with_inputs_old 
                                   bdd_term groupings_term g inputs
                    val table = process_group_table raw_table
                    val next_states = mk_set (map (fn t =>
                        let val (_, rest) = dest_pair t
                            val (_, state) = dest_pair rest
                            val (_, num) = dest_comb state
                        in num_of_term num
                        end) table)
                in
                    iterate next_states gs (table::acc)
                end;

        (* 5. Generate final tables *)
        val tables = iterate [0] (map #1 groupings) []

        (* 6. Convert to string with proper types *)
        fun tables_to_string ts =
            let fun tbl_to_str t = "[" ^ String.concatWith "; " (map term_to_string t) ^ "]"
            in "[" ^ String.concatWith "; " (map tbl_to_str ts) ^ "]" end
    in
        Parse.Term [QUOTE ("((" ^ tables_to_string tables ^ ") : (atom_var list # num # (string # num list) action_expr) list list, " ^ 
                   term_to_string (term_of_num 0) ^ " : num)")]
    end;




(******************************************************)


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
        SOME (_, label) => label | NONE => ``dummy``;

fun get_node_variable labelings node_id =
    let val label = get_node_label labelings node_id
        val (constructor, args) = dest_comb label
    in if same_const constructor ``non_termn`` then
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
            in same_const constructor ``termn`` end
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
                                                val before = List.take (main_path_vars, idx_in_seq)
                                                val negation_prefix = before @ [(var, false)]
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
                                        val before = List.take (main_path_vars, idx_in_seq)
                                    in (before @ [(var, false)], shared_right)
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
                                     (* Pattern 2: CUTOFF *)
                                     let val cutoff_rules = explore_restricted edges labelings group_vars shared_right
                                     in
                                         process_positions (idx - 1) (acc @ cutoff_rules)
                                     end
                                 else
                                     (* Pattern 1: NOT at entry - restricted exploration *)
                                     let
                                         fun append_restricted_exploration idx_in_seq =
                                             let val (_, var, _) = List.nth (main_path_nodes, idx_in_seq)
                                                 val before = List.take (main_path_vars, idx_in_seq)
                                                 val negation_prefix = before @ [(var, false)]
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
                             (* Pattern 3: OUT OF GROUP - negation only *)
                             let
                                 fun create_negation_rule idx_in_seq =
                                     let val (_, var, _) = List.nth (main_path_nodes, idx_in_seq)
                                         val before = List.take (main_path_vars, idx_in_seq)
                                     in (before @ [(var, false)], shared_right)
                                     end

                                 val negation_rules = map create_negation_rule shared_indices
                             in
                                 process_positions (idx - 1) (acc @ negation_rules)
                             end)
                    else
                        process_positions (idx - 1) acc
                end

        val path_rules = process_positions (length main_path_nodes - 1) []

        (* NEW: Process individual unshared right children *)
        fun process_individual_nodes idx acc =
            if idx < 0 then
                acc
            else if List.exists (fn i => i = idx) (!processed_indices) then
                process_individual_nodes (idx - 1) acc
            else
                let
                    val (node_id, var, _) = List.nth (main_path_nodes, idx)
                    val (_, right_child) = get_children edges node_id
                    val before = List.take (main_path_vars, idx)
                in
                    if right_child >= 0 then
                        if in_group labelings group_vars right_child then
                            (* Right child is in group - need to explore it as a new main path *)
                            let
                                val exploration_rules = explore_restricted edges labelings group_vars right_child
                                fun add_prefix (path, exit) = (before @ [(var, false)] @ path, exit)
                                val prefixed_rules = map add_prefix exploration_rules
                            in
                                process_individual_nodes (idx - 1) (acc @ prefixed_rules)
                            end
                        else
                            (* Right child is out of group - just create negation rule *)
                            let val rule = (before @ [(var, false)], right_child)
                            in
                                process_individual_nodes (idx - 1) (rule :: acc)
                            end
                    else
                        process_individual_nodes (idx - 1) acc
                end

        val individual_rules = process_individual_nodes (length main_path_nodes - 1) []

        val default_exit = find_default_exit edges labelings group_vars entry_node

        val all_rules = main_rule :: path_rules @ individual_rules @ [([], default_exit)]

        val rules_with_entry = map (fn (path, exit) => (parent_entry, path, exit)) all_rules
    in
        rules_with_entry
    end;

fun process_entry_point_rec edges labelings group_vars entry_node parent_entry is_original =
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

        fun rule_to_term (inp, path, exit) =
            let val atom_vars = map (fn (var, value) => if value then ``Var ^(fromMLstring var)`` else ``Not ^(fromMLstring var)``) path
                val atom_list = if null atom_vars then [``True``] else atom_vars
            in ``(^(mk_list (atom_list, ``:atom_var``)), ^(term_of_num inp), ^(mk_state_expr exit))``
            end
    in map rule_to_term deduped_rules
    end handle e => (print ("ERROR in find_paths_for_group: " ^ exnMessage e ^ "\n"); []);

fun generate_action_table bdd_term =
    let val (_, _, labelings) = extract_bdd bdd_term
        fun process_labeling (node_id, label) =
            let val (constructor, args) = dest_comb label
            in if same_const constructor ``termn`` then
                    let val (action_term, _) = dest_pair args
                    in SOME ``([True], ^(term_of_num node_id), ^action_term)``
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

        fun mk_table_list [] = ``[] : (atom_var list # num # (string # num list) action_expr) list list``
          | mk_table_list tables =
                let val table_terms = map (fn t => mk_list (t, ``:(atom_var list # num # (string # num list) action_expr)``)) tables
                in mk_list (table_terms, ``:(atom_var list # num # (string # num list) action_expr) list``)
                end
    in ``(^(mk_table_list tables), ^(term_of_num 0))``
    end
    handle e => (print ("ERROR in bdd_to_tables_iterative: " ^ exnMessage e ^ "\n"); ``([], ^(term_of_num 0))``);




(*************************************************)
(*************************************************)
(*************************************************)
(*************************************************)
(*************************************************)


(* MTBDD to Rules:simple outout *)
fun mtbdd_to_rules_all_paths bdd_term =
let
  open pairSyntax listSyntax stringSyntax numSyntax;

  fun num_of_term t = Arbnum.toInt (dest_numeral t);

  val (root_term, rest) = dest_pair bdd_term
  val (edges_term, labels_term) = dest_pair rest

  val edges_list = fst (dest_list edges_term)
  val edges = map (fn edge =>
        let
          val (parent, children) = dest_pair edge
          val (left, right) = dest_pair children
        in
          (num_of_term parent, num_of_term left, num_of_term right)
        end) edges_list

  val labels_list = fst (dest_list labels_term)
  val labels = map (fn label =>
        let val (id, data) = dest_pair label
        in (num_of_term id, data) end) labels_list

  fun get_var_name node_data =
      let
        val (_, args) = strip_comb node_data
        val arg = hd args
        val (some_part, _) = dest_pair arg
        val (_, some_args) = strip_comb some_part
        val str_term = hd some_args
      in
        stringSyntax.fromHOLstring str_term
      end

  fun get_action node_data =
      let
        val (_, args) = strip_comb node_data
        val arg = hd args
      in
        fst (dest_pair arg)
      end

  fun node_type node_data =
      let val (const, _) = strip_comb node_data
      in #Name (dest_thy_const const) end

  (* DFS: TRUE branch first, then FALSE branch *)
  fun collect_paths start =
      let
        fun dfs node path visited =
            if List.exists (fn n => n = node) visited then []
            else
              let
                val node_data =
                  case List.find (fn (id, _) => id = node) labels of
                      SOME (_, data) => data
                    | NONE => raise Fail ("Node " ^ Int.toString node ^ " not found")

                val ntype = node_type node_data
                val new_visited = node :: visited
              in
                if ntype = "termn" then
                  [(path, node_data)]  (* Don't reverse:keep root-to-leaf order *)
                else if ntype = "non_termn" then
                  let
                    val var_name = get_var_name node_data
                    val (left, right) =
                      case List.find (fn (p, _, _) => p = node) edges of
                          SOME (_, l, r) => (l, r)
                        | NONE => raise Fail ("Children not found: " ^ Int.toString node)

                    (* TRUE first, then FALSE:this gives natural ordering *)
                    val true_paths = dfs left ((var_name, true)::path) new_visited
                    val false_paths = dfs right ((var_name, false)::path) new_visited
                  in
                    true_paths @ false_paths
                  end
                else
                  raise Fail ("Unknown node type: " ^ ntype)
              end
      in
        dfs start [] []
      end

  (* Build predicate:path is already root-to-leaf *)
  fun build_predicate path =
      let
        fun mk_var v = ``(Var ^(stringSyntax.fromMLstring v)) : pred``

        (* Build in reverse to get proper And nesting *)
        fun build_rev [] = ``(True : pred)``
          | build_rev ((v, true)::rest) =
              let val rest_pred = build_rev rest
              in if aconv rest_pred ``(True : pred)`` then mk_var v
                 else ``(And ^(mk_var v) ^rest_pred) : pred`` end
          | build_rev ((v, false)::rest) =
              let val rest_pred = build_rev rest
              in if aconv rest_pred ``(True : pred)`` then ``(Not ^(mk_var v)) : pred``
                 else ``(And (Not ^(mk_var v)) ^rest_pred) : pred`` end
      in
        build_rev (rev path)  (* Reverse to build from root to leaf *)
      end

  val root = num_of_term root_term
  val paths = collect_paths root

  (* Create rules in the order they were found (TRUE branches first) *)
  val rules = map (fn (path, term_data) =>
        (build_predicate path, get_action term_data)) paths

  (* Filter out (True, drop) if we have specific drop rules *)
  fun is_true_drop (pred, act) =
      let
        val (const, args) = strip_comb act
      in
        aconv pred ``(True : pred)`` andalso
        #Name (dest_thy_const const) = "action" andalso
        (case args of
             [pair, _] =>
               let val (cmd, _) = dest_pair pair
               in stringSyntax.fromHOLstring cmd = "drop" end
           | _ => false)
      end

  val has_explicit_drop = List.exists (fn (_, act) =>
          let
            val (const, args) = strip_comb act
          in
            if #Name (dest_thy_const const) = "action" then
              case args of
                  [pair, _] =>
                    let val (cmd, _) = dest_pair pair
                    in stringSyntax.fromHOLstring cmd = "drop" end
                | _ => false
            else false
          end) rules

  val final_rules =
      if has_explicit_drop then
        (* Remove True->drop if we have specific drops *)
        List.filter (fn rule => not (is_true_drop rule)) rules
      else rules  (* Keep it if it's the only drop rule *)

  val rule_terms = map (fn (pred, act) => mk_pair (pred, act)) final_rules
in
  mk_list (rule_terms, type_of (hd rule_terms))
end


(* MTBDD to Rules with or combinations grouped by action *)
fun mtbdd_to_rules_grouped_by_action_simple bdd_term =
let
  open pairSyntax listSyntax stringSyntax numSyntax;

  fun num_of_term t = Arbnum.toInt (dest_numeral t);
  fun fromMLstring s = stringSyntax.fromMLstring s;
  fun fromHOLstring t = stringSyntax.fromHOLstring t;

  val (root_term, rest) = dest_pair bdd_term
  val (edges_term, labels_term) = dest_pair rest

  val edges_list = fst (dest_list edges_term)
  val edges = map (fn edge =>
        let
          val (parent, children) = dest_pair edge
          val (left, right) = dest_pair children
        in
          (num_of_term parent, num_of_term left, num_of_term right)
        end) edges_list

  val labels_list = fst (dest_list labels_term)
  val labels = map (fn label =>
        let val (id, data) = dest_pair label
        in (num_of_term id, data) end) labels_list

  fun get_var_name node_data =
      let
        val (_, args) = strip_comb node_data
        val arg = hd args
        val (some_part, _) = dest_pair arg
        val (_, some_args) = strip_comb some_part
        val str_term = hd some_args
      in
        fromHOLstring str_term
      end

  fun get_action node_data =
      let
        val (_, args) = strip_comb node_data
        val arg = hd args
      in
        fst (dest_pair arg)
      end

  fun node_type node_data =
      let val (const, _) = strip_comb node_data
      in #Name (dest_thy_const const) end

  fun find_children node_id =
      case List.find (fn (p, _, _) => p = node_id) edges of
          SOME (_, left, right) => (left, right)
        | NONE => raise Fail ("find_children: node " ^ Int.toString node_id ^ " not found")

  fun find_node_data node_id =
      case List.find (fn (id, _) => id = node_id) labels of
          SOME (_, data) => data
        | NONE => raise Fail ("find_node_data: node " ^ Int.toString node_id ^ " not found")

  (* Collect paths:keep them in DFS order *)
  fun collect_paths start =
      let
        fun dfs node path visited =
            if List.exists (fn n => n = node) visited then []
            else
              let
                val node_data = find_node_data node
                val ntype = node_type node_data
                val new_visited = node :: visited
              in
                if ntype = "termn" then
                  [(rev path, node_data)]
                else if ntype = "non_termn" then
                  let
                    val var_name = get_var_name node_data
                    val (left, right) = find_children node

                    val left_paths = dfs left ((var_name, true)::path) new_visited
                    val right_paths = dfs right ((var_name, false)::path) new_visited
                  in
                    left_paths @ right_paths
                  end
                else
                  raise Fail ("dfs: unknown node type")
              end
      in
        dfs start [] []
      end

  (* Build minterm *)
  fun build_minterm path =
      let
        fun mk_var_term v = ``(Var ^(fromMLstring v)) : pred``

        fun build_conj [] = ``(True : pred)``
          | build_conj [(v, true)] = mk_var_term v
          | build_conj [(v, false)] = ``(Not ^(mk_var_term v)) : pred``
          | build_conj ((v, true)::rest) =
              ``(And ^(mk_var_term v) ^(build_conj rest)) : pred``
          | build_conj ((v, false)::rest) =
              ``(And (Not ^(mk_var_term v)) ^(build_conj rest)) : pred``
      in
        build_conj path
      end

  val root = num_of_term root_term
  val paths = collect_paths root  (* In DFS order: leftmost first, rightmost last *)

  (* Group by action:but we need to preserve the order of actions as they first appear *)
  val action_order_list = ref ([] : term list)  (* Order of first appearance *)
  val action_map = ref ([] : (term * term list) list)

  fun add_to_map (path, node_data) =
      let
        val minterm = build_minterm path
        val action = get_action node_data

        fun find_and_update [] =
            (action_map := (action, [minterm]) :: (!action_map);
             action_order_list := action :: (!action_order_list); ())
          | find_and_update ((a, preds)::rest) =
              if aconv a action then
                (action_map := (a, minterm::preds) :: rest; ())
              else
                (find_and_update rest; ())
      in
        find_and_update (!action_map)
      end

  val _ = List.app add_to_map paths

  (* Combine with OR *)
  fun combine_group (action, preds) =
      let
        (* Remove duplicates *)
        val unique =
            let
              fun distinct [] acc = acc
                | distinct (x::xs) acc =
                    if List.exists (fn y => aconv x y) acc
                    then distinct xs acc
                    else distinct xs (x::acc)
            in
              distinct preds []
            end

        val combined =
            case unique of
                [] => ``(True : pred)``
              | [p] => p
              | p1::p2::rest =>
                  let
                    val init = ``(Or ^p1 ^p2) : pred``
                    fun fold acc [] = acc
                      | fold acc (x::xs) = fold ``(Or ^acc ^x) : pred`` xs
                  in
                    fold init rest
                  end
      in
        (combined, action)
      end

  (* Create rules in the order actions first appear in the path traversal *)
  val rules =
      let
        fun process_order [] acc = rev acc
          | process_order (act::rest) acc =
              case List.find (fn (a, _) => aconv a act) (!action_map) of
                  SOME (_, preds) =>
                    process_order rest (combine_group (act, preds) :: acc)
                | NONE => process_order rest acc
      in
        process_order (rev (!action_order_list)) []  (* Reverse because we added in reverse order *)
      end

  (* Now rules are in the order actions first appear in DFS traversal *)
  (* Build result *)
  fun build_list [] = ``[] : action_policy_type``
    | build_list ((pred, act)::rest) =
        ``(^(pred), ^(act)) :: ^(build_list rest)``

in
  build_list rules
end


(* best policy output from BDD *)
fun mtbdd_to_rules bdd_term =
let
  open pairSyntax listSyntax stringSyntax numSyntax;

  fun num_of_term t = Arbnum.toInt (dest_numeral t);

  val (root_term, rest) = dest_pair bdd_term
  val (edges_term, labels_term) = dest_pair rest

  val edges_list = fst (dest_list edges_term)
  val edges = map (fn edge =>
        let
          val (parent, children) = dest_pair edge
          val (left, right) = dest_pair children
        in
          (num_of_term parent, num_of_term left, num_of_term right)
        end) edges_list

  val labels_list = fst (dest_list labels_term)
  val labels = map (fn label =>
        let val (id, data) = dest_pair label
        in (num_of_term id, data) end) labels_list

  fun get_var_name node_data =
      let
        val (const, args) = strip_comb node_data
        val const_name = #Name (dest_thy_const const)
      in
        if const_name = "non_termn" then
          let
            val arg = hd args
            val (some_part, _) = dest_pair arg
            val (_, some_args) = strip_comb some_part
            val str_term = hd some_args
          in
            stringSyntax.fromHOLstring str_term
          end
        else
          raise Fail ("Not a non-terminal node: " ^ const_name)
      end

  fun get_action node_data =
      let
        val (const, args) = strip_comb node_data
        val const_name = #Name (dest_thy_const const)
      in
        if const_name = "termn" then
          let
            val first_arg = hd args
            val (actual_action, _) = dest_pair first_arg
                handle _ => (first_arg, ``()``)
          in
            actual_action
          end
        else
          raise Fail ("Not a terminal node: " ^ const_name)
      end

  fun node_type node_data =
      let 
        val (const, _) = strip_comb node_data
        val const_name = #Name (dest_thy_const const)
      in
        const_name
      end

  fun is_terminal node_data = node_type node_data = "termn"

  val root_id = num_of_term root_term

  (* Find all terminals in left-to-right order, remove duplicates *)
  fun dfs_collect node_id =
      let
        val node_data = case List.find (fn (id, _) => id = node_id) labels of
                            SOME (_, data) => data
                          | NONE => raise Fail ("Node not found: " ^ Int.toString node_id)
      in
        if is_terminal node_data then
          [node_id]
        else
          let
            val (left_child, right_child) = 
                  case List.find (fn (src, l, r) => src = node_id) edges of
                      SOME (_, l, r) => (l, r)
                    | NONE => raise Fail ("No edges from node " ^ Int.toString node_id)
          in
            dfs_collect left_child @ dfs_collect right_child
          end
      end

  val terminal_ids = dfs_collect root_id
  val unique_terminals = 
      let
        val seen = ref []
        fun keep_unique [] = []
          | keep_unique (x::xs) = 
              if List.exists (fn y => y = x) (!seen) then keep_unique xs
              else (seen := x :: !seen; x :: keep_unique xs)
      in
        keep_unique terminal_ids
      end

  (* Get left child of a node *)
  fun get_left_child node_id =
      case List.find (fn (src, l, r) => src = node_id) edges of
          SOME (_, left, _) => left
        | NONE => raise Fail ("No edges from node " ^ Int.toString node_id)

  (* Get all parents of a node *)
  fun get_parents node_id =
      List.map (fn (src, _, _) => src)
          (List.filter (fn (_, left, right) => left = node_id orelse right = node_id) edges)

  (* Check if a node can be a rule starting point *)
  fun can_be_rule_start node_id =
      if node_id = root_id then
        true  (* Root can always start a rule *)
      else
        let
          (* Condition 1: All parents reach this node via RIGHT branch *)
          val incoming_edges = List.filter (fn (_, left, right) => 
              left = node_id orelse right = node_id) edges
          
          val all_via_right = List.all (fn (_, left, right) => right = node_id) incoming_edges
          
          (* Condition 2: Node's left child has only this node as parent (via left branch) *)
          val left_child = get_left_child node_id
          val left_child_parents = get_parents left_child
          
          (* Check if left child has exactly one parent AND it's this node via left branch *)
          val left_child_has_single_parent = 
              length left_child_parents = 1 andalso
              hd left_child_parents = node_id andalso
              List.exists (fn (src, left, _) => src = node_id andalso left = left_child) edges
        in
          all_via_right andalso left_child_has_single_parent
        end

  (* Find starting nodes for rules - nodes that can start rules *)
  fun find_rule_starting_nodes target_terminal =
      let
        (* Find all nodes that point to target_terminal via LEFT branch *)
        val left_parents = List.map (fn (src, left, _) => src)
                               (List.filter (fn (_, left, _) => left = target_terminal) edges)
        
        (* For each left parent, find the closest ancestor that can start a rule *)
        fun find_starting_node_for_parent parent_id =
            let
              fun trace_back node_id =
                  if can_be_rule_start node_id then
                    node_id  (* Found a valid starting point *)
                  else if node_id = root_id then
                    root_id  (* Reached root, use it as starting point *)
                  else
                    (* Find parent and continue *)
                    let
                      val parents = get_parents node_id
                    in
                      case parents of
                          [parent] => trace_back parent
                        | _ => raise Fail ("Multiple or no parents for node " ^ Int.toString node_id)
                    end
            in
              trace_back parent_id
            end
        
        (* Also check if terminal is directly at root *)
        val root_start = 
            if target_terminal = root_id then
              [root_id]
            else if List.exists (fn (src, left, _) => src = root_id andalso left = target_terminal) edges then
              [root_id]
            else []
      in
        (* Remove duplicates from starting nodes *)
        let
          val all_starts = root_start @ (map find_starting_node_for_parent left_parents)
          fun remove_dups [] = []
            | remove_dups (x::xs) = 
                if List.exists (fn y => y = x) xs then remove_dups xs
                else x::remove_dups xs
        in
          remove_dups all_starts
        end
      end

  (* Find all paths from a starting node to target terminal *)
  fun find_paths_from_start start_id target_id =
      let
        fun dfs current_id current_path =
            if current_id = target_id then
              [List.rev current_path]  (* Found target *)
            else
              let
                val node_data = case List.find (fn (id, _) => id = current_id) labels of
                                    SOME (_, data) => data
                                  | NONE => raise Fail ("Node not found")
              in
                if is_terminal node_data then
                  []  (* Different terminal *)
                else
                  let
                    val (left_child, right_child) = 
                          case List.find (fn (src, l, r) => src = current_id) edges of
                              SOME (_, l, r) => (l, r)
                            | NONE => raise Fail ("No edges from node")
                    
                    val var_name = get_var_name node_data
                    
                    (* Try left branch *)
                    val left_paths = dfs left_child ((current_id, var_name, true)::current_path)
                    
                    (* Try right branch *)
                    val right_paths = dfs right_child ((current_id, var_name, false)::current_path)
                  in
                    left_paths @ right_paths
                  end
              end
      in
        dfs start_id []
      end

  (* Build rule for a terminal (except last one) *)
  fun build_rule_for_terminal term_id =
      let
        val term_data = case List.find (fn (id, _) => id = term_id) labels of
                            SOME (_, data) => data
                          | NONE => raise Fail ("Terminal not found")
        val action = get_action term_data
        
        (* Find starting nodes for rules *)
        val starting_nodes = find_rule_starting_nodes term_id
        
        (* For each starting node, find paths to terminal *)
        val all_paths = 
            List.concat (map (fn start_id => find_paths_from_start start_id term_id) starting_nodes)
        
        (* Convert a path to predicate: AND of variables where we took LEFT branch *)
        fun path_to_predicate path =
            let
              val positive_vars = List.map (fn (_, var_name, _) => var_name)
                                   (List.filter (fn (_, _, decision) => decision) path)
              
              fun build_and [] = ``(True : pred)``
                | build_and [var] = ``(Var ^(stringSyntax.fromMLstring var)) : pred``
                | build_and (var::vars) =
                    let
                      val first_pred = ``(Var ^(stringSyntax.fromMLstring var)) : pred``
                      val rest_pred = build_and vars
                    in
                      if aconv rest_pred ``(True : pred)`` then
                        first_pred
                      else
                        ``(And ^first_pred ^rest_pred) : pred``
                    end
            in
              build_and positive_vars
            end
        
        (* Convert all paths to predicates *)
        val predicates = map path_to_predicate all_paths
        
        (* Remove duplicate predicates *)
        val unique_predicates =
            let
              fun remove_dups [] = []
                | remove_dups (p::ps) =
                    if List.exists (fn q => aconv p q) ps then remove_dups ps
                    else p::remove_dups ps
            in
              remove_dups predicates
            end
        
        (* Combine unique predicates with OR *)
        val final_predicate =
            case unique_predicates of
                [] => ``(True : pred)``
              | [p] => p
              | p::ps => List.foldl (fn (pred, acc) => ``(Or ^acc ^pred) : pred``) p ps
      in
        (final_predicate, action)
      end

  (* Build all rules - last terminal gets True *)
  fun build_rules [] = []
    | build_rules terminals =
      let
        val num_terms = length terminals
        fun build idx remaining =
            case remaining of
                [] => []
              | [term_id] =>  (* Last terminal gets True *)
                  let
                    val term_data = case List.find (fn (id, _) => id = term_id) labels of
                                        SOME (_, data) => data
                                      | NONE => raise Fail ("Terminal not found")
                    val action = get_action term_data
                  in
                    [(``(True : pred)``, action)]
                  end
              | term_id::rest =>
                  let
                    val rule = build_rule_for_terminal term_id
                  in
                    rule :: build (idx+1) rest
                  end
      in
        build 0 terminals
      end

  val rules = build_rules unique_terminals

  val rule_terms = 
      if null rules then
        listSyntax.mk_list ([], ``:pred # action``)
      else
        let
          val rule_pairs = map (fn (pred, act) => mk_pair (pred, act)) rules
          val pair_type = type_of (hd rule_pairs)
        in
          listSyntax.mk_list (rule_pairs, pair_type)
        end
  
in
  rule_terms
end



end

(*
(* Individual table generation *)
val result_a = find_paths_for_group_fixed bdd_term1 groupings_term1 "a";
val result_b = find_paths_for_group_fixed bdd_term1 groupings_term1 "b";
val actions = generate_action_table bdd_term1;

(* Complete table generation *)
val result_2_groups = bdd_to_tables_iterative bdd_term1 groupings_term1;

(* Test with 3 groups *)
val groupings_3 = ``[("group1",["x"]); ("group2",["y"]); ("group3",["z"])]``;
val result_3_groups = bdd_to_tables_iterative bdd_term1 groupings_3;

(* Manual result creation *)
val final_result = create_final_result result_a result_b actions;
*)





