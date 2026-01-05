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
fun find_paths_for_group_with_inputs bdd_term groupings_term group_name input_states =
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


fun bdd_to_tables_iterative bdd_term groupings_term =
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
                    val raw_table = find_paths_for_group_with_inputs 
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







(* MTBDD to Rules:simple outout *)
fun mtbdd_to_rules1 bdd_term =
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
fun mtbdd_to_rules2 bdd_term =
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





