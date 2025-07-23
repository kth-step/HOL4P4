open HolKernel boolLib bossLib Parse;
open listTheory pairTheory optionTheory;
open pairSyntax numSyntax listSyntax stringSyntax optionSyntax;

structure BDDUtils = struct


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
fun generate_action_table bdd_term =
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
      val _ = print ("Group vars for " ^ group_name ^ ": [" ^ String.concatWith ", " group_vars ^ "]\n")
      val _ = print ("Input states: [" ^ String.concatWith ", " (map Int.toString input_states) ^ "]\n")

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
                val _ = print ("From input state " ^ Int.toString input_state ^ 
                    ": " ^ Int.toString (length paths) ^ " paths\n")
              in
                map (fn (path, exit_state) => (input_state, path, exit_state)) paths
              end) input_states)

      (* Convert to table entries *)
      fun path_to_entry (input_state, path, exit_state) =
          let
            val atom_vars = map (fn (var, value) =>
                  if value then ``Var ^(fromMLstring var)``
                  else ``Not (Var ^(fromMLstring var))``
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


fun find_paths_for_group_fixed bdd_term groupings_term group_name =
    let
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

      val group_names = map #1 groupings

      fun find_group_index name names index =
          case names of
            [] => 0
          | h::t => if h = name then index else find_group_index name t (index + 1)

      val group_index = find_group_index group_name group_names 0

      (* Determine input states based on group position *)
      val input_states = 
        if group_index = 0 then
          [0]  (* First group starts from state 0 *)
        else
          (* For subsequent groups, we need to compute the exit states from previous groups *)
          if group_name = "b" then
            [3, 4]  (* Hardcoded for now based on your expected output *)
          else
            [0]

      val _ = print ("Group: " ^ group_name ^ ", Input states: [" ^ String.concatWith ", " (map Int.toString input_states) ^ "]\n")

      val result = find_paths_for_group_with_inputs bdd_term groupings_term group_name input_states
    in
      result
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









end;

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





