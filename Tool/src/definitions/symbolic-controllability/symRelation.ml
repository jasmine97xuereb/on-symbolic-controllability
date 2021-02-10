open EnvFunctions
open EnvResources
open Queue
open SymResources
open SymEventGenerator
open ExpressionEvaluator
open SatFunction
open SymTransitions
open PrettyPrint
open VisibilityLevel

(* Queue of monitors we still need to exhibit (taking care of the aggregating constraints) *)
let unseen_cms = Queue.create ()

(* Reachable Conditions *)
let rec rc (ms: Ast.Monitor.t list) (sevt: Ast.SymbolicEvent.t) (cs: Ast.Expression.t list): Ast.Expression.t list =
  (* inner_rc generates the relevant conditions for a single monitor given an event *)
  let rec inner_rc (m: Ast.Monitor.t) (evt: Ast.SymbolicEvent.t) (c: Ast.Expression.t list): Ast.Expression.t list =
    match m with
      | Ast.Monitor.Verdict(_) -> []
      | Ast.Monitor.TVar(x) -> get_tvar_conditions x evt c
      | Ast.Monitor.Choice(x) -> (inner_rc x.left evt c) @ (inner_rc x.right evt c)
      (* inner_rc x.right evt (inner_rc x.left evt c)  *)
      | Ast.Monitor.ExpressionGuard(x) -> get_exp_guard_conditions x evt c
      | Ast.Monitor.QuantifiedGuard(x) -> get_quant_guard_conditions x evt c 
      | Ast.Monitor.Conditional(x) -> get_if_conditions x evt c
      | Ast.Monitor.Recurse(x) -> inner_rc x.consume evt c
      | Ast.Monitor.Evaluate(x) -> get_evaluate_conditions x evt c

  and get_tvar_conditions (tvar: Ast.TVar.t) (evt: Ast.SymbolicEvent.t) (c: Ast.Expression.t list): Ast.Expression.t list =
    match TVars.find_opt tvar.tvar !mapTVar with
    | Some m -> inner_rc m evt c
    | None -> []
   
  and get_exp_guard_conditions (m: Ast.Monitor.ExpressionGuard.t) (evt: Ast.SymbolicEvent.t) (c: Ast.Expression.t list): Ast.Expression.t list =
    if (compare_values (reduce_identifier m.label ) (reduce_identifier evt.label ))
    then
      (             
        let b = create_exp_identifier evt.payload.name in
          let op = Ast.Expression.BinaryExp.Compare in
            match (reduce_expression m.payload ) with
            | INT(x) ->
              (let a = Ast.Expression.Literal(Ast.Literal.Int(x)) in
                let cond = add_binary_condition a b op in
                  c @ [cond])
            | BOOL(x) ->
              (let a = Ast.Expression.Literal(Ast.Literal.Bool(x)) in
                let cond = add_binary_condition a b op in
                  c @ [cond]) 
            | STRING(x) ->
              (let a = create_exp_identifier x in
                let cond = add_binary_condition a b op in
                  c @ [cond]) 
            | ERR(x) -> (*it is an expression example <x+1>*) 
              (let a = m.payload in 
                let cond = add_binary_condition a b op in 
                  c @ [cond])
          ) 
      else c 

  and get_quant_guard_conditions (m: Ast.Monitor.QuantifiedGuard.t) (evt: Ast.SymbolicEvent.t) (c: Ast.Expression.t list): Ast.Expression.t list =
    if (compare_values (reduce_identifier m.label ) (reduce_identifier evt.label ))
    then [Ast.Expression.Literal(Bool(true))]
    else c

(* the expression is of the form ExpressionTree since many of the conditions are mutually exclusive *)
and get_if_conditions (m: Ast.Monitor.Conditional.t) (evt: Ast.SymbolicEvent.t) (c: Ast.Expression.t list): Ast.Expression.t list =
  let a = m.condition in 
    let b_true = List.sort_uniq compare (inner_rc m.if_true evt c) in 
      let b_false = List.sort_uniq compare (inner_rc m.if_false evt c) in
        [add_expression_tree a b_true b_false] @ c

  and get_evaluate_conditions (m: Ast.Monitor.Evaluate.t) (evt: Ast.SymbolicEvent.t) (c: Ast.Expression.t list): Ast.Expression.t list =
    let rec sub_all_conds (var: Ast.Expression.t) (to_sub: Ast.Expression.t) (b: Ast.Expression.t list) (c: Ast.Expression.t list): Ast.Expression.t list =
      match b with 
      | [] -> c
      | b1::b2 -> sub_all_conds var to_sub b2 (c @ [substitute_expression b1 var to_sub])  
    in sub_all_conds m.var m.subst (inner_rc m.stmt evt c) c 

  in match ms with
    | [] -> []
    | mon::mons -> ((inner_rc mon sevt cs) @ (rc mons sevt cs))

let rec combnk k lst =
  let rec inner result k lst =
    match k with
    | 0 -> [[]]
    | _ ->
      match lst with
      | []      -> result
      | x :: xs ->
        let rec innermost result f = function
          | []      -> result
          | x :: xs -> innermost ((f x) :: result) f xs
        in
          let new_result = innermost result (fun z -> x :: z) (inner [] (k - 1) xs)
          in
            inner new_result k xs
    in inner [] k lst  


let rec filter_sat (condition_list: Ast.Expression.t list list): Ast.Expression.t list = 
  match condition_list with 
  | [] -> []
  | c::cs ->
    let sat_result = sat c
    in if (fst sat_result) 
        then (snd sat_result) @ (filter_sat cs)
        else filter_sat cs

let rec create_one_combination (cs: Ast.Expression.t list) (indices: int list) (counter: int) (result: Ast.Expression.t list): Ast.Expression.t list = 
  match cs with
  | [] -> result
  | x::xs -> 
    if element_exists_in_list indices counter
    then (create_one_combination xs indices (counter + 1)) (result @ [add_unary_condition x]) 
    else (create_one_combination xs indices (counter + 1)) (result @ [x])   
        
let rec create_all_combinations (indices_list: int list list) (b: Ast.Expression.t list) (cs: Ast.Expression.t list) (to_add: Ast.Expression.t list list): Ast.Expression.t list = 
  match indices_list with
  | [] -> filter_sat (combine (combine to_add cs) b) (*then none of the conditions are negated*)
  | i::[] -> filter_sat (combine (combine to_add (create_one_combination cs i 1 []) ) b) 
  | i::is -> 
    let comb = filter_sat (combine (combine to_add (create_one_combination cs i 1 []) ) b) 
    in (
      match comb with 
      | [] -> (create_all_combinations is b cs to_add)
      | _ -> comb  @ (create_all_combinations is b cs to_add))

(* function that takes as parameter an expression and returns a list of mutually exclusive expressions *)
(* each expression represents a combination *)
(* traverse all expression trees and compute all the possible combinations *)
(* at each node, compute the cartesian product to get all combinations *)

let rec traverse_expression_tree (e: Ast.Expression.t) (c: Ast.Expression.t list): Ast.Expression.t list =
  match e with 
  | Ast.Expression.ExpressionTree(x) ->
    
    let if_true = List.map (fun y -> traverse_expression_tree y (c @ [x.cond])) x.if_true in 
    print_all_messages("true trav at node " ^ pretty_print_evt_list [e] );
    List.iter (fun x -> print_all_messages(pretty_print_evt_list x)) if_true; 
    let ct = final_cart_prod if_true in
    print_all_messages("true cart prod:" ^ pretty_print_evt_list ct);

    let if_false = List.map (fun y -> traverse_expression_tree y (c @ [add_unary_condition x.cond])) x.if_false in 
    let cf = final_cart_prod if_false in
    print_all_messages("false cart prod:" ^ pretty_print_evt_list cf); 

    (* retrieve the all false combination *)
    let get_false = (fun x -> if List.length x > 0 then [List.hd x] else []) in

    let n_c_n_true = get_false ct
    in print_all_messages("all_false of true is ");
    print_all_messages(pretty_print_evt_list n_c_n_true);

    let n_c_n_false = get_false cf
    in print_all_messages("all_false of false is ");
    print_all_messages(pretty_print_evt_list n_c_n_false);

    let all_false = and_list (n_c_n_true @ n_c_n_false) in 
    print_all_messages("all false at node " ^ pretty_print_evt_list [e]);
    print_all_messages(pretty_print_evt_list [all_false]); 
    
    let remove_false = (fun x -> if List.length x > 1 then List.tl x else [])
    in
    (remove_false cf) @ (remove_false ct) @ [all_false]

  | _ -> 
    [add_unary_condition (and_list (c @ [e]))] @ [and_list (c @ [e])]


(* optimisation 1 --> all exp negated but for one, all exp negated*)
(* A list of all the mutually exclusive conditions is returned *)

let rec sc_o1 (var_ass: Ast.Expression.t list): Ast.Expression.t list list = 
  let n_c_n_minus_1_vass = List.map (fun x -> [x]) (var_ass)  (*negate all but for one *)
    in let n_c_n_vass = 
      if (List.length (var_ass)) > 0 
      then List.map (fun x -> create_one_combination var_ass x 1 []) [create_list (List.length (var_ass))] (*negate all*)
      else []
    in (n_c_n_vass @ n_c_n_minus_1_vass)

(* optimisation 2 -- traversing the expression trees *)

and sc_o2 (exp_trees: Ast.Expression.t list): Ast.Expression.t list list = 
  let rec filter (condition_list: Ast.Expression.t list): Ast.Expression.t list = 
    match condition_list with 
    | [] -> []
    | c::cs ->
      let sat_result = sat [c]
      in if (fst sat_result) 
          then (snd sat_result) @ (filter cs)
          else filter cs
  in 
  let t_list = List.map (fun x -> traverse_expression_tree x []) exp_trees in 
  print_all_messages("traversed tree is "); 
  List.iter (fun x -> print_all_messages (pretty_print_evt_list x)) t_list;  
    
  (* compute the generalised cartesian product of the combinations of all expression trees *)
  let traversed_list = final_cart_prod t_list in 
  List.map (fun x -> [x]) (filter traversed_list)

(* [Satisfiably Combinations] returns a list of satisfiable combinations  *)   
(* This function is optimised by partitioning the set of conditions in cs into three *)
(* The first partition contains all expressions which are or contain expression trees *)
(* The second partition contain all expression that are variable assignments *)
(* The third partition contains all other expressions *)
(* A list of all the mutually exclusive conditions from the fst and second paritition is returned *)
(* For the third partition, all the possible combinations are generated as usual *)
(* The combinations of 'n choose n' @ 'n choose n-1' and those of third partition are computed *)
(* The satisfiability is computed for every list of combinations for each k (where k ranges from 0 to n where n is the length of the second patition) *)
(* A list of simplified satisfiable combinations is returned *)

and sc (b: Ast.Expression.t list) (cs: Ast.Expression.t list) (result: Ast.Expression.t list list): Ast.Expression.t list =
  let partition = List.partition check_contains_expression_tree cs 
    in let exp_trees = fst partition
    in let partition = List.partition check_comparison (snd partition)
    in let var_ass = fst partition 
    in let others = snd partition
    in 
    print_all_messages("Exp partition is " ^ pretty_print_evt_list exp_trees);
    print_all_messages("Equal partition is " ^ pretty_print_evt_list var_ass);
    print_all_messages("Others partition is " ^ pretty_print_evt_list others);

    let exp_combs = sc_o2 exp_trees   
    in let vass_combs = sc_o1 var_ass
    in let num_list = create_list (List.length others)

    in let fst_comb = combine_ll exp_combs vass_combs

    in 
    print_all_messages("fst comb are "); 
    List.iter (fun x -> print_all_messages (pretty_print_evt_list x)) fst_comb;  
    
    let rec combinations (n:int) (to_add: Ast.Expression.t list list) = 
      match n with
      | 0 -> filter_sat (combine (combine to_add b) (others)) (*in "n choose 0" none of the conditions are negated*)
      | n -> (create_all_combinations (combnk n num_list) b (others) to_add) @ (combinations (n-1) to_add)

    in combinations (List.length others) fst_comb 

(* A constrained monitor-set <b,M> symbolically potentially reaches a verdict spr(<b,M>,w) if the monitor set M can immediately reach a verdict without requiring tau transitions *)
let rec spr (cms: Ast.Expression.t list * Ast.Monitor.t list) (verdict_list: int list): bool =
  match (snd cms) with (*match monitor list*)
    | [] -> (match (List.length verdict_list) with (*if no monitors, check the list of potential verdicts*) 
      | 1 -> true (*one verdict reached*)
      | _ -> false 
    ) (*can only reach one verdict - either 1 or 2*) 

    | elt::elts -> (match elt with (*there are montiors left to analyse*)
      (* Check that the monitor is actually a verdict, and match the verdict.
          If the verdicts match then the monitor is can potentially reach a verdict, else it doesn't *)
      | Ast.Monitor.Verdict(x) -> (match x.verd with
          (* acceptance verdict *)
          | ONE -> 
            if (element_exists_in_list verdict_list 1)
            then spr (fst cms, elts) verdict_list (*verdict already expsts in verdict_list, check other monitors in M*)
            else spr (fst cms, elts) (verdict_list @ [1]) (*add verdict to verdict_list and check other monitors in M*)
          (*reject verdict*)
          | TWO -> 
            if (element_exists_in_list verdict_list 2)
            then spr (fst cms, elts) verdict_list
            else spr (fst cms, elts) (verdict_list @ [2])
          (*anything else - note that inconclusive verdicts are not externally observable*)
          | _ -> 
            if (element_exists_in_list verdict_list 0)
            then spr (fst cms, elts) verdict_list
            else spr (fst cms, elts) (verdict_list @ [0]))

      (* If the monitor is not a verdict, then the case holds trivially *)
      | _ -> 
        if (element_exists_in_list verdict_list 0)
        then spr (fst cms, elts) verdict_list
        else spr (fst cms, elts) (verdict_list @ [0])
    ) 

(*return a tuple made up of a boolean value and the simplified boolean condition *)
(*the second element of the tuple is always [] whenver spa is false *)
let rec spa (cms: Ast.Expression.t list * Ast.Monitor.t list) (evt: Ast.SymbolicEvent.t) (c: Ast.Expression.t) (spa_list: int list): bool =
    let rec check_all_conds (mon_list:Ast.Monitor.t list) = 
      match mon_list with
      | [] -> false
      | m1::m2 ->  
        (*use simplified boolean condition returned by sat*)
        match sym_reduce m1 (fst cms) evt c  with 
          | REDUCED(x)::_ -> true (*if one monitor reduces it is enough*)
          | ERROR(x)::xs -> 
            let rec check_remaining xs = 
              match xs with 
              | [] -> check_all_conds m2
              | REDUCED(y)::ys -> true
              | _::ys -> check_remaining ys  
            in check_remaining xs
          | [] -> false
            
    in check_all_conds (snd cms)

let rec print_all (a) = 
  match a with 
  | [] -> ()
  | x::xs -> 
    print_all xs; 
    print_all_messages (print_identifier_string x)

let rec print_components (comp: (Ast.Expression.t list * Vars.t) list) = 
  match comp with 
  | [] -> ()
  | c::cs -> 
    (* get the string representation of variable set *)
    let v_string = List.fold_right (fun x final -> x ^ " " ^ final) (List.map print_identifier_string (Vars.elements (snd c))) ""
      in let evt_string = pretty_print_evt_list (fst c)
        in print_all_messages("<" ^ evt_string ^ ", " ^ v_string ^ ">");
        print_components cs

let rec get_components (b: Ast.Expression.t list) (comp: (Ast.Expression.t list * Vars.t) list): (Ast.Expression.t list * Vars.t) list =
  let rec connected (e: Ast.Expression.t) (v: Vars.t) (comp: (Ast.Expression.t list * Vars.t) list): (Ast.Expression.t list * Vars.t) list =
    (match comp with
    | [] -> [[e], v]
    | c::cs -> 
      if Vars.is_empty (Vars.inter (snd c) v)
      then [c] @ (connected e v cs)
      else [[e] @ (fst c), Vars.union (snd c) v] @ cs
    )
    in match b with 
    | [] -> comp
    | b::bs -> 
      let rec inner_comp (b: Ast.Expression.t) (comp: (Ast.Expression.t list * Vars.t) list) = 
        match b with 
        | Ast.Expression.BinaryExp(x) -> 
          (match x.operator with 
          | Ast.Expression.BinaryExp.And -> inner_comp x.arg_rt (inner_comp x.arg_lt comp)
          (* | _ -> connected b (fv ([x.arg_lt], []) Vars.empty) comp *)
          | _ -> connected b (fv ([x.arg_lt], []) (fv ([x.arg_rt], []) Vars.empty)) comp
          )
        | _ -> connected b (fv ([b], []) Vars.empty) comp
      in get_components bs (inner_comp b comp)
 
let prt (comp: (Ast.Expression.t list * Vars.t) list) (v: Vars.t): (Ast.Expression.t list * Vars.t) list =
  let rec filter_components (comp: (Ast.Expression.t list * Vars.t) list): (Ast.Expression.t list * Vars.t) list =
    match comp with 
    | [] -> []
    | c::cs -> 
      if Vars.is_empty (Vars.inter (snd c) v) 
      then filter_components cs
      else [c] @ (filter_components cs)
    
    in let fc = filter_components comp
      in print_all_messages ("Components after filtering are: ");
      print_components fc;
      fc

(* function to simplify the boolean conditions *)
(* convert each component into dnf *)
(* for each component ck = d1 \/ ... \/ dn discard ck if either i. or ii. *)
(*  i. exists di s.t. chn(di) inter V = { }  *)
(*  ii. for all i in [n] . value not in chn(di) and chn(di) inter V = {x} (i.e. singleton) *)

let smp (comp: (Ast.Expression.t list * Vars.t) list) (v: Vars.t): (Ast.Expression.t list * Vars.t) list =
  let rec filter_components (comp: (Ast.Expression.t list * Vars.t) list): (Ast.Expression.t list * Vars.t) list =
    let rec inner_filter (c: (Ast.Expression.t list * Vars.t)): (Ast.Expression.t list * Vars.t) list =
      (* convert the component to DNF form *)
      let dnf_comp = exp_list_to_dnf (fst c) in
      (* print_endline("component is: " ^ pretty_print_evt_list (fst c)); *)
      (* print_endline("dnf component is: " ^ pretty_print_evt_list dnf_comp); *)
      let f_comp = snd c in
      
      (* returns true if at least one of the expression does not have free vars in common with v *)
      if List.exists (fun d -> (Vars.is_empty (Vars.inter v (fv ([d], []) Vars.empty))) && fst (sat [d])) dnf_comp
      then (
        (* print_endline("method 1 -- di with fv(di) cap V = empty");  *)
        [])
      else
        (* returns true if one of the expressions is not linked to a concrete value and v inter fv of componenent is a singleton *)
        if (List.length (Vars.elements (Vars.inter v f_comp)) == 1) && (List.exists (fun d -> (not (chn d)) && fst (sat [d])) dnf_comp)         
        then ( 
          (* print_endline("method 2 -- di with fv(di) cap V = x and not chn");  *)
          [])
        else [c] 

      in match comp with 
      | [] -> []
      | c::cs -> inner_filter c @ filter_components cs

    in filter_components comp
        
let cns (b: Ast.Expression.t list) (mon_list: Ast.Monitor.t list): Ast.Expression.t list =
  (* V = fv(saft(M, B, $)) *)
  let v = fv ([], mon_list) Vars.empty  
    in print_all_messages("free V: ");
    print_all (Vars.elements v);   

    (* if v = empty, all the boolean conditions can be removed, otherwise partition and simplify *)
    if Vars.is_empty v 
    then []
    else (
      let components = get_components b []
        in print_all_messages("All components are: ");
        print_components components;
        let fc = prt components v
          in 
          let sfc = smp fc v
            in print_all_messages("");
            List.fold_right (fun x final -> (fst x) @ final) sfc [] 
    )  

let rec osaft (cm: (Ast.Expression.t list * Ast.Monitor.t list)) (evt: Ast.SymbolicEvent.t) (c: Ast.Expression.t) (relation: (Ast.Expression.t list * Ast.Monitor.t list) list) =
  let rec saft_aux (m: Ast.Monitor.t list) (res: (Ast.Expression.t list * Ast.Monitor.t list)) =

    let rec new_monitors mon_list = 
      match mon_list with
      | [] -> []
      | REDUCED(x)::m2 -> [x] @ (new_monitors m2)
      | ERROR(x)::m2 -> [add_verdict 0] @ (new_monitors m2)
    in 

    (match m with
    | [] -> 
        print_all_messages ("\nReturned by SAFT " ^ (pretty_print_monitor_list_string (snd res)));
        let optimized_res = ((cns (fst res) (snd res)), (snd res)) in
        print_all_messages ("cond before was " ^ (pretty_print_evt_list (fst res)));
        print_all_messages ("cond after is " ^ (pretty_print_evt_list (fst optimized_res)));
        print_all_messages ("\nOptimized by OSAFT " ^ (pretty_print_monitor_list_string (snd optimized_res)));
        (Queue.push optimized_res unseen_cms)
    | ms::mss -> (
        let resulting_mons = sym_reduce ms (fst cm) evt c 
        in saft_aux mss ([c], (add_monitors_not_in_list (snd res) (new_monitors resulting_mons))) (*use add_monitors_not_in_list to make sure not to add duplicates*)              
    ))
  in saft_aux (snd cm) ([],[])

(*get the next tuple that is not already in the relation*)
let rec get_next_unseen (relation: (Ast.Expression.t list * Ast.Monitor.t list) list): (Ast.Expression.t list * Ast.Monitor.t list) = 
  if (Queue.is_empty unseen_cms) 
  then ([],[]) 
  else(
    let next_m = Queue.pop unseen_cms in
      if tuple_exists_in_relation next_m relation 
      then (
        print_all_messages ("it already exists in the relation");
        get_next_unseen relation
      )
      else (
        print_all_messages ("it does not exist");
        next_m
      )    
  ) 

(*check if the tuple is already in the relation, if not add it*)
let rec add_to_relation (relation: (Ast.Expression.t list * Ast.Monitor.t list) list) (to_add: (Ast.Expression.t list * Ast.Monitor.t list)): (Ast.Expression.t list * Ast.Monitor.t list) list =
  print_all_messages ("adding " ^ (pretty_print_monitor_list_string (snd to_add)));
  if not (tuple_exists_in_relation to_add relation)
  then (
    print_all_messages ("not there"); 
    [to_add] @ relation)
  else (
    print_all_messages ("there"); 
    relation)

let isSymControllable (mon: Ast.Monitor.t list) =

  let rec computeSymRelation (cm: (Ast.Expression.t list * Ast.Monitor.t list)) (relation: (Ast.Expression.t list * Ast.Monitor.t list) list): bool =

    let relation = add_to_relation relation cm in 
    print_all_messages ("RELATION IS " ^ pretty_print_relation relation ^ "\n---------------------");

    (*check symbolic potential reach*)
    if (spr cm []) 
    then(
        print_all_messages ("MONITOR TO EVAL IS " ^ pretty_print_monitor_list_string (snd cm));
		
        let frsh_v = fresh(fv cm (Vars.empty)) in
          let sym_events = generateSymEventsForMonitorList (snd cm) frsh_v [] in
            print_all_messages (pretty_print_sym_event sym_events);
            
            let rec exhibitSymEvents (sym_events: Ast.SymbolicEvent.t list): bool =
              match sym_events with
                |[] ->             
                  if (Queue.is_empty unseen_cms)
                  then( 
					          print_basic ("---------------------\nThe Witness Relation is \n" ^ pretty_print_relation relation);
                    true)
                  else 
                    (let next_m = get_next_unseen relation in 
                      match next_m with 
                      | ([],[]) -> (
                        print_basic ("---------------------\nThe Witness Relation is \n" ^ pretty_print_relation relation);
						            true)
                      | _-> computeSymRelation next_m relation
                    )
                |s::ss ->
                  print_all_messages ("Reachable Conditions (RC) for SymbolicEvent " ^ pretty_print_sym_event [s]);
                  (*List.sort_uniq drops all the duplicate elements in the list returned by rc*)
                  let c = List.sort_uniq compare (rc (snd cm) s []) in (
                    print_all_messages (pretty_print_evt_list c);
                    
                    let sat_cond = sc (fst cm) c [] in 
                                        
                      let rec spa_all_options conds = 
                        match conds with 
                         | [] -> print_all_messages ("there are no more conditions to analyse")
                         | sc1::sc2 -> 
							              let spa_result = spa cm s sc1 [] in 	
                              (* print_all_messages ("SPA For condition " ^ (pretty_print_evt_list sc1) ^ " is " ^ string_of_bool (spa_result));       *)
                              if spa_result (*if spa is true, then saft must also hold, otherwise go to the next condition*)
                              then (
                                osaft cm s sc1 relation;
                                spa_all_options sc2
                              )
                              else spa_all_options sc2
                        in spa_all_options sat_cond;  
                  );
                              
                  exhibitSymEvents ss;
            in exhibitSymEvents sym_events;
	) 
    else (
		false 
    )      
  in (computeSymRelation ([], mon) [([], mon)])
