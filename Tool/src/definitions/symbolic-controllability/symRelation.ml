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

  and get_if_conditions (m: Ast.Monitor.Conditional.t) (evt: Ast.SymbolicEvent.t) (c: Ast.Expression.t list): Ast.Expression.t list =
    let a = m.condition in 
      let b_true = (inner_rc m.if_true evt c) in 
        let b_false = (inner_rc m.if_false evt c) in
          let op = Ast.Expression.BinaryExp.And in
            let rec add_all_conds (a: Ast.Expression.t) (b: Ast.Expression.t list) (c: Ast.Expression.t list): Ast.Expression.t list =
            match b with 
            | [] -> c 
            | b1::b2 ->
              add_all_conds a b2 (c @ [add_binary_condition a b1 op])  
          in
          match b_true, b_false with 
          | [], [] -> [a] @ [(add_unary_condition a)] @ c 
          | _ ->
            (match m.condition with
              | Ast.Expression.BinaryExp(x) -> 
                (add_all_conds a b_true c) @ (add_all_conds (add_unary_condition a) b_false c)
              | Ast.Expression.UnaryExp(x) ->
                (add_all_conds a b_true c) @ (add_all_conds (x.arg) b_false c)
              | _ -> c)

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
  print_all_messages("choose "^string_of_int(k));
  let rec inner result k lst =
    match k with
    | 0 -> [[]]
    | _ ->
      match lst with
      | [] -> result
      | x :: xs ->
        let rec innermost result f = function
          | [] -> result
          | x :: xs -> innermost ((f x) :: result) f xs
        in let new_result = innermost result (fun z -> x :: z) (inner [] (k - 1) xs)
      in inner new_result k xs
    in inner [] k lst  

let rec filter_sat (condition_list: Ast.Expression.t list) = 
  (* print_endline("filtering" ^ pretty_print_evt_list condition_list); *)
  let sat_result = sat condition_list
  in if (fst sat_result) 
  then snd sat_result
  else []

let rec create_one_combination (cs: Ast.Expression.t list) (indices: int list) (counter: int) (result: Ast.Expression.t list): Ast.Expression.t list = 
  match cs with
  | [] -> result
  | x::xs -> 
    if element_exists_in_list indices counter
    then (create_one_combination xs indices (counter + 1)) (result @ [add_unary_condition x]) 
    else (create_one_combination xs indices (counter + 1)) (result @ [x])   

let rec create_all_combinations (indices_list: int list list) (b: Ast.Expression.t list) (cs: Ast.Expression.t list): Ast.Expression.t list list = 
  (* print_endline("all combs for"); *)
  (* List.iter (fun x -> print_string(" ------ "); List.iter (fun y -> print_string ((string_of_int y) ^ " ")) x) indices_list; *)
  match indices_list with
  | [] -> [filter_sat (b @ cs)] (*then none of the conditions are negated*)
  | i::[] -> [filter_sat (b @ (create_one_combination cs i 1 []))] 
  | i::is -> 
    let combination = [filter_sat (b @ (create_one_combination cs i 1 []))] 
    in (
      match combination with 
      | [[]] -> (create_all_combinations is b cs)
      | _ -> (
      (* print_endline("new comb is "); *)
      (* List.iter (fun x -> print_string ("[" ^(pretty_print_evt_list x) ^ "] " )) combination; *)
      combination @ (create_all_combinations is b cs)))

          
(* * [Satisfiably Combinations] returns a list of satisfiable combinations *)
(* b stores the list of boolean conditions of the constrained-monitor set *)
(* cs stores the list of reachable boolean condition *)
(* returns a list of lists of boolean condition where each list represents boolean conditions added together usings ANDs *)
let rec sc (b: Ast.Expression.t list) (cs: Ast.Expression.t list) (result: Ast.Expression.t list list): Ast.Expression.t list list =
  (*create a list of consecutive numbers*)
  let rec create_list (n:int): int list =
    match n with 
      | 0 -> []
      | some_n -> some_n :: (create_list (n-1))  
    in let num_list = create_list ((List.length cs)) 

    in let rec combinations (n: int): Ast.Expression.t list list = 
      match n with 
      | 0 -> [filter_sat (b @ cs)] (*in "n choose 0" none of the conditions are negated*)
      | n ->  (create_all_combinations (combnk n num_list) b cs) @ (combinations (n-1))
    
      in
      (* remove any possible empty lists and duplicates *)
      List.sort_uniq compare (List.filter (fun x -> List.length x != 0) (combinations (List.length cs)))

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
let rec spa (cms: Ast.Expression.t list * Ast.Monitor.t list) (evt: Ast.SymbolicEvent.t) (c: Ast.Expression.t list) (spa_list: int list): bool =
    let rec check_all_conds (mon_list:Ast.Monitor.t list) = 
      match mon_list with
      | [] -> false
      | m1::m2 ->  
        (*use simplified boolean condition returned by sat*)
        match sym_reduce m1 (fst cms) evt c  with 
          | REDUCED(x)::_ -> true (*if one monitor reduces it is enough*)
          | ERROR(x)::xs -> 
            (let rec check_remaining xs = 
              match xs with 
              | [] -> check_all_conds m2
              | REDUCED(y)::ys -> true
              | _::ys -> check_remaining ys  
            in check_remaining xs)
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
  

(* function get_components, given a list of expressions, returns a list of components *)
(* each component is a pair made up of an expression list and corr. free variables *)
(* function connected checks whether e is connected to any other that is already in comp*)
(*  if is connected, merge it *)
(*  else add a new component *)

let rec get_components (b: Ast.Expression.t list) (comp: (Ast.Expression.t list * Vars.t) list): (Ast.Expression.t list * Vars.t) list =
  match b with 
  | [] -> comp
  | b::bs ->
    let v = fv ([b], []) Vars.empty
      in 
      let rec connected (e: Ast.Expression.t) (comp: (Ast.Expression.t list * Vars.t) list): (Ast.Expression.t list * Vars.t) list = 
        match comp with
        | [] -> [([e], v)]
        | c::cs -> 
          if Vars.is_empty (Vars.inter (snd c) v)
          then [c] @ (connected e cs)
          else [[e] @ (fst c), Vars.union (snd c) v] @ cs
      in get_components bs (connected b comp)


let rec get_components_v (b: Ast.Expression.t list) (v: Vars.t) (comp: (Ast.Expression.t list * Vars.t) list): (Ast.Expression.t list * Vars.t) list =
  match b with 
  | [] -> comp
  | b::bs ->
    let b_v = fv ([b], []) Vars.empty
      in let rec connected (e: Ast.Expression.t) (comp: (Ast.Expression.t list * Vars.t) list): (Ast.Expression.t list * Vars.t) list = 
      match comp with
      | [] -> [([e], b_v)]
      | c::cs -> 
        if Vars.subset (Vars.inter (snd c) b_v) v
        then [c] @ (connected e cs)
        else [[e] @ (fst c), Vars.union (snd c) b_v] @ cs
        in get_components_v bs v (connected b comp)
    
            
(* discard all the components that do not have any free variables in common with v *)
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

(* let rec clause1 (comp: (Ast.Expression.t list * Vars.t) ) (v: Vars.t): (Ast.Expression.t list * Vars.t) =
  let rec inner_c1 (b: Ast.Expression.t list) = 
    match b with
    | [] -> []
    | b::bs -> 
      let disjunction_b = split_or [b] in
      if List.length disjunction_b > 1
      then if List.exists (fun d -> (Vars.is_empty (Vars.inter v (fv ([d], []) Vars.empty))) && fst (sat [d])) (disjunction_b)
      then inner_c1 bs
      else [b] @ (inner_c1 bs)
      else [b] @ (inner_c1 bs)
  in ((inner_c1 (fst comp)), snd comp) *)

let rec clause1 (comp: (Ast.Expression.t list * Vars.t) ) (v: Vars.t): (Ast.Expression.t list * Vars.t) =
  let dnf = exp_list_to_dnf (fst comp) in 
  print_endline("dnf is " ^ pretty_print_evt_list dnf);
  if List.exists (fun d -> (Vars.is_empty (Vars.inter v (fv ([d], []) Vars.empty))) && fst (sat [d])) (dnf)
  then ([],Vars.empty)
  else comp
  (* let rec inner_c1 (b: Ast.Expression.t list) = 
    match b with
    | [] -> []
    | b::bs -> 
      let disjunction_b = split_or [b] in
      if List.length disjunction_b > 1
      then if List.exists (fun d -> (Vars.is_empty (Vars.inter v (fv ([d], []) Vars.empty))) && fst (sat [d])) (disjunction_b)
      then inner_c1 bs
      else [b] @ (inner_c1 bs)
      else [b] @ (inner_c1 bs)
  in ((inner_c1 (fst comp)), snd comp) *)

let rec clause2 (comp: (Ast.Expression.t list * Vars.t)) (v: Vars.t): (Ast.Expression.t list * Vars.t) =
  let dnf = exp_list_to_dnf (fst comp) in 
  if List.exists (fun d -> 
    let inter = (Vars.elements (Vars.inter v (fv ([d], []) Vars.empty))) in
    if List.length inter == 1 then (uch (List.hd inter) d) && fst (sat [d])
    else false
  ) dnf
  then ([],Vars.empty)
  else comp


(* let rec clause2 (comp: (Ast.Expression.t list * Vars.t)) (v: Vars.t): (Ast.Expression.t list * Vars.t) =
  let rec inner_c2 (b: Ast.Expression.t list) = 
    match b with
    | [] -> []
    | b::bs -> 
      let disjunction_b = split_or [b] in
      if List.length disjunction_b > 1
      then if List.exists (fun d -> 
        let inter = (Vars.elements (Vars.inter v (fv ([d], []) Vars.empty))) in
        if List.length inter == 1 then (uch (List.hd inter) d) && fst (sat [d])
        else false
      ) (disjunction_b)

      (* then if List.exists (fun d -> (List.length (Vars.elements (Vars.inter v (fv ([d], []) Vars.empty))) == 1) && (not (chn d)) && fst (sat [d])) (disjunction_b) *)
      then inner_c2 bs
      else [b] @ (inner_c2 bs)
      else [b] @ (inner_c2 bs)
  in 
  let new_c = inner_c2 (fst comp) in 
  if (List.length (Vars.elements (Vars.inter v (fv (new_c, []) Vars.empty))) == 1) && (not (chn (and_list new_c))) && fst (sat new_c)
  then ([],Vars.empty)
  else (new_c, snd comp) *)


let rec smp (b: (Ast.Expression.t list * Vars.t) list) (v: Vars.t): (Ast.Expression.t list * Vars.t) list =
  
  let rec filter_components (b: (Ast.Expression.t list * Vars.t) list): (Ast.Expression.t list * Vars.t) list =
    let rec inner_filter (c: (Ast.Expression.t list * Vars.t)): (Ast.Expression.t list * Vars.t)  =
      
      let after_c1 = clause1 c v in
      (* print_all_messages("after first condition");  *)
      (* print_components([after_c1] ); *)
      
      let after_c2 = clause2 after_c1 v in 
      (* print_endline("after second condition"); *)
      (* print_components( [after_c2] ); *)
      after_c2
    

    in match b with 
    | [] -> []
    | c::cs -> [inner_filter c] @ filter_components cs
    
  in match b with 
  | [] -> []
  | b::bs -> 
    (* print_endline("IN SMP COMP BEFORE IS " ^ pretty_print_evt_list (fst b)); *)
    (* print_endline("IN SMP COMP AFTER " ); *)
    let c = get_components_v (fst b) v [] in 
    print_components c;
    (filter_components c) @ (smp bs v)


let cns (b: Ast.Expression.t list) (mon_list: Ast.Monitor.t list): Ast.Expression.t list =
  (* V = fv(saft(M, B, $)) *)
  let v = fv ([], mon_list) Vars.empty  
    in print_all_messages("free V: ");
    print_all (Vars.elements v);   

    (* if v = empty, all the boolean conditions can be removed, otherwise partition and simplify *)
    if Vars.is_empty v 
    then []
    else (
      let b_list = split_and b in
      let components = get_components b_list []
        in print_all_messages("All components are: ");
        print_components components;
        let fc = prt components v
          in let sfc = smp fc v
            in print_all_messages("");
            List.fold_right (fun x final -> (fst x) @ final) sfc [] 
    )
    
let rec osaft (cm: (Ast.Expression.t list * Ast.Monitor.t list)) (evt: Ast.SymbolicEvent.t) (c: Ast.Expression.t list) (relation: (Ast.Expression.t list * Ast.Monitor.t list) list) =
  let rec saft_aux (m: Ast.Monitor.t list) (res: (Ast.Expression.t list * Ast.Monitor.t list)) =

    let rec new_monitors mon_list = 
      match mon_list with
      | [] -> []
      | REDUCED(x)::m2 -> [x] @ (new_monitors m2)
      | ERROR(x)::m2 -> [add_verdict 0] @ (new_monitors m2)
    in 

    (match m with
    | [] -> 
        (* print_all_messages ("\nReturned by SAFT " ^ (pretty_print_monitor_list_string (snd res))); *)
        print_all_messages ("\nReturned by SAFT <" ^ pretty_print_evt_list (fst res) ^ ", " ^ pretty_print_monitor_list_string (snd res) ^ ">");
        let optimized_res = ((cns (fst res) (snd res)), (snd res)) in
        print_all_messages ("cond before was " ^ (pretty_print_evt_list (fst res)));
        print_all_messages ("cond after is " ^ (pretty_print_evt_list (fst optimized_res)));
        print_all_messages ("\nOptimized by OSAFT " ^ (pretty_print_monitor_list_string (snd optimized_res)));
        (Queue.push optimized_res unseen_cms)
    | ms::mss -> (
        let resulting_mons = sym_reduce ms (fst cm) evt c 
        in saft_aux mss (c, (add_monitors_not_in_list (snd res) (new_monitors resulting_mons))) (*use add_monitors_not_in_list to make sure not to add duplicates*)              
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
                      (* print_all_messages ("\nSatisfiability Conditions (SC) " ^ (pretty_print_evt_list sat_cond)); *)
                      let sat_cond_string = List.fold_right (fun x final -> final ^ (pretty_print_evt_list x) ^ "\n") sat_cond ""
                      in print_all_messages ("\nSatisfiability Conditions (SC) " ^ sat_cond_string);

                      let rec spa_all_options (conds: Ast.Expression.t list list) = 
                        match conds with 
                         | [] -> print_all_messages ("there are no more conditions to analyse")
                         | sc1::sc2 -> 
                            let spa_result = spa cm s sc1 [] in 
                              print_all_messages ("SPA For condition " ^ (pretty_print_evt_list sc1) ^ " is " ^ string_of_bool (spa_result));      
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











(* open EnvFunctions
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

  and get_if_conditions (m: Ast.Monitor.Conditional.t) (evt: Ast.SymbolicEvent.t) (c: Ast.Expression.t list): Ast.Expression.t list =
    let a = m.condition in 
      let b_true = (inner_rc m.if_true evt c) in 
        let b_false = (inner_rc m.if_false evt c) in
          let op = Ast.Expression.BinaryExp.And in
            let rec add_all_conds (a: Ast.Expression.t) (b: Ast.Expression.t list) (c: Ast.Expression.t list): Ast.Expression.t list =
            match b with 
            | [] -> c 
            | b1::b2 ->
              add_all_conds a b2 (c @ [add_binary_condition a b1 op])  
          in
          match b_true, b_false with 
          | [], [] -> [a] @ [(add_unary_condition a)] @ c 
          | _ ->
            (match m.condition with
              | Ast.Expression.BinaryExp(x) -> 
                (add_all_conds a b_true c) @ (add_all_conds (add_unary_condition a) b_false c)
              | Ast.Expression.UnaryExp(x) ->
                (add_all_conds a b_true c) @ (add_all_conds (x.arg) b_false c)
              | _ -> c)

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
  print_all_messages("choose "^string_of_int(k));
  let rec inner result k lst =
    match k with
    | 0 -> [[]]
    | _ ->
      match lst with
      | [] -> result
      | x :: xs ->
        let rec innermost result f = function
          | [] -> result
          | x :: xs -> innermost ((f x) :: result) f xs
        in let new_result = innermost result (fun z -> x :: z) (inner [] (k - 1) xs)
      in inner new_result k xs
    in inner [] k lst  

let rec filter_sat (condition_list: Ast.Expression.t list) = 
  (* print_endline("filtering"); *)
  let sat_result = sat condition_list
  in if (fst sat_result) 
  then snd sat_result
  else []

let rec create_one_combination (cs: Ast.Expression.t list) (indices: int list) (counter: int) (result: Ast.Expression.t list): Ast.Expression.t list = 
  match cs with
  | [] -> result
  | x::xs -> 
    if element_exists_in_list indices counter
    then (create_one_combination xs indices (counter + 1)) (result @ [add_unary_condition x]) 
    else (create_one_combination xs indices (counter + 1)) (result @ [x])   

let rec create_all_combinations (indices_list: int list list) (b: Ast.Expression.t list) (cs: Ast.Expression.t list): Ast.Expression.t list list = 
  (* print_endline("all combs for"); *)
  (* List.iter (fun x -> print_string(" ------ "); List.iter (fun y -> print_string ((string_of_int y) ^ " ")) x) indices_list; *)
  match indices_list with
  | [] -> [filter_sat (b @ cs)] (*then none of the conditions are negated*)
  | i::[] -> [filter_sat (b @ (create_one_combination cs i 1 []))] 
  | i::is -> 
    let combination = [filter_sat (b @ (create_one_combination cs i 1 []))] 
    in (
      match combination with 
      | [[]] -> (create_all_combinations is b cs)
      | _ -> (
      (* print_endline("new comb is "); *)
      (* List.iter (fun x -> print_string ("[" ^(pretty_print_evt_list x) ^ "] " )) combination; *)
      combination @ (create_all_combinations is b cs)))

          
(* * [Satisfiably Combinations] returns a list of satisfiable combinations *)
(* b stores the list of boolean conditions of the constrained-monitor set *)
(* cs stores the list of reachable boolean condition *)
(* returns a list of lists of boolean condition where each list represents boolean conditions added together usings ANDs *)
let rec sc (b: Ast.Expression.t list) (cs: Ast.Expression.t list) (result: Ast.Expression.t list list): Ast.Expression.t list list =
  (*create a list of consecutive numbers*)
  let rec create_list (n:int): int list =
    match n with 
      | 0 -> []
      | some_n -> some_n :: (create_list (n-1))  
    in let num_list = create_list ((List.length cs)) 

    in let rec combinations (n: int): Ast.Expression.t list list = 
      match n with 
      | 0 -> [filter_sat (b @ cs)] (*in "n choose 0" none of the conditions are negated*)
      | n ->  (create_all_combinations (combnk n num_list) b cs) @ (combinations (n-1))
    
      in
      (* remove any possible empty lists and duplicates *)
      List.sort_uniq compare (List.filter (fun x -> List.length x != 0) (combinations (List.length cs)))

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
let rec spa (cms: Ast.Expression.t list * Ast.Monitor.t list) (evt: Ast.SymbolicEvent.t) (c: Ast.Expression.t list) (spa_list: int list): bool =
    let rec check_all_conds (mon_list:Ast.Monitor.t list) = 
      match mon_list with
      | [] -> false
      | m1::m2 ->  
        (*use simplified boolean condition returned by sat*)
        match sym_reduce m1 (fst cms) evt c  with 
          | REDUCED(x)::_ -> true (*if one monitor reduces it is enough*)
          | ERROR(x)::xs -> 
            (let rec check_remaining xs = 
              match xs with 
              | [] -> check_all_conds m2
              | REDUCED(y)::ys -> true
              | _::ys -> check_remaining ys  
            in check_remaining xs)
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
  
(* function get_components, given a list of expressions, returns a list of components *)
(* each component is a pair made up of an expression list and corr. free variables *)
(* function connected checks whether e is connected to any other that is already in comp*)
(*  if is connected, merge it *)
(*  else add a new component *)
let rec get_components (b: Ast.Expression.t list) (comp: (Ast.Expression.t list * Vars.t) list): (Ast.Expression.t list * Vars.t) list =
  match b with 
  | [] -> comp
  | b::bs -> 
    let v = fv ([b], []) Vars.empty
      in let rec connected (e: Ast.Expression.t) (comp: (Ast.Expression.t list * Vars.t) list): (Ast.Expression.t list * Vars.t) list = 
      match comp with
      | [] -> [[e], v]
      | c::cs -> 
        if Vars.is_empty (Vars.inter (snd c) v)
        then [c] @ (connected e cs)
        else [[e] @ (fst c), Vars.union (snd c) v] @ cs
        in get_components bs (connected b comp)
    
(* discard all the components that do not have any free variables in common with v *)
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
      let dnf_comp = exp_list_to_dnf (fst c) in  (* convert the component to DNF form *)
      let f_comp = snd c in
      (* print_endline("dnf comp is " ^ pretty_print_evt_list dnf_comp); *)
      
      (* returns true if at least one of the expression does not have free vars in common with v *)
      if List.exists (fun d -> (Vars.is_empty (Vars.inter v (fv ([d], []) Vars.empty))) && fst (sat [d])) dnf_comp
      then (print_endline("method 1"); [])
      else
        (* returns true if one of the expressions is not linked to a concrete value and v inter fv of componenent is a singleton *)
        if (List.length (Vars.elements (Vars.inter v f_comp)) == 1) && (List.exists (fun d -> (not (chn d)) && fst (sat [d])) dnf_comp)  
        then (print_endline("method 2"); [])
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
          in let sfc = smp fc v
            in print_all_messages("");
            List.fold_right (fun x final -> (fst x) @ final) sfc [] 
    )
    
let rec osaft (cm: (Ast.Expression.t list * Ast.Monitor.t list)) (evt: Ast.SymbolicEvent.t) (c: Ast.Expression.t list) (relation: (Ast.Expression.t list * Ast.Monitor.t list) list) =
  let rec saft_aux (m: Ast.Monitor.t list) (res: (Ast.Expression.t list * Ast.Monitor.t list)) =

    let rec new_monitors mon_list = 
      match mon_list with
      | [] -> []
      | REDUCED(x)::m2 -> [x] @ (new_monitors m2)
      | ERROR(x)::m2 -> [add_verdict 0] @ (new_monitors m2)
    in 

    (match m with
    | [] -> 
        (* print_all_messages ("\nReturned by SAFT " ^ (pretty_print_monitor_list_string (snd res))); *)
        print_all_messages ("\nReturned by SAFT <" ^ pretty_print_evt_list (fst res) ^ ", " ^ pretty_print_monitor_list_string (snd res) ^ ">");
        let optimized_res = ((cns (fst res) (snd res)), (snd res)) in
        print_all_messages ("cond before was " ^ (pretty_print_evt_list (fst res)));
        print_all_messages ("cond after is " ^ (pretty_print_evt_list (fst optimized_res)));
        print_all_messages ("\nOptimized by OSAFT " ^ (pretty_print_monitor_list_string (snd optimized_res)));
        (Queue.push optimized_res unseen_cms)
    | ms::mss -> (
        let resulting_mons = sym_reduce ms (fst cm) evt c 
        in saft_aux mss (c, (add_monitors_not_in_list (snd res) (new_monitors resulting_mons))) (*use add_monitors_not_in_list to make sure not to add duplicates*)              
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
                      (* print_all_messages ("\nSatisfiability Conditions (SC) " ^ (pretty_print_evt_list sat_cond)); *)
                      let sat_cond_string = List.fold_right (fun x final -> final ^ (pretty_print_evt_list x) ^ "\n") sat_cond ""
                      in print_all_messages ("\nSatisfiability Conditions (SC) " ^ sat_cond_string);

                      let rec spa_all_options (conds: Ast.Expression.t list list) = 
                        match conds with 
                         | [] -> print_all_messages ("there are no more conditions to analyse")
                         | sc1::sc2 -> 
                            let spa_result = spa cm s sc1 [] in 
                              print_all_messages ("SPA For condition " ^ (pretty_print_evt_list sc1) ^ " is " ^ string_of_bool (spa_result));      
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
  in (computeSymRelation ([], mon) [([], mon)]) *)