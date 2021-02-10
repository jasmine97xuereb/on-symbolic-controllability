open SymFunctions
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
open ReachRelation
open ReachResources

(* Queue of monitors we still need to exhibit (taking care of the aggregating constraints) *)
let unseen_cms = Queue.create ()

(* set to store analysed constrained monitor sets and the verdict sets they reach *)
let checked = ref CMReachesVS.empty

let isSymControllable (mon: Ast.Monitor.t list) =

  (* if there are more cms in the queue, analyse the next cm *)
  (* otherwise return true *)
  let rec analyse_next_cm (relation: (Ast.Expression.t list * Ast.Monitor.t list) list) = 
    if (Queue.is_empty unseen_cms)
    then( 
      print_basic ("---------------------\nThe Witness Relation is \n" ^ pretty_print_relation relation);
      true)
    else 
      (let next_m = get_next_unseen relation unseen_cms in 
        match next_m with 
        | ([],[]) -> (
          print_basic ("---------------------\nThe Witness Relation is \n" ^ pretty_print_relation relation);
          true)
        | _-> (computeSymRelation next_m relation)
      )

  (* resulting cms are all the cms returned by the function osaft for all symbolic events possible*)
  and exhibitSymEvents (cm: cm) (relation: cm list) (sym_events: Ast.SymbolicEvent.t list): bool =
    match sym_events with
    |[] -> 
      analyse_next_cm relation 
    |s::ss ->
      print_all_messages ("Reachable Conditions (RC) for SymbolicEvent " ^ pretty_print_sym_event [s]);
      (*List.sort_uniq drops all the duplicate elements in the list returned by rc*)
      let c = List.sort_uniq compare (rc (snd cm) s []) in (
        print_all_messages (pretty_print_evt_list c);
        
        let sat_cond = sc (fst cm) c []
          in print_all_messages ("\nSatisfiability Conditions (SC) " ^ pretty_print_evt_list sat_cond);

          let rec spa_all_options (conds: Ast.Expression.t list) = 
            match conds with 
            | [] -> print_all_messages ("there are no more conditions to analyse")
            | sc1::sc2 -> 
              let spa_result = spa cm s sc1 [] in 
                print_all_messages ("SPA For condition " ^ (pretty_print_evt_list [sc1]) ^ " is " ^ string_of_bool (spa_result));      
                (*if spa is true, then saft must also hold, otherwise go to the next condition*)
                if spa_result 
                then (
                  let res = osaft cm s sc1 relation unseen_cms 
                  in (Queue.push res unseen_cms);
                  spa_all_options sc2
                )
                else spa_all_options sc2
            in spa_all_options sat_cond;  
      );      
      exhibitSymEvents cm relation ss


  and computeSymRelation (cm: cm) (relation: cm list): bool =

    let relation = add_to_relation relation cm in 
    print_all_messages ("SYMBOLIC RELATION IS " ^ pretty_print_relation relation ^ "\n---------------------");

    if (spr cm []) 
    then(      
      (* if the current constrained monitor-set is not reachable, then do not push it to the queue *)
      (* return whether there exists a violation and if no, which verdict sets can be reached *)
      let rec monsReach (ms: Ast.Monitor.t list) (acc: VerdictSet.t list): (bool * VerdictSet.t list) = 
        (match ms with
        | [] -> (false, acc)
        | m::ms -> 
            print_all_messages("checking " ^ pretty_print_monitor_list_string [m]);
            let reach_m = 
              (try 
                let info_m = CMReachesVS.find_first (fun x -> CMSet.mem (fst cm, [m]) (snd x)) !checked in
                  print_all_messages("already checked - we found the set containing our mon, it is ");
                  print_path [info_m]; 
                  fst info_m (* return the verdict set *)

              with Not_found ->
                  (* analyse the monitor for reachability: isReachable returns a list of type < VerdictSet, CMSet > *)
                  let r = isReachable (fst cm, [m]) in
                  (* if cm_rw is empty, then m is reachable wrt { } => it is not reachable *)
                  let cm_rw = List.fold_right (fun x acc -> VerdictSet.union (fst x) acc) r VerdictSet.empty in 
                  print_reach("W is " ^ pretty_print_verdict_list (VerdictSet.elements cm_rw));
                  (* update the set of analysed monitors *)
                  checked := CMReachesVS.union !checked (CMReachesVS.of_list r);  
                  (* return the verdictset that <b,[m]> is reachable wrt *)
                  cm_rw
              ) 
            (* get the rw of the monitors in the monitor-set until a violating rw is found or the end of the list *)
            (* a monitor-set violates contr when m, m' reach different verdicts or only one of them reaches a verdict *)     
            in let violation = (fun x -> (VerdictSet.disjoint reach_m x) && (not (VerdictSet.is_empty x) || not (VerdictSet.is_empty reach_m))) in
            if (List.exists violation acc)
            then (true, acc @ [reach_m]) 
            else monsReach ms (acc @ [reach_m])
        )

      in 
      let (violation, rw_list) = monsReach (snd cm) [] in
      (* a monitor-set is reachable when some m reaches w for w not empty i.e. m is reachable *)   
      let existsReach = List.exists (fun x -> not (VerdictSet.is_empty x)) rw_list in

      if violation
      then (  
        print_all_messages("cm cannot be controllable because it violates some cond");
        false
      )
      else if not existsReach 
      then (
        print_all_messages("cm is not reachable");
        analyse_next_cm relation 
      ) 
      else ( 
        print_all_messages("cm is reachable");
        match ReachableMonitorsMap.find_opt cm !mapCm with 
        | Some x -> 
          List.iter (fun y -> Queue.push y unseen_cms) x;
          analyse_next_cm relation
        | None ->
          let frsh_v = fresh(fv cm (Vars.empty)) in
            let sym_events = generateSymEventsForMonitorList (snd cm) frsh_v [] in
              print_all_messages (pretty_print_sym_event sym_events);
              exhibitSymEvents cm relation sym_events
      ) 
    )
    else false

in (computeSymRelation ([], mon) [([], mon)])





