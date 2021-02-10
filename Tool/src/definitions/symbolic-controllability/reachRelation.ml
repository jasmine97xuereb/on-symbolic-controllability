open SymFunctions 
open Queue
open EnvFunctions
open EnvResources
open VisibilityLevel
open SymResources
open SymEventGenerator
open PrettyPrint
open SymTransitions
open SatFunction
open ExpressionEvaluator
open ReachResources

let unvisited_queue = Queue.create ()

(* map that stores mappings fom ReachableMonitorsMap to the resulting reach sets *)
let mapCm = ref ReachableMonitorsMap.empty

(* if the queue is empty *)
(*  the entries that are in relation but not in result are not reachable i.e. reachable wrt verdict-set { } *)
(*  return the list of monitor-sets and the verdict-sets wrt which they are reachable *)
(* otherwise pop a cm from the queue and call ComputeReachRelation *)

let rec analyse_next_cm (relation: cm list) (result: (VerdictSet.t * CMSet.t) list): ((VerdictSet.t * CMSet.t) list) = 
  if (Queue.is_empty unvisited_queue)
  then( 
    let rset = CMSet.of_list relation in
    let reach_sets = List.fold_right (fun x acc -> CMSet.union (snd x) acc) result CMSet.empty in
    let not_reach = CMSet.diff rset reach_sets in
    result @ [(VerdictSet.empty, not_reach)]    
  )
  else (
    let (p, next_m) = get_next_unseen_r relation unvisited_queue in 
    print_reach("The next in line to be analysed for reach is " ^ pretty_print_evt_list (fst (next_m)) ^ ", " ^ pretty_print_monitor_list_string (snd next_m));
      match next_m with 
      | ([],[]) -> 
        print_reach ("---------------------\nThe Reachable Relation is \n" ^ pretty_print_relation relation);
        let rset = CMSet.of_list relation in 
        let reach_sets = List.fold_right (fun x acc -> CMSet.union (snd x) acc) result CMSet.empty in
        let not_reach = CMSet.diff rset reach_sets in
        result @ [(VerdictSet.empty, not_reach)]
      | _-> 
        computeReachRelation p next_m relation result
  ) 

(* reaches generates the next monitor-set that the current one can transition to *)
(* these are added to the queue for futher analysis *)
(* once the sets are generated, it calls analyse_next_cm to analyse the next monitor in the queue *)

and reaches (p: CMSet.t) (cm: (Ast.Expression.t list * Ast.Monitor.t list))  (relation: (Ast.Expression.t list * Ast.Monitor.t list) list) (result: (VerdictSet.t * CMSet.t) list): (VerdictSet.t * CMSet.t) list = 
  match ReachableMonitorsMap.find_opt cm !mapCm with 
  | Some x -> 
    print_reach("aft already computed and is "); 
    List.iter (fun y -> print_reach(pretty_print_evt_list (fst y) ^ "," ^ pretty_print_monitor_list_string (snd y))) x;
    List.iter (fun x -> List.iter (fun y -> Queue.push ((CMSet.add cm p), (fst x, [y])) unvisited_queue) (snd x)) x;
    analyse_next_cm relation result
  
  | None ->
    let frsh_v = fresh(fv cm (Vars.empty)) in
      let sym_events = generateSymEventsForMonitorList (snd cm) frsh_v [] in
        print_reach (pretty_print_sym_event sym_events);
        
        let rec exhibitSymEvents (aft_set: (Ast.Expression.t list * Ast.Monitor.t list) list) (sym_events: Ast.SymbolicEvent.t list): (VerdictSet.t * CMSet.t) list =
          match sym_events with
          |[] -> (
            mapCm := ReachableMonitorsMap.add cm aft_set !mapCm;
            analyse_next_cm relation result
          )
          |s::ss ->
            print_reach ("Reachable Conditions (RC) for SymbolicEvent " ^ pretty_print_sym_event [s]);
            (* List.sort_uniq drops all the duplicate elements in the list returned by rc *)
            let c = List.sort_uniq compare (rc (snd cm) s []) in 
              print_reach (pretty_print_evt_list c);

              let sat_cond = sc (fst cm) c [] 
                in print_reach ("\nSatisfiability Conditions (SC) " ^ pretty_print_evt_list sat_cond);

                let rec spa_all_options (aft_set: cm list) (conds: Ast.Expression.t list): cm list = 
                  match conds with 
                  | [] -> aft_set
                  | sc1::sc2 -> 
                    print_reach("for event " ^ pretty_print_evt_list [sc1]);
                    let spa_result = spa cm s sc1 [] in
                      if spa_result
                      then (
                        let res = reach_osaft cm s sc1 relation unvisited_queue in 
                        print_reach("p is : ");
                        print_cmset p;
                        List.iter (fun x -> Queue.push (CMSet.add cm p, (fst res, [x])) unvisited_queue) (snd res);
                        spa_all_options (aft_set @ [res]) sc2
                      )
                      else spa_all_options aft_set sc2
                in let aft_set = spa_all_options aft_set sat_cond           
            in exhibitSymEvents aft_set ss;        
        in exhibitSymEvents [] sym_events

(* this fn checks whether the cm is reachable *)
(* if contains a visible verdict and no branching *)
(*  add the path of monitors and the verdict set reached to the final result *)
(*  analyse the next cm in the queue *)   
(* else if contains visible verdict and branching *)
(*  call isReach to perform the reachability analysis *)
(* else analyse the next cm in the queue *)

and computeReachRelation (p: CMSet.t) (cm: cm) (relation: cm list) (result: (VerdictSet.t * CMSet.t) list): ((VerdictSet.t * CMSet.t) list) =
  let relation = add_to_relation relation cm in 
  print_reach ("REACHABLE RELATION IS " ^ pretty_print_relation relation ^ "\n---------------------");
  let m_list = (snd cm) in
  print_reach("CURRENT M IS "^ pretty_print_evt_list (fst cm) ^ ", "^ pretty_print_monitor_list_string m_list);
  
  if (vrd m_list) && not (brc m_list) 
  then(
    print_reach("contains verdict and no branching => reachable");
    print_reach("all these monitors are reachable wrt: " ^ pretty_print_verdict_list (VerdictSet.elements (get_rw m_list)));
    print_cmset p;
    let new_result = add_rw_path result (get_rw m_list) (CMSet.add cm p) in
    analyse_next_cm relation new_result 
  ) 
  else if (vrd m_list)
  then (
    print_reach("checking it");
    reaches p cm relation result
  )
  else (
    print_reach("monitor " ^ pretty_print_monitor_list_string m_list ^ " does not contain verdict - moving to next");
    analyse_next_cm relation result
  )

(* the elements of the queue are of the type < CMSet, cm > *)
(* the first element cmset will store the path from the intial cm to the current cm *)
(* given cm=<b,M> push all <b,m> for m in M to the queue *)
(* once all elements have been analysed for reachability do : *)
(*  return a list of < VerdictSets, CMsets > *)
(*  the CMsets in the tuple will be reachable wrt the VerdictSets *)
(* note that the initial cm is reachabe wrt the union of all VerdictSets in the above list *)
(* cm is reachable if at least one verdict set in res is not empty *)

and isReachable (cm: (Ast.Expression.t list * Ast.Monitor.t list)): ((VerdictSet.t * CMSet.t) list) =  
  Queue.clear unvisited_queue;
  List.iter (fun x -> Queue.push (CMSet.empty, (fst cm, [x])) unvisited_queue) (snd cm);
  let (p, first_cm) = Queue.pop unvisited_queue in
  let res = computeReachRelation p first_cm [cm] [VerdictSet.empty, CMSet.empty] in
  res