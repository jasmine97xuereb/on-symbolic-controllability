open EnvResources
open EnvFunctions
open PrettyPrint
open List 
open ExpressionEvaluator

(** different from the events used in the notion of controllability,
  a symbolic event is of the form l<x>, where x is a variable and not a value  *)
let rec generateAllSymbolicEvents (mon: Ast.Monitor.t) (frsh: Ast.Identifier.t) (evt_list: Ast.SymbolicEvent.t list): Ast.SymbolicEvent.t list =
  match mon with
    | Ast.Monitor.Verdict(x) -> gen_symb_verdict_events x.verd evt_list  
    | Ast.Monitor.TVar(x) -> gen_symb_tvar_events x frsh evt_list
    | Ast.Monitor.ExpressionGuard(x) -> gen_symb_exp_guard_events x frsh evt_list
    | Ast.Monitor.QuantifiedGuard(x) -> gen_symb_quant_guard_events x frsh evt_list
    | Ast.Monitor.Choice(x) -> generateAllSymbolicEvents x.left frsh (generateAllSymbolicEvents x.right frsh evt_list)
    | Ast.Monitor.Recurse(x) -> generateAllSymbolicEvents x.consume frsh evt_list
    | Ast.Monitor.Evaluate(x) -> generateAllSymbolicEvents x.stmt frsh evt_list
    | Ast.Monitor.Conditional(x) -> generateAllSymbolicEvents x.if_false frsh (generateAllSymbolicEvents x.if_true frsh evt_list)

and gen_symb_tvar_events (tvar: Ast.TVar.t) (frsh: Ast.Identifier.t) (evt_list: Ast.SymbolicEvent.t list): Ast.SymbolicEvent.t list =
  match TVars.find_opt tvar.tvar !mapTVar with
  | Some m -> generateAllSymbolicEvents m frsh evt_list
  | None -> []

and gen_symb_verdict_events (x) (evt_list: Ast.SymbolicEvent.t list): Ast.SymbolicEvent.t list = 
  let sevt = {Ast.SymbolicEvent.label = create_identifier(STRING("any")); Ast.SymbolicEvent.payload = create_identifier(STRING("any"))}
  in if check_sevt_exists evt_list sevt 
  then evt_list
  else evt_list @ [sevt]

and gen_symb_exp_guard_events (mon: Ast.Monitor.ExpressionGuard.t) (frsh: Ast.Identifier.t) (evt_list: Ast.SymbolicEvent.t list): Ast.SymbolicEvent.t list =
  let sevt = {Ast.SymbolicEvent.label = mon.label; Ast.SymbolicEvent.payload = frsh;}
  in if check_sevt_exists evt_list sevt 
  then evt_list 
  else evt_list @ [sevt]

and gen_symb_quant_guard_events (mon: Ast.Monitor.QuantifiedGuard.t) (frsh: Ast.Identifier.t) (evt_list: Ast.SymbolicEvent.t list): Ast.SymbolicEvent.t list =
  let sevt = {Ast.SymbolicEvent.label = mon.label; Ast.SymbolicEvent.payload = frsh;}
  in if check_sevt_exists evt_list sevt 
  then evt_list 
  else evt_list @ [sevt]
  
let rec generateSymEventsForMonitorList (mon: Ast.Monitor.t list) (frsh: Ast.Identifier.t) (sevt_list: Ast.SymbolicEvent.t list): Ast.SymbolicEvent.t list =
 match mon with
   | [] -> sevt_list
   | m::ms -> (generateSymEventsForMonitorList ms frsh (generateAllSymbolicEvents m frsh sevt_list))
