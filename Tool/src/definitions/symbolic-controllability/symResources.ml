open EnvFunctions
open EnvResources
open ExpressionEvaluator
open PrettyPrint

(*mutable data structure to be used for generating the next fresh tvariable - used in rename_monvar function*)
let tvar_counter = ref 0 

(* set structure for identifiers - used in fv() function *)
module VarTypes = struct
  type t = Ast.Identifier.t
  let compare (x:t) (y:t): int = compare x y
end
module Vars = Set.Make(VarTypes)

(*used to check in the main module to rename bound tvars*)
module TVarTypes = struct
  type t = Ast.TVar.t
  let compare (x:t) (y:t): int = compare x y
end 
module BoundTVars = Set.Make(TVarTypes)

(*map that stores mappings from TVars to their respective free variables*)
let mapTVarFv = ref TVars.empty

(* Function to calculate the set of free variables in a constrained monitor set <b, M>, where fv(<b,M>) = {fv(b)} union {fv(M)} *)
let rec fv (cms: Ast.Expression.t list * Ast.Monitor.t list) (var_set: Vars.t): Vars.t =
   Vars.union (fv_exp (fst cms) var_set []) (fv_mon (snd cms) var_set [])

and fv_mon (m_list: Ast.Monitor.t list) (var_set: Vars.t) (tvars_checked: Ast.TVar.t list): Vars.t =
  match m_list with
  | [] -> var_set
  | mon::mons ->
    (match mon with
      | Ast.Monitor.Verdict(x) -> fv_mon mons var_set tvars_checked
      | Ast.Monitor.TVar(x) -> 
        if check_tvar_exists tvars_checked x == false 
        then fv_mon mons (fv_tvar x var_set ([x] @ tvars_checked)) ([x] @ tvars_checked)
        else fv_mon mons var_set tvars_checked 
      | Ast.Monitor.Choice(x) -> fv_mon mons (Vars.union (fv_mon [x.right] var_set tvars_checked) (fv_mon [x.left] var_set tvars_checked)) tvars_checked
      | Ast.Monitor.ExpressionGuard(x) -> fv_mon mons (fv_eg x var_set tvars_checked) tvars_checked
      | Ast.Monitor.QuantifiedGuard(x) -> fv_mon mons (fv_qg x var_set tvars_checked) tvars_checked
      | Ast.Monitor.Conditional(x) -> fv_mon mons (fv_if x var_set tvars_checked) tvars_checked 
      | Ast.Monitor.Evaluate(x) -> fv_mon mons (fv_let x var_set tvars_checked) tvars_checked
      | Ast.Monitor.Recurse(x) -> fv_mon mons (fv_mon [x.consume] var_set tvars_checked) tvars_checked) 

and fv_expression (expr: Ast.Expression.t) (var_set: Vars.t): Vars.t = 
  match expr with 
  | Ast.Expression.Identifier(x) -> Vars.add x var_set
  | Ast.Expression.BinaryExp(x) -> Vars.union (fv_expression x.arg_lt var_set) (fv_expression x.arg_rt var_set)
  | _ -> var_set

and fv_tvar (tvar: Ast.TVar.t) (var_set: Vars.t) (tvars_checked: Ast.TVar.t list): Vars.t = 
  match TVars.find_opt tvar.tvar !mapTVar with
  | Some m -> 
    (* print_endline(pretty_print_monitor_list_string [m]); *)
    (match TVars.find_opt tvar.tvar !mapTVarFv with 
    | Some n -> 
      Vars.union n var_set
    | None -> 
      let free_vars = fv_mon [m] Vars.empty tvars_checked 
      in mapTVarFv := TVars.add tvar.tvar free_vars !mapTVarFv;
      Vars.union free_vars var_set
    )
  | None -> var_set

and fv_eg (mon: Ast.Monitor.ExpressionGuard.t) (var_set: Vars.t) (tvars_checked: Ast.TVar.t list): Vars.t =
  match mon.payload with
    | Ast.Expression.Identifier(x) -> fv_mon [mon.consume] (Vars.add x var_set) tvars_checked
    | Ast.Expression.BinaryExp(x) -> fv_mon [mon.consume] (fv_expression mon.payload var_set) tvars_checked
    | _ -> fv_mon [mon.consume] var_set tvars_checked

and fv_qg (mon: Ast.Monitor.QuantifiedGuard.t) (var_set: Vars.t) (tvars_checked: Ast.TVar.t list): Vars.t =
  match mon.payload with
    | Ast.Expression.Identifier(x) -> Vars.remove x (fv_mon [mon.consume] var_set tvars_checked) (*(Vars.add x var_set)*)
    | _ -> fv_mon [mon.consume] var_set tvars_checked

and fv_if (mon: Ast.Monitor.Conditional.t) (var_set: Vars.t) (tvars_checked: Ast.TVar.t list): Vars.t =
  let condition_vars = fv_exp [mon.condition] var_set tvars_checked in
    Vars.union (Vars.union (fv_mon [mon.if_true] var_set tvars_checked) (fv_mon [mon.if_false] var_set tvars_checked)) condition_vars

and fv_let (mon: Ast.Monitor.Evaluate.t) (var_set: Vars.t) (tvars_checked: Ast.TVar.t list): Vars.t =
  match mon.var with
    | Ast.Expression.Identifier(x) -> (
      if Vars.mem x var_set
      then (Vars.remove x (Vars.union (fv_exp [mon.subst] var_set tvars_checked) (fv_mon [mon.stmt] var_set tvars_checked)))
      else (Vars.remove x (Vars.union (fv_exp [mon.subst] var_set tvars_checked) (fv_mon [mon.stmt] var_set tvars_checked))))
    | _ -> var_set

and fv_exp (e_list: Ast.Expression.t list) (var_set: Vars.t) (tvars_checked: Ast.TVar.t list): Vars.t =
  match e_list with
    | [] -> var_set
    | exp::exps ->
      (match exp with
        | Ast.Expression.Identifier(x) -> fv_exp exps (Vars.add x var_set) tvars_checked
        | Ast.Expression.Literal(x) -> fv_exp exps var_set tvars_checked
        | Ast.Expression.BinaryExp(x) -> fv_exp exps (Vars.union (fv_exp [x.arg_rt] var_set tvars_checked) (fv_exp [x.arg_lt] var_set tvars_checked)) tvars_checked
        | Ast.Expression.UnaryExp(x) -> fv_exp exps (fv_exp [x.arg] var_set tvars_checked) tvars_checked)

(*function to calculate the set of bound tvariables (recursion variables) in a monitor list*)
let rec btv (cms: Ast.Monitor.t list) (bound_set: BoundTVars.t): BoundTVars.t = 
  match cms with 
  | [] -> bound_set
  | mon::mons ->
    (match mon with
    | Ast.Monitor.Verdict(x) -> btv mons bound_set
    | Ast.Monitor.TVar(x) -> btv mons bound_set
    | Ast.Monitor.Choice(x) -> btv mons (BoundTVars.union (btv [x.right] bound_set) (btv [x.left] bound_set))
    | Ast.Monitor.ExpressionGuard(x) -> btv mons (btv [x.consume] bound_set) 
    | Ast.Monitor.QuantifiedGuard(x) -> btv mons (btv [x.consume] bound_set) 
    | Ast.Monitor.Conditional(x) -> btv mons (BoundTVars.union (btv [x.if_true] bound_set) (btv [x.if_false] bound_set))  
    | Ast.Monitor.Evaluate(x) -> btv mons (btv [x.stmt] bound_set) 
    | Ast.Monitor.Recurse(x) -> btv mons (btv [x.consume] (BoundTVars.add x.monvar bound_set)) 
    )

(*function to check the whole monitor structure and rename all the monitor variables 
that were already bound to some other recursion monitor*)
let rec rename_monvar (m: Ast.Monitor.t) (bound: BoundTVars.t): Ast.Monitor.t = 
  match m with 
  | Ast.Monitor.QuantifiedGuard(x) -> 
    create_quant_guard_mon x.label x.payload (rename_monvar x.consume bound)
  | Ast.Monitor.ExpressionGuard(x) -> 
    create_exp_guard_mon x.label x.payload (rename_monvar x.consume bound) 
  | Ast.Monitor.Choice(x) ->
    (*check lhs and then get all the bound vars*)
    let left_mon = (rename_monvar x.left bound) in
      create_choice_mon left_mon (rename_monvar x.right (btv [left_mon] bound))
  | Ast.Monitor.Conditional(x) ->
    create_conditional_mon x.condition (rename_monvar x.if_true bound) (rename_monvar x.if_false bound)
  | Ast.Monitor.Evaluate(x) ->
    create_evaluate_mon x.var x.subst (rename_monvar x.stmt bound) 
  | Ast.Monitor.Recurse(x) -> 
    if BoundTVars.mem x.monvar bound
    then
      (*if it already bound, create a fresh tvar *)
      (let new_tvar = fresh_tvar !tvar_counter
      in incr tvar_counter; 
      create_recurse_mon new_tvar (rename_monvar (substitute_tvar x.consume x.monvar new_tvar) (BoundTVars.add new_tvar bound))
      )
    else(
      create_recurse_mon x.monvar (rename_monvar x.consume (BoundTVars.add x.monvar bound)))
  | _ -> m

(* frsh(fv(<b,M>)) deterministically returns the next fresh variable that is not in the variable set.
For the purpose of this task, we denote any fresh variables generated by a '$' and a counter as we go along.*)
let fresh (free_vars: Vars.t): Ast.Identifier.t =
  (* print_endline("GENERATING FRESH"); *)
  let counter = 0 in
    let init_f = "$" in
      let rec generateFrsh (last_f: Ast.Identifier.t) (counter: int): Ast.Identifier.t =
        if (not (Vars.mem last_f free_vars))
        then last_f
        else (
          generateFrsh ({Ast.Identifier.name = "$" ^  string_of_int(counter)}) (counter+1)
        )
      in generateFrsh ({Ast.Identifier.name = init_f ^ string_of_int(counter)}) counter

