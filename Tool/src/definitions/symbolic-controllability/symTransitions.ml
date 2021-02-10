open EnvFunctions
open EnvResources
open ExpressionEvaluator
open SatFunction
open PrettyPrint

(*transition rules for the definition of Symbolic Controllability*)
let rec sym_reduce (mon_in: Ast.Monitor.t) (b: Ast.Expression.t list) (tr_in: Ast.SymbolicEvent.t) (c: Ast.Expression.t): monitor_type list =
  (match mon_in with
  | Ast.Monitor.Verdict(_) as x ->  
      [REDUCED(x)]
  | Ast.Monitor.TVar(x) -> 
      rule_tvar mon_in b tr_in c
  | Ast.Monitor.Choice(x) -> 
      rule_schoice mon_in b tr_in c
  | Ast.Monitor.ExpressionGuard(x) -> 
      rule_sgre mon_in b tr_in c
  | Ast.Monitor.QuantifiedGuard(x) -> 
      rule_sgrq mon_in b tr_in c
  | Ast.Monitor.Conditional(x) ->
     rule_sif mon_in b tr_in c
  | Ast.Monitor.Evaluate(x) -> 
      rule_slet mon_in b tr_in c
  | Ast.Monitor.Recurse(x) -> 
      rule_srec mon_in b tr_in c)

and rule_tvar  (mon_in: Ast.Monitor.t) (b: Ast.Expression.t list) (tr_in: Ast.SymbolicEvent.t) (c: Ast.Expression.t) : monitor_type list =
  match mon_in with
  | Ast.Monitor.TVar(x) ->  
    (match TVars.find_opt x.tvar !mapTVar with
    | Some m -> sym_reduce m b tr_in c
    | None -> [ERROR("Not found in map")])
  | _ -> [ERROR("Incorrect Structure")]

  and rule_schoice (mon_in: Ast.Monitor.t) (b: Ast.Expression.t list) (tr_in: Ast.SymbolicEvent.t) (c: Ast.Expression.t) : monitor_type list =
    match mon_in with
      | Ast.Monitor.Choice(x) ->
        let reduced_rt = sym_reduce x.right b tr_in c
        in let reduced_lt = sym_reduce x.left b tr_in c
        in 
        let rec add (reduced) (resulting_cs) = 
          (match reduced with 
          | [] -> (*if one reduces, then it is enough*)
              if List.length resulting_cs == 0 
              then [ERROR("Unable to Reduce")]
              else resulting_cs
          | REDUCED(x)::xs -> add xs ([REDUCED(x)] @ resulting_cs)
          | ERROR(x)::xs -> add xs resulting_cs)
        in add (reduced_rt @ reduced_lt) []
      | _ -> [ERROR("Incorrect Structure")]

and rule_sgre (mon_in: Ast.Monitor.t) (b: Ast.Expression.t list) (tr_in: Ast.SymbolicEvent.t) (c: Ast.Expression.t): monitor_type list =
  match mon_in with
  | Ast.Monitor.ExpressionGuard(x) ->
    (if (compare_values (reduce_identifier x.label) (reduce_identifier tr_in.label))
    then
      let new_cond = (add_binary_condition x.payload (create_exp_identifier tr_in.payload.name) Ast.Expression.BinaryExp.Compare) in
      (if (fst (sat [add_binary_condition c new_cond Ast.Expression.BinaryExp.And]))
        then [REDUCED(x.consume)]
      else [ERROR("Payload does not match")])
    else [ERROR("Label does not match\n")])

  | _ -> [ERROR("Incorrect Structure")]

and rule_sgrq (mon_in: Ast.Monitor.t) (b: Ast.Expression.t list) (tr_in: Ast.SymbolicEvent.t) (c: Ast.Expression.t): monitor_type list =
  match mon_in with
  | Ast.Monitor.QuantifiedGuard(x) ->
    (if (compare_values (reduce_identifier x.label ) (reduce_identifier tr_in.label ))
    then
      let new_cond = (add_binary_condition x.payload x.payload Ast.Expression.BinaryExp.Compare) in
      (if (fst (sat [add_binary_condition c new_cond Ast.Expression.BinaryExp.And]))
        then (*substitute all occurences of x.payload by the symbolic event's payload*)
          let to_consume = inner_sub_eval x.consume x.payload (Ast.Expression.Identifier(tr_in.payload)) 
          in [REDUCED(to_consume)]
      else [ERROR("Payload does not match")])
    else [ERROR("Label does not match\n")])
  | _ -> [ERROR("Incorrect Structure")]

and rule_sif (mon_in: Ast.Monitor.t) (b: Ast.Expression.t list) (tr_in: Ast.SymbolicEvent.t) (c: Ast.Expression.t): monitor_type list =
  match mon_in with
    | Ast.Monitor.Conditional(x) -> (
        let c_true = add_binary_condition c x.condition Ast.Expression.BinaryExp.And in 
        let c_false = add_binary_condition c (add_unary_condition x.condition) Ast.Expression.BinaryExp.And in 
        if (fst (sat [c_true]))
        then sym_reduce x.if_true b tr_in c_true
        else if (fst (sat [c_false]))
        then sym_reduce x.if_false b tr_in c_false 
        else [ERROR("unable to reduce")]      
      )
    | _ ->              
        [ERROR("Incorrect structure")]

and rule_slet (mon_in: Ast.Monitor.t) (b: Ast.Expression.t list) (tr_in: Ast.SymbolicEvent.t) (c: Ast.Expression.t): monitor_type list =
  match mon_in with
    | Ast.Monitor.Evaluate(x) -> (
      (* let new_cond = add_binary_condition c (add_binary_condition x.var x.subst Ast.Expression.BinaryExp.Compare) Ast.Expression.BinaryExp.And in *)
      match (reduce_expression x.subst) with
        | INT(y) -> 
          (match reduce_expression x.var with
            | STRING(z) -> (sym_reduce (inner_sub_eval x.stmt x.var x.subst) b tr_in c)
            | _ -> [ERROR("Cannot reduce\n")])
        | BOOL(y) -> 
          (match reduce_expression x.var with
            | STRING(z) -> (sym_reduce (inner_sub_eval x.stmt x.var x.subst) b tr_in c)
            | _ -> [ERROR("Cannot reduce\n")])
        | _ -> 
          sym_reduce (inner_sub_eval x.stmt x.var x.subst) b tr_in c (*it is in the form x + 1 for example*)
        )
    | _ -> [ERROR ("Incorrect Structure")]

(*Upon encountering a recursion monitor, check if it is already in the map
If it was already in the map, then monvar was already bound, thus continue reducing
Otherwise, add the monvar (mapping to the consume mon of rec) to the map and continue reducing *)
and rule_srec (mon: Ast.Monitor.t) (b: Ast.Expression.t list) (tr_in: Ast.SymbolicEvent.t) (c: Ast.Expression.t): monitor_type list =
  match mon with
    | Ast.Monitor.Recurse(x) -> 
      (match TVars.find_opt x.monvar.tvar !mapTVar with
      | None -> 
        mapTVar := TVars.add x.monvar.tvar x.consume !mapTVar; 
        sym_reduce x.consume b tr_in c
      | Some n -> 
        sym_reduce n b tr_in c)
    | _ -> [ERROR ("Incorrect Structure")]


