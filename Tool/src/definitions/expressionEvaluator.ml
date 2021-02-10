open EnvResources
open EnvFunctions
open PrettyPrint

(*function to compute values for expressions which can be found within a monitor description*)
let rec reduce_expression (exp: Ast.Expression.t): expression_type =
  match exp with
    | Ast.Expression.Identifier(x) -> reduce_identifier x 
    | Ast.Expression.Literal(x) -> reduce_literal x
    | Ast.Expression.BinaryExp(x) -> reduce_binaryexp x
    | Ast.Expression.UnaryExp(x) -> reduce_unaryexp x 

and reduce_identifier (idt: Ast.Identifier.t): expression_type =
  STRING(idt.name)

and reduce_literal (lit: Ast.Literal.t): expression_type = 
  match lit with
    | Ast.Literal.Int(n) -> INT(n)
    | Ast.Literal.Bool(b) -> BOOL(b)

and reduce_binaryexp (tree: Ast.Expression.BinaryExp.t): expression_type =
  match tree.operator with
    | Plus -> eval_basic_operators tree tree.operator 
    | Minus -> eval_basic_operators tree tree.operator 
    | Mult -> eval_basic_operators tree tree.operator 
    | Div -> eval_basic_operators tree tree.operator 
    | Leq -> eval_basic_operators tree tree.operator 
    | Geq -> eval_basic_operators tree tree.operator 
    | Lt -> eval_basic_operators tree tree.operator 
    | Gt -> eval_basic_operators tree tree.operator 
    | Compare -> eval_comparison_operators tree tree.operator 
    | And -> eval_logic_operators tree tree.operator 
    | Or -> eval_logic_operators tree tree.operator 
    | Mod -> eval_logic_operators tree tree.operator 

and eval_basic_operators tree op : expression_type =
  match (reduce_expression tree.arg_lt, reduce_expression tree.arg_rt) with
    | INT(x), INT(y) -> evaluations_basic op x y
    | _ -> ERR ("Incompatible Types\n")

and evaluations_basic (op: Ast.Expression.BinaryExp.operator) (a: int) (b: int): expression_type =
  match op with
    | Plus -> INT(a + b)
    | Minus -> INT(a - b)
    | Mult -> INT(a * b)
    | Div -> INT(a / b)
    | Leq -> BOOL(a <= b)
    | Geq -> BOOL(a >= b)
    | Lt -> BOOL(a < b)
    | Gt -> BOOL(a > b)
    | Mod -> INT(a mod b)
    | _ -> INT(0)

and eval_comparison_operators tree op: expression_type =
  match reduce_expression tree.arg_lt, reduce_expression tree.arg_rt with
    | INT(x), INT(y) -> BOOL (x == y)
    | BOOL(x), BOOL(y) -> BOOL (x == y)
    | _ -> ERR("Incompatible Types\n")

and eval_logic_operators tree op: expression_type =
  match reduce_expression tree.arg_lt, reduce_expression tree.arg_rt with
    | BOOL(x), BOOL(y) -> evaluations_logic op x y
    | _ -> ERR("Incompatible Types\n")

and evaluations_logic (op: Ast.Expression.BinaryExp.operator) a b : expression_type =
  match op with
    | And -> BOOL(a && b)
    | Or -> BOOL(a || b)
    | _ -> BOOL(false)

and reduce_unaryexp (tree: Ast.Expression.UnaryExp.t): expression_type =
  match reduce_expression tree.arg with
    | BOOL(x) -> BOOL(not x)
    | _ -> ERR("Expression cannot be negated. Type error\n")

module BoundVarTypes = struct
  type t = Ast.Expression.t
  let compare (x:t) (y:t): int = compare (reduce_expression x) (reduce_expression y)
end

module BoundVars = Set.Make(BoundVarTypes)

(*reference to a set of bound expressions*)
let bound_vars = ref BoundVars.empty
let mapTVar = ref TVars.empty
  
let rec substitute_expression (exp: Ast.Expression.t) (y: Ast.Expression.t) (to_sub: Ast.Expression.t): Ast.Expression.t = 
  let get_val (to_sub:Ast.Expression.t) = 
    match reduce_expression to_sub  with 
    | INT(x) -> Ast.Expression.Literal(Ast.Literal.Int(x))
    | BOOL(x) -> Ast.Expression.Literal(Ast.Literal.Bool(x))
    | STRING(x) -> create_exp_identifier x
    | _ -> to_sub
  in
  match exp with
    | Ast.Expression.Literal(x) -> exp
    | Ast.Expression.Identifier(x) -> 
      if compare_values (reduce_identifier x) (reduce_expression y)
      then get_val to_sub
      else exp
    | Ast.Expression.BinaryExp(x) -> 
      add_binary_condition (substitute_expression x.arg_lt y to_sub) (substitute_expression x.arg_rt y to_sub) x.operator
    | Ast.Expression.UnaryExp(x) -> add_unary_condition (substitute_expression x.arg y to_sub)

(*substitute all free occurences of tvar by new_tvar*)
let rec substitute_tvar (mon: Ast.Monitor.t) (monvar: Ast.TVar.t) (new_tvar: Ast.TVar.t): Ast.Monitor.t = 
  match mon with 
  | Ast.Monitor.Verdict(x) -> 
    mon
  | Ast.Monitor.Choice(x) -> 
    create_choice_mon (substitute_tvar x.left monvar new_tvar) (substitute_tvar x.right monvar new_tvar)
  | Ast.Monitor.ExpressionGuard(x) -> 
    create_exp_guard_mon x.label x.payload (substitute_tvar x.consume monvar new_tvar)    
  | Ast.Monitor.QuantifiedGuard(x) -> 
    create_quant_guard_mon x.label x.payload (substitute_tvar x.consume monvar new_tvar)    
  | Ast.Monitor.Conditional(x) -> 
    create_conditional_mon x.condition (substitute_tvar x.if_true monvar new_tvar) (substitute_tvar x.if_false monvar new_tvar)
  | Ast.Monitor.TVar(x) -> 
    create_tvar new_tvar.tvar
  | Ast.Monitor.Recurse(x) ->  
    (*stop in case of tvariable shadowing*)
    if x.monvar.tvar == new_tvar.tvar
    then create_recurse_mon x.monvar x.consume
    else create_recurse_mon x.monvar (substitute_tvar x.consume monvar new_tvar)
  | Ast.Monitor.Evaluate(x) -> 
    create_evaluate_mon x.var x.subst (substitute_tvar x.stmt monvar new_tvar)   

(*substitues all free occurences of y by to_sub*)
let rec inner_sub_eval (mon: Ast.Monitor.t) (y) (to_sub): Ast.Monitor.t =
   match mon with 
   | Ast.Monitor.Verdict(x) -> mon
   | Ast.Monitor.Choice(x) -> 
      create_choice_mon (inner_sub_eval x.left y to_sub) (inner_sub_eval x.right y to_sub)
   | Ast.Monitor.ExpressionGuard(x) -> 
      create_exp_guard_mon x.label (substitute_expression x.payload y to_sub) (inner_sub_eval x.consume y to_sub)    
   | Ast.Monitor.QuantifiedGuard(x) -> 
      if compare_values (reduce_expression x.payload) (reduce_expression y)
      then(
        if BoundVars.mem x.payload !bound_vars
        then mon
        else (
          bound_vars := BoundVars.add x.payload !bound_vars;
          create_quant_guard_mon x.label (substitute_expression x.payload y to_sub) (inner_sub_eval x.consume y to_sub)
        )
      )
      else create_quant_guard_mon x.label x.payload (inner_sub_eval x.consume y to_sub)

   | Ast.Monitor.Conditional(x) -> 
      create_conditional_mon (substitute_expression x.condition y to_sub) (inner_sub_eval x.if_true y to_sub) (inner_sub_eval x.if_false y to_sub)
   | Ast.Monitor.TVar(x) -> mon
   | Ast.Monitor.Recurse(x) -> create_recurse_mon x.monvar (inner_sub_eval x.consume y to_sub)
   | Ast.Monitor.Evaluate(x) ->  
      (*check if the var is equal to y (the var we want to sub), if yes then stop, else continue substituting*)
      (*in the case where m = let x=2 in let x=x+3 in ... the x of let x=x+3 is bound to the outer let *)
      if compare_values (reduce_expression x.var) (reduce_expression y) 
      then create_evaluate_mon x.var (substitute_expression x.subst y to_sub) x.stmt
      else create_evaluate_mon x.var (substitute_expression x.subst y to_sub) (inner_sub_eval x.stmt y to_sub)    

  let rec inner_sub_rec (mon: Ast.Monitor.t) (y: Ast.TVar.t) (to_sub: Ast.Monitor.t) = 
    match mon with 
    | Ast.Monitor.TVar(x) ->
      if String.compare x.tvar y.tvar == 0
      then 
        (*substitute with the recursion monitor in the mapping*)
        (match TVars.find_opt y.tvar !mapTVar with
        | Some m -> m
        | None -> mon)
      else mon
    | Ast.Monitor.QuantifiedGuard(x) -> 
      create_quant_guard_mon x.label x.payload (inner_sub_rec x.consume y to_sub)
    | Ast.Monitor.ExpressionGuard(x) -> 
      create_exp_guard_mon x.label x.payload (inner_sub_rec x.consume y to_sub)
    | Ast.Monitor.Choice(x) ->
      create_choice_mon (inner_sub_rec x.left y to_sub) (inner_sub_rec x.right y to_sub)
    | Ast.Monitor.Conditional(x) -> 
      create_conditional_mon x.condition (inner_sub_rec x.if_true y to_sub) (inner_sub_rec x.if_false y to_sub)
    | Ast.Monitor.Evaluate(x) ->  
      create_evaluate_mon x.var x.subst (inner_sub_rec x.stmt y to_sub)
    | Ast.Monitor.Recurse(x) ->
      (match TVars.find_opt x.monvar.tvar !mapTVar with
      | None -> 
        mapTVar := TVars.add x.monvar.tvar x.consume !mapTVar; 
      | Some n -> print_endline("must rename"));    
        x.consume
    | _ -> mon

(*checks if an expression is in a list of identifiers*)
let rec check_in_list (e: Ast.Expression.t) (l: Ast.Identifier.t list): bool = 
  match l with
  | [] -> false
  | x::xs -> 
    match e with 
    | Ast.Expression.Identifier(y) -> 
	  if compare_values (reduce_expression e) (reduce_identifier x) 
      then true 
      else check_in_list e xs 
    | Ast.Expression.BinaryExp(y) ->
      if check_in_list y.arg_lt l || check_in_list y.arg_rt l
      then true
      else check_in_list e xs
    | Ast.Expression.UnaryExp(y) -> 
      if check_in_list y.arg l
      then true
      else check_in_list e xs
    | _ -> check_in_list e xs 
  
(*filters an expression by trying to remove all the expressions which are not in to_keep*)
let rec filter_b (cond: Ast.Expression.t list) (to_keep: Ast.Identifier.t list) =
  let rec inner_filter_b (cond: Ast.Expression.t list): Ast.Expression.t list =
  match cond with
  | [] -> []
  | b::bs ->
    (match b with 
    | Ast.Expression.BinaryExp(x) -> 
      (match x.operator with 
      | And ->
          (match (inner_filter_b [x.arg_lt]), (inner_filter_b [x.arg_rt]) with 
            | [], [] -> (inner_filter_b bs)
            | [], rt -> rt @ (inner_filter_b bs)
            | lt, [] -> lt @ (inner_filter_b bs)
            | lt, rt -> [add_binary_condition (List.hd lt) (List.hd rt) x.operator] @ (inner_filter_b bs)
          )
      | _ -> (
          if (check_in_list x.arg_lt to_keep) || (check_in_list x.arg_rt to_keep)
          then [b] @ (inner_filter_b bs)
          else (inner_filter_b bs)))

    | Ast.Expression.UnaryExp(x) ->
      if check_in_list x.arg to_keep 
      then [b] @ (inner_filter_b bs)
      else (inner_filter_b bs)
    | Ast.Expression.Literal(x) -> (inner_filter_b bs) (*in the case when the bool cond is true*)
    | _ -> [b] @ (inner_filter_b bs)  
    )
  in inner_filter_b cond 