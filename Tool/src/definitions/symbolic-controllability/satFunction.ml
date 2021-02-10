open EnvResources
open EnvFunctions
open Z3
open Z3.Symbol
open Z3.Sort
open Z3.Expr
open Z3.Boolean
open Z3.Arithmetic
open Z3.Arithmetic.Integer
open Z3.Solver
open Z3.Goal
open Z3.Tactic
open Z3.Tactic.ApplyResult
open PrettyPrint
open VisibilityLevel

(*mutable data structure to store the cumulative time for sat calls*)
let sat_timer = ref 0.0 

(** function to convert a list of expressions in the form Ast.Expression.t into the Z3.Expr.expr required by the Z3 library  *)
let rec exp_list_to_z3 (c: Ast.Expression.t list) (a: Z3.Expr.expr list) (ctx: context) =
  let rec single_exp_to_z3 (e: Ast.Expression.t) (ctx: context) =
    (match e with
      | Ast.Expression.Identifier(x) -> (Expr.mk_const ctx (Symbol.mk_string ctx x.name) (Integer.mk_sort ctx))
      | Ast.Expression.Literal(x) -> (match x with
        | Ast.Literal.Int(n) -> (Integer.mk_numeral_i ctx n)
        | Ast.Literal.Bool(b) -> (
          match b with
            | true -> (Boolean.mk_true ctx)
            | false -> (Boolean.mk_false ctx)))
      | Ast.Expression.BinaryExp(x) ->
        (match x.operator with
          | Plus -> (Arithmetic.mk_add ctx [(single_exp_to_z3 x.arg_lt ctx); (single_exp_to_z3 x.arg_rt ctx)])
          | Minus -> (Arithmetic.mk_sub ctx [(single_exp_to_z3 x.arg_lt ctx); (single_exp_to_z3 x.arg_rt ctx)])
          | Mult -> (Arithmetic.mk_mul ctx [(single_exp_to_z3 x.arg_lt ctx); (single_exp_to_z3 x.arg_rt ctx)])
          | Div -> (Arithmetic.mk_div ctx (single_exp_to_z3 x.arg_lt ctx) (single_exp_to_z3 x.arg_rt ctx))
          | Leq -> (Arithmetic.mk_le ctx (single_exp_to_z3 x.arg_lt ctx) (single_exp_to_z3 x.arg_rt ctx))
          | Geq -> (Arithmetic.mk_ge ctx (single_exp_to_z3 x.arg_lt ctx) (single_exp_to_z3 x.arg_rt ctx))
          | Lt -> (Arithmetic.mk_lt ctx (single_exp_to_z3 x.arg_lt ctx) (single_exp_to_z3 x.arg_rt ctx))
          | Gt -> (Arithmetic.mk_gt ctx (single_exp_to_z3 x.arg_lt ctx) (single_exp_to_z3 x.arg_rt ctx))
          | Mod -> (Arithmetic.Integer.mk_mod ctx (single_exp_to_z3 x.arg_lt ctx) (single_exp_to_z3 x.arg_rt ctx))
          | Compare -> (Boolean.mk_eq ctx (single_exp_to_z3 x.arg_lt ctx) (single_exp_to_z3 x.arg_rt ctx))
          | And -> (Boolean.mk_and ctx [(single_exp_to_z3 x.arg_lt ctx); (single_exp_to_z3 x.arg_rt ctx)])
          | Or -> (Boolean.mk_or ctx [(single_exp_to_z3 x.arg_lt ctx); (single_exp_to_z3 x.arg_rt ctx)]))
      | Ast.Expression.UnaryExp(x) ->
        match x.operator with
        | Not -> (Boolean.mk_not ctx (single_exp_to_z3 x.arg ctx)))
  in match c with
    | [] -> (Boolean.mk_and ctx a)
    | e::es -> exp_list_to_z3 es (a @ [single_exp_to_z3 e ctx]) ctx

(*function to convert a list of goals into a list of expressions of the form Ast.Expression.t*)
let rec goals_to_exp (goals: Z3.Goal.goal list): Ast.Expression.t = 
  let rec z3_to_exp (exp: Expr.expr list): Ast.Expression.t =
    let rec single_z3_to_exp (e: Expr.expr): Ast.Expression.t =  
      if is_true e then Ast.Expression.Literal(Bool(true))
      else if is_false e then Ast.Expression.Literal(Bool(true))
      else if is_const e then create_exp_identifier (Expr.to_string e)
      else if is_numeral e then ( (*when the resulting int is negative, the string returned is of the form (- x) -> string must be modified*)
        let new_s = Str.global_replace (Str.regexp "[\r\n\t() ]") "" (Expr.to_string e)
        in Ast.Expression.Literal(Int(int_of_string new_s)) 
      )
      else if is_not e then (
        let args = get_args e 
        in let stmt = single_z3_to_exp (List.nth args 0) 
        in add_unary_condition stmt 
      )
      (*otherwise it must be some binary expression*)
      else 
        (let args = get_args e  
        in let lt = single_z3_to_exp (List.nth args 0) 
        in let rt = z3_to_exp (List.tl args) in
        if is_add e then add_binary_condition lt rt Ast.Expression.BinaryExp.Plus
        else if is_sub e then add_binary_condition lt rt Ast.Expression.BinaryExp.Minus
        else if is_mul e then add_binary_condition lt rt Ast.Expression.BinaryExp.Mult
        else if is_div e then add_binary_condition lt rt Ast.Expression.BinaryExp.Div
        else if is_idiv e then add_binary_condition lt rt Ast.Expression.BinaryExp.Div
        else if is_and e then add_binary_condition lt rt Ast.Expression.BinaryExp.And
        else if is_le e then add_binary_condition lt rt Ast.Expression.BinaryExp.Leq
        else if is_lt e then add_binary_condition lt rt Ast.Expression.BinaryExp.Lt
        else if is_ge e then add_binary_condition lt rt Ast.Expression.BinaryExp.Geq
        else if is_gt e then add_binary_condition lt rt Ast.Expression.BinaryExp.Gt
        else if is_or e then add_binary_condition lt rt Ast.Expression.BinaryExp.Or
        else if is_eq e then add_binary_condition lt rt Ast.Expression.BinaryExp.Compare
        else if is_modulus e then add_binary_condition lt rt Ast.Expression.BinaryExp.Mod
        else Ast.Expression.Literal(Bool(true)))
    
    in match exp with 
    | [] -> Ast.Expression.Literal(Bool(true))
    | e::[] -> single_z3_to_exp e 
    | e::es -> add_binary_condition (single_z3_to_exp e) (z3_to_exp es) Ast.Expression.BinaryExp.And

  in match goals with 
  | [] -> Ast.Expression.Literal(Bool(true))
  | g::[] -> z3_to_exp [Goal.as_expr g]
  | g::gs -> add_binary_condition (z3_to_exp [Goal.as_expr g]) (goals_to_exp gs) Ast.Expression.BinaryExp.And

(*check if a list of expressions is satisfiable*)
(*if it is satisfiable, then there the ctx solver must return at least one subgoal*)
(*if the subgoal returned is false, then return (false, []) since the list of expressions in unsat*)
(*otherwise get the list of subgoals and convert them back to AST expressions*)
(*return (true, [Ast.Expression])*)            
let sat (c: Ast.Expression.t list): (bool * Ast.Expression.t list) =
  (* print_all_messages ("\nChecking SAT for " ^ (pretty_print_evt_list c)); *)
  (* let p (x: Ast.Expression.t) (identifier: string): bool=
    (Str.string_match (Str.regexp "[0-9]+==$[a-z0-9]+") (print_evt x) 0)
  in
  if List.length (List.filter p c) > 1 
  then (false, [])
  else *)
  
  (* let start_time = Sys.time () in *)

  let cfg = [("model", "true")] in 
    let ctx = (mk_context cfg) in
      let cndts = exp_list_to_z3 c [] ctx in
        
        let g = (mk_goal ctx true false false) in
        (Goal.add g [ cndts ]) ;
        (*print_endline("-------------------");
        print_endline(Goal.to_string g) ;
        print_endline("-------------------");*)

        (
          let result = (Tactic.apply (and_then ctx (mk_tactic ctx ("ctx-solver-simplify")) (mk_tactic ctx "propagate-ineqs") []) g None) in
            (if is_decided_unsat (get_subgoal result 0) 
            then(
              (*print_endline("unsat");*)
              (* let finish_time = Sys.time () *)
              (* in sat_timer := !sat_timer +. (finish_time -. start_time); *)

              (false, [])
            )
            else( 
              (* print_endline("sat");
              print_endline("subgoals are: ");
              List.iter (fun x -> print_endline(Goal.to_string x)) (get_subgoals result);  *)
              let subgoals = get_subgoals result
              in let resulting_exp = [goals_to_exp subgoals] 
              (* in print_endline(pretty_print_evt_list [goals_to_exp subgoals]);
              print_endline("RESULTING:");
              print_endline (pretty_print_evt_list resulting_exp); *)
              in 
              
              (* let finish_time = Sys.time () *)
              (* in sat_timer := !sat_timer +. (finish_time -. start_time); *)
              
              (true, resulting_exp)
            ));
        )