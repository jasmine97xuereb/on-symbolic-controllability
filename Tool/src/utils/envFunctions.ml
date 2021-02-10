open EnvResources
open PrettyPrint

(*let tvar_counter = ref 0 *)(*counter used to generate fresh tvars*)

(*create fresh tvariables*)
let fresh_tvar (last: int): Ast.TVar.t =
  {Ast.TVar.tvar = "@" ^ string_of_int(last+1)}

(*miscellaneous functions used throughout the definition implementations for comparison and creating structures*)
let get_bool_compare_result (i: int): bool =
  match i with
     | 0 -> true
     | _ -> false

let compare_values (v1: expression_type) (v2: expression_type): bool =
  match v1, v2 with
    | STRING(v1), STRING(v2) -> v1 = v2
    | INT(v1), INT(v2) -> v1 = v2
    | BOOL(v1), BOOL(v2) -> v1 = v2
    | _, _ -> false

let rec element_exists_in_list l e : bool =
  match l with
    | l::ls -> if (l == e)
        then true
        else element_exists_in_list ls e
    | [] -> false
    
let rec match_lists list1 list2: bool =
  if (List.length list1 == List.length list2)
    then (List.for_all (fun elem -> (List.mem elem) list2) list1)
    else false

let rec element_exists_in_relation (rel) (elem): bool =
  match rel with
    | [] -> false
    | r::rs -> (if (match_lists r elem) then true else (element_exists_in_relation rs elem))

let rec tuple_exists_in_relation (cm: (Ast.Expression.t list * Ast.Monitor.t list)) (relation: (Ast.Expression.t list * Ast.Monitor.t list) list): bool = 
  let mon_string = pretty_print_monitor_list_string (snd cm) in
  let con_string = pretty_print_evt_list (fst cm) in
  match relation with
  | [] -> false
  | x::xs -> 
    if (String.equal mon_string (pretty_print_monitor_list_string (snd x)) && String.equal con_string (pretty_print_evt_list (fst x)))
    then true
    else tuple_exists_in_relation cm xs

let rec pretty_print_relation (relation: (Ast.Expression.t list * Ast.Monitor.t list) list) = 
  match relation with 
  | [] -> ""
  | x::xs -> "<" ^ (pretty_print_evt_list (fst x)) ^ ", " ^ pretty_print_monitor_list_string (snd x) ^ ">\n" ^ (pretty_print_relation xs)

let rec mon_exists (mon_list: Ast.Monitor.t list) (mon: Ast.Monitor.t) : bool = 
  let mon_string = pretty_print_monitor mon 0 in 
    let rec check_next_mon (mon_list: Ast.Monitor.t list) = 
      match mon_list with 
      | [] -> false
      | m1::m2 -> 
        if ((String.compare (pretty_print_monitor m1 0) mon_string) == 0) 
        then true  (*monitor exists in list*)
        else check_next_mon m2
    in check_next_mon mon_list

let add_verdict (ver: int): Ast.Monitor.t = match ver with
  | 0 -> Ast.Monitor.Verdict{Ast.Monitor.Verdict.verd = ZERO}
  | 1 -> Ast.Monitor.Verdict{Ast.Monitor.Verdict.verd = ONE}
  | 2 -> Ast.Monitor.Verdict{Ast.Monitor.Verdict.verd = TWO}
  | _ -> Ast.Monitor.Verdict{Ast.Monitor.Verdict.verd = ERR}

let create_literal (l: expression_type): Ast.Literal.t =
  match l with
    | INT(x) -> Ast.Literal.Int(x)
    | BOOL(x) -> Ast.Literal.Bool(x)
    | _ -> Ast.Literal.Bool(false)

let create_identifier (id: expression_type): Ast.Identifier.t = 
  match id with
    | STRING(x) -> {Ast.Identifier.name = x}
    | _ -> {Ast.Identifier.name = "x"}

let create_tvar (tvar: string) =
  Ast.Monitor.TVar{tvar}

let create_choice_mon (left: Ast.Monitor.t) (right: Ast.Monitor.t) = 
  Ast.Monitor.Choice(
    {Ast.Monitor.Choice.left = left;
    Ast.Monitor.Choice.right = right; 
  })

let create_exp_guard_mon (label: Ast.Identifier.t) (payload: Ast.Expression.t) (consume: Ast.Monitor.t) =
  Ast.Monitor.ExpressionGuard(
    {Ast.Monitor.ExpressionGuard.label = label;
    Ast.Monitor.ExpressionGuard.payload = payload;
    Ast.Monitor.ExpressionGuard.consume = consume; 
  })

let create_recurse_mon (monvar: Ast.TVar.t) (consume: Ast.Monitor.t) = 
  Ast.Monitor.Recurse(
    {Ast.Monitor.Recurse.monvar = monvar;
    Ast.Monitor.Recurse.consume = consume; 
  })

let create_evaluate_mon (var: Ast.Expression.t) (subst: Ast.Expression.t) (stmt: Ast.Monitor.t) = 
  Ast.Monitor.Evaluate({    
    Ast.Monitor.Evaluate.var = var;
    Ast.Monitor.Evaluate.subst = subst;
    Ast.Monitor.Evaluate.stmt = stmt;  
  })

let create_conditional_mon (condition: Ast.Expression.t) (if_true: Ast.Monitor.t) (if_false: Ast.Monitor.t) = 
  Ast.Monitor.Conditional( 
    {Ast.Monitor.Conditional.condition = condition;
    Ast.Monitor.Conditional.if_true = if_true;
    Ast.Monitor.Conditional.if_false = if_false; 
  })

let create_quant_guard_mon (label: Ast.Identifier.t) (payload: Ast.Expression.t) (consume: Ast.Monitor.t) = 
  Ast.Monitor.QuantifiedGuard( 
    {Ast.Monitor.QuantifiedGuard.consume = consume;
    Ast.Monitor.QuantifiedGuard.payload = payload;
    Ast.Monitor.QuantifiedGuard.label = label; 
  })

let create_trace_element (lbl: Ast.Identifier.t) (pyld: Ast.Literal.t) = {
    Ast.TraceElement.label = lbl;
    Ast.TraceElement.payload = pyld;
}

let create_symbolic_evt (lbl: Ast.Identifier.t) (pyld: Ast.Identifier.t) = {
    Ast.SymbolicEvent.label = lbl;
    Ast.SymbolicEvent.payload = pyld;
}

let create_exp_identifier (id: string): Ast.Expression.t =
  Ast.Expression.Identifier {
    Ast.Identifier.name = id
  }

let add_binary_condition (arg_lt: Ast.Expression.t) (arg_rt: Ast.Expression.t) (op: Ast.Expression.BinaryExp.operator) = 
  Ast.Expression.BinaryExp ({
    Ast.Expression.BinaryExp.operator = op;
    Ast.Expression.BinaryExp.arg_lt = arg_lt;
    Ast.Expression.BinaryExp.arg_rt = arg_rt;
  })

let add_unary_condition (ex: Ast.Expression.t) = Ast.Expression.UnaryExp {
  Ast.Expression.UnaryExp.operator = Ast.Expression.UnaryExp.Not;
  Ast.Expression.UnaryExp.arg = ex;
}

let rec check_sevt_exists (l: Ast.SymbolicEvent.t list) (sevt: Ast.SymbolicEvent.t): bool = 
  match l with
    | [] -> false
    | l::ls -> 
     if((String.compare sevt.label.name l.label.name == 0) && (String.compare sevt.payload.name l.payload.name == 0))
        then true
      else check_sevt_exists ls sevt

(*checks if s2 is a substring of s1*)
let contains s1 s2 =
  try
    let len = String.length s2 in
    for i = 0 to String.length s1 - len do
      if String.sub s1 i len = s2 then raise Exit
    done;
    false
  with Exit -> true

let rec check_exp_exists (l: Ast.Expression.t list) (evt: Ast.Expression.t): bool = 
  match l with
    | [] -> false
    | _ -> 
      contains (pretty_print_evt_list l) (pretty_print_evt_list [evt]) 

let rec check_tvar_exists (l: Ast.TVar.t list) (tvar: Ast.TVar.t): bool =
    match l with 
    | [] -> false
    | x::xs -> 
      if x.tvar == tvar.tvar 
      then true
      else check_tvar_exists xs tvar

(*adds unique elements only to new_list and concatenates it with existing list mon_list*)
(* let rec add_monitors_not_in_list (mon_list) (to_check) (new_list) =
  match to_check with 
  | [] -> mon_list @ new_list
  | y::z -> 
    if mon_exists new_list y 
    then add_monitors_not_in_list mon_list z (new_list) 
    else add_monitors_not_in_list mon_list z (new_list @ [y]) *)

(*adds unique elements only to new_list and concatenates it with existing list mon_list*)
let rec add_monitors_not_in_list (mon_list: Ast.Monitor.t list) (to_check: Ast.Monitor.t list): Ast.Monitor.t list =
  List.sort_uniq compare (mon_list @ to_check)

(*create a list of n consecutive numbers*)
let rec create_list (n:int): int list =
  match n with 
    | 0 -> []
    | some_n -> some_n :: (create_list (n-1))  

(*predicate function that takes an Ast Expressions and returns a boolean value*)
(*if e is a binary expression with an Equal operator, return true, else return false*)
let check_comparison (e: Ast.Expression.t): bool = 
  match e with
  | Ast.Expression.BinaryExp(x) ->
    (match x.arg_lt, x.operator, x.arg_rt with
    (* | Ast.Expression.Identifier(x), Compare, Ast.Expression.Identifier(y) -> true *)
    | Ast.Expression.Literal(x), Compare, Ast.Expression.Identifier(y) -> true
    | Ast.Expression.Identifier(x), Compare, Ast.Expression.Literal(y) -> true
    (* | Ast.Expression.Literal(x), Compare, Ast.Expression.Literal(y) -> true *)
    | _ -> false)
  | _ -> false

(*takes a lists of lists and a list of expressions*)
(*adds each list in to_add to condition_list*)
(*ex. combine [[a,b],[c,d]] [x,y,z] -> [[a,b,x,y,z], [c,d,x,y,z]] *)
let rec combine (to_add: Ast.Expression.t list list) (condition_list: Ast.Expression.t list): Ast.Expression.t list list =
    match to_add with 
    | [] -> [condition_list]
    | x::[] -> [condition_list @ x]
    | x::xs -> [condition_list @ x] @ (combine xs condition_list)