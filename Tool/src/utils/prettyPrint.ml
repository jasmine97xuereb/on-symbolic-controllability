(*print monitor descriptions in XML format from an AST*)
let rec tabulate tab = match tab with
  | 0 -> ""
  | _ -> "  " ^ tabulate (tab - 1)

let rec pretty_print_monitor input tab =
  let mon_to_string tree tab = match tree with
    | Ast.Monitor.TVar(x) -> print_tvar x tab
    | Ast.Monitor.Verdict(x) -> print_verdict x tab
    | Ast.Monitor.ExpressionGuard(x) -> print_exp_guard x tab
    | Ast.Monitor.QuantifiedGuard(x) -> print_quant_guard x tab
    | Ast.Monitor.Choice(x) -> print_choice x tab
    | Ast.Monitor.Conditional(x) -> print_conditional x tab
    | Ast.Monitor.Evaluate(x) -> print_eval x tab
    | Ast.Monitor.Recurse(x) -> print_recurse x tab
  in tabulate tab ^ "<Monitor>\n" ^
    mon_to_string input (tab + 1) ^
    tabulate tab ^ "</Monitor>"

and print_tvar (tv: Ast.TVar.t) tab =
  tabulate tab ^ "<TVAR>\n" ^
  tabulate (tab+1) ^ tv.tvar ^ "\n" ^
  tabulate tab ^ "</TVAR>\n"

and print_verdict (ver: Ast.Monitor.Verdict.t) tab: string =
  let rec str_oper(op: Ast.Monitor.Verdict.v): string = match op with
      ZERO -> "0"
    | ONE -> "1"
    | TWO -> "2"
    | ERR -> "ERR"
  in tabulate tab ^ "<Verdict>\n" ^
      tabulate (tab + 1) ^ str_oper ver.verd ^ "\n" ^
      tabulate tab ^ "</Verdict>\n"

and print_exp_guard tree tab =
  tabulate tab ^ "<ExpressionGuard>\n" ^
  print_identifier tree.label (tab + 1) ^
  print_expression tree.payload (tab + 1)^ "\n" ^
  pretty_print_monitor tree.consume (tab + 1) ^ "\n" ^
  tabulate tab ^ "</ExpressionGuard>\n"

and print_quant_guard tree tab =
  tabulate tab ^ "<QuantifiedGuard>\n" ^
  print_identifier tree.label (tab + 1) ^
  print_expression tree.payload (tab + 1) ^ "\n" ^
  pretty_print_monitor tree.consume (tab + 1) ^ "\n" ^
  tabulate tab ^ "</QuantifiedGuard>\n"

and print_choice tree tab =
  tabulate tab ^ "<Choice>\n" ^
  pretty_print_monitor tree.left (tab + 1) ^ "\n" ^
  pretty_print_monitor tree.right (tab + 1) ^ "\n" ^
  tabulate tab ^ "</Choice>\n"

and print_conditional tree tab =
  tabulate tab ^ "<Conditional>\n" ^
  print_expression tree.condition (tab + 1)^ "\n" ^
  pretty_print_monitor tree.if_true (tab + 1) ^ "\n" ^
  pretty_print_monitor tree.if_false (tab + 1) ^ "\n" ^
  tabulate tab ^ "\n</Conditional>\n"

and print_eval tree tab =
  tabulate tab ^ "<Evaluate>\n" ^
  print_expression tree.var (tab + 1) ^ "\n" ^
  print_expression tree.subst (tab + 1) ^ "\n" ^
  pretty_print_monitor tree.stmt (tab + 1) ^ "\n" ^
  tabulate tab ^ "</Evaluate>\n"

and print_recurse tree tab =
  tabulate tab ^ "<Recursion>\n" ^
  print_tvar tree.monvar (tab + 1) ^ "\n" ^
  pretty_print_monitor tree.consume (tab + 1) ^ "\n" ^
  tabulate tab ^ "</Recursion>\n"

and print_expression tree tab =
  let inside_exp_to_string tree tab = match tree with
      | Ast.Expression.Identifier(x) -> print_identifier x tab
      | Ast.Expression.Literal(x) -> print_literal x tab
      | Ast.Expression.BinaryExp(x) -> print_bin_exp x tab
      | Ast.Expression.UnaryExp(x) -> print_unary_exp x tab
  in tabulate tab ^ "<Expression>\n" ^
      inside_exp_to_string tree (tab + 1) ^
      tabulate tab ^ "</Expression>"

  and print_identifier (id: Ast.Identifier.t) tab =
    tabulate tab ^ "<Identifier>\n" ^
    tabulate (tab + 1) ^ id.name ^ "\n" ^
    tabulate tab ^ "</Identifier>\n"

and print_literal tree tab = match tree with
  | Ast.Literal.Int(n) -> tabulate tab ^ "<Literal>\n" ^
                          tabulate (tab + 1 ) ^ string_of_int n ^ "\n" ^
                          tabulate tab ^ "</Literal>\n"
  | Ast.Literal.Bool(b) -> tabulate tab ^ "<Literal>\n" ^
                            tabulate (tab + 1 ) ^ string_of_bool b ^ "\n" ^
                            tabulate tab ^ "</Literal>\n"

and print_bin_exp (tree: Ast.Expression.BinaryExp.t) tab: string =
  let str_bin_oper (op: Ast.Expression.BinaryExp.operator): string = match op with
    | Plus -> "+"
    | Minus -> "-"
    | Mult -> "*"
    | Div -> "/"
    | Leq -> "<="
    | Geq -> ">="
    | Lt -> "<"
    | Gt -> ">"
    | Compare -> "=="
    | And -> "&"
    | Or -> "|"
    | Mod -> "mod"

  in tabulate tab ^ "<BinaryExpression>\n" ^
    print_expression tree.arg_lt (tab + 1) ^ "\n" ^
    tabulate (tab+1) ^ str_bin_oper tree.operator ^ "\n" ^
    print_expression tree.arg_rt (tab + 1) ^ "\n" ^
    tabulate tab ^ "</BinaryExpression>\n"

and print_unary_exp (tree: Ast.Expression.UnaryExp.t) tab: string =
  let str_un_oper (op: Ast.Expression.UnaryExp.operator): string = match op with
    | Not -> "!"

  in tabulate tab ^ "<UnaryExpression>\n" ^
    tabulate (tab + 1) ^ str_un_oper tree.operator ^ "\n" ^
    print_expression tree.arg (tab + 1) ^ "\n" ^
    tabulate tab ^ "</UnaryExpression>\n"

let rec pretty_print_trace_list tr =
  let rec string_trc_list trc out = match trc with
      [] -> out
    | [t] -> (out ^ print_single_trace t)
    | t::ts -> string_trc_list ts (out ^ print_single_trace t ^ ";")
  in "Trace List:\n[" ^ string_trc_list tr ""  ^ "]\n"

and print_single_trace (tree: Ast.TraceElement.t) = match tree.payload with
  | Ast.Literal.Int(n) -> " label: " ^ tree.label.name ^ ", value: " ^ string_of_int n
  | Ast.Literal.Bool(b) -> " label: " ^ tree.label.name ^ ", value: " ^ string_of_bool b

let rec pretty_print_sym_event (se: Ast.SymbolicEvent.t list) =
  let rec string_symevt_list symevt out = match symevt with
      [] -> out
    | [s] -> (out ^ print_sym_evt s)
    | s::ss -> string_symevt_list ss (out ^ print_sym_evt s ^ ";")
  in "Symbolic Event List:\n[" ^ string_symevt_list se ""  ^ "]\n"

and print_sym_evt (tree: Ast.SymbolicEvent.t) = " label: " ^ tree.label.name ^ ", value: " ^ tree.payload.name

(*let rec pretty_print_sym_event (se: Ast.SymbolicEvent.t list) =
  let rec string_symevt_list symevt out = match symevt with
      [] -> out
    | [s] -> (out ^ print_sym_evt s)
    | s::ss -> string_symevt_list ss (out ^ print_sym_evt s ^ ";")
  in "Symbolic Event List:\n[" ^ string_symevt_list se ""  ^ "]\n"

and print_sym_evt (tree: Ast.SymbolicEvent.t) = 
  match tree with 
  | Ast.SymbolicEvent.SymbolicEvent(x) -> " label: " ^ x.label.name ^ ", value: " ^ x.payload.name
  | Ast.SymbolicEvent.Any -> "any"*)

let rec print_evt (tree:Ast.Expression.t)  =
  let inside_exp_to_string tree = match tree with
      | Ast.Expression.Identifier(x) -> print_identifier x 
      | Ast.Expression.Literal(x) -> print_literal x 
      | Ast.Expression.BinaryExp(x) -> print_bin_exp x 
      | Ast.Expression.UnaryExp(x) -> "(" ^ (print_unary_exp x) ^ ")" 
  in inside_exp_to_string tree 

and print_identifier (id: Ast.Identifier.t): string =
  id.name 
    
and print_literal tree = match tree with
  | Ast.Literal.Int(n) -> string_of_int n 
  | Ast.Literal.Bool(b) -> string_of_bool b

and print_bin_exp (tree: Ast.Expression.BinaryExp.t) =
  let str_bin_oper (op: Ast.Expression.BinaryExp.operator): string = match op with
    | Plus -> "+"
    | Minus -> "-"
    | Mult -> "*"
    | Div -> "/"
    | Leq -> "<="
    | Geq -> ">="
    | Lt -> "<"
    | Gt -> ">"
    | Compare -> "=="
    | And -> "&"
    | Or -> "|"
    | Mod -> "mod"
  in
    print_evt tree.arg_lt ^ str_bin_oper tree.operator ^ print_evt tree.arg_rt 

and print_unary_exp (tree: Ast.Expression.UnaryExp.t): string =
  let str_un_oper (op: Ast.Expression.UnaryExp.operator): string = match op with
    | Not -> "!"
  in str_un_oper tree.operator ^ print_evt tree.arg

(*let rec pretty_print_evt_list (se: Ast.Expression.t list) =
  let rec string_symevt_list symevt out = match symevt with
      [] -> out
    | [s] -> (out ^ print_evt s)
    | s::ss -> string_symevt_list ss (out ^ print_evt s ^ ";\n")
  in "Event List:\n[" ^ string_symevt_list se ""  ^ "]\n"
*)
let rec pretty_print_evt_list (se: Ast.Expression.t list) =
  let rec string_symevt_list symevt out = match symevt with
      [] -> out
    | [s] -> (out ^ print_evt s)
    | s::ss -> string_symevt_list ss (out ^ print_evt s ^ "; ")
  in "b = " ^ string_symevt_list se "" 

let rec rowToString r:string =
  match r with
  | [] -> ""
  | h :: [] -> string_of_int h
  | h :: t -> string_of_int h ^ ";" ^ (rowToString t)

let rec imageToString i =
  match i with
  | [] -> ""
  | h :: t -> "[" ^ (rowToString h) ^ "];\n" ^ (imageToString t)

(*to print a list of lists*)
let pp_my_image s =
  imageToString s

(*let rec print_nested (l: Ast.Expression.t list list): string = 
  match l with
  | [] -> ""
  | x::xs -> "[" ^ (pretty_print_evt_list x) ^ "];\n" ^ (print_nested xs)

let rec pretty_print_sc (l: Ast.Expression.t list list): string = 
  print_nested l
*)

let rec pretty_print_monitor_list (monList: Ast.Monitor.t list): string =
  match monList with
    | [] -> ""
    | ml::mls -> print_endline (pretty_print_monitor ml 0); pretty_print_monitor_list mls


(*--------------- to print string rep of monitor ---------------------*)

let rec pretty_print_monitor_string input =
  let mon_to_string tree = match tree with
    | Ast.Monitor.TVar(x) -> print_tvar_string x 
    | Ast.Monitor.Verdict(x) -> print_verdict_string x 
    | Ast.Monitor.ExpressionGuard(x) -> print_exp_guard_string x 
    | Ast.Monitor.QuantifiedGuard(x) -> print_quant_guard_string x 
    | Ast.Monitor.Choice(x) -> print_choice_string x 
    | Ast.Monitor.Conditional(x) -> print_conditional_string x 
    | Ast.Monitor.Evaluate(x) -> print_eval_string x 
    | Ast.Monitor.Recurse(x) -> print_recurse_string x 
  in mon_to_string input

and print_tvar_string (tv: Ast.TVar.t) =
  tv.tvar 

and print_verdict_string (ver: Ast.Monitor.Verdict.t): string =
  let rec str_oper(op: Ast.Monitor.Verdict.v): string = match op with
      ZERO -> "0"
    | ONE -> "1"
    | TWO -> "2"
    | ERR -> "ERR"
  in str_oper ver.verd

and print_exp_guard_string tree =
  print_identifier_string tree.label ^ "<" ^ print_expression_string tree.payload ^ ">." ^ pretty_print_monitor_string tree.consume

and print_quant_guard_string tree =
  print_identifier_string tree.label ^ "(" ^ print_expression_string tree.payload ^ ")." ^ pretty_print_monitor_string tree.consume 

and print_choice_string tree =
  pretty_print_monitor_string tree.left ^ " + " ^ pretty_print_monitor_string tree.right

and print_conditional_string tree =
  " if " ^ print_expression_string tree.condition ^ " then " ^ pretty_print_monitor_string tree.if_true ^ " else " ^ pretty_print_monitor_string tree.if_false 

and print_eval_string tree =
  " let " ^ print_expression_string tree.var ^ " = " ^ print_expression_string tree.subst ^ " in " ^ pretty_print_monitor_string tree.stmt

and print_recurse_string tree =
  " rec " ^ print_tvar_string tree.monvar ^ "." ^ pretty_print_monitor_string tree.consume 

and print_expression_string tree =
  let inside_exp_to_string tree = match tree with
      | Ast.Expression.Identifier(x) -> print_identifier_string x 
      | Ast.Expression.Literal(x) -> print_literal_string x 
      | Ast.Expression.BinaryExp(x) -> print_bin_exp_string x 
      | Ast.Expression.UnaryExp(x) -> print_unary_exp_string x 
  in inside_exp_to_string tree 

and print_identifier_string (id: Ast.Identifier.t) =
  id.name 
  
and print_literal_string tree = match tree with
  | Ast.Literal.Int(n) -> string_of_int n
  | Ast.Literal.Bool(b) -> string_of_bool b

and print_bin_exp_string (tree: Ast.Expression.BinaryExp.t): string =
  let str_bin_oper (op: Ast.Expression.BinaryExp.operator): string = match op with
    | Plus -> "+"
    | Minus -> "-"
    | Mult -> "*"
    | Div -> "/"
    | Leq -> "<="
    | Geq -> ">="
    | Lt -> "<"
    | Gt -> ">"
    | Compare -> "=="
    | And -> "&"
    | Or -> "|"
    | Mod -> "mod"
  in print_expression_string tree.arg_lt ^ str_bin_oper tree.operator ^ print_expression_string tree.arg_rt 

and print_unary_exp_string (tree: Ast.Expression.UnaryExp.t): string =
  let str_un_oper (op: Ast.Expression.UnaryExp.operator): string = match op with
    | Not -> "!"
  in str_un_oper tree.operator ^ print_expression_string tree.arg 

let rec pretty_print_monitor_list_string (monList: Ast.Monitor.t list): string =
  match monList with
    | [] -> ""
    | ml::mls -> pretty_print_monitor_string ml ^ "; " ^ pretty_print_monitor_list_string mls
