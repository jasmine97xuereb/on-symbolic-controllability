open Map

type monitor_type = REDUCED of Ast.Monitor.t | ERROR of string 
type expression_type = INT of int | STRING of string | BOOL of bool | ERR of string
type cond_type = EXPRESSION of Ast.Expression.t | ERR_EXP of bool
type rec_mon = MONITOR of Ast.Monitor.t

(* Map Structure *)
module Variables = Map.Make(String)
module TVars = Map.Make(String) (*use for recursion unfolding*)

module rec VarTypes : sig
  type t = expression_type Variables.t
end = VarTypes

(*module rec TVarTypes : sig
  type t = expression_type Variables.t
end = VarTypes*)

(* Initialise an empty map *)
let map = Variables.empty
