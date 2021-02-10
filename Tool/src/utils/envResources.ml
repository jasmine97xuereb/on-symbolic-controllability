open Map

type monitor_type = REDUCED of Ast.Monitor.t | ERROR of string 
type expression_type = INT of int | STRING of string | BOOL of bool | ERR of string
type cond_type = EXPRESSION of Ast.Expression.t | ERR_EXP of bool
type cm =  Ast.Expression.t list * Ast.Monitor.t list

(* used for union-find algorithm *)
type t = { parent: int array; rank: int array; tvar: Ast.TVar.t list }

(* type truth = TRUE | FALSE | UNDECIDED *)

(* map uses for recursion unfolding *)
module TVars = Map.Make(String) 

(* used to store the mappings from cm to reachable cms *) 
module ReachableMonitorsMap =
  Map.Make(struct type t = cm let compare = compare end)

(* set structure for identifiers - used in fv() function *)
module Vars = 
  Set.Make(struct type t = Ast.Identifier.t let compare = compare end)

(* used to rename bound tvars *)
module BoundTVars = 
  Set.Make(struct type t = Ast.TVar.t let compare = compare end)

(* used to rename bound variables *)  
module BoundVars = 
  Set.Make(struct type t = Ast.Expression.t let compare = compare end)

module CMSet =
  Set.Make(struct type t = cm let compare = compare end)

module DepTVars = 
  Set.Make(struct type t = Ast.TVar.t list let compare = compare end)

module VerdictSet = 
  Set.Make(struct type t = Ast.Monitor.Verdict.t let compare = compare end)

module CMReachesVS = 
  Set.Make(struct type t = VerdictSet.t * CMSet.t let compare = compare end)