(* eval $(opam config env --switch 4.06.0) *)
open Str
open Lexing
open PrettyPrint
open EnvResources
open SymRelation
open SymResources
open EnvFunctions
open ExpressionEvaluator
open VisibilityLevel

let parse_mon m = Parser.monitor Lexer.token (from_string m)

let rec parse_mon_list (ml: string list) (parsed_list: Ast.Monitor.t list): Ast.Monitor.t list =
  match ml with
    | [] -> parsed_list
    | m::ms -> parse_mon_list ms (parsed_list @ [parse_mon m])

let rec print_monitor_list (monList: Ast.Monitor.t list): string =
  match monList with
    | [] -> ""
    | ml::mls -> (pretty_print_monitor ml 0) ^ (print_monitor_list mls)

(*loop through all the monitors and check whether each one is symbolically controllable or not*)
let rec check_sym_controllability (monList: Ast.Monitor.t list) =
  match monList with
    | [] -> ()
    | m::ms -> 
      print_default (string_of_bool(isSymControllable [m])); 
      check_sym_controllability ms 

let time_it action arg =
      let start_time = Sys.time () in
      action arg;
      let finish_time = Sys.time () in
      (finish_time -. start_time)
         
let main =
  let mon_list = [Sys.argv.(1)^"\n"] in
    (*get the visibility level from the command line
    if it has not been enetered, then leave it to 0*)
    if Array.length Sys.argv > 2
    then visibilityLevel := int_of_string Sys.argv.(2);

    let parsed_monitor_list = parse_mon_list mon_list [] in
      print_basic ("\nAST REPRESENTATION OF MONITORS: " ^ print_monitor_list (parsed_monitor_list));

      (*check if the monitor list is well defined *)
      let free_vars = fv ([], parsed_monitor_list) (Vars.empty) in 
        (if Vars.is_empty free_vars
        then print_warnings ("Monitor is well-defined")
        else (
          print_warnings ("Monitor is not well-defined. The following variables are free: ");
          Vars.iter (fun v -> print_warnings v.name) free_vars;
          exit 0;
        ));

      (*make sure that all recursion variables are only bound once - otherwise rename them*)
      let final_mon_list = List.map (fun m -> rename_monvar m BoundTVars.empty) parsed_monitor_list in
        print_warnings ("After renaming bound tvariables, the monitor is " ^ pretty_print_monitor_list_string final_mon_list);
        
      print_all_messages ("SYMBOLIC CONTROLLABILITY:");
      let time_taken = time_it check_sym_controllability final_mon_list
        in print_basic ("time taken is " ^ string_of_float time_taken ^ " seconds");

