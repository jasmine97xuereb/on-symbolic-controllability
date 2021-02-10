(*default visibility level suppresses all the output apart from final boolean value*)
(*basic visibility level prints the messages printed in the default level and the AST of the inputted monitor description*)
(*warnings visibility level prints the messages in the default and basic level and all the error messages and warnings*)
(*all_messages visibility level prints all the messages*)
let default = 0
let basic = 1 
let warnings = 2
let all_messages = 3
let timing = -1

(*mutable data structure to be used for defining the visibility level of printing*)
(*the default visibility level is 0 i.e. suppress all output *)
let visibilityLevel = ref 0 

let print (messageLevel: int) (message: string): unit = 
  if messageLevel <= !visibilityLevel
  then print_endline message
  else ()

let print_default (message: string) = 
  print default message

let print_basic (message: string) = 
  print basic message

let print_warnings (message: string) = 
  print warnings message

let print_all_messages (message: string) = 
  print all_messages message

let print_timing (message: string) = 
  print timing message
