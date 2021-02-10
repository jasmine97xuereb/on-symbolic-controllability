{
  open Parser
}

let digit = ['0'-'9']
let sletter = ['a'-'z']
let bletter = ['A'-'Z']
let whitespace = [' ' '\t' '\r']

rule token = parse
   whitespace+                    {token lexbuf}
  |digit+ as lxm                  {INT(int_of_string lxm)}
  |'('                            {OP_ROUND}
  |')'                            {CLS_ROUND}
  |'.'                            {DOT}
  |'+'                            {PLUS}
  |'-'                            {MINUS}
  |'*'                            {MULT}
  |'/'                            {DIV}
  |'<'                            {OP_ANGLE}
  |'>'                            {CLS_ANGLE}
  |"<="                           {LEQ}
  |">="                           {GEQ}
  |"=="                           {COMPARE}
  |'='                            {EQUAL}
  |'&'                            {AND}
  |'|'                            {OR}
  |'!'                            {NOT}
  |"mod"                          {MOD}
  |"true"                         {TRUE}
  |"false"                        {FALSE}
  |"if"                           {IF}
  |"then"                         {THEN}
  |"else"                         {ELSE}
  |"let"                          {LET}
  |"in"                           {IN}
  |"rec"                          {REC}
  |bletter+as lxm                 {TVAR(lxm)}
  |sletter(sletter|digit)* as lxm {IDENTIFIER(lxm)}
  |'\n'                           {EOL}
