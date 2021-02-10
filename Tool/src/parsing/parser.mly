%{
open Ast
let identifier id = {
    Identifier.name = id;
}

let monitorvariable mv = {
    TVar.tvar = mv;
}

let const_int n = Expression.Literal(Literal.Int(n))

let const_bool b = Expression.Literal(Literal.Bool(b))

let binary_exp op left right = Expression.BinaryExp {
  Expression.BinaryExp.operator = op;
  Expression.BinaryExp.arg_lt = left;
  Expression.BinaryExp.arg_rt = right;
}

let unary_exp op argu = Expression.UnaryExp {
  Expression.UnaryExp.operator = op;
  Expression.UnaryExp.arg = argu;
}

let verdict v = match v with
    0 -> {Monitor.Verdict.verd = ZERO}
  | 1 -> {Monitor.Verdict.verd = ONE}
  | 2 -> {Monitor.Verdict.verd = TWO}
  | _ -> {Monitor.Verdict.verd = ERR}

let choice lt rt = Monitor.Choice {
  Monitor.Choice.left = lt;
  Monitor.Choice.right = rt;
}

let expression_guard label payload cons = Monitor.ExpressionGuard {
  Monitor.ExpressionGuard.label = label;
  Monitor.ExpressionGuard.payload = payload;
  Monitor.ExpressionGuard.consume = cons;
}

let quantified_guard label payload cons = Monitor.QuantifiedGuard {
  Monitor.QuantifiedGuard.label = label;
  Monitor.QuantifiedGuard.payload = payload;
  Monitor.QuantifiedGuard.consume = cons;
}

let if_then_else_exp cond if_tr if_fls = Monitor.Conditional {
  Monitor.Conditional.condition = cond;
  Monitor.Conditional.if_true = if_tr;
  Monitor.Conditional.if_false = if_fls;
}

let let_in v sub expr = Monitor.Evaluate {
  Monitor.Evaluate.var = v;
  Monitor.Evaluate.subst = sub;
  Monitor.Evaluate.stmt = expr;
}

let recX mv cons = Monitor.Recurse {
  Monitor.Recurse.monvar = mv;
  Monitor.Recurse.consume = cons;
}

%}

%token <int> INT
%token <string> TVAR
%token <string> IDENTIFIER
%token EQUAL
%token PLUS MINUS MULT DIV MOD
%token COMPARE AND OR LEQ GEQ
%token NOT
%token DOT
%token OP_ROUND CLS_ROUND
%token OP_ANGLE CLS_ANGLE
%token TRUE FALSE
%token IF THEN ELSE
%token LET IN
%token REC
%token EOL

%right COMPARE
%left  PLUS MINUS
%left  MULT DIV
%left MOD

%start monitor
%type <Ast.Monitor.t> monitor

%%
monitor:
  m = mon EOL { m }
;

mon:
  | monvar      {Monitor.TVar($1)}
  | monverdict  {Monitor.Verdict($1)}
  | choice      {$1} 
  | expguard    {$1}
  | quantguard  {$1}
  | ifthenelse  {$1}
  | letin       {$1}
  | recmon      {$1}
;

monvar:
  | mv = TVAR {monitorvariable mv}
;

monverdict:
  | INT {verdict $1}
;

choice:
  | OP_ROUND lt=mon CLS_ROUND PLUS OP_ROUND rt=mon CLS_ROUND {choice lt rt}
  | OP_ROUND lt=mon CLS_ROUND PLUS rt=choice {choice lt rt}
;

expguard:
  | label=ident; OP_ANGLE payload=expression; CLS_ANGLE DOT consume=mon;                   {expression_guard label payload consume}
  /* | label=ident; OP_ANGLE payload=expression; CLS_ANGLE DOT OP_ROUND consume=mon; CLS_ROUND {expression_guard label payload consume} */
;

quantguard:
  | label=ident; OP_ROUND payload=expression; CLS_ROUND DOT consume=mon;                   {quantified_guard label payload consume}
  /* | label=ident; OP_ROUND payload=expression; CLS_ROUND DOT OP_ROUND consume=mon; CLS_ROUND {quantified_guard label payload consume} */
;

ifthenelse:
  | IF cond=expression THEN if_tr=mon ELSE if_fls=mon                    {if_then_else_exp cond if_tr if_fls}
  | IF cond=expression THEN OP_ROUND if_tr=mon CLS_ROUND ELSE if_fls=mon                    {if_then_else_exp cond if_tr if_fls}
;

letin:
  | LET v=expression EQUAL sub=expression IN expr=mon                     {let_in v sub expr}
  | LET v=expression EQUAL sub=expression IN OP_ROUND expr=mon CLS_ROUND  {let_in v sub expr}
;

recmon:
  | REC mv=monvar DOT cons=mon                     {recX mv cons}
  | REC mv=monvar DOT OP_ROUND cons=mon CLS_ROUND  {recX mv cons}
;

expression:
  | ident                 {Expression.Identifier($1)}
  | literal               {$1}
  | binaryexp             {$1}
  | unaryexp              {$1}
;

ident:
  | id = IDENTIFIER {identifier id}
;

literal:
  | INT       {const_int $1}
  | boolean   {const_bool $1}
;

boolean:
  | TRUE    {true}
  | FALSE   {false}
;

binaryexp:
  | left = expression; op=bin_op; right = expression                       {binary_exp op left right}
  | OP_ROUND left = expression; op=bin_op; right = expression CLS_ROUND    {binary_exp op left right} 
;

%inline bin_op:
    PLUS      {Expression.BinaryExp.Plus}
  | MINUS     {Expression.BinaryExp.Minus}
  | MULT      {Expression.BinaryExp.Mult}
  | DIV       {Expression.BinaryExp.Div}
  | LEQ       {Expression.BinaryExp.Leq}
  | GEQ       {Expression.BinaryExp.Geq}
  | OP_ANGLE  {Expression.BinaryExp.Lt}
  | CLS_ANGLE {Expression.BinaryExp.Gt}
  | COMPARE   {Expression.BinaryExp.Compare}
  | AND       {Expression.BinaryExp.And}
  | OR        {Expression.BinaryExp.Or}
  | MOD       {Expression.BinaryExp.Mod}
;

unaryexp:
  | op=un_op argu=expression   {unary_exp op argu}
;
%inline un_op:
  | NOT   {Expression.UnaryExp.Not}
;
