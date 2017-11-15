%{

%}

%token <int> NUM
%token <string> ID
%token INT PLUS MINUS STAR SLASH EQUAL EQUALEQUAL LE LT GE GT NOT AND OR IF ELSE
    WHILE DO READ PRINT SEMICOLON BEGIN END VAR
%token LBRACE RBRACE LBLOCK RBLOCK LPAREN RPAREN EOF TRUE FALSE

%left SEMICOLON
%left OR
%left AND
%left LT LE GT GE EQUALEQUAL
%left PLUS MINUS
%left STAR SLASH 
%right NOT 
%nonassoc RPAREN
%nonassoc ELSE


%start program
%type <C.program> program
%%

program:
    stmt EOF { $1 }
    ;

stmt:
  | stmt SEMICOLON stmt { C.SEQ ($1, $3) }
  | stmt SEMICOLON { $1 }
  | ID EQUAL aexp { C.ASSIGN ($1, $3) }
  | IF LPAREN bexp RPAREN LBRACE stmt RBRACE ELSE LBRACE stmt RBRACE { C.IF ($3,$6,$10) }
  | IF LPAREN bexp RPAREN LBRACE stmt RBRACE { C.IF ($3,$6,C.SKIP) }
  | WHILE LPAREN bexp RPAREN LBRACE stmt RBRACE {C.WHILE ($3,$6)}
  | BEGIN VAR ID EQUAL aexp SEMICOLON stmt END { C.BLOCK ($3,$5,$7) }
  | READ LPAREN ID RPAREN { C.READ $3 }
  | PRINT LPAREN aexp RPAREN { C.PRINT $3 }
  ;

aexp:
  | aexp PLUS aexp  { C.ADD ($1,$3) }
  | aexp MINUS aexp { C.SUB ($1,$3) }
  | aexp STAR aexp  { C.MUL ($1,$3) }
  | NUM { C.CONST $1 }
  | ID { C.VAR $1 }
  | LPAREN aexp RPAREN { $2 }
  ;

bexp:
  | TRUE { C.TRUE }
  | FALSE { C.FALSE }
  | NOT bexp { C.NOT $2 }
  | aexp EQUALEQUAL aexp { C.EQ ($1,$3) }
  | aexp LE aexp { C.LT ($1,$3) } 
  | bexp AND bexp { C.AND ($1,$3) }
  | LPAREN bexp RPAREN { $2 }
  ;
%%

let parse_error s = print_endline s
