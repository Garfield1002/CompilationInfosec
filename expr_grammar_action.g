tokens SYM_EOF SYM_IDENTIFIER<string> SYM_INTEGER<int> SYM_CHARACTER<char> SYM_PLUS SYM_MINUS SYM_ASTERISK SYM_DIV SYM_MOD SYM_AMPERSAND SYM_STRUCT SYM_POINT
tokens SYM_LPARENTHESIS SYM_RPARENTHESIS SYM_LBRACE SYM_RBRACE
tokens SYM_ASSIGN SYM_SEMICOLON SYM_RETURN SYM_IF SYM_WHILE SYM_ELSE SYM_COMMA SYM_PRINT SYM_LBRACKET SYM_RBRACKET
tokens SYM_EQUALITY SYM_NOTEQ SYM_LT SYM_LEQ SYM_GT SYM_GEQ SYM_BOOL_NOT SYM_BOOL_OR SYM_BOOL_AND
tokens SYM_INT SYM_CHAR SYM_VOID SYM_ARROW

non-terminals S INSTR INSTRS BLOC ELSE EXPR FACTOR
non-terminals LPARAMS REST_PARAMS
non-terminals IDENTIFIER INTEGER
non-terminals FUNDEF
non-terminals ADD_EXPRS ADD_EXPR
non-terminals MUL_EXPRS MUL_EXPR
non-terminals CMP_EXPRS CMP_EXPR
non-terminals EQ_EXPRS EQ_EXPR
non-terminals FUNCALL CALL_PARAMS CALL_REST_PARAMS
non-terminals FUN_OR_VAR
non-terminals TYPE CHAR ASSIGNMENT FUNDEF_DECL
non-terminals TYPEPTR
non-terminals STRUCT_BODY STRUCTDEF_DECL STRUCTDEF FUN_OR_STRUCT_DEFS FUN_OR_STRUCT_DEF STRUCT ASSIGN_OR_IGNORE STRUCT_TABLE
non-terminals FUNDEF_OR_GLOBAL
non-terminals OR_EXPR AND_EXPR BAND_EXPR OR_EXPRS AND_EXPRS BAND_EXPRS

axiom S
{
  open Symbols
  open Ast
  open BatPrintf
  open BatBuffer
  open Batteries
  open Utils
}

/* Comment test */

rules
S           -> FUN_OR_STRUCT_DEFS SYM_EOF         { Node (Tlistglobdef, $1) }

IDENTIFIER  -> SYM_IDENTIFIER                     { StringLeaf $1 }

CHAR        -> SYM_CHARACTER                      { CharLeaf $1}

INTEGER     -> SYM_INTEGER                        { IntLeaf $1 }

TYPE        -> SYM_CHAR TYPEPTR                   { TypeLeaf ($2 Prog.Tchar) }
TYPE        -> SYM_INT TYPEPTR                    { TypeLeaf ($2 Prog.Tint)  }
TYPE        -> SYM_VOID TYPEPTR                   { TypeLeaf ($2 Prog.Tvoid) }
TYPE        -> SYM_STRUCT SYM_IDENTIFIER TYPEPTR  { TypeLeaf ($3 (Prog.Tstruct $2)) }

TYPEPTR -> SYM_ASTERISK TYPEPTR                   { fun t -> $2 (Tptr t) }
TYPEPTR ->                                        { identity }

FUNCALL     -> SYM_LPARENTHESIS CALL_PARAMS SYM_RPARENTHESIS { fun identifier -> Node(Tcall, [identifier; Node(Targs, $2)])}

CALL_PARAMS -> EXPR CALL_REST_PARAMS                { $1::$2 }
CALL_PARAMS ->                                      { [] }

CALL_REST_PARAMS -> SYM_COMMA EXPR CALL_REST_PARAMS { $2::$3 }
CALL_REST_PARAMS ->                                 { [] }

FUN_OR_STRUCT_DEFS -> TYPE FUN_OR_STRUCT_DEF FUN_OR_STRUCT_DEFS { ($2 $1)::$3 }
FUN_OR_STRUCT_DEFS ->                                           { [] }

FUN_OR_STRUCT_DEF -> IDENTIFIER FUNDEF_OR_GLOBAL    { $2 $1 }
FUN_OR_STRUCT_DEF -> STRUCTDEF                      { $1 }

FUNDEF_OR_GLOBAL -> FUNDEF                          { $1 }
FUNDEF_OR_GLOBAL -> ASSIGNMENT SYM_SEMICOLON        { $1 }

FUNDEF      -> SYM_LPARENTHESIS LPARAMS SYM_RPARENTHESIS FUNDEF_DECL { fun id t -> Node (Tfundef, t :: Node (Tfunname, [id]) :: Node (Tfunargs, $2) :: $4) }

FUNDEF_DECL -> INSTR                                { [Node (Tfunbody, [$1])] }
FUNDEF_DECL -> SYM_SEMICOLON                        { [] }

STRUCTDEF ->  STRUCTDEF_DECL SYM_SEMICOLON          { fun t -> Node(Tstructdef, [t; Node(Tstructbody, $1)])}

STRUCTDEF_DECL -> SYM_LBRACE STRUCT_BODY SYM_RBRACE { $2 }
STRUCTDEF_DECL ->                                   { [] }

STRUCT_BODY -> TYPE IDENTIFIER STRUCT_TABLE SYM_SEMICOLON STRUCT_BODY  {($3 $1 $2)::$5}
/* STRUCT_BODY -> STRUCTDEF STRUCT_BODY */
STRUCT_BODY ->  {[]}

STRUCT_TABLE  -> SYM_LBRACKET SYM_INTEGER SYM_RBRACKET  { fun t i -> Node (Tdeclare, [TypeLeaf (Ttab (type_of_leaf t, $2)); i;]) }
STRUCT_TABLE  ->                                        { fun t i -> Node (Tdeclare, [t; i]) }

LPARAMS     -> TYPE IDENTIFIER REST_PARAMS            { Node (Targ, [$1; $2])::$3}
LPARAMS     ->                                        { [] }

REST_PARAMS -> SYM_COMMA TYPE IDENTIFIER REST_PARAMS  { Node (Targ, [$2; $3])::$4 }
REST_PARAMS ->                                        { [] }

INSTR       -> SYM_IF SYM_LPARENTHESIS EXPR SYM_RPARENTHESIS BLOC ELSE  { Node (Tif, [$3; $5; $6]) }
INSTR       -> SYM_WHILE SYM_LPARENTHESIS EXPR SYM_RPARENTHESIS INSTR   { Node (Twhile, [$3; $5]) }
INSTR       -> SYM_RETURN EXPR SYM_SEMICOLON                            { Node (Treturn, [$2]) }
INSTR       -> SYM_PRINT EXPR SYM_SEMICOLON                             { Node (Tprint, [$2]) }
INSTR       -> BLOC                                                     { $1 }
INSTR       -> TYPE IDENTIFIER ASSIGNMENT SYM_SEMICOLON                 { $3 $2 $1 }
INSTR       -> EXPR ASSIGN_OR_IGNORE SYM_SEMICOLON                      { $2 $1 }

ASSIGN_OR_IGNORE -> SYM_ASSIGN EXPR               { fun e -> Node (Tassign, [e; $2]) }
ASSIGN_OR_IGNORE ->                               { identity }

ASSIGNMENT  -> SYM_ASSIGN EXPR                        { fun i t -> Node (Tdeclare, [t; i; $2]) }
ASSIGNMENT  -> SYM_LBRACKET SYM_INTEGER SYM_RBRACKET  { fun i t -> Node (Tdeclare, [TypeLeaf (Ttab (type_of_leaf t, $2)); i;]) }
ASSIGNMENT  ->                                        { fun i t -> Node (Tdeclare, [t; i]) }

FUN_OR_VAR  -> FUNCALL                            { $1 }
FUN_OR_VAR  ->                                    { identity }

EXPR        -> OR_EXPR OR_EXPRS                   { resolve_associativity $1 $2 }

OR_EXPR     -> AND_EXPR AND_EXPRS                 { resolve_associativity $1 $2 }

AND_EXPR    -> BAND_EXPR BAND_EXPRS               { resolve_associativity $1 $2 }

BAND_EXPR   -> EQ_EXPR EQ_EXPRS                   { resolve_associativity $1 $2 }

EQ_EXPR     -> CMP_EXPR CMP_EXPRS                 { resolve_associativity $1 $2 }

CMP_EXPR    -> ADD_EXPR ADD_EXPRS                 { resolve_associativity $1 $2 }

ADD_EXPR    -> MUL_EXPR MUL_EXPRS                 { resolve_associativity $1 $2 }

MUL_EXPR    -> FACTOR                             { $1 }
MUL_EXPR    -> SYM_PLUS MUL_EXPR                  { $2 }
MUL_EXPR    -> SYM_BOOL_NOT MUL_EXPR              { Node (Tnot, [$2]) }
MUL_EXPR    -> SYM_MINUS MUL_EXPR                 { Node (Tneg, [$2]) }
MUL_EXPR    -> SYM_AMPERSAND MUL_EXPR             { Node (Taddrof, [$2]) }
MUL_EXPR    -> SYM_ASTERISK MUL_EXPR              { Node (Tindirection, [$2]) }

FACTOR      -> CHAR                                           { Node (Tchar, [$1])}
FACTOR      -> INTEGER                                        { Node (Tint, [$1]) }
FACTOR      -> SYM_LPARENTHESIS EXPR SYM_RPARENTHESIS STRUCT  { $4 $2 }
FACTOR      -> IDENTIFIER FUN_OR_VAR STRUCT                   { $3 ($2 $1) }

STRUCT      ->  SYM_LBRACKET EXPR SYM_RBRACKET STRUCT         { fun e -> $4 (Node(Tarray, [e; $2])) }
STRUCT      ->  SYM_POINT IDENTIFIER STRUCT       { fun e -> $3 (Node(Tstruct, [e; $2])) }
STRUCT      ->  SYM_ARROW IDENTIFIER STRUCT       { fun e -> $3 (Node(Tarrow, [e; $2])) }
STRUCT      ->                                    { identity }

MUL_EXPRS   -> SYM_ASTERISK MUL_EXPR MUL_EXPRS    { Node (Tmul, [$2])::$3 }
MUL_EXPRS   -> SYM_DIV MUL_EXPR MUL_EXPRS         { Node (Tdiv, [$2])::$3 }
MUL_EXPRS   -> SYM_MOD MUL_EXPR MUL_EXPRS         { Node (Tmod, [$2])::$3 }
MUL_EXPRS   ->                                    { [] }

ADD_EXPRS   -> SYM_PLUS  ADD_EXPR ADD_EXPRS       { Node (Tadd, [$2])::$3 }
ADD_EXPRS   -> SYM_MINUS ADD_EXPR ADD_EXPRS       { Node (Tsub, [$2])::$3 }
ADD_EXPRS   ->                                    { [] }

CMP_EXPRS   -> SYM_LT   CMP_EXPR CMP_EXPRS        { Node(Tclt, [$2])::$3 }
CMP_EXPRS   -> SYM_LEQ  CMP_EXPR CMP_EXPRS        { Node(Tcle, [$2])::$3 }
CMP_EXPRS   -> SYM_GT   CMP_EXPR CMP_EXPRS        { Node(Tcgt, [$2])::$3 }
CMP_EXPRS   -> SYM_GEQ  CMP_EXPR CMP_EXPRS        { Node(Tcge, [$2])::$3 }
CMP_EXPRS   ->                                    { [] }

EQ_EXPRS    -> SYM_EQUALITY EQ_EXPR EQ_EXPRS      { Node (Tceq, [$2])::$3 }
EQ_EXPRS    -> SYM_NOTEQ EQ_EXPR EQ_EXPRS         { Node (Tcne, [$2])::$3 }
EQ_EXPRS    ->                                    { [] }

BAND_EXPRS  -> SYM_AMPERSAND BAND_EXPR BAND_EXPRS { Node (Tband, [$2])::$3 }
BAND_EXPRS  ->                                    { [] }

AND_EXPRS   -> SYM_BOOL_AND AND_EXPR AND_EXPRS    { Node (Tand, [$2])::$3 }
AND_EXPRS   ->                                    { [] }

OR_EXPRS    -> SYM_BOOL_OR OR_EXPR OR_EXPRS       { Node (Tor, [$2])::$3 }
OR_EXPRS    ->                                    { [] }

ELSE        -> SYM_ELSE BLOC                      { $2 }
ELSE        ->                                    { NullLeaf }

BLOC        -> SYM_LBRACE INSTRS SYM_RBRACE       { Node (Tblock, $2) }

INSTRS      -> INSTR INSTRS                       { $1::$2 }
INSTRS      ->                                    { []  }
