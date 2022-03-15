open BatPrintf
open Batteries
open Utils

let string_of_position pos =
  let open Lexing in
  Printf.sprintf "%s:%d:%d" pos.pos_fname pos.pos_lnum
    (pos.pos_cnum - pos.pos_bol + 1)

type token =
  | SYM_EOF
  | SYM_IDENTIFIER of string
  | SYM_INTEGER of int
  | SYM_VOID
  | SYM_CHAR
  | SYM_INT
  | SYM_STRUCT
  | SYM_SEMICOLON
  | SYM_POINT
  | SYM_IF
  | SYM_ELSE
  | SYM_PLUS
  | SYM_MINUS
  | SYM_ASTERISK
  | SYM_DIV
  | SYM_EQUALITY
  | SYM_ASSIGN
  | SYM_LPARENTHESIS
  | SYM_RPARENTHESIS
  | SYM_LBRACE
  | SYM_RBRACE
  | SYM_WHILE
  | SYM_RETURN
  | SYM_COMMA
  | SYM_LT
  | SYM_LEQ
  | SYM_GT
  | SYM_GEQ
  | SYM_NOTEQ
  | SYM_MOD
  | SYM_BOOL_NOT
  | SYM_BOOL_AND
  | SYM_BOOL_OR
  | SYM_ARROW
  | SYM_BITWISE_OR
  | SYM_BITWISE_AND
  | SYM_BIT_NOT
  | SYM_XOR
  | SYM_CHARACTER of char
  | SYM_STRING of string
  | SYM_LBRACKET
  | SYM_RBRACKET
  | SYM_ALLOC
  | SYM_PRINT
  | SYM_EXTERN
  | SYM_INCLUDE of string
  | SYM_AMPERSAND

let string_of_symbol = function
  | SYM_EOF -> "SYM_EOF"
  | SYM_IDENTIFIER s -> Printf.sprintf "SYM_IDENTIFIER(%s)" s
  | SYM_INTEGER i -> Printf.sprintf "SYM_INTEGER(%d)" i
  | SYM_VOID -> "SYM_VOID"
  | SYM_CHAR -> "SYM_CHAR"
  | SYM_INT -> "SYM_INT"
  | SYM_STRUCT -> "SYM_STRUCT"
  | SYM_SEMICOLON -> "SYM_SEMICOLON"
  | SYM_POINT -> "SYM_POINT"
  | SYM_IF -> "SYM_IF"
  | SYM_ELSE -> "SYM_ELSE"
  | SYM_PLUS -> "SYM_PLUS"
  | SYM_MINUS -> "SYM_MINUS"
  | SYM_ASTERISK -> "SYM_ASTERISK"
  | SYM_DIV -> "SYM_DIV"
  | SYM_EQUALITY -> "SYM_EQUALITY"
  | SYM_ASSIGN -> "SYM_ASSIGN"
  | SYM_LPARENTHESIS -> "SYM_LPARENTHESIS"
  | SYM_RPARENTHESIS -> "SYM_RPARENTHESIS"
  | SYM_LBRACE -> "SYM_LBRACE"
  | SYM_RBRACE -> "SYM_RBRACE"
  | SYM_WHILE -> "SYM_WHILE"
  | SYM_RETURN -> "SYM_RETURN"
  | SYM_COMMA -> "SYM_COMMA"
  | SYM_LT -> "SYM_LT"
  | SYM_LEQ -> "SYM_LEQ"
  | SYM_GT -> "SYM_GT"
  | SYM_GEQ -> "SYM_GEQ"
  | SYM_NOTEQ -> "SYM_NOTEQ"
  | SYM_MOD -> "SYM_MOD"
  | SYM_BOOL_NOT -> "SYM_BOOL_NOT"
  | SYM_BOOL_AND -> "SYM_BOOL_AND"
  | SYM_BOOL_OR -> "SYM_BOOL_OR"
  | SYM_ARROW -> "SYM_ARROW"
  | SYM_BITWISE_OR -> "SYM_BITWISE_OR"
  | SYM_BITWISE_AND -> "SYM_BITWISE_AND"
  | SYM_BIT_NOT -> "SYM_BIT_NOT"
  | SYM_XOR -> "SYM_XOR"
  | SYM_CHARACTER c -> Printf.sprintf "SYM_CHARACTER(%c)" c
  | SYM_STRING s -> Printf.sprintf "SYM_STRING(%s)" s
  | SYM_LBRACKET -> "SYM_LBRACKET"
  | SYM_RBRACKET -> "SYM_RBRACKET"
  | SYM_ALLOC -> "SYM_ALLOC"
  | SYM_PRINT -> "SYM_PRINT"
  | SYM_EXTERN -> "SYM_EXTERN"
  | SYM_INCLUDE s -> Printf.sprintf "SYM_INCLUDE(%s)" s
  | SYM_AMPERSAND -> "SYM_AMPERSAND"
