open Ast
open Batteries
open Prog
open Utils

type binop =
  | Eadd
  | Emul
  | Emod
  | Exor
  | Ediv
  | Esub (* binary operations *)
  | Eclt
  | Ecle
  | Ecgt
  | Ecge
  | Eceq
  | Ecne
(* comparisons *)

type unop = Eneg

type expr =
  | Ebinop of binop * (expr * typ) * (expr * typ)
  | Eunop of unop * expr
  | Eint of int
  | Evar of string
  | Ecall of string * expr list
  | Echar of char
  | Eaddr of expr
  | Eload of expr * typ
  | Egetfield of expr * string * string

type texpr = typ * expr

type instr =
  | Iassign of string * expr
  | Iif of expr * instr * instr
  | Iwhile of expr * instr
  | Iblock of instr list
  | Ireturn of expr
  | Iprint of expr
  | Icall of string * expr list
  | Istore of expr * expr * typ
  | Isetfield of expr * string * expr * string

type efun = {
  funargs : (string * typ) list;
  funbody : instr;
  funvartyp : (string, typ) Hashtbl.t;
  funrettype : typ;
  funvarinmem : (string, int) Hashtbl.t;
  funstksz : int;
}

type eprog = efun prog * (string, (string * typ) list) Hashtbl.t
