open Batteries
open BatList
open Elang
open Cfg
open Utils
open Prog

type reg = int
type rtl_cmp = Rclt | Rcle | Rcgt | Rcge | Rceq | Rcne

type rtl_instr =
  | Rbinop of binop * reg * reg * reg
  | Runop of unop * reg * reg
  | Rconst of reg * int
  | Rbranch of rtl_cmp * reg * reg * int
  | Rjmp of int
  | Rmov of reg * reg
  | Rret of reg
  | Rlabel of int
  | Rprint of reg
  | Rcall of reg option * string * reg list
  | Rstk of reg * int
  | Rload of reg * reg * int
  | Rstore of reg * reg * int
  | Rglobvar of reg * string

type rtl_fun = {
  rtlfunargs : reg list;
  rtlfunbody : (int, rtl_instr list) Hashtbl.t;
  rtlfunentry : int;
  rtlfuninfo : (string * reg) list;
  rtlfunstksz : int;
}

let written_rtl_regs_instr (i : rtl_instr) =
  match i with
  | Rglobvar (rd, _)
  | Rbinop (_, rd, _, _)
  | Runop (_, rd, _)
  | Rconst (rd, _)
  | Rmov (rd, _)
  | Rload (rd, _, _)
  | Rstk (rd, _)
  | Rcall (Some rd, _, _) ->
      Set.singleton rd
  | Rprint _ | Rret _ | Rlabel _
  | Rbranch (_, _, _, _)
  | Rjmp _ | Rstore _
  | Rcall (None, _, _) ->
      Set.empty

let written_rtl_regs (l : rtl_instr list) =
  List.fold_left
    (fun acc i -> Set.union acc (written_rtl_regs_instr i))
    Set.empty l
