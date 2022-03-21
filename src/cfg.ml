open Elang
open Prog
open Utils
open Batteries
open BatList

type expr =
  | Ebinop of binop * expr * expr
  | Eunop of unop * expr
  | Eint of int
  | Evar of string
  | Ecall of string * expr list
  | Estk of int
  | Eload of expr * int

type cfg_node =
  | Cassign of string * expr * int
  | Creturn of expr
  | Cprint of expr * int
  | Ccmp of expr * int * int
  | Cnop of int
  | Ccall of string * expr list * int
  | Cstore of expr * expr * int * int

type cfg_fun = {
  cfgfunargs : string list;
  cfgfunbody : (int, cfg_node) Hashtbl.t;
  cfgentry : int;
  cfgfunstksz : int;
}

type cprog = cfg_fun prog

(**  [succs cfg n] returns the set of successors of a node [n] in a CFG
   [cfg]. *)
let succs cfg n =
  match Hashtbl.find_option cfg n with
  | None -> Set.empty
  | Some (Ccall (_, _, succ))
  | Some (Cnop succ)
  | Some (Cprint (_, succ))
  | Some (Cassign (_, _, succ))
  | Some (Cstore (_, _, _, succ)) ->
      Set.singleton succ
  | Some (Creturn _) -> Set.empty
  | Some (Ccmp (_, s1, s2)) -> Set.of_list [ s1; s2 ]

(** [preds cfg n] returns the set of predecessors of a node [n] in the CFG [cfg].
   *)
let preds cfgfunbody n =
  Hashtbl.fold
    (fun m m' acc ->
      match m' with
      | Cassign (_, _, succ)
      | Cprint (_, succ)
      | Cnop succ
      | Ccall (_, _, succ)
      | Cstore (_, _, _, succ) ->
          if succ = n then Set.add m acc else acc
      | Creturn _ -> acc
      | Ccmp (_, s1, s2) -> if s1 = n || s2 = n then Set.add m acc else acc)
    cfgfunbody Set.empty

let size_binop b e1 e2 = 1 + e1 + e2
let size_unop u e = 1 + e

(** DEPRECATED / UNUSED *)
let rec size_expr (e : expr) : int =
  match e with
  | Ebinop (b, e1, e2) -> size_binop b (size_expr e1) (size_expr e2)
  | Eunop (u, e) -> size_unop u (size_expr e)
  | Eint _ -> 1
  | Evar v -> 1
  | _ -> 1

(** DEPRECATED / UNUSED *)
let rec size_instr (i : cfg_node) : int =
  match (i : cfg_node) with
  | Cassign (v, e, _) -> 1 + size_expr e
  | Creturn e -> 1 + size_expr e
  | Cprint (e, _) -> 1 + size_expr e
  | Ccmp (e, _, _) -> 1 + size_expr e
  | Cnop _ -> 1
  | _ -> 1

let size_fun f = Hashtbl.fold (fun k v acc -> acc + size_instr v) f 0
