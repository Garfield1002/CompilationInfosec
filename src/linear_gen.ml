open Batteries
open Rtl
open Linear
open Prog
open Utils
open Report
open Linear_print
open Options
open Linear_liveness

(** [succs_of_rtl_instrs] returns the list of indexes of the successors of a list of [rtl_nodes]. *)
let rec succs_of_rtl_instrs (il : rtl_instr list) : int list =
  let succs_of_rtl_instr (i : rtl_instr) : int option =
    match i with
    | Rtl.Rbranch (_, _, _, s) -> Some s
    | Rtl.Rjmp s -> Some s
    | _ -> None
  in
  let f (acc : int list) (x : int option) =
    match x with None -> acc | Some n -> n :: acc
  in
  List.fold f [] (List.map succs_of_rtl_instr il)

(** [sort_blocks] sorts the elements of a CFG topologically. *)
let sort_blocks (nodes : (int, rtl_instr list) Hashtbl.t) entry =
  let rec add_block (order : int list) (n : int) : int list =
    if List.mem n order then order
    else
      let succs = succs_of_rtl_instrs (Hashtbl.find nodes n) in
      List.fold_left add_block (n :: order) succs
  in
  List.rev (add_block [] entry)

(** [remove_useless_jumps] removes jumps that are directly followed by their tag. *)
let rec remove_useless_jumps (l : rtl_instr list) =
  match l with
  | Rtl.Rjmp i1 :: Rtl.Rlabel i2 :: t when i1 = i2 ->
      Rtl.Rlabel i2 :: remove_useless_jumps t
  | h :: t -> h :: remove_useless_jumps t
  | [] -> []

(** [remove_useless_labels] remove labels that are never jumped to. *)
let remove_useless_labels (l : rtl_instr list) =
  let g (i : int) (inst : rtl_instr) : bool =
    match inst with
    | Rtl.Rjmp j when i = j -> true
    | Rtl.Rbranch (_, _, _, j) when i = j -> true
    | _ -> false
  in
  let f (inst : rtl_instr) : bool =
    match inst with Rtl.Rlabel i -> List.exists (g i) l | _ -> true
  in
  List.filter f l

let linear_of_rtl_fun
    ({ rtlfunargs; rtlfunbody; rtlfunentry; rtlfuninfo } : rtl_fun) =
  let block_order = sort_blocks rtlfunbody rtlfunentry in
  let linearinstrs =
    Rjmp rtlfunentry
    :: List.fold_left
         (fun l n ->
           match Hashtbl.find_option rtlfunbody n with
           | None -> l
           | Some li -> l @ (Rlabel n :: li))
         [] block_order
  in
  {
    linearfunargs = rtlfunargs;
    linearfunbody =
      linearinstrs |> remove_useless_jumps |> remove_useless_labels;
    linearfuninfo = rtlfuninfo;
  }

let linear_of_rtl_gdef = function Gfun f -> Gfun (linear_of_rtl_fun f)
let linear_of_rtl r = assoc_map linear_of_rtl_gdef r

let pass_linearize rtl =
  let linear = linear_of_rtl rtl in
  let lives = liveness_linear_prog linear in
  dump !linear_dump
    (fun oc -> dump_linear_prog oc (Some lives))
    linear
    (fun file () -> add_to_report "linear" "Linear" (Code (file_contents file)));
  OK (linear, lives)
