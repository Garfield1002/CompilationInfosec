open Batteries
open Cfg
open Elang_run
open Prog
open Utils
open Report
open Cfg_print
open Options

(** [simple_eval_eexpr e] evaluates an expression [e] with no variables.
Raises an exception if the expression contains variables. *)
(* let rec simple_eval_eexpr (e: expr) : int res=
   match e with
   | Ebinop (binop, e1, e2) ->
     simple_eval_eexpr e1 >>= fun i1 ->
     simple_eval_eexpr e2 >>= fun i2 ->
     OK (eval_binop binop i1 i2)
   | Eunop (unop, e) ->
     simple_eval_eexpr e >>= fun i ->
     OK (eval_unop unop i)
   | Eint i -> OK i
   | Evar s -> Error (Printf.sprintf "The variable %s appears in the expression" s) *)

(* If an expression contains variables, we cannot simply evaluate it. *)

(** [has_vars e] indicates whether [e] contains variables. *)
(* let rec has_vars (e: expr) =
     match e with
     | Evar _ -> true
     | Eint _ -> false
     | Eunop (_, e)        -> has_vars e
     | Ebinop (_, e1, e2)  -> has_vars e1 && has_vars e2

   let const_prop_binop b e1 e2 =
     let e = Ebinop (b, e1, e2) in
     if has_vars e
     then e
     else Eint (simple_eval_eexpr e)

   let const_prop_unop u e =
     let e = Eunop (u, e) in
     if has_vars e
     then e
     else Eint (simple_eval_eexpr e) *)

(** [const_prop_expr e] propogates constants in the expression [e]. *)
let rec const_prop_expr (e : expr) : expr =
  match e with
  | Ebinop (binop, e1, e2) -> (
      let e1 = const_prop_expr e1 in
      let e2 = const_prop_expr e2 in
      match (e1, e2) with
      | Eint i1, Eint i2 -> Eint (eval_binop binop i1 i2)
      | _ -> Ebinop (binop, e1, e2))
  | Eunop (unop, e) -> (
      let e = const_prop_expr e in
      match e with Eint i -> Eint (eval_unop unop i) | _ -> Eunop (unop, e))
  | _ -> e

let constant_propagation_instr (n : cfg_node) : cfg_node =
  match n with
  | Cassign (s, e, i) -> Cassign (s, const_prop_expr e, i)
  | Creturn e -> Creturn (const_prop_expr e)
  | Cprint (e, i) -> Cprint (const_prop_expr e, i)
  | Ccmp (e, i1, i2) -> Ccmp (const_prop_expr e, i1, i2)
  | _ -> n

let constant_propagation_fun
    ({ cfgfunargs; cfgfunbody; cfgentry } as f : cfg_fun) =
  let ht = Hashtbl.map (fun n m -> constant_propagation_instr m) cfgfunbody in
  { f with cfgfunbody = ht }

let constant_propagation_gdef = function
  | Gfun f -> Gfun (constant_propagation_fun f)

let constant_propagation p =
  if !Options.no_cfg_constprop then p else assoc_map constant_propagation_gdef p

let pass_constant_propagation p =
  let cfg = constant_propagation p in
  record_compile_result "Constprop";
  dump
    (!cfg_dump >*> fun s -> s ^ "1")
    dump_cfg_prog cfg
    (call_dot "cfg-after-cstprop" "CFG after Constant Propagation");
  OK cfg
