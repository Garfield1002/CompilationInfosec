open Batteries
open Cfg
open Prog
open Utils
open Cfg_liveness
open Report
open Cfg_print
open Options

(* Dead Assign Elimination  -- Élimination des affectations mortes *)

let rec has_fcall (e : expr) =
  match e with
  | Ebinop (_, e1, e2) -> has_fcall e1 || has_fcall e2
  | Eload (e, _) | Eunop (_, e) -> has_fcall e
  | Ecall _ -> true
  | _ -> false

(* [dead_assign_elimination_fun f] élimine les affectations mortes dans la
   function [f]. Cette fonction renvoie un couple [(f',c)] oú [f'] est la
   nouvelle fonction, et [c] est un booléen qui indique si du progrès a été
   fait. *)
let dead_assign_elimination_fun
    ({ cfgfunargs; cfgfunbody; cfgentry } as f : cfg_fun) =
  let lives = live_cfg_fun f in
  let changed =
    Hashtbl.fold
      (fun (n : int) (m : cfg_node) (acc : bool) ->
        match m with
        | Cassign (s, e, i) ->
            let lan = live_after_node cfgfunbody n lives in
            if Set.mem s lan || has_fcall e then acc
            else (
              Hashtbl.replace cfgfunbody n (Cnop i);
              true)
        | _ -> acc)
      cfgfunbody false
  in
  (f, changed)

(* Applique l'élimination de code mort autant de fois que nécessaire. Testez
   notamment sur le fichier de test [basic/useless_assigns.e]. *)
let rec iter_dead_assign_elimination_fun f =
  let f, c = dead_assign_elimination_fun f in
  if c then iter_dead_assign_elimination_fun f else f

let dead_assign_elimination_gdef gd =
  match gd with Gfun f -> Gfun (iter_dead_assign_elimination_fun f) | _ -> gd

let dead_assign_elimination p =
  if !Options.no_cfg_dae then p else assoc_map dead_assign_elimination_gdef p

let pass_dead_assign_elimination cfg =
  let cfg = dead_assign_elimination cfg in
  record_compile_result "DeadAssign";
  dump
    (!cfg_dump >*> fun s -> s ^ "2")
    dump_cfg_prog cfg
    (call_dot "cfg-after-dae" "CFG after DAE");
  OK cfg
