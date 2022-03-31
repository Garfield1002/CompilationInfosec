open Batteries
open Elang
open Cfg
open Rtl
open Prog
open Utils
open Report
open Rtl_print
open Options

(* Une partie de la génération de RTL consiste à allouer les variables dans des
   pseudo-registres RTL.

   Ces registres sont en nombre illimité donc ce problème est facile.

   Étant donnés :
   - [next_reg], le premier numéro de registre disponible (pas encore alloué à
   une variable)
   - [var2reg], une liste d'associations dont les clés sont des variables et les
   valeurs des numéros de registres
   - [v] un nom de variable (de type [string]),

   [find_var (next_reg, var2reg) v] renvoie un triplet [(r, next_reg, var2reg)]:

   - [r] est le registre RTL associé à la variable [v]
   - [next_reg] est le nouveau premier registre disponible
   - [var2reg] est la nouvelle association nom de variable/registre.
*)
let find_var (next_reg, var2reg) v =
  match List.assoc_opt v var2reg with
  | Some r -> (r, next_reg, var2reg)
  | None -> (next_reg, next_reg + 1, assoc_set var2reg v next_reg)

(* [rtl_instrs_of_cfg_expr (next_reg, var2reg) e] construit une liste
   d'instructions RTL correspondant à l'évaluation d'une expression E.

   Le retour de cette fonction est un quadruplet [(r,l,next_reg,var2reg)], où :
   - [r] est le registre RTL dans lequel le résultat de l'évaluation de [e] aura
     été stocké
   - [l] est une liste d'instructions RTL.
   - [next_reg] est le nouveau premier registre disponible
   - [var2reg] est la nouvelle association nom de variable/registre.
*)
let rec rtl_instrs_of_cfg_expr (next_reg, var2reg) (e : expr) =
  match e with
  | Evar s ->
      let r, next_reg, var2reg = find_var (next_reg, var2reg) s in
      (r, [], next_reg, var2reg)
  | Eint i -> (next_reg, [ Rconst (next_reg, i) ], next_reg + 1, var2reg)
  | Ebinop (binop, e1, e2) ->
      let r1, l1, next_reg, var2reg =
        rtl_instrs_of_cfg_expr (next_reg, var2reg) e1
      in
      let r2, l2, next_reg, var2reg =
        rtl_instrs_of_cfg_expr (next_reg, var2reg) e2
      in
      ( next_reg,
        (Rbinop (binop, next_reg, r1, r2) :: l2) @ l1,
        next_reg + 1,
        var2reg )
  | Eunop (unop, e) ->
      let r, l, next_reg, var2reg =
        rtl_instrs_of_cfg_expr (next_reg, var2reg) e
      in
      (next_reg, Runop (unop, next_reg, r) :: l, next_reg + 1, var2reg)
  | Ecall (fname, params) ->
      let f (rs, ls, next_reg, var2reg) param =
        let r, l, next_reg, var2reg =
          rtl_instrs_of_cfg_expr (next_reg, var2reg) param
        in
        (r :: rs, l @ ls, next_reg, var2reg)
      in
      let rs, ls, next_reg, var2reg =
        List.fold_left f ([], [], next_reg, var2reg) params
      in
      ( next_reg,
        Rcall (Some next_reg, fname, List.rev rs) :: ls,
        next_reg + 1,
        var2reg )
  | Estk addr -> (next_reg, [ Rstk (next_reg, addr) ], next_reg + 1, var2reg)
  | Eload (e, sz) ->
      let rs, l, next_reg, var2reg =
        rtl_instrs_of_cfg_expr (next_reg, var2reg) e
      in
      (next_reg, Rload (next_reg, rs, sz) :: l, next_reg + 1, var2reg)
  | Eglobvar v -> (next_reg, [ Rglobvar (next_reg, v) ], next_reg + 1, var2reg)

let is_cmp_op = function
  | Eclt -> Some Rclt
  | Ecle -> Some Rcle
  | Ecgt -> Some Rcgt
  | Ecge -> Some Rcge
  | Eceq -> Some Rceq
  | Ecne -> Some Rcne
  | _ -> None

let rtl_cmp_of_cfg_expr (e : expr) =
  match e with
  | Ebinop (b, e1, e2) -> (
      match is_cmp_op b with
      | None -> (Rcne, e, Eint 0)
      | Some rop -> (rop, e1, e2))
  | _ -> (Rcne, e, Eint 0)

let rtl_instrs_of_cfg_node ((next_reg : int), (var2reg : (string * int) list))
    (c : cfg_node) =
  match c with
  | Cassign (s, e, i) -> (
      let r, l, next_reg, var2reg =
        rtl_instrs_of_cfg_expr (next_reg, var2reg) e
      in
      let o = List.find_opt (fun (s', _) -> s = s') var2reg in
      match o with
      | Some (s, i') -> (Rjmp i :: Rmov (i', r) :: l, next_reg, var2reg)
      | None ->
          ( Rjmp i :: Rmov (next_reg, r) :: l,
            next_reg + 1,
            (s, next_reg) :: var2reg ))
  | Creturn e ->
      let r, l, next_reg, var2reg =
        rtl_instrs_of_cfg_expr (next_reg, var2reg) e
      in
      (Rret r :: l, next_reg, var2reg)
  | Cprint (e, next) ->
      let r, l, next_reg, var2reg =
        rtl_instrs_of_cfg_expr (next_reg, var2reg) e
      in
      (Rjmp next :: Rprint r :: l, next_reg, var2reg)
  | Ccmp (e, i1, i2) ->
      let rtl_cmp, e1, e2 = rtl_cmp_of_cfg_expr e in
      let r1, l1, next_reg, var2reg =
        rtl_instrs_of_cfg_expr (next_reg, var2reg) e1
      in
      let r2, l2, next_reg, var2reg =
        rtl_instrs_of_cfg_expr (next_reg, var2reg) e2
      in
      ((Rjmp i2 :: Rbranch (rtl_cmp, r1, r2, i1) :: l2) @ l1, next_reg, var2reg)
  | Cnop _ -> ([], next_reg, var2reg)
  | Ccall (fname, params, next) ->
      let f (rs, ls, next_reg, var2reg) param =
        let r, l, next_reg, var2reg =
          rtl_instrs_of_cfg_expr (next_reg, var2reg) param
        in
        (r :: rs, l @ ls, next_reg, var2reg)
      in
      let rs, ls, next_reg, var2reg =
        List.fold_left f ([], [], next_reg, var2reg) params
      in
      (Rjmp next :: Rcall (None, fname, List.rev rs) :: ls, next_reg, var2reg)
  | Cstore (addr, e, sz, next) ->
      let rd, l1, next_reg, var2reg =
        rtl_instrs_of_cfg_expr (next_reg, var2reg) addr
      in
      let rs, l2, next_reg, var2reg =
        rtl_instrs_of_cfg_expr (next_reg, var2reg) e
      in
      ((Rjmp next :: Rstore (rd, rs, sz) :: l2) @ l1, next_reg, var2reg)

let rtl_instrs_of_cfg_fun cfgfunname
    ({ cfgfunargs; cfgfunbody; cfgentry; cfgfunstksz } : cfg_fun) =
  let rargs, next_reg, var2reg =
    List.fold_left
      (fun (rargs, next_reg, var2reg) a ->
        let r, next_reg, var2reg = find_var (next_reg, var2reg) a in
        (rargs @ [ r ], next_reg, var2reg))
      ([], 0, []) cfgfunargs
  in
  let rtlfunbody = Hashtbl.create 17 in
  let next_reg, var2reg =
    Hashtbl.fold
      (fun n node (next_reg, var2reg) ->
        let l, next_reg, var2reg =
          rtl_instrs_of_cfg_node (next_reg, var2reg) node
        in
        Hashtbl.replace rtlfunbody n (List.rev l);
        (next_reg, var2reg))
      cfgfunbody (next_reg, var2reg)
  in
  {
    rtlfunargs = rargs;
    rtlfunentry = cfgentry;
    rtlfunbody;
    rtlfuninfo = var2reg;
    rtlfunstksz = cfgfunstksz;
  }

let rtl_of_gdef funname = function
  | Gfun f -> Gfun (rtl_instrs_of_cfg_fun funname f)
  | Gvar (t, i) -> Gvar (t, i)

let rtl_of_cfg cp = List.map (fun (s, gd) -> (s, rtl_of_gdef s gd)) cp

let pass_rtl_gen cfg =
  let rtl = rtl_of_cfg cfg in
  dump !rtl_dump dump_rtl_prog rtl (fun file () ->
      add_to_report "rtl" "RTL" (Code (file_contents file)));
  OK rtl
