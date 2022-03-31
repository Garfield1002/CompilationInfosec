open Batteries
open Elang
open Cfg
open Utils
open Prog
open Report
open Cfg_print
open Options

let cfg_fun_of_efun typ_struct
    ({ funargs; funvartyp; funvarinmem; funbody; funstksz } : Elang.efun) =
  (* [cfg_expr_of_eexpr e] converts an [Elang.expr] into a [expr res]. This should
     always succeed and be straightforward.

     In later versions of this compiler, you will add more things to [Elang.expr]
     but not to [Cfg.expr], hence the distinction.
  *)
  let size_of_type_param = size_of_type typ_struct in
  let rec cfg_expr_of_eexpr (e : Elang.expr) : expr res =
    match e with
    | Elang.Ebinop (b, (e1, t1), (e2, t2)) -> (
        cfg_expr_of_eexpr e1 >>= fun e1 ->
        cfg_expr_of_eexpr e2 >>= fun e2 ->
        match (t1, t2) with
        | Tptr p, _ ->
            OK (Ebinop (b, e1, Ebinop (Emul, e2, Eint (size_of_type_param p))))
        | _, Tptr p ->
            OK (Ebinop (b, Ebinop (Emul, e1, Eint (size_of_type_param p)), e2))
        | Ttab (p, _), _ ->
            OK (Ebinop (b, e1, Ebinop (Emul, e2, Eint (size_of_type_param p))))
        | _, Ttab (p, _) ->
            OK (Ebinop (b, Ebinop (Emul, e1, Eint (size_of_type_param p)), e2))
        | _ -> OK (Ebinop (b, e1, e2)))
    | Elang.Eunop (u, e) -> cfg_expr_of_eexpr e >>= fun e -> OK (Eunop (u, e))
    | Elang.Eaddr (Elang.Evar v) -> (
        let opt = Hashtbl.find_option funvarinmem v in
        match opt with
        | Some addr -> OK (Estk addr)
        | _ -> Error "Variable not in memory")
    | Elang.Eaddr _ -> Error "Not Implemented"
    | Elang.Eload (e, t) ->
        cfg_expr_of_eexpr e >>= fun e -> OK (Eload (e, size_of_type_param t))
    | Elang.Eint i -> OK (Eint i)
    | Elang.Echar c -> OK (Eint (int_of_char c))
    | Elang.Evar v -> (
        let opt = Hashtbl.find_option funvarinmem v in
        let t = Hashtbl.find_option funvartyp v in
        match (opt, t) with
        | Some offset, Some t -> OK (Eload (Estk offset, size_of_type_param t))
        | _ -> OK (Evar v))
    | Elang.Ecall (fname, params) ->
        Utils.list_map_res cfg_expr_of_eexpr params >>= fun params ->
        OK (Ecall (fname, params))
    | Elang.Egetfield (e, f, sname) -> (
        field_offset typ_struct sname f >>= fun offset ->
        field_type typ_struct sname f >>= fun t ->
        cfg_expr_of_eexpr e >>= fun e ->
        match t with
        | Tstruct _ | Ttab _ -> OK (Ebinop (Eadd, e, Eint offset))
        | _ -> OK (Eload (Ebinop (Eadd, e, Eint offset), size_of_type_param t)))
  in
  (* [cfg_node_of_einstr next cfg succ i] builds the CFG node(s) that correspond
     to the E instruction [i].

     [cfg] is the current state of the control-flow graph.

     [succ] is the successor of this node in the CFG, i.e. where to go after this
     instruction.

     [next] is the next available CFG node identifier.

     This function returns a pair (n, next) where [n] is the identifer of the
     node generated, and [next] is the new next available CFG node identifier.

     Hint: several nodes may be generated for a single E instruction.
  *)
  let rec cfg_node_of_einstr (next : int) (cfg : (int, cfg_node) Hashtbl.t)
      (succ : int) (i : instr) : (int * int) res =
    match i with
    | Elang.Iassign (v, e) -> (
        cfg_expr_of_eexpr e >>= fun e ->
        let opt = Hashtbl.find_option funvarinmem v in
        let t = Hashtbl.find_option funvartyp v in
        match (opt, t) with
        | Some addr, Some t ->
            Hashtbl.replace cfg next
              (Cstore (Estk addr, e, size_of_type_param t, succ));
            OK (next, next + 1)
        | _ ->
            Hashtbl.replace cfg next (Cassign (v, e, succ));
            OK (next, next + 1))
    | Elang.Iif (c, ithen, ielse) ->
        cfg_expr_of_eexpr c >>= fun c ->
        cfg_node_of_einstr next cfg succ ithen >>= fun (nthen, next) ->
        cfg_node_of_einstr next cfg succ ielse >>= fun (nelse, next) ->
        Hashtbl.replace cfg next (Ccmp (c, nthen, nelse));
        OK (next, next + 1)
    | Elang.Iwhile (c, i) ->
        cfg_expr_of_eexpr c >>= fun c ->
        let cmp, next = (next, next + 1) in
        cfg_node_of_einstr next cfg cmp i >>= fun (nthen, next) ->
        Hashtbl.replace cfg cmp (Ccmp (c, nthen, succ));
        OK (cmp, next + 1)
    | Elang.Iblock il ->
        List.fold_right
          (fun i acc ->
            acc >>= fun (succ, next) -> cfg_node_of_einstr next cfg succ i)
          il
          (OK (succ, next))
    | Elang.Ireturn e ->
        cfg_expr_of_eexpr e >>= fun e ->
        Hashtbl.replace cfg next (Creturn e);
        OK (next, next + 1)
    | Elang.Iprint e ->
        cfg_expr_of_eexpr e >>= fun e ->
        Hashtbl.replace cfg next (Cprint (e, succ));
        OK (next, next + 1)
    | Elang.Icall (fname, params) ->
        Utils.list_map_res cfg_expr_of_eexpr params >>= fun params ->
        Hashtbl.replace cfg next (Ccall (fname, params, succ));
        OK (next, next + 1)
    | Elang.Istore (addr, v, t) ->
        cfg_expr_of_eexpr addr >>= fun addr ->
        cfg_expr_of_eexpr v >>= fun v ->
        Hashtbl.replace cfg next (Cstore (addr, v, size_of_type_param t, succ));
        OK (next, next + 1)
    | Elang.Isetfield (e, f, v, sname) ->
        field_offset typ_struct sname f >>= fun offset ->
        field_type typ_struct sname f >>= fun t ->
        cfg_expr_of_eexpr e >>= fun e ->
        cfg_expr_of_eexpr v >>= fun v ->
        Hashtbl.replace cfg next
          (Cstore (Ebinop (Eadd, e, Eint offset), v, size_of_type_param t, succ));
        OK (next, next + 1)
  in
  (* Some nodes may be unreachable after the CFG is entirely generated. The
     [reachable_nodes n cfg] constructs the set of node identifiers that are
     reachable from the entry node [n]. *)
  let rec reachable_nodes n (cfg : (int, cfg_node) Hashtbl.t) =
    let rec reachable_aux n reach =
      if Set.mem n reach then reach
      else
        let reach = Set.add n reach in
        match Hashtbl.find_option cfg n with
        | None -> reach
        | Some (Cnop succ)
        | Some (Cprint (_, succ))
        | Some (Cassign (_, _, succ))
        | Some (Cstore (_, _, _, succ))
        | Some (Ccall (_, _, succ)) ->
            reachable_aux succ reach
        | Some (Creturn _) -> reach
        | Some (Ccmp (_, s1, s2)) -> reachable_aux s1 (reachable_aux s2 reach)
    in
    reachable_aux n Set.empty
  in

  (* [cfg_fun_of_efun f] builds the CFG for E function [f]. *)
  let cfg = Hashtbl.create 17 in
  Hashtbl.replace cfg 0 (Creturn (Eint 0));
  cfg_node_of_einstr 1 cfg 0 funbody >>= fun (node, _) ->
  (* remove unreachable nodes *)
  let r = reachable_nodes node cfg in
  Hashtbl.filteri_inplace (fun k _ -> Set.mem k r) cfg;
  OK
    {
      cfgfunargs = List.map fst funargs;
      cfgfunbody = cfg;
      cfgentry = node;
      cfgfunstksz = funstksz;
    }

let cfg_gdef_of_edef typ_struct gd =
  match gd with
  | Gfun f -> cfg_fun_of_efun typ_struct f >>= fun f -> OK (Gfun f)

let cfg_prog_of_eprog ((ep, typ_struct) : eprog) : cfg_fun prog res =
  assoc_map_res (fun fname -> cfg_gdef_of_edef typ_struct) ep

let pass_cfg_gen ep =
  match cfg_prog_of_eprog ep with
  | Error msg ->
      record_compile_result ~error:(Some msg) "CFG";
      Error msg
  | OK cfg ->
      record_compile_result "CFG";
      dump !cfg_dump dump_cfg_prog cfg (call_dot "cfg" "CFG");
      OK cfg
