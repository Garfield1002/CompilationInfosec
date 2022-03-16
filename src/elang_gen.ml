open Ast
open Elang
open Prog
open Report
open Options
open Batteries
open Elang_print
open Utils

let tag_is_binop = function
  | Tadd -> true
  | Tsub -> true
  | Tmul -> true
  | Tdiv -> true
  | Tmod -> true
  | Txor -> true
  | Tcle -> true
  | Tclt -> true
  | Tcge -> true
  | Tcgt -> true
  | Tceq -> true
  | Tcne -> true
  | _ -> false

let binop_of_tag = function
  | Tadd -> Eadd
  | Tsub -> Esub
  | Tmul -> Emul
  | Tdiv -> Ediv
  | Tmod -> Emod
  | Txor -> Exor
  | Tcle -> Ecle
  | Tclt -> Eclt
  | Tcge -> Ecge
  | Tcgt -> Ecgt
  | Tceq -> Eceq
  | Tcne -> Ecne
  | _ -> assert false

let rec type_expr (typ_var : (string, typ) Hashtbl.t)
    (typ_fun : (string, typ list * typ) Hashtbl.t) (e : expr) : typ res =
  match e with
  | Ebinop (_, e1, e2) ->
      type_expr typ_var typ_fun e1 >>= fun t1 ->
      type_expr typ_var typ_fun e2 >>= fun t2 ->
      if typCompat t1 t2 then OK t1
      else
        Error
          (Printf.sprintf "Incompatible types [%s] and [%s]" (string_of_typ t1)
             (string_of_typ t2))
  | Eunop (_, e) -> type_expr typ_var typ_fun e
  | Eint _ -> OK Tint
  | Echar _ -> OK Tchar
  | Evar v -> (
      match Hashtbl.find_option typ_var v with
      | None ->
          v |> Printf.sprintf "Variable \'%s\' is undeclared" |> fun x ->
          Error x
      | Some t -> OK t)
  | Ecall (fname, params) -> (
      match Hashtbl.find_option typ_fun fname with
      | None ->
          fname |> Printf.sprintf "Function \'%s\' is undeclared" |> fun x ->
          Error x
      | Some (expectedParamsT, t) ->
          Utils.list_map_res (type_expr typ_var typ_fun) params
          >>= fun paramsT ->
          if
            List.fold_left2
              (fun acc t et -> acc && typCompat t et)
              true paramsT expectedParamsT
          then OK t
          else
            fname |> Printf.sprintf "Called \'%s\' with arguments of wrong type"
            |> fun x -> Error x)

(* [make_eexpr_of_ast a] builds an expression corresponding to a tree [a]. If
   the tree is not well-formed, fails with an [Error] message. *)
let rec make_eexpr_of_ast (typ_var : (string, typ) Hashtbl.t)
    (typ_fun : (string, typ list * typ) Hashtbl.t) (a : tree) : (expr * typ) res
    =
  let res =
    match a with
    | Node (t, [ e1; e2 ]) when tag_is_binop t ->
        make_eexpr_of_ast typ_var typ_fun e1 >>= fun (a1, t1) ->
        make_eexpr_of_ast typ_var typ_fun e2 >>= fun (a2, t2) ->
        if typCompat t1 t2 then OK (Ebinop (binop_of_tag t, a1, a2), t1)
        else
          Error
            (Printf.sprintf "Incompatible types [%s] and [%s]"
               (string_of_typ t1) (string_of_typ t2))
    | Node (Tneg, [ e ]) ->
        make_eexpr_of_ast typ_var typ_fun e >>= fun (a, t) ->
        OK (Eunop (Eneg, a), t)
    | Node (Tint, [ IntLeaf i ]) -> OK (Eint i, Tint)
    | Node (Tchar, [ CharLeaf c ]) -> OK (Echar c, Tchar)
    | StringLeaf v -> (
        match Hashtbl.find_option typ_var v with
        | None ->
            v |> Printf.sprintf "Variable \'%s\' is undeclared" |> fun x ->
            Error x
        | Some t -> OK (Evar v, t))
    | Node (Tcall, [ StringLeaf fname; Node (Targs, params) ]) -> (
        match Hashtbl.find_option typ_fun fname with
        | None ->
            fname |> Printf.sprintf "Function \'%s\' is undeclared" |> fun x ->
            Error x
        | Some (expectedParamsT, t) ->
            Utils.list_map_res (make_eexpr_of_ast typ_var typ_fun) params
            >>= fun paramsT ->
            if typ_compat_list (List.map snd paramsT) expectedParamsT then
              OK (Ecall (fname, List.map fst paramsT), t)
            else (
              Printf.printf "Expected types \n";
              print_typ_list expectedParamsT;
              Printf.printf "\n\nGot types \n";
              print_typ_list (List.map snd paramsT);
              fname
              |> Printf.sprintf "Called \'%s\' with arguments of wrong type"
              |> fun x -> Error x))
    | _ ->
        Error
          (Printf.sprintf "Unacceptable ast in make_eexpr_of_ast %s"
             (string_of_ast a))
  in
  match res with
  | OK o -> res
  | Error msg ->
      Error
        (Format.sprintf "In make_eexpr_of_ast %s:\n%s" (string_of_ast a) msg)

let rec make_einstr_of_ast (typ_var : (string, typ) Hashtbl.t)
    (typ_fun : (string, typ list * typ) Hashtbl.t) (a : tree) : instr res =
  let res =
    match a with
    | Node (Tdeclare, [ TypeLeaf t; StringLeaf v ]) -> (
        match Hashtbl.find_option typ_var v with
        | None ->
            Hashtbl.replace typ_var v t;
            OK (Iblock [])
        | Some et ->
            v |> Printf.sprintf "Variable \'%s\' is already defined" |> fun x ->
            Error x)
    | Node (Tdeclare, [ TypeLeaf et; StringLeaf v; e ]) -> (
        match Hashtbl.find_option typ_var v with
        | None ->
            Hashtbl.replace typ_var v et;
            make_eexpr_of_ast typ_var typ_fun e >>= fun (a, t) ->
            if typCompat et t then OK (Iassign (v, a))
            else
              Printf.sprintf "Expected type [%s], got type [%s]"
                (string_of_typ et) (string_of_typ t)
              |> fun x -> Error x
        | Some et ->
            v |> Printf.sprintf "Variable \'%s\' is already defined" |> fun x ->
            Error x)
    | Node (Tassign, [ StringLeaf v; e ]) -> (
        match Hashtbl.find_option typ_var v with
        | None ->
            v |> Printf.sprintf "Variable \'%s\' is undeclared" |> fun x ->
            Error x
        | Some et ->
            make_eexpr_of_ast typ_var typ_fun e >>= fun (a, t) ->
            if typCompat et t then OK (Iassign (v, a))
            else
              Printf.sprintf "Expected type [%s], got type [%s]"
                (string_of_typ et) (string_of_typ t)
              |> fun x -> Error x)
    | Node (Tif, [ e; i; NullLeaf ]) ->
        (* if without an else *)
        make_eexpr_of_ast typ_var typ_fun e >>= fun (a, t) ->
        if typCompat t Tint then
          make_einstr_of_ast typ_var typ_fun i >>= fun j ->
          OK (Iif (a, j, Iblock []))
        else
          Printf.sprintf "Expected type [int], got type [%s]" (string_of_typ t)
          |> fun x -> Error x
    | Node (Tif, [ e; i1; i2 ]) ->
        make_eexpr_of_ast typ_var typ_fun e >>= fun (a, t) ->
        if typCompat t Tint then
          make_einstr_of_ast typ_var typ_fun i1 >>= fun j1 ->
          make_einstr_of_ast typ_var typ_fun i2 >>= fun j2 ->
          OK (Iif (a, j1, j2))
        else
          Printf.sprintf "Expected type [int], got type [%s]" (string_of_typ t)
          |> fun x -> Error x
    | Node (Twhile, [ e; i ]) ->
        make_eexpr_of_ast typ_var typ_fun e >>= fun (a, t) ->
        if typCompat t Tint then
          make_einstr_of_ast typ_var typ_fun i >>= fun j -> OK (Iwhile (a, j))
        else
          Printf.sprintf "Expected type [int], got type [%s]" (string_of_typ t)
          |> fun x -> Error x
    | Node (Treturn, [ e ]) ->
        make_eexpr_of_ast typ_var typ_fun e >>= fun (a, t) -> OK (Ireturn a)
    | Node (Tprint, [ e ]) ->
        make_eexpr_of_ast typ_var typ_fun e >>= fun (a, _) -> OK (Iprint a)
    | Node (Tblock, instrs) ->
        Utils.list_map_res (make_einstr_of_ast typ_var typ_fun) instrs
        >>= fun instrs -> OK (Iblock instrs)
    | Node (Tcall, [ StringLeaf fname; Node (Targs, params) ]) -> (
        match Hashtbl.find_option typ_fun fname with
        | None ->
            fname |> Printf.sprintf "Function \'%s\' is undeclared" |> fun x ->
            Error x
        | Some (expectedParamsT, t) ->
            Utils.list_map_res (make_eexpr_of_ast typ_var typ_fun) params
            >>= fun paramsT ->
            if
              List.fold_left2
                (fun acc (_, t) et -> acc && typCompat t et)
                true paramsT expectedParamsT
            then OK (Icall (fname, List.map fst paramsT))
            else
              fname
              |> Printf.sprintf "Called \'%s\' with arguments of wrong type"
              |> fun x -> Error x)
    | _ ->
        Error
          (Printf.sprintf "Unacceptable ast in make_einstr_of_ast %s"
             (string_of_ast a))
  in
  match res with
  | OK o -> res
  | Error msg ->
      Error
        (Format.sprintf "In make_einstr_of_ast %s:\n%s" (string_of_ast a) msg)

let make_ident (a : tree) : (string * typ) res =
  match a with
  | Node (Targ, [ TypeLeaf t; StringLeaf s ]) -> OK (s, t)
  | a ->
      Error (Printf.sprintf "make_ident: unexpected AST: %s" (string_of_ast a))

let make_fundef_of_ast (typ_fun : (string, typ list * typ) Hashtbl.t) (a : tree)
    : (string * efun) option res =
  match a with
  | Node
      ( Tfundef,
        [
          TypeLeaf t;
          Node (Tfunname, [ StringLeaf fname ]);
          Node (Tfunargs, fargs);
        ] ) ->
      list_map_res make_ident fargs >>= fun fargs ->
      (match Hashtbl.find_option typ_fun fname with
      | None ->
          Hashtbl.replace typ_fun fname (List.map snd fargs, t);
          OK ()
      | Some (argt, et)
        when typCompat et t && typ_compat_list (List.map snd fargs) argt ->
          OK ()
      | _ ->
          fname
          |> Printf.sprintf "Function \'%s\' does not match previous definition"
          |> fun x -> Error x)
      >>= fun () -> OK None
  | Node
      ( Tfundef,
        [
          TypeLeaf t;
          Node (Tfunname, [ StringLeaf fname ]);
          Node (Tfunargs, fargs);
          Node (Tfunbody, [ fbody ]);
        ] ) ->
      list_map_res make_ident fargs >>= fun fargs ->
      (match Hashtbl.find_option typ_fun fname with
      | None ->
          Hashtbl.replace typ_fun fname (List.map snd fargs, t);
          OK ()
      | Some (argt, et)
        when typCompat et t && typ_compat_list (List.map snd fargs) argt ->
          OK ()
      | _ ->
          fname
          |> Printf.sprintf "Function \'%s\' does not match previous definition"
          |> fun x -> Error x)
      >>= fun () ->
      let typ_var = Hashtbl.of_list fargs in
      make_einstr_of_ast typ_var typ_fun fbody >>= fun fbody ->
      OK
        (Some
           ( fname,
             {
               funargs = fargs;
               funbody = fbody;
               funvartyp = typ_var;
               funrettype = t;
             } ))
  | _ ->
      Error
        (Printf.sprintf "make_fundef_of_ast: Expected a Tfundef, got %s."
           (string_of_ast a))

let make_eprog_of_ast (a : tree) : eprog res =
  match a with
  | Node (Tlistglobdef, l) ->
      let typ_fun = Hashtbl.create (List.length l) in
      Hashtbl.replace typ_fun "print" ([ Tint ], Tvoid);
      Hashtbl.replace typ_fun "print_int" ([ Tint ], Tvoid);
      Hashtbl.replace typ_fun "print_char" ([ Tchar ], Tvoid);
      list_map_res
        (fun a ->
          make_fundef_of_ast typ_fun a >>= fun res ->
          match res with
          | Some (fname, efun) -> OK (Some (fname, Gfun efun))
          | None -> OK None)
        l
      >>= fun l -> OK (List.filter_map identity l)
  | _ ->
      Error
        (Printf.sprintf "make_fundef_of_ast: Expected a Tlistglobdef, got %s."
           (string_of_ast a))

let pass_elang ast =
  match make_eprog_of_ast ast with
  | Error msg ->
      record_compile_result ~error:(Some msg) "Elang";
      Error msg
  | OK ep ->
      dump !e_dump dump_e ep (fun file () ->
          add_to_report "e" "E" (Code (file_contents file)));
      OK ep
