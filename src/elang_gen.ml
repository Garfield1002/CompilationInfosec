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

let string_of_binary = function
  | Tadd -> "+"
  | Tsub -> "-"
  | Tmul -> "*"
  | Tdiv -> "/"
  | Tmod -> "%"
  | Txor -> "^"
  | Tcle -> "<="
  | Tclt -> "<"
  | Tcge -> ">="
  | Tcgt -> ">"
  | Tceq -> "=="
  | Tcne -> "!="
  | _ -> ""

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

let type_of_leaf typ_struct leaf =
  match leaf with
  | TypeLeaf (Tstruct sname) ->
      if Option.is_some (Hashtbl.find_option typ_struct sname) then
        OK (Tstruct sname)
      else Error "Incomplete type"
  | TypeLeaf t -> OK t
  | _ ->
      Error
        (Printf.sprintf "type_of_leaf: unexpected AST: %s" (string_of_ast leaf))

let rec typCompatBinop b t1 t2 =
  match (t1, t2) with
  | _, _ when t1 = t2 -> true
  | Tptr t1', Tptr t2' -> typCompat t1' t2'
  | Tptr _, _ | _, Tptr _ -> false
  | Tvoid, _ | _, Tvoid -> false
  | _ -> true

(* let rec type_expr (typ_var : (string, typ) Hashtbl.t)
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
             |> fun x -> Error x) *)

(* [make_eexpr_of_ast a] builds an expression corresponding to a tree [a]. If
   the tree is not well-formed, fails with an [Error] message. *)
let rec make_eexpr_of_ast (typ_var : (string, typ) Hashtbl.t)
    (typ_fun : (string, typ list * typ) Hashtbl.t)
    (typ_struct : (string, (string * typ) list) Hashtbl.t)
    (funvarinmem : (string, int) Hashtbl.t) (funstksz : int ref) (a : tree) :
    (expr * typ) res =
  let make_eexpr_of_ast_params =
    make_eexpr_of_ast typ_var typ_fun typ_struct funvarinmem funstksz
  in
  let res =
    match a with
    | Node (t, [ e1; e2 ]) when tag_is_binop t -> (
        make_eexpr_of_ast_params e1 >>= fun (a1, t1) ->
        make_eexpr_of_ast_params e2 >>= fun (a2, t2) ->
        match (t, t1, t2) with
        | Tadd, Tptr p, _ when isArithmetic t2 ->
            OK (Ebinop (Eadd, (a1, t1), (a2, t2)), Tptr p)
        | Tadd, _, Tptr p when isArithmetic t1 ->
            OK (Ebinop (Eadd, (a1, t1), (a2, t2)), Tptr p)
        | Tsub, Tptr p, _ when isArithmetic t2 ->
            OK (Ebinop (Esub, (a1, t1), (a2, t2)), Tptr p)
        | _, _, _ when isArithmetic t1 && isArithmetic t2 ->
            OK (Ebinop (binop_of_tag t, (a1, t1), (a2, t2)), t1)
        | _, _, _ ->
            Error
              (Printf.sprintf
                 "Invalid operands to binary %s (have \'%s\' and \'%s\')"
                 (string_of_binary t) (string_of_typ t1) (string_of_typ t2)))
    | Node (Tneg, [ e ]) ->
        make_eexpr_of_ast_params e >>= fun (a, t) ->
        if isArithmetic t then OK (Eunop (Eneg, a), t)
        else
          Error
            (Printf.sprintf "Wrong type argument to unary minus (have \'%s\')"
               (string_of_typ t))
    | Node (Taddrof, [ Node (Tindirection, [ e ]) ]) ->
        (* special case: & and * cancel each other, neither one is evaluated (since C99) https://en.cppreference.com/w/c/language/operator_member_access#Address_of *)
        make_eexpr_of_ast_params e
    | Node (Tindirection, [ e ]) -> (
        make_eexpr_of_ast_params e >>= fun (e, t) ->
        match t with
        | Tptr t' -> OK (Eload (e, t'), t')
        | _ ->
            Error
              (Printf.sprintf
                 "Invalid type argument of unary \'*\' (have \'%s\')"
                 (string_of_typ t)))
    | Node (Taddrof, [ e ]) ->
        make_eexpr_of_ast_params e >>= fun (e, t) ->
        (match e with
        | Evar v -> (
            match Hashtbl.find_option funvarinmem v with
            | Some _ -> ()
            | None ->
                Hashtbl.add funvarinmem v !funstksz;
                funstksz := !funstksz + size_of_type typ_struct t)
        | _ -> ());
        OK (Eaddr e, Tptr t)
    | Node (Tstruct, [ e; StringLeaf f ]) ->
        make_eexpr_of_ast_params e >>= fun (e, t) ->
        (match t with Tstruct sname -> OK sname | _ -> Error "Incorrect type")
        >>= fun sname ->
        field_type typ_struct sname f >>= fun t ->
        OK (Egetfield (Eaddr e, f, sname), t)
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
            Utils.list_map_res make_eexpr_of_ast_params params
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
    (typ_fun : (string, typ list * typ) Hashtbl.t)
    (typ_struct : (string, (string * typ) list) Hashtbl.t) (funrettype : typ)
    (funvarinmem : (string, int) Hashtbl.t) (funstksz : int ref) (a : tree) :
    instr res =
  let make_einstr_of_ast_params =
    make_einstr_of_ast typ_var typ_fun typ_struct funrettype funvarinmem
      funstksz
  in
  let make_eexpr_of_ast_params =
    make_eexpr_of_ast typ_var typ_fun typ_struct funvarinmem funstksz
  in
  let res =
    match a with
    | Node (Tdeclare, [ typeLeaf; StringLeaf v ]) -> (
        type_of_leaf typ_struct typeLeaf >>= fun t ->
        (match t with
        | Tvoid ->
            Error (Printf.sprintf "Variable or field \'%s\' declared void" v)
        | Tstruct _ ->
            Hashtbl.add funvarinmem v !funstksz;
            funstksz := !funstksz + size_of_type typ_struct t;
            OK ()
        | _ -> OK ())
        >>= fun () ->
        match Hashtbl.find_option typ_var v with
        | None ->
            Hashtbl.replace typ_var v t;
            OK (Iblock [])
        | Some et ->
            v |> Printf.sprintf "Redefinition of \'%s\'" |> fun x -> Error x)
    | Node (Tdeclare, [ typeLeaf; StringLeaf v; e ]) -> (
        type_of_leaf typ_struct typeLeaf >>= fun et ->
        (match et with
        | Tvoid ->
            Error (Printf.sprintf "Variable or field \'%s\' declared void" v)
        | Tstruct _ ->
            Hashtbl.add funvarinmem v !funstksz;
            funstksz := !funstksz + size_of_type typ_struct et;
            OK ()
        | _ -> OK ())
        >>= fun () ->
        match Hashtbl.find_option typ_var v with
        | None ->
            Hashtbl.replace typ_var v et;
            make_eexpr_of_ast_params e >>= fun (a, t) ->
            if typCompat et t then OK (Iassign (v, a))
            else
              Printf.sprintf "Expected type [%s], got type [%s]"
                (string_of_typ et) (string_of_typ t)
              |> fun x -> Error x
        | Some et ->
            v |> Printf.sprintf "Redefinition of \'%s\'" |> fun x -> Error x)
    | Node (Tassign, [ Node (Tindirection, [ e1 ]); e2 ]) ->
        make_eexpr_of_ast_params e1 >>= fun (e1, t) ->
        (match t with
        | Tptr _ -> OK ()
        | _ ->
            Printf.sprintf "Invalid type argument of unary \'*\' (have \'%s\')"
              (string_of_typ t)
            |> fun x -> Error x)
        >>= fun () ->
        make_eexpr_of_ast_params e2 >>= fun (e2, t) -> OK (Istore (e1, e2, t))
    | Node (Tassign, [ StringLeaf v; e ]) -> (
        match Hashtbl.find_option typ_var v with
        | None ->
            v |> Printf.sprintf "Variable \'%s\' is undeclared" |> fun x ->
            Error x
        | Some et ->
            make_eexpr_of_ast_params e >>= fun (a, t) ->
            if typCompat et t then OK (Iassign (v, a))
            else
              Printf.sprintf "Expected type [%s], got type [%s]"
                (string_of_typ et) (string_of_typ t)
              |> fun x -> Error x)
    | Node (Tassign, [ Node (Tstruct, [ s; StringLeaf f ]); e ]) ->
        make_eexpr_of_ast_params s >>= fun (s, t) ->
        (match t with
        | Tstruct sname -> OK sname
        | _ ->
            Error
              (Printf.sprintf
                 "Request for member \'%s\' in something not a structure or \
                  union"
                 f))
        >>= fun sname ->
        field_type typ_struct sname f >>= fun et ->
        make_eexpr_of_ast_params e >>= fun (e, t) ->
        if typCompat t et then OK (Isetfield (Eaddr s, f, e, sname))
        else
          Error
            (Printf.sprintf
               "Incompatible types when assigning to type \'%s\' from type \
                \'%s\'"
               (string_of_typ et) (string_of_typ t))
    | Node (Tif, [ e; i; NullLeaf ]) ->
        (* if without an else *)
        make_eexpr_of_ast_params e >>= fun (a, t) ->
        if typCompat t Tint then
          make_einstr_of_ast_params i >>= fun j -> OK (Iif (a, j, Iblock []))
        else
          Printf.sprintf "Expected type [int], got type [%s]" (string_of_typ t)
          |> fun x -> Error x
    | Node (Tif, [ e; i1; i2 ]) ->
        make_eexpr_of_ast_params e >>= fun (a, t) ->
        if typCompat t Tint then
          make_einstr_of_ast_params i1 >>= fun j1 ->
          make_einstr_of_ast_params i2 >>= fun j2 -> OK (Iif (a, j1, j2))
        else
          Printf.sprintf "Expected type [int], got type [%s]" (string_of_typ t)
          |> fun x -> Error x
    | Node (Twhile, [ e; i ]) ->
        make_eexpr_of_ast_params e >>= fun (a, t) ->
        if typCompat t Tint then
          make_einstr_of_ast_params i >>= fun j -> OK (Iwhile (a, j))
        else
          Printf.sprintf "Expected type [int], got type [%s]" (string_of_typ t)
          |> fun x -> Error x
    | Node (Treturn, [ e ]) ->
        make_eexpr_of_ast_params e >>= fun (a, t) ->
        if typCompat t funrettype then OK (Ireturn a)
        else
          Printf.sprintf
            "incompatible types when returning type \'%s\' but \'%s\' was \
             expected"
            (string_of_typ t) (string_of_typ funrettype)
          |> fun x -> Error x
    | Node (Tprint, [ e ]) ->
        make_eexpr_of_ast_params e >>= fun (a, _) -> OK (Iprint a)
    | Node (Tblock, instrs) ->
        Utils.list_map_res make_einstr_of_ast_params instrs >>= fun instrs ->
        OK (Iblock instrs)
    | Node (Tcall, [ StringLeaf fname; Node (Targs, params) ]) -> (
        match Hashtbl.find_option typ_fun fname with
        | None ->
            fname |> Printf.sprintf "Function \'%s\' is undeclared" |> fun x ->
            Error x
        | Some (expectedParamsT, t) ->
            Utils.list_map_res make_eexpr_of_ast_params params
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

let make_ident typ_struct (a : tree) : (string * typ) res =
  match a with
  | Node (Targ, [ typeLeaf; StringLeaf s ]) ->
      type_of_leaf typ_struct typeLeaf >>= fun t -> OK (s, t)
  | a ->
      Error (Printf.sprintf "make_ident: unexpected AST: %s" (string_of_ast a))

let make_fundef_of_ast (typ_fun : (string, typ list * typ) Hashtbl.t)
    (typ_struct : (string, (string * typ) list) Hashtbl.t) (a : tree) :
    (string * efun) option res =
  match a with
  | Node (Tstructdef, [ TypeLeaf (Tstruct sname); Node (Tstructbody, []) ]) -> (
      let opt = Hashtbl.find_option typ_struct sname in
      match opt with
      | None | Some [] ->
          Hashtbl.replace typ_struct sname [];
          OK None
      | _ -> OK None)
  | Node (Tstructdef, [ TypeLeaf (Tstruct sname); Node (Tstructbody, l) ]) -> (
      let opt = Hashtbl.find_option typ_struct sname in
      match opt with
      | None | Some [] ->
          Utils.list_map_res
            (fun n ->
              match n with
              | Node (Tdeclare, [ typeLeaf; StringLeaf s ]) ->
                  type_of_leaf typ_struct typeLeaf >>= fun t -> OK (s, t)
              | _ ->
                  Error
                    (Printf.sprintf "make_fundef_of_ast: unexpected AST: %s"
                       (string_of_ast n)))
            l
          >>= fun l ->
          Hashtbl.replace typ_struct sname l;
          OK None
      | _ -> Error (Printf.sprintf "Redefinition of \'struct %s\'" sname))
  | Node
      ( Tfundef,
        [
          typeLeaf; Node (Tfunname, [ StringLeaf fname ]); Node (Tfunargs, fargs);
        ] ) ->
      type_of_leaf typ_struct typeLeaf >>= fun t ->
      list_map_res (make_ident typ_struct) fargs >>= fun fargs ->
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
          typeLeaf;
          Node (Tfunname, [ StringLeaf fname ]);
          Node (Tfunargs, fargs);
          Node (Tfunbody, [ fbody ]);
        ] ) ->
      type_of_leaf typ_struct typeLeaf >>= fun t ->
      list_map_res (make_ident typ_struct) fargs >>= fun fargs ->
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
      let funstksz = ref 0 in
      let funvarinmem = Hashtbl.create 1 in
      List.iter
        (fun (v, t) ->
          match t with
          | Tstruct sname ->
              Hashtbl.add funvarinmem v !funstksz;
              funstksz := !funstksz + size_of_type typ_struct t
          | _ -> ())
        fargs;
      make_einstr_of_ast typ_var typ_fun typ_struct t funvarinmem funstksz fbody
      >>= fun fbody ->
      OK
        (Some
           ( fname,
             {
               funargs = fargs;
               funbody = fbody;
               funvartyp = typ_var;
               funrettype = t;
               funvarinmem;
               funstksz = !funstksz;
             } ))
  | _ ->
      Error
        (Printf.sprintf "make_fundef_of_ast: Expected a Tfundef, got %s."
           (string_of_ast a))

let make_eprog_of_ast (a : tree) : eprog res =
  match a with
  | Node (Tlistglobdef, l) ->
      let typ_fun = Hashtbl.create (List.length l) in
      let typ_struct = Hashtbl.create (List.length l) in
      Hashtbl.replace typ_fun "print" ([ Tint ], Tvoid);
      Hashtbl.replace typ_fun "print_int" ([ Tint ], Tvoid);
      Hashtbl.replace typ_fun "print_char" ([ Tchar ], Tvoid);
      list_map_res
        (fun a ->
          make_fundef_of_ast typ_fun typ_struct a >>= fun res ->
          match res with
          | Some (fname, efun) -> OK (Some (fname, Gfun efun))
          | None -> OK None)
        l
      >>= fun l -> OK (List.filter_map identity l, typ_struct)
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
