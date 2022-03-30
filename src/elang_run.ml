open Elang
open Batteries
open BatList
open Prog
open Utils
open Builtins
open Utils
open Int
open Elang_gen

let binop_bool_to_int f x y = if f x y then 1 else 0

(* [eval_binop b x y] évalue l'opération binaire [b] sur les arguments [x]
   et [y]. *)
let eval_binop (b : binop) : int -> int -> int =
  match b with
  | Eadd -> ( + )
  | Emul -> ( * )
  | Emod -> ( mod )
  | Exor -> ( lxor )
  | Esub -> ( - )
  | Ediv -> ( / )
  | Eclt -> binop_bool_to_int ( < )
  | Ecle -> binop_bool_to_int ( <= )
  | Ecgt -> binop_bool_to_int ( > )
  | Ecge -> binop_bool_to_int ( >= )
  | Eceq -> binop_bool_to_int ( = )
  | Ecne -> binop_bool_to_int ( <> )

(* [eval_unop u x] évalue l'opération unaire [u] sur l'argument [x]. *)
let eval_unop (u : unop) : int -> int = match u with Eneg -> Int.neg

let eval_eprog oc ((ep, typ_struct) : eprog) (memsize : int) (params : int list)
    : int option res =
  (* [eval_eexpr st e] évalue l'expression [e] dans l'état [st]. Renvoie une
     erreur si besoin. *)
  let size_of_type_param = size_of_type typ_struct in
  let rec eval_eexpr st funvarinmem (typ_var : (string, typ) Hashtbl.t)
      (typ_fun : (string, typ list * typ) Hashtbl.t) (sp : int)
      (sp_offset : int) (e : expr) : (int * typ) res =
    let eval_eexpr_params =
      eval_eexpr st funvarinmem typ_var typ_fun sp sp_offset
    in
    match e with
    | Ebinop (binop, (a, _), (b, _)) -> (
        eval_eexpr_params a >>= fun (a, t1) ->
        eval_eexpr_params b >>= fun (b, t2) ->
        match (binop, a, b, t1, t2) with
        | Ediv, _, 0, _, _ -> Error "Error division by 0"
        | Emod, _, 0, _, _ -> Error "Error modulos by 0"
        | Eadd, _, _, Tptr p, _ -> OK (a + (b * size_of_type_param p), Tptr p)
        | Eadd, _, _, _, Tptr p -> OK (a + (b * size_of_type_param p), Tptr p)
        | Esub, _, _, Tptr p, _ -> OK (a - (b * size_of_type_param p), Tptr p)
        | _ -> OK (eval_binop binop a b, t1))
    | Eunop (unop, a) ->
        eval_eexpr_params a >>= fun (a, t) -> OK (eval_unop unop a, t)
    | Eaddr (Evar v) ->
        let opt = Hashtbl.find_option funvarinmem v in
        let t = Hashtbl.find_option typ_var v in
        if Option.is_none opt || Option.is_none t then
          Error (Printf.sprintf "\'%s\' undeclared" v)
        else OK (sp + Option.get opt, Tptr (Option.get t))
    | Eaddr _ -> Error "Not implemented"
    | Eload (e, _) -> (
        eval_eexpr_params e >>= fun (i, t) ->
        match t with
        | Tptr p ->
            Mem.read_bytes_as_int st.mem i (size_of_type_param p) >>= fun i ->
            OK (i, p)
        | _ ->
            Printf.sprintf "Invalid type argument of unary \'*\' (have \'%s\')"
              (string_of_typ t)
            |> fun x -> Error x)
    | Egetfield (e, f, _) -> (
        eval_eexpr_params e >>= fun (i, t) ->
        match t with
        | Tptr (Tstruct sname) ->
            field_type typ_struct sname f >>= fun t ->
            field_offset typ_struct sname f >>= fun off ->
            Mem.read_bytes_as_int st.mem (i + off) (size_of_type_param t)
            >>= fun i -> OK (i, t)
        | _ ->
            Error
              (Printf.sprintf
                 "Request for member \'%s\' in something not a structure or \
                  union"
                 f))
    | Eint i -> OK (i, Tint)
    | Echar c -> OK (int_of_char c, Tchar)
    | Evar s -> (
        let opt = Hashtbl.find_option funvarinmem s in
        let t = Hashtbl.find_option typ_var s in
        match (opt, t) with
        | Some offset, Some t ->
            Mem.read_bytes_as_int st.mem (sp + offset) (size_of_type_param t)
            >>= fun i -> OK (i, t)
        | _ ->
            let v = Hashtbl.find_option st.env s in
            if Option.is_none v || Option.is_none t then
              Error (Printf.sprintf "\'%s\' undeclared" s)
            else OK (Option.get v, Option.get t))
    | Ecall (fname, params) when is_builtin fname ->
        Utils.list_map_res eval_eexpr_params params >>= fun params ->
        let params = List.map fst params in
        do_builtin oc st.mem fname params >>= fun res ->
        (let opt = Hashtbl.find_option typ_fun fname in
         match opt with Some (_, t) -> OK t | None -> Error "No type")
        >>= fun t ->
        if Option.is_some res then OK (Option.get res, t) else Error "No output"
    | Ecall (fname, params) -> (
        Utils.list_map_res eval_eexpr_params params >>= fun params ->
        let params = List.map fst params in
        find_function ep fname >>= fun f ->
        (let opt = Hashtbl.find_option typ_fun fname in
         match opt with Some (_, t) -> OK t | None -> Error "No type")
        >>= fun t ->
        eval_efun oc st sp_offset typ_fun f fname params >>= fun (v, st) ->
        match v with None -> Error "No output" | Some ret -> OK (ret, t))
  (* [eval_einstr oc st ins] évalue l'instrution [ins] en partant de l'état [st].

     Le paramètre [oc] est un "output channel", dans lequel la fonction "print"
     écrit sa sortie, au moyen de l'instruction [Format.fprintf].

     Cette fonction renvoie [(ret, st')] :

     - [ret] est de type [int option]. [Some v] doit être renvoyé lorsqu'une
     instruction [return] est évaluée. [None] signifie qu'aucun [return] n'a eu
     lieu et que l'exécution doit continuer.

     - [st'] est l'état mis à jour. *)
  and eval_einstr oc (st : int state) funvarinmem fname
      (typ_var : (string, typ) Hashtbl.t)
      (typ_fun : (string, typ list * typ) Hashtbl.t) (sp : int)
      (sp_offset : int) (ins : instr) : (int option * int state) res =
    let eval_einstr_params =
      eval_einstr oc st funvarinmem fname typ_var typ_fun sp sp_offset
    in
    let eval_eexpr_params =
      eval_eexpr st funvarinmem typ_var typ_fun sp sp_offset
    in
    match ins with
    | Istore (addr, v, _) ->
        eval_eexpr_params addr >>= fun (addr, t) ->
        (match t with
        | Tptr p -> OK p
        | _ ->
            Printf.sprintf "Invalid type argument of unary \'*\' (have \'%s\')"
              (string_of_typ t)
            |> fun x -> Error x)
        >>= fun p ->
        eval_eexpr_params v >>= fun (v, _) ->
        let v = split_bytes (size_of_type_param p) v in
        Mem.write_bytes st.mem addr v >>= fun () -> OK (None, st)
    | Iassign (s, e) -> (
        eval_eexpr_params e >>= fun (e, _) ->
        let opt = Hashtbl.find_option funvarinmem s in
        let t = Hashtbl.find_option typ_var s in
        match (opt, t) with
        | Some offset, Some t ->
            Mem.write_bytes st.mem (sp + offset)
              (split_bytes (size_of_type_param t) e)
            >>= fun () -> OK (None, st)
        | _ ->
            Hashtbl.replace st.env s e;
            OK (None, st))
    | Iif (e, i1, i2) ->
        eval_eexpr_params e >>= fun (e, _) ->
        if e <> 0 then eval_einstr_params i1 else eval_einstr_params i2
    | Iwhile (e, i) ->
        eval_eexpr_params e >>= fun (e, _) ->
        if e <> 0 then
          eval_einstr_params i >>= fun (ret, s) ->
          if Option.is_none ret then eval_einstr_params ins else OK (ret, s)
        else OK (None, st)
    | Ireturn e -> eval_eexpr_params e >>= fun (e, _) -> OK (Some e, st)
    | Iprint e ->
        eval_eexpr_params e >>= fun (e, _) ->
        Format.fprintf oc "%d\n" e;
        OK (None, st)
    | Iblock [] -> OK (None, st)
    | Isetfield (e, f, v, _) -> (
        eval_eexpr_params e >>= fun (i, t) ->
        eval_eexpr_params v >>= fun (e, _) ->
        match t with
        | Tptr (Tstruct sname) ->
            field_type typ_struct sname f >>= fun t ->
            field_offset typ_struct sname f >>= fun offset ->
            Mem.write_bytes st.mem
              (sp + i + offset)
              (split_bytes (size_of_type_param t) e)
            >>= fun () -> OK (None, st)
        | _ ->
            Error
              (Printf.sprintf
                 "Request for member \'%s\' in something not a structure or \
                  union"
                 f))
    | Iblock (h :: t) ->
        eval_einstr_params h >>= fun (ret, s) ->
        if Option.is_none ret then eval_einstr_params (Iblock t) else OK (ret, s)
    | Icall (fname, params) when is_builtin fname ->
        Utils.list_map_res eval_eexpr_params params >>= fun params ->
        let params = List.map fst params in
        do_builtin oc st.mem fname params >>= fun res -> OK (None, st)
    | Icall (fname, params) ->
        Utils.list_map_res eval_eexpr_params params >>= fun params ->
        let params = List.map fst params in
        find_function ep fname >>= fun f ->
        eval_efun oc st sp_offset typ_fun f fname params >>= fun (_, st) ->
        OK (None, st)
  (* [eval_efun oc st f fname vargs] évalue la fonction [f] (dont le nom est
     [fname]) en partant de l'état [st], avec les arguments [vargs].

     Cette fonction renvoie un couple (ret, st') avec la même signification que
     pour [eval_einstr]. *)
  and eval_efun oc (st : int state) (sp : int)
      (typ_fun : (string, typ list * typ) Hashtbl.t)
      ({
         funargs;
         funrettype;
         funbody;
         funvarinmem : (string, int) Batteries.Hashtbl.t;
         funstksz : int;
         funvartyp;
       } :
        efun) (fname : string) (vargs : int list) : (int option * int state) res
      =
    (* L'environnement d'une fonction (mapping des variables locales vers leurs
       valeurs) est local et un appel de fonction ne devrait pas modifier les
       variables de l'appelant. Donc, on sauvegarde l'environnement de l'appelant
       dans [env_save], on appelle la fonction dans un environnement propre (Avec
       seulement ses arguments), puis on restore l'environnement de l'appelant. *)
    let env_save = Hashtbl.copy st.env in
    let env = Hashtbl.create 17 in
    match
      List.iter2
        (fun a v -> Hashtbl.replace env a v)
        (List.map fst funargs) vargs
    with
    | () -> (
        match
          eval_einstr oc { st with env } funvarinmem fname funvartyp typ_fun sp
            (sp + funstksz) funbody
        with
        | OK (v, st') -> OK (v, { st' with env = env_save })
        | Error e ->
            Error (Printf.sprintf "Error in execution of \'%s\'\n%s" fname e))
    | exception Invalid_argument _ ->
        Error
          (Format.sprintf
             "E: Called function %s with %d arguments, expected %d.\n" fname
             (List.length vargs) (List.length funargs))
  in
  (* [eval_eprog oc ep memsize params] évalue un programme complet [ep], avec les
     arguments [params].

     Le paramètre [memsize] donne la taille de la mémoire dont ce programme va
     disposer. Ce n'est pas utile tout de suite (nos programmes n'utilisent pas de
     mémoire), mais ça le sera lorsqu'on ajoutera de l'allocation dynamique dans
     nos programmes.

     Renvoie:

     - [OK (Some v)] lorsque l'évaluation de la fonction a lieu sans problèmes et renvoie une valeur [v].

     - [OK None] lorsque l'évaluation de la fonction termine sans renvoyer de valeur.

     - [Error msg] lorsqu'une erreur survient.
  *)
  let st = init_state memsize in
  let typ_fun = Hashtbl.create (List.length ep + 3) in
  Hashtbl.replace typ_fun "print" ([ Tint ], Tvoid);
  Hashtbl.replace typ_fun "print_int" ([ Tint ], Tvoid);
  Hashtbl.replace typ_fun "print_char" ([ Tchar ], Tvoid);

  List.iter
    (fun (fname, _) ->
      let res = find_function ep fname in
      match res with
      | OK { funargs; funrettype } ->
          Hashtbl.replace typ_fun fname (List.map snd funargs, funrettype)
      | _ -> ())
    ep;
  find_function ep "main" >>= fun f ->
  (* ne garde que le nombre nécessaire de paramètres pour la fonction "main". *)
  let n = List.length f.funargs in
  let params = take n params in
  let _ =
    List.map
      (uncurry (Hashtbl.replace st.env))
      (combine (List.map fst f.funargs) params)
  in
  eval_efun oc st 0 typ_fun f "main" params >>= fun (v, st) -> OK v

(* (match Hashtbl.find_option typ_fun fname with
   | None ->
       Hashtbl.replace typ_fun fname (List.map snd funargs, funrettype);
       OK ()
   | Some (argt, et)
     when typCompat et funrettype
          && typ_compat_list (List.map snd funargs) argt ->
       OK ()
   | _ ->
       fname
       |> Printf.sprintf "Function \'%s\' does not match previous definition"
       |> fun x -> Error x)
   >>= fun () -> *)
