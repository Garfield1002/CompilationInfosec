open Elang
open Batteries
open BatList
open Prog
open Utils
open Builtins
open Utils
open Int

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

let eval_eprog oc (ep : eprog) (memsize : int) (params : int list) :
    int option res =
  (* [eval_eexpr st e] évalue l'expression [e] dans l'état [st]. Renvoie une
     erreur si besoin. *)
  let rec eval_eexpr st (e : expr) : int res =
    match e with
    | Ebinop (binop, i, j) -> (
        eval_eexpr st i >>= fun i ->
        eval_eexpr st j >>= fun j ->
        match (binop, i, j) with
        | Ediv, _, 0 -> Error "Error division by 0"
        | Emod, _, 0 -> Error "Error modulos by 0"
        | _ -> OK (eval_binop binop i j))
    | Eunop (unop, i) -> eval_eexpr st i >>= fun i -> OK (eval_unop unop i)
    | Eint i -> OK i
    | Echar c -> OK (int_of_char c)
    | Evar s ->
        let v = Hashtbl.find_option st.env s in
        if Option.is_none v then Error (Printf.sprintf "Unknown variable %s" s)
        else OK (Option.get v)
    | Ecall (fname, params) when is_builtin fname ->
        Utils.list_map_res (eval_eexpr st) params >>= fun params ->
        do_builtin oc st.mem fname params >>= fun res ->
        if Option.is_some res then OK (Option.get res) else Error "No output"
    | Ecall (fname, params) -> (
        Utils.list_map_res (eval_eexpr st) params >>= fun params ->
        find_function ep fname >>= fun f ->
        eval_efun oc st f fname params >>= fun (v, st) ->
        match v with None -> Error "No output" | Some ret -> OK ret)
  (* [eval_einstr oc st ins] évalue l'instrution [ins] en partant de l'état [st].

     Le paramètre [oc] est un "output channel", dans lequel la fonction "print"
     écrit sa sortie, au moyen de l'instruction [Format.fprintf].

     Cette fonction renvoie [(ret, st')] :

     - [ret] est de type [int option]. [Some v] doit être renvoyé lorsqu'une
     instruction [return] est évaluée. [None] signifie qu'aucun [return] n'a eu
     lieu et que l'exécution doit continuer.

     - [st'] est l'état mis à jour. *)
  and eval_einstr oc (st : int state) (ins : instr) :
      (int option * int state) res =
    match ins with
    | Iassign (s, e) ->
        eval_eexpr st e >>= fun e ->
        Hashtbl.replace st.env s e;
        OK (None, st)
    | Iif (e, i1, i2) ->
        eval_eexpr st e >>= fun e ->
        if e <> 0 then eval_einstr oc st i1 else eval_einstr oc st i2
    | Iwhile (e, i) ->
        eval_eexpr st e >>= fun e ->
        if e <> 0 then
          eval_einstr oc st i >>= fun (ret, s) ->
          if Option.is_none ret then eval_einstr oc s ins else OK (ret, s)
        else OK (None, st)
    | Ireturn e -> eval_eexpr st e >>= fun e -> OK (Some e, st)
    | Iprint e ->
        eval_eexpr st e >>= fun e ->
        Format.fprintf oc "%d\n" e;
        OK (None, st)
    | Iblock [] -> OK (None, st)
    | Iblock (h :: t) ->
        eval_einstr oc st h >>= fun (ret, s) ->
        if Option.is_none ret then eval_einstr oc s (Iblock t) else OK (ret, s)
    | Icall (fname, params) when is_builtin fname ->
        Utils.list_map_res (eval_eexpr st) params >>= fun params ->
        do_builtin oc st.mem fname params >>= fun res -> OK (res, st)
    | Icall (fname, params) ->
        Utils.list_map_res (eval_eexpr st) params >>= fun params ->
        find_function ep fname >>= fun f ->
        eval_efun oc st f fname params >>= fun ret -> OK ret
  (* [eval_efun oc st f fname vargs] évalue la fonction [f] (dont le nom est
     [fname]) en partant de l'état [st], avec les arguments [vargs].

     Cette fonction renvoie un couple (ret, st') avec la même signification que
     pour [eval_einstr]. *)
  and eval_efun oc (st : int state) ({ funargs; funbody } : efun)
      (fname : string) (vargs : int list) : (int option * int state) res =
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
    | () ->
        eval_einstr oc { st with env } funbody >>= fun (v, st') ->
        OK (v, { st' with env = env_save })
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
  find_function ep "main" >>= fun f ->
  (* ne garde que le nombre nécessaire de paramètres pour la fonction "main". *)
  let n = List.length f.funargs in
  let params = take n params in
  let _ =
    List.map
      (uncurry (Hashtbl.replace st.env))
      (combine (List.map fst f.funargs) params)
  in
  eval_efun oc st f "main" params >>= fun (v, st) -> OK v
