open Prog
open Elang
open Elang_run
open Batteries
open BatList
open Cfg
open Utils
open Builtins

let eval_cfgprog oc cp memsize params =
  let rec eval_cfgexpr st (sp : int) (sp_offset : int) (e : expr) : int res =
    let eval_cfgexpr_params = eval_cfgexpr st sp sp_offset in
    match e with
    | Ebinop (b, e1, e2) ->
        eval_cfgexpr_params e1 >>= fun v1 ->
        eval_cfgexpr_params e2 >>= fun v2 ->
        let v = eval_binop b v1 v2 in
        OK v
    | Eunop (u, e) ->
        eval_cfgexpr_params e >>= fun v1 ->
        let v = eval_unop u v1 in
        OK v
    | Eint i -> OK i
    | Evar s -> (
        match Hashtbl.find_option st.env s with
        | Some v -> OK v
        | None -> Error (Printf.sprintf "Unknown variable %s\n" s))
    | Ecall (fname, params) when is_builtin fname ->
        Utils.list_map_res eval_cfgexpr_params params >>= fun params ->
        do_builtin oc st.mem fname params >>= fun res ->
        if Option.is_some res then OK (Option.get res) else Error "No output"
    | Ecall (fname, params) -> (
        Utils.list_map_res eval_cfgexpr_params params >>= fun params ->
        find_function cp fname >>= fun f ->
        eval_cfgfun oc st sp_offset f fname params >>= fun (v, _) ->
        match v with None -> Error "No output" | Some ret -> OK ret)
    | Estk addr -> OK (sp + addr)
    | Eload (addr, sz) ->
        eval_cfgexpr_params addr >>= fun addr ->
        Mem.read_bytes_as_int st.mem addr sz >>= fun res ->
        (* Format.fprintf oc "Read %d at address %d with size %d\n" res addr sz; *)
        OK res
    | Eglobvar v ->
        let i = Hashtbl.find st.glob_env v in
        OK i
  and eval_cfginstr oc st ht sp sp_offset (n : int) : (int * int state) res =
    let eval_cfgexpr_params = eval_cfgexpr st sp sp_offset in
    let eval_cfginstr_params = eval_cfginstr oc st ht sp sp_offset in
    match Hashtbl.find_option ht n with
    | None -> Error (Printf.sprintf "Invalid node identifier\n")
    | Some node -> (
        match node with
        | Cnop succ -> eval_cfginstr_params succ
        | Cassign (v, e, succ) ->
            eval_cfgexpr_params e >>= fun i ->
            Hashtbl.replace st.env v i;
            eval_cfginstr_params succ
        | Ccmp (cond, i1, i2) ->
            eval_cfgexpr_params cond >>= fun i ->
            if i = 0 then eval_cfginstr_params i2 else eval_cfginstr_params i1
        | Creturn e -> eval_cfgexpr_params e >>= fun e -> OK (e, st)
        | Cprint (e, succ) ->
            eval_cfgexpr_params e >>= fun e ->
            Format.fprintf oc "%d\n" e;
            eval_cfginstr_params succ
        | Ccall (fname, params, succ) when is_builtin fname ->
            Utils.list_map_res eval_cfgexpr_params params >>= fun params ->
            do_builtin oc st.mem fname params >>= fun _ ->
            eval_cfginstr_params succ
        | Ccall (fname, params, succ) ->
            Utils.list_map_res eval_cfgexpr_params params >>= fun params ->
            find_function cp fname >>= fun f ->
            eval_cfgfun oc st sp_offset f fname params >>= fun _ ->
            eval_cfginstr_params succ
        | Cstore (addr, e, sz, succ) ->
            eval_cfgexpr_params addr >>= fun addr ->
            eval_cfgexpr_params e >>= fun e ->
            (* Format.fprintf oc "Writing %d at address %d with size %d\n" e addr
               sz; *)
            Mem.write_bytes st.mem addr (split_bytes sz e) >>= fun () ->
            eval_cfginstr_params succ)
  and eval_cfgfun oc st sp { cfgfunargs; cfgfunbody; cfgentry; cfgfunstksz }
      cfgfunname vargs =
    let st' = { st with env = Hashtbl.create 17 } in
    match
      List.iter2 (fun a v -> Hashtbl.replace st'.env a v) cfgfunargs vargs
    with
    | () ->
        eval_cfginstr oc st' cfgfunbody sp (sp + cfgfunstksz) cfgentry
        >>= fun (v, st') -> OK (Some v, { st' with env = st.env })
    | exception Invalid_argument _ ->
        Error
          (Format.sprintf
             "CFG: Called function %s with %d arguments, expected %d.\n"
             cfgfunname (List.length vargs) (List.length cfgfunargs))
  in
  let st = init_state memsize in
  init_glob st.mem st.glob_env cp 0x1000 >>= fun _ ->
  find_function cp "main" >>= fun f ->
  let n = List.length f.cfgfunargs in
  let params = take n params in
  eval_cfgfun oc st 0 f "main" params >>= fun (v, st) -> OK v
