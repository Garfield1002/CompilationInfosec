open Batteries
open BatList
open Elang
open Cfg
open Elang_run
open Cfg_run
open Rtl
open Rtl_print
open Utils
open Builtins
open Prog

type state = {
  mem : Mem.t;
  regs : (reg, int) Hashtbl.t;
  glob_env : (string, int) Hashtbl.t;
}

let init_state memsize =
  {
    mem = Mem.init memsize;
    regs = Hashtbl.create 17;
    glob_env = Hashtbl.create 17;
  }

let eval_rtl_cmp = function
  | Rcle -> ( <= )
  | Rclt -> ( < )
  | Rcge -> ( >= )
  | Rcgt -> ( > )
  | Rceq -> ( = )
  | Rcne -> ( <> )

let rec exec_rtl_instr oc rp rtlfunname f st sp next_sp (i : rtl_instr) =
  match i with
  | Rbinop (b, rd, rs1, rs2) -> (
      match
        (Hashtbl.find_option st.regs rs1, Hashtbl.find_option st.regs rs2)
      with
      | Some v1, Some v2 ->
          Hashtbl.replace st.regs rd (eval_binop b v1 v2);
          OK (None, st)
      | _ ->
          Error
            (Printf.sprintf "Binop applied on undefined registers (%s and %s)"
               (print_reg rs1) (print_reg rs2)))
  | Runop (u, rd, rs) -> (
      match Hashtbl.find_option st.regs rs with
      | Some v ->
          Hashtbl.replace st.regs rd (eval_unop u v);
          OK (None, st)
      | _ ->
          Error
            (Printf.sprintf "Unop applied on undefined register %s"
               (print_reg rs)))
  | Rconst (rd, i) ->
      Hashtbl.replace st.regs rd i;
      OK (None, st)
  | Rglobvar (rd, s) ->
      let addr = Hashtbl.find st.glob_env s in
      Hashtbl.replace st.regs rd addr;
      OK (None, st)
  | Rstk (rd, addr) ->
      Hashtbl.replace st.regs rd (addr + sp);
      OK (None, st)
  | Rstore (rd, rs, sz) -> (
      match
        (Hashtbl.find_option st.regs rd, Hashtbl.find_option st.regs rs)
      with
      | Some rd, Some rs ->
          Mem.write_bytes st.mem rd (split_bytes sz rs) >>= fun () ->
          OK (None, st)
      | _ ->
          Error
            (Printf.sprintf "Binop applied on undefined registers (%s and %s)"
               (print_reg rd) (print_reg rs)))
  | Rload (rd, rs, sz) -> (
      match Hashtbl.find_option st.regs rs with
      | Some addr ->
          Mem.read_bytes_as_int st.mem addr sz >>= fun res ->
          Hashtbl.replace st.regs rd res;
          OK (None, st)
      | _ ->
          Error
            (Printf.sprintf "Binop applied on undefined registers (%s and %s)"
               (print_reg rd) (print_reg rs)))
  | Rbranch (cmp, r1, r2, s1) -> (
      match
        (Hashtbl.find_option st.regs r1, Hashtbl.find_option st.regs r2)
      with
      | Some v1, Some v2 ->
          if eval_rtl_cmp cmp v1 v2 then
            exec_rtl_instr_at oc rp rtlfunname f st sp next_sp s1
          else OK (None, st)
      | _, _ ->
          Error
            (Printf.sprintf "Branching on undefined registers (%s and %s)"
               (print_reg r1) (print_reg r2)))
  | Rjmp s -> exec_rtl_instr_at oc rp rtlfunname f st sp next_sp s
  | Rmov (rd, rs) -> (
      match Hashtbl.find_option st.regs rs with
      | Some s ->
          Hashtbl.replace st.regs rd s;
          OK (None, st)
      | _ ->
          Error (Printf.sprintf "Mov on undefined register (%s)" (print_reg rs))
      )
  | Rret r -> (
      match Hashtbl.find_option st.regs r with
      | Some s -> OK (Some s, st)
      | _ ->
          Error (Printf.sprintf "Ret on undefined register (%s)" (print_reg r)))
  | Rprint r -> (
      match Hashtbl.find_option st.regs r with
      | Some s ->
          Format.fprintf oc "%d\n" s;
          OK (None, st)
      | _ ->
          Error
            (Printf.sprintf "Print on undefined register (%s)" (print_reg r)))
  | Rlabel n -> OK (None, st)
  | Rcall (Some rd, fname, params) when is_builtin fname ->
      let params = List.filter_map (Hashtbl.find_option st.regs) params in
      do_builtin oc st.mem fname params >>= fun res ->
      if Option.is_some res then (
        Hashtbl.replace st.regs rd (Option.get res);
        OK (None, st))
      else
        fname |> Printf.sprintf "Function %s did not return a value" |> fun x ->
        Error x
  | Rcall (None, fname, params) when is_builtin fname ->
      let params = List.filter_map (Hashtbl.find_option st.regs) params in
      do_builtin oc st.mem fname params >>= fun _ -> OK (None, st)
  | Rcall (Some rd, fname, params) ->
      let params = List.filter_map (Hashtbl.find_option st.regs) params in
      find_function rp fname >>= fun f ->
      exec_rtl_fun oc rp st next_sp fname f params >>= fun (v, st) ->
      if Option.is_none v then
        fname |> Printf.sprintf "Function %s did not return a value" |> fun x ->
        Error x
      else (
        Hashtbl.replace st.regs rd (Option.get v);
        OK (None, st))
  | Rcall (None, fname, params) ->
      let params = List.filter_map (Hashtbl.find_option st.regs) params in
      find_function rp fname >>= fun f ->
      exec_rtl_fun oc rp st next_sp fname f params >>= fun (_, st) ->
      OK (None, st)

and exec_rtl_instr_at oc rp rtlfunname ({ rtlfunbody } as f : rtl_fun) st sp
    next_sp i =
  match Hashtbl.find_option rtlfunbody i with
  | Some l -> exec_rtl_instrs oc rp rtlfunname f st sp next_sp l
  | None ->
      Error (Printf.sprintf "Jump to undefined label (%s_%d)" rtlfunname i)

and exec_rtl_instrs oc rp rtlfunname f st sp next_sp l =
  List.fold_left
    (fun acc i ->
      match acc with
      | Error _ -> acc
      | OK (Some v, st) -> OK (Some v, st)
      | OK (None, st) -> exec_rtl_instr oc rp rtlfunname f st sp next_sp i)
    (OK (None, st))
    l

and exec_rtl_fun oc rp st sp rtlfunname f params =
  let regs' = Hashtbl.create 17 in
  match
    List.iter2 (fun n v -> Hashtbl.replace regs' n v) f.rtlfunargs params
  with
  | exception Invalid_argument _ ->
      Error
        (Format.sprintf
           "RTL: Called function %s with %d arguments, expected %d\n" rtlfunname
           (List.length params) (List.length f.rtlfunargs))
  | _ -> (
      match Hashtbl.find_option f.rtlfunbody f.rtlfunentry with
      | None ->
          Error (Printf.sprintf "Unknown node (%s_%d)" rtlfunname f.rtlfunentry)
      | Some l ->
          let regs_save = Hashtbl.copy st.regs in
          let st' = { st with regs = regs' } in
          exec_rtl_instrs oc rp rtlfunname f st' sp (sp + f.rtlfunstksz) l
          >>= fun (v, st) -> OK (v, { st with regs = regs_save }))

and exec_rtl_prog oc rp memsize params =
  let st = init_state memsize in
  init_glob st.mem st.glob_env rp global_start_address >>= fun _ ->
  find_function rp "main" >>= fun f ->
  let n = List.length f.rtlfunargs in
  let params = take n params in
  exec_rtl_fun oc rp st 0 "main" f params >>= fun (v, st) -> OK v
