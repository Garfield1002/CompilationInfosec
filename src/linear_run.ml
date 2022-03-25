open Batteries
open BatList
open Prog
open Elang
open Cfg
open Elang_run
open Cfg_run
open Rtl
open Rtl_print
open Rtl_run
open Linear
open Builtins
open Utils

let rec exec_linear_instr oc lp fname f st sp next_sp (i : rtl_instr) =
  match i with
  | Rbinop (b, rd, rs1, rs2) -> (
      match
        (Hashtbl.find_option st.regs rs1, Hashtbl.find_option st.regs rs2)
      with
      | Some v1, Some v2 ->
          Hashtbl.replace st.regs rd (eval_binop b v1 v2);
          OK (None, st)
      | _, _ ->
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
            exec_linear_instr_at oc lp fname f st sp next_sp s1
          else OK (None, st)
      | _, _ ->
          Error
            (Printf.sprintf "Branching on undefined registers (%s and %s)"
               (print_reg r1) (print_reg r2)))
  | Rjmp s -> exec_linear_instr_at oc lp fname f st sp next_sp s
  | Rmov (rd, rs) -> (
      match Hashtbl.find_option st.regs rs with
      | Some s ->
          Hashtbl.replace st.regs rd s;
          OK (None, st)
      | _ ->
          Error (Printf.sprintf "Mov on undefined register (%s)" (print_reg rs))
      )
  | Rprint r -> (
      match Hashtbl.find_option st.regs r with
      | Some s ->
          Format.fprintf oc "%d\n" s;
          OK (None, st)
      | _ ->
          Error
            (Printf.sprintf "Print on undefined register (%s)" (print_reg r)))
  | Rret r -> (
      match Hashtbl.find_option st.regs r with
      | Some s -> OK (Some s, st)
      | _ ->
          Error (Printf.sprintf "Ret on undefined register (%s)" (print_reg r)))
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
      find_function lp fname >>= fun f ->
      exec_linear_fun oc lp st next_sp fname f params >>= fun (v, st) ->
      if Option.is_none v then
        fname |> Printf.sprintf "Function %s did not return a value" |> fun x ->
        Error x
      else (
        Hashtbl.replace st.regs rd (Option.get v);
        OK (None, st))
  | Rcall (None, fname, params) ->
      let params = List.filter_map (Hashtbl.find_option st.regs) params in
      find_function lp fname >>= fun f ->
      exec_linear_fun oc lp st next_sp fname f params >>= fun (v, _) ->
      OK (None, st)

and exec_linear_instr_at oc lp fname ({ linearfunbody } as f) st sp next_sp i =
  let l = List.drop_while (fun x -> x <> Rlabel i) linearfunbody in
  exec_linear_instrs oc lp fname f st sp next_sp l

and exec_linear_instrs oc lp fname f st sp next_sp l =
  List.fold_left
    (fun acc i ->
      match acc with
      | Error _ -> acc
      | OK (Some v, st) -> OK (Some v, st)
      | OK (None, st) -> exec_linear_instr oc lp fname f st sp next_sp i)
    (OK (None, st))
    l

and exec_linear_fun oc lp st sp fname f params =
  let regs' = Hashtbl.create 17 in
  match
    List.iter2 (fun n v -> Hashtbl.replace regs' n v) f.linearfunargs params
  with
  | exception Invalid_argument _ ->
      Error
        (Format.sprintf
           "Linear: Called function %s with %d arguments, expected %d\n" fname
           (List.length params)
           (List.length f.linearfunargs))
  | _ ->
      let l = f.linearfunbody in
      let regs_save = Hashtbl.copy st.regs in
      let st' = { st with regs = regs' } in
      exec_linear_instrs oc lp fname f st' sp (sp + f.linearfunstksz) l
      >>= fun (v, st) -> OK (v, { st with regs = regs_save })

and exec_linear_prog oc lp memsize params =
  let st = init_state memsize in
  find_function lp "main" >>= fun f ->
  let n = List.length f.linearfunargs in
  let params = take n params in
  exec_linear_fun oc lp st 0 "main" f params >>= fun (v, st) -> OK v
