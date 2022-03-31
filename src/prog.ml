open Batteries
open Utils

let global_start_address = 0x1000

type mem_access_size = MAS1 | MAS4 | MAS8

let string_of_mem_access_size mas =
  match mas with MAS1 -> "{1}" | MAS4 -> "{4}" | MAS8 -> "{8}"

let mas_of_size n =
  match n with
  | 1 -> OK MAS1
  | 4 -> OK MAS4
  | 8 -> OK MAS8
  | _ -> Error (Printf.sprintf "Unknown memory access size for size = %d" n)

let size_of_mas mas = match mas with MAS1 -> 1 | MAS4 -> 4 | MAS8 -> 8
let archi_mas () = match !Archi.archi with A64 -> MAS8 | A32 -> MAS4

type typ =
  | Tint
  | Tchar
  | Tvoid
  | Tptr of typ
  | Tstruct of string
  | Ttab of typ * int

let rec typCompat t1 t2 =
  match (t1, t2) with
  | _, _ when t1 = t2 -> true
  | Tchar, Tint | Tint, Tchar -> true
  | Tptr p1, Ttab (p2, _) when p1 = p2 -> true
  | Ttab (p2, _), Tptr p1 when p1 = p2 -> true
  | _ -> false

let isArithmetic = typCompat Tint

let rec size_of_type (structs : (string, (string * typ) list) Hashtbl.t)
    (t : typ) : int =
  match t with
  | Tchar | Tvoid -> 1
  | Tint | Tptr _ -> size_of_mas (archi_mas ())
  | Ttab (t, l) -> size_of_type structs t * l
  | Tstruct s -> (
      let opt = Hashtbl.find_option structs s in
      match opt with
      | Some l ->
          List.fold_left (fun acc (_, t) -> size_of_type structs t + acc) 0 l
      | None -> failwith "Undefinned structure")

let rec size_of_type_simple (t : typ) : int =
  match t with
  | Tchar | Tvoid -> 1
  | Tint | Tptr _ -> size_of_mas (archi_mas ())
  | Ttab (t, l) -> size_of_type_simple t * l
  | _ -> failwith "Unknown size"

let rec string_of_typ t =
  match t with
  | Tint -> "int"
  | Tchar -> "char"
  | Tvoid -> "void"
  | Tstruct s -> Printf.sprintf "struct %s" s
  | Tptr t -> t |> string_of_typ |> Printf.sprintf "%s*"
  | Ttab (t, l) -> Printf.sprintf "%s[%d]" (string_of_typ t) l

type init_data = Iint of int | Ichar of char | Ispace of int

let string_of_init i =
  match i with
  | Iint e -> Printf.sprintf "%d" e
  | Ichar c -> Printf.sprintf "\'%c\'" c
  | Ispace e -> Printf.sprintf "space(%d)" e

type 'a gdef = Gfun of 'a | Gvar of typ * init_data
type 'a prog = (string * 'a gdef) list

let dump_gdef dump_fun oc gd =
  match gd with
  | fname, Gfun f ->
      dump_fun oc fname f;
      Format.fprintf oc "\n"
  | varname, Gvar (t, init) ->
      Format.fprintf oc "// %s g_%s = %s;\n" (string_of_typ t) varname
        (string_of_init init)

let dump_prog dump_fun oc = List.iter (dump_gdef dump_fun oc)

type 'a state = {
  env : (string, 'a) Hashtbl.t;
  mem : Mem.t;
  glob_env : (string, 'a) Hashtbl.t;
}

let init_state memsize =
  {
    mem = Mem.init memsize;
    env = Hashtbl.create 17;
    glob_env = Hashtbl.create 17;
  }

let rec init_glob (mem : Mem.t) (glob_env : (string, int) Hashtbl.t)
    (p : 'a prog) (startglob : int) : int res =
  match p with
  | [] -> OK startglob
  | (_, Gfun _) :: t -> init_glob mem glob_env t startglob
  | (varname, Gvar (_, Ichar c)) :: p ->
      Hashtbl.replace glob_env varname startglob;
      Mem.write_bytes mem startglob (split_bytes 1 (int_of_char c))
      >>= fun () -> init_glob mem glob_env p (startglob + 1)
  | (varname, Gvar (_, Iint i)) :: p ->
      Hashtbl.replace glob_env varname startglob;
      Mem.write_bytes mem startglob (split_bytes (size_of_mas (archi_mas ())) i)
      >>= fun () ->
      init_glob mem glob_env p (startglob + size_of_mas (archi_mas ()))
  | (varname, Gvar (_, Ispace s)) :: p ->
      Hashtbl.replace glob_env varname startglob;
      init_glob mem glob_env p (startglob + s)

let set_val env v i = Hashtbl.replace env v i
let get_val env v = Hashtbl.find_option env v

let find_function (ep : 'a prog) fname : 'a res =
  match List.assoc_opt fname ep with
  | Some (Gfun f) -> OK f
  | _ -> Error (Format.sprintf "Unknown function %s\n" fname)

let rec field_offset (structs : (string, (string * typ) list) Hashtbl.t)
    (s : string) (f : string) : int res =
  let rec foo l =
    match l with
    | [] -> Error (Printf.sprintf "\'%s\' has no member named \'%s\'" s f)
    | (h, _) :: t when h = f -> OK 0
    | (_, h) :: t -> foo t >>= fun acc -> OK (acc + size_of_type structs h)
  in
  let opt = Hashtbl.find_option structs s in
  match opt with Some l -> foo l | None -> Error "Undefined structure"

let rec field_type (structs : (string, (string * typ) list) Hashtbl.t)
    (s : string) (f : string) : typ res =
  let opt = Hashtbl.find_option structs s in
  match opt with
  | Some l -> (
      let opt = List.find_opt (fun (name, _) -> name = f) l in
      match opt with
      | Some (_, t) -> OK t
      | None -> Error (Printf.sprintf "\'%s\' has no member named \'%s\'" s f))
  | None -> Error "Undefined structure"

let rec typ_compat_list l1 l2 =
  match (l1, l2) with
  | [], [] -> true
  | t1 :: t1s, t2 :: t2s when typCompat t1 t2 -> typ_compat_list t1s t2s
  | _, _ -> false

let print_typ_list (l : typ list) : unit =
  Printf.printf "[";
  l |> List.map string_of_typ |> List.iter (Printf.printf "%s, ");
  Printf.printf "]"
