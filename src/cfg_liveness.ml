open Batteries
open Cfg
open Prog
open Utils

(* Analyse de vivacité *)

(* [vars_in_expr e] renvoie l'ensemble des variables qui apparaissent dans [e]. *)
let rec vars_in_expr (e : expr) =
  match e with
  | Ebinop (_, e1, e2) -> Set.union (vars_in_expr e1) (vars_in_expr e2)
  | Eunop (_, e) -> vars_in_expr e
  | Eint _ -> Set.empty
  | Estk _ -> Set.empty
  | Eload (e, _) -> vars_in_expr e
  | Evar s -> Set.singleton s
  | Ecall (_, params) ->
      List.map vars_in_expr params |> List.fold Set.union Set.empty

(* [live_cfg_node node live_after] renvoie l'ensemble des variables vivantes
   avant un nœud [node], étant donné l'ensemble [live_after] des variables
   vivantes après ce nœud. *)
let live_cfg_node (node : cfg_node) (live_after : string Set.t) =
  match node with
  | Cassign (s, e, _) -> Set.union (vars_in_expr e) (Set.remove s live_after)
  | Cstore (e1, e2, _, _) ->
      List.fold Set.union live_after [ vars_in_expr e1; vars_in_expr e2 ]
  | Creturn e -> Set.union (vars_in_expr e) live_after
  | Cprint (e, _) -> Set.union (vars_in_expr e) live_after
  | Ccmp (e, _, _) -> Set.union (vars_in_expr e) live_after
  | Cnop _ -> live_after
  | Ccall (_, params, _) ->
      List.map vars_in_expr params |> List.fold Set.union live_after

let findSet t n =
  let s = Hashtbl.find_option t n in
  if Option.is_none s then Set.empty else Option.get s

(* [live_after_node cfg n] renvoie l'ensemble des variables vivantes après le
   nœud [n] dans un CFG [cfg]. [lives] est l'état courant de l'analyse,
   c'est-à-dire une table dont les clés sont     des identifiants de nœuds du CFG et
   les valeurs sont les ensembles de variables vivantes avant chaque nœud. *)
let live_after_node cfg n (lives : (int, string Set.t) Hashtbl.t) : string Set.t
    =
  Set.fold
    (fun n acc -> Set.union acc (findSet lives n))
    (succs cfg n) Set.empty

(* [live_cfg_nodes cfg lives] effectue une itération du calcul de point fixe.

   Cette fonction met à jour l'état de l'analyse [lives] et renvoie un booléen
   qui indique si le calcul a progressé durant cette itération (i.e. s'il existe
   au moins un nœud n pour lequel l'ensemble des variables vivantes avant ce
   nœud a changé). *)
let live_cfg_nodes cfg (lives : (int, string Set.t) Hashtbl.t) =
  Hashtbl.fold
    (fun i n acc ->
      let outSet = live_after_node cfg i lives in
      let inSet = live_cfg_node n outSet in
      if Set.equal inSet (findSet lives i) then acc
      else (
        Hashtbl.replace lives i inSet;
        true))
    cfg false

(* [live_cfg_fun f] calcule l'ensemble des variables vivantes avant chaque nœud
   du CFG en itérant [live_cfg_nodes] jusqu'à ce qu'un point fixe soit atteint.
*)
let live_cfg_fun (f : cfg_fun) : (int, string Set.t) Hashtbl.t =
  let lives = Hashtbl.create 17 in
  while live_cfg_nodes f.cfgfunbody lives do
    ()
  done;
  lives
