open Batteries
open BatPrintf
open Prog

(* Les AST sont des arbres, du type [tree], étiquetés par des [tag].

   Un arbre [tree] est soit un nœud [Node(t, children)] où [t] est un tag et
   [children] une liste de sous-arbres ; soit une feuille qui contient une
   chaîne de caractères ([StringLeaf]), un entier ([IntLeaf]), un caractère
   ([CharLeaf]), ou rien du tout ([NullLeaf]).

   La signification des différents tags :

   - importe peu : vous pouvez définir de nouveaux types de tags si ça vous
   semble nécessaire / profitable, pour peu de compléter la fonction
   [string_of_tag] ci-dessous.

   - devrait être assez claire d'après le nom du tag ou l'utilisation qui en est
   faite dans l'exemple donné dans le sujet.

   - peut être demandée à votre encadrant de TP favori (ou celui présent en
   séance, à défaut)
*)

type tag =
  | Tdeclare
  | Tassign
  | Tif
  | Twhile
  | Tblock
  | Treturn
  | Tprint
  | Tint
  | Tadd
  | Tmul
  | Tdiv
  | Tmod
  | Txor
  | Tsub
  | Tclt
  | Tcgt
  | Tcle
  | Tcge
  | Tceq
  | Tcne
  | Tne
  | Telse
  | Tneg
  | Tlistglobdef
  | Tfundef
  | Tfunname
  | Tfunargs
  | Tfunbody
  | Tassignvar
  | Targ
  | Targs
  | Tcall
  | Tassignchar
  | Tchar
  | Taddrof
  | Tindirection
  | Tstruct
  | Tstructdef
  | Tstructbody
  | Tarray
  | Tnot
  | Tand
  | Tor
  | Tband
  | Tarrow

type tree =
  | Node of tag * tree list
  | StringLeaf of string
  | IntLeaf of int
  | NullLeaf
  | CharLeaf of char
  | TypeLeaf of typ

let string_of_stringleaf = function
  | StringLeaf s -> s
  | _ -> failwith "string_of_stringleaf called on non-stringleaf nodes."

type astfun = string list * tree
type ast = (string * astfun) list

let string_of_tag = function
  | Tassign -> "Tassign"
  | Tdeclare -> "Tdeclare"
  | Tif -> "Tif"
  | Twhile -> "Twhile"
  | Tblock -> "Tblock"
  | Treturn -> "Treturn"
  | Tprint -> "Tprint"
  | Tint -> "Tint"
  | Tadd -> "Tadd"
  | Tmul -> "Tmul"
  | Tdiv -> "Tdiv"
  | Tmod -> "Tmod"
  | Txor -> "Txor"
  | Tsub -> "Tsub"
  | Tclt -> "Tclt"
  | Tcgt -> "Tcgt"
  | Tcle -> "Tcle"
  | Tcge -> "Tcge"
  | Tceq -> "Tceq"
  | Tcne -> "Tcne"
  | Tlistglobdef -> "Tlistglobdef"
  | Tfundef -> "Tfundef"
  | Tfunname -> "Tfunname"
  | Tfunargs -> "Tfunargs"
  | Tfunbody -> "Tfunbody"
  | Tassignvar -> "Tassignvar"
  | Tassignchar -> "Tassignchar"
  | Targ -> "Targ"
  | Telse -> "Telse"
  | Tneg -> "Tneg"
  | Tne -> "Tneg"
  | Tcall -> "Tcall"
  | Targs -> "Targs"
  | Tchar -> "Tchar"
  | Taddrof -> "Taddrof"
  | Tindirection -> "Tindirection"
  | Tstruct -> "Tstruct"
  | Tstructdef -> "Tstructdef"
  | Tstructbody -> "Tstructbody"
  | Tarray -> "Tarray"
  | Tnot -> "Tnot"
  | Tand -> "Tand"
  | Tor -> "Tor"
  | Tband -> "Tband"
  | Tarrow -> "Tarrow"

let type_of_leaf l =
  match l with TypeLeaf t -> t | _ -> failwith "type_of_leaf: unexpected AST"

(* Écrit un fichier .dot qui correspond à un AST *)
let rec draw_ast a next =
  match a with
  | Node (t, l) ->
      let code, nodes, next =
        List.fold_left
          (fun (code, nodes, nextnode) n ->
            let node, next, ncode = draw_ast n nextnode in
            (code @ ncode, node :: nodes, next))
          ([], [], next) l
      in
      ( next,
        next + 1,
        code
        @ [ Format.sprintf "n%d [label=\"%s\"]\n" next (string_of_tag t) ]
        @ List.map (fun n -> Format.sprintf "n%d -> n%d\n" next n) nodes )
  | StringLeaf s ->
      (next, next + 1, [ Format.sprintf "n%d [label=\"%s\"]\n" next s ])
  | TypeLeaf t ->
      ( next,
        next + 1,
        [ Format.sprintf "n%d [label=\"%s\"]\n" next (string_of_typ t) ] )
  | IntLeaf i ->
      (next, next + 1, [ Format.sprintf "n%d [label=\"%d\"]\n" next i ])
  | CharLeaf c ->
      (next, next + 1, [ Format.sprintf "n%d [label=\"%c\"]\n" next c ])
  | NullLeaf ->
      (next, next + 1, [ Format.sprintf "n%d [label=\"null\"]\n" next ])

let draw_ast_tree oc ast =
  let _, _, s = draw_ast ast 1 in
  let s = String.concat "" s in
  Format.fprintf oc "digraph G{\n%s\n}\n" s

let rec string_of_ast a =
  match a with
  | Node (t, l) ->
      Format.sprintf "Node(%s,%s)" (string_of_tag t)
        (String.concat ", " (List.map string_of_ast l))
  | StringLeaf s -> Format.sprintf "\"%s\"" s
  | CharLeaf c -> Format.sprintf "\"%c\"" c
  | TypeLeaf t -> t |> string_of_typ |> Format.sprintf "\"%s\""
  | IntLeaf i -> Format.sprintf "%d" i
  | NullLeaf -> "null"

let rec resolve_associativity (term : tree) (other : tree list) : tree =
  match other with
  | Node (tag, l) :: t -> resolve_associativity (Node (tag, term :: l)) t
  | _ -> term
