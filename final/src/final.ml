open Stdlib

let _  = Random.self_init ()

type term =
  | Constant of string
  | Variable of string
  | Function of string * term list

type head = term
type body = term list

type clause = Fact of head | Rule of head * body

type program = clause list

type goal = term list

let rec string_of_f_list f tl =
  let _, s = List.fold_left (fun (first, s) t ->
    let prefix = if first then "" else s ^ ", " in
    false, prefix ^ (f t)) (true,"") tl
  in
  s

let rec string_of_term t =
  match t with
  | Constant c -> c
  | Variable v -> v
  | Function (f,tl) ->
      f ^ "(" ^ (string_of_f_list string_of_term tl) ^ ")"

let string_of_term_list fl =
  string_of_f_list string_of_term fl

let string_of_goal g =
  "?- " ^ (string_of_term_list g)

let string_of_clause c =
  match c with
  | Fact f -> string_of_term f ^ "."
  | Rule (h,b) -> string_of_term h ^ " :- " ^ (string_of_term_list b) ^ "."

let string_of_program p =
  let rec loop p acc =
    match p with
    | [] -> acc
    | [c] -> acc ^ (string_of_clause c)
    | c::t ->  loop t (acc ^ (string_of_clause c) ^ "\n")
  in loop p ""

let var v = Variable v
let const c = Constant c
let func f l = Function (f,l)
let fact f = Fact f
let rule h b = Rule (h,b)

(* Problem 1 *)

let rec occurs_check v t =
  match t with
  | Constant _ -> false
  | Variable _ -> if v=t then true else false
  | Function (_,tl) -> List.fold_left(fun acc x -> if occurs_check v x then true else acc)false tl

(* Problem 2 *)

module VarSet = Set.Make(struct type t = term let compare = Stdlib.compare end)
(* API Docs for Set : https://caml.inria.fr/pub/docs/manual-ocaml/libref/Set.S.html *)

let rec loop f t =
match t with
| []-> VarSet.empty
| h::tl -> VarSet.union (f h) (loop f tl)
(*loop takes a list and applies f to each element and unionizes them*)

let rec variables_of_term t =
match t with
| Constant _ -> VarSet.empty
| Variable _ -> VarSet.singleton t
| Function (_,tl) -> loop (variables_of_term) tl


let variables_of_clause c =
match c with
| Fact f -> variables_of_term f
| Rule (h,b) -> VarSet.union (variables_of_term h) (loop (variables_of_term) b)

(* Problem 3 *)

module Substitution = Map.Make(struct type t = term let compare = Stdlib.compare end)
(* See API docs for OCaml Map: https://caml.inria.fr/pub/docs/manual-ocaml/libref/Map.S.html *)

let string_of_substitution s =
  "{" ^ (
    Substitution.fold (
      fun v t s ->
        match v with
        | Variable v -> s ^ "; " ^ v ^ " -> " ^ (string_of_term t)
        | Constant _ -> assert false (* substitution maps a variable to a term *)
        | Function _ -> assert false (* substitution maps a variable to a term *)
    ) s ""
  ) ^ "}"

(*To update the structures deconstruct, apply, and reconstruct*)

let subl f s t =
List.fold_left(fun acc x -> acc@[f s x]) [] t
(*subl takes a list of terms or clauses and applies substitution f on each element*)

let rec substitute_in_term s t =
 match t with
 | Constant _ -> t
 | Variable _ ->
 (match Substitution.find_opt t s with
  | None -> t
  | Some t' -> t')
 | Function (f,tl) -> Function (f, subl substitute_in_term s tl)

let substitute_in_clause s c =
  match c with
  | Fact f -> Fact (substitute_in_term s f)
  | Rule (h,b) -> Rule (substitute_in_term s h, subl substitute_in_term s b)

(* Problem 4 *)

let counter = ref 0
let fresh () =
  let c = !counter in
  counter := !counter + 1;
  Variable ("_G" ^ string_of_int c)

let freshen c =
  let vars = variables_of_clause c in
  let s = VarSet.fold (fun v s -> Substitution.add v (fresh()) s) vars Substitution.empty in
  substitute_in_clause s c

(*
let c = (rule (func "p" [var "X"; var "Y"; const "a"]) [func "q" [var "X"; const "b"; const "a"]])
let _ = print_endline (string_of_clause c)
let _ = print_endline (string_of_clause (freshen c))
*)

exception Not_unifiable

(*
ðœƒ{X/Y} : Substitution.map (fun t-> sub {X/Y} into t) 
{X/Y} : Substitution.singleton v t
U : Substitution.add then
 *)

let unify t1 t2 =

let rec reunify t1 t2 s =
(*apply theta/s to x and y*)
let t1 = substitute_in_term s t1 in
let t2 = substitute_in_term s t2 in
match t1,t2 with
| Variable x, _ -> (*X dne in Y -> ðœƒ{X/Y} âˆª {X/Y}*)
if t1=t2 then s
else if occurs_check t1 t2 then raise Not_unifiable
else Substitution.add t1 t2 (Substitution.map (fun t -> substitute_in_term (Substitution.singleton t1 t2) t) s)

| _,Variable x -> (*Y dne in X -> ðœƒ{Y/X} âˆª {Y/X}*)
if t1=t2 then s
else if occurs_check t2 t1 then raise Not_unifiable
else Substitution.add t2 t1 (Substitution.map (fun t -> substitute_in_term (Substitution.singleton t2 t1) t) s)

| Constant x, Constant y -> (*x=y -> theta*)
if t1=t2 then s
else raise Not_unifiable

|Function(h1,b1),Function(h2,b2)-> (*X is f(X1,...,Xn) and Y is f(Y1,...,Yn) -> (fold_left (fun ðœƒ (X,Y) -> unify(X,Y,ðœƒ)) ðœƒ [(X1,Y1),...,(Xn,Yn)]) *)
List.fold_left2(fun s x y -> reunify x y s)s b1 b2

| _ -> raise Not_unifiable (*failure*)
in reunify t1 t2 Substitution.empty

(* Problem 5 *)

let nondet_query program goal =
(*loop 1*)
let rec query g resolvant =
(*loop while the resolvant is not empty*)
match resolvant with
| [] -> g
| r -> (*putt a random goal out from resolvant*)
let a = List.nth r (Random.int (List.length r)) in
let r = List.fold_left(fun acc x -> if x=a then acc else acc@[x])[] r in
(*get a random renamed clause*)
match freshen (List.nth program (Random.int (List.length program))) with
  | Fact f ->(
    match unify f a with (*get theta/s from unifying a' and a*)
    | exception (Not_unifiable) -> raise (Not_unifiable) (*if no goal and clause exist, break*)
    | s -> query (subl substitute_in_term s g) (subl substitute_in_term s r)) (*apply theta/s to g and r*)
  | Rule (h,b) ->
    match unify h a with
    | exception (Not_unifiable) -> raise (Not_unifiable)
    | s -> query (subl substitute_in_term s g) (subl substitute_in_term s (r@b)) (*append the [b1...bn] into r*)
  (*loop 2*)
  in let rec loop () =
  match query goal goal with (*initialize the resolvant with the goal*)
  | exception (Not_unifiable) -> loop() (*when it fails, try again*)
  | result -> result
  in loop()

(* Problem Bonus *)

let det_query program goal =
raise (Failure "Problem Bonus Not implemented")