open Syntax
let parse_string = Lambda_parse.parse_string
let string_of_expr = string_of_expr

let r = ref 0

let fresh s =
  let v = !r in
  r := !r + 1;
  s ^ (string_of_int v)

(* Your implementation begins from here *)

let mem e l =
List.fold_left(fun acc x -> if x=e then true else acc) false l
;;

let remove e l =
 let l2 = [] in
 List.fold_left (fun acc x->if x=e then acc else acc@[x]) l2 l
;;

(*helper functions for union*)
let rec stutterhelp prev l l2=
  match l with
  | [] -> l2@[prev]
  | head::tail ->
  if prev = head then stutterhelp head tail l2
  else
  let l2=l2@[prev] in stutterhelp head tail l2
  ;;

  let remove_stutter l =
  match l with
  | [] -> l
  | head::tail ->
  stutterhelp head tail []
  ;;

let union l1 l2 =
 let l3 = List.sort String.compare (l1@l2) in remove_stutter l3
 ;;

let add e l =
let ex = mem e l in
if ex then List.sort String.compare l
else
List.sort String.compare (l@[e])
;;


let rec free_variables e =
match e with
|Var x -> [x]
|App(e1,e2) -> union(free_variables e1)(free_variables e2)
|Lam (x,y) -> remove x (free_variables y)
;;

let rec substitute expr a b =
  match expr with
  |Var x->
    if a = x then b
    else expr
  | App (e1,e2) -> App(substitute e1 a b, substitute e2 a b)
  | Lam (x,y) ->
    if a = x then expr
    else if (mem x (free_variables b)) then let z = fresh "z" 
    in Lam (z, substitute (substitute y x (Var z)) a b)
    else Lam (x, substitute y a b)
;;

(*cbv does the opposite of normal, and according to the strategy notations, the logic process goes somewhat in reverse, so the code should follow*)
let rec reduce_cbv e =
match e with
  | Var x -> (e,false)
  | Lam (x,y) -> (Lam(x,y),false)
  | App (e1, e2) ->
    let e1', is_reduced = reduce_cbv e1 in
    if is_reduced then (App (e1', e2), true)
    else 
    let e2', is_reduced =reduce_cbv e2 in
    if is_reduced then (App(e1,e2'),true)
    else
        match e1 with
        |Lam(x,y)-> (substitute y x e2',true) (*You want to substitute last since cbv starts at the rightmost side*)
        |_-> (App(e1,e2),false)
  ;;
(*cbn is similar to normal, except it cuts out half the strategy notation. Instead of reducing first, it plugs in first, then reduces, therefore we plug in chug till the very end. That is the biggest difference.*)
(*cbn shares a lot of code with normal for this reason*)
let rec reduce_cbn e =
match e with
  |App (Lam (x,e),e2)->(substitute e x e2, true)
  | App (e1, e2) ->
    let e1', is_reduced = reduce_cbn e1 in
    if is_reduced then (App (e1', e2), true)
    else 
        let e2', is_reduced = reduce_cbn e2 in
        if is_reduced then (App (e1, e2'), true)
        else (App (e1, e2), false)
  | Lam (x,y) -> (Lam(x,y),false) (*plug and chug: you don't break down the interior expression*)
  | _-> e, false
;;

(*normal starts on the leftmost expression and plugs and reduces in the right ones until there is only one expression*)
let rec reduce_normal e =
  match e with
  |App (Lam (x,e),e2)->(substitute e x e2, true)
  | App (e1, e2) ->
    let e1', is_reduced = reduce_normal e1 in
    if is_reduced then (App (e1', e2), true)
    else 
        let e2', is_reduced = reduce_normal e2 in
        if is_reduced then (App (e1, e2'), true)
        else (App (e1, e2), false)
  | Lam (x,y) -> let z, is_reduced = reduce_normal y in (Lam (x,z), is_reduced) (*reduced won't always return true, so you cannot return a blanket boolean for all cases*)
  | _->(e, false)
  ;;

(* Your implementation done here *)

(* Debug your code by printing out evaluation results *)
let rec eval log depth reduce expr =
  if depth = 0 then failwith "non-termination?"
  else begin
    let expr', reduced = reduce expr in
    if not reduced then expr else begin
      if log then print_endline ("= " ^ (string_of_expr expr'));
      eval log (depth-1) reduce expr'
    end
  end
let eval_cbv = eval true 1000 reduce_cbv
let eval_cbn = eval true 1000 reduce_cbn
let eval_normal = eval true 1000 reduce_normal

(* To debug and observe the evaluation steps of your `reduce_cbv`, `reduce_cbn`
 * or `reduce_normal` implementation, use the following code.
 *
 *let _ = eval_cbv (parse_string "(\\x.x) ((\\x.x) (\\z.(\\x.x) z))")
 *let _ = print_endline ""
 *
 *let _ = eval_cbn (parse_string "(\\x.x) ((\\x.x) (\\z.(\\x.x) z))")
 *let _ = print_endline ""
 *
 *let _ = eval_normal (parse_string "(\\x.x) ((\\x.x) (\\z.(\\x.x) z))")
 *let _ = print_endline ""
 *)
