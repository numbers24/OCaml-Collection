(*Problem 1*)
   let rec cond_dup l f =
  let list = [] in
  match l with
  | []->list
  | head::tail->
  let list = [head] in
  if f head then let list = list@[head] in list@cond_dup tail f
  else
  list@cond_dup tail f
  ;;

(*Problem 2*)
  let rec n_times (f, n, v) =
    if n<=0 then v
    else n_times(f,n-1,f v);;


(*Problem 3*)
exception IncorrectRange

  let rec range num1 num2 =
  if num2<num1 then raise(IncorrectRange)
  else
  let list = [num1] in
  if num1==num2 then list
  else
  list@range (num1+1) num2
  ;;


(*Problem 4*)

  let rec zipwith f l1 l2 =
  let lz = [] in
  match l1 with
  | []->lz
  | h1::t1->
  match l2 with
  | []->lz
  | h2::t2->
  let lz=lz@[f h1 h2] in lz@zipwith f t1 t2
  ;;

  
(*Problem 5*)
  let rec update l bucket newbuck up=
    match l with
    | []-> bucket
    | head::_ ->
    match bucket with
    | []-> 
    if up then newbuck
    else
    newbuck@[l]
    | front::back ->
    match front with
    | []-> []
    | h::_ ->
    if head==h then let newbuck=newbuck@[l] in update l back newbuck true
    else
    let newbuck = newbuck@[front] in update l back newbuck up
    ;;

    let rec check p head bucket=
    match bucket with
    | []-> [head]
    | front::back ->
    match front with
    | []-> []
    | h::_ ->
    if p h head then front@[head]
    else
    check p head back
    ;;
    
    let rec buckhelp p l bucket =
    match l with
    | []->bucket
    | head::tail ->
    let temp = check p head bucket in
    let bucket = update temp bucket [] false in buckhelp p tail bucket
    ;;
  

    let buckets p l=
    buckhelp p l []
    ;;
  
  
(*Problem 6*)
  let rec stutterhelp prev l l2=
  match l with
  | [] -> l2@[prev]
  | head::tail ->
  if prev == head then stutterhelp head tail l2
  else
  let l2=l2@[prev] in stutterhelp head tail l2
  ;;

  let remove_stutter l =
  match l with
  | [] -> l
  | head::tail ->
  stutterhelp head tail []
  ;;

(*Problem 7*)
 
  let rec scan head l2 =
 match head with
 | []->l2
 | h::t->
 let l2 = l2@[h] in scan t l2
 ;; 

 let rec flatten l =
 let l2 = [] in
 match l with
 | []->l2
 | head::tail->
 let l2 = scan head l2 in l2@flatten tail
 ;;


(*Problem 8*)

  type 'a tree = Leaf | Node of 'a tree * 'a * 'a tree;;

  let checkNode node =
  match node with
  Leaf->false
  | Node (_,_,_)->true
  ;;

  let rec fold_inorder f acc t =
  match t with
  Leaf -> acc
  | Node (l,x,r) ->
  if checkNode l then let acc = f (fold_inorder f acc l) x in
  if checkNode r then fold_inorder f acc r
  else
  f acc x
  else
  f acc x
  ;;

(*Problem 9*)

  let rec fib prev curr m n =
  if m==n then curr
  else
  fib curr (prev+curr) (m+1) n
  ;;

  let fib_tailrec n =
  fib 0 1 1 n
  ;;