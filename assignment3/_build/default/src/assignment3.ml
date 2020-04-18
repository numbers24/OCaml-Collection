(******************** Problem 1 ********************)

type 'a element = {
  content : 'a;
  mutable next : 'a element option;
  mutable prev : 'a element option
}

let create () = ref None

let is_empty t = !t = None

let insert_first l c =
  let n = {content = c; next = !l; prev = None} in
  let _ = match !l with
    | Some o -> (o.prev <- Some n)
    | None -> () in
  let _ = (l := Some n) in
  n

let insert_after n c =
  let n' = {content = c; next = n.next; prev = Some n} in
  let _ =  match n.next with
    | Some o -> (o.prev <- (Some n'))
    | None -> () in
  let _ = (n.next <- (Some n')) in
  n'

let remove t elt =
  let prev, next = elt.prev, elt.next in
  let _ = match prev with
    | Some prev -> (prev.next <- next)
    | None -> t := next in
  let _ =  match next with
    | Some next -> (next.prev <- prev)
    | None -> () in
  let _ = (elt.prev <- None) in
  let _ = (elt.next <- None) in
  ()      (* return void *)

let iter t f =
  let rec loop node =
    match node with
      | None -> ()
      | Some el ->
        let next = el.next in
        let _ = f el in
        loop (next)
  in
  loop !t

(***************************************************)

let rec dloop e t dll =
match t with
| []->dll
| h::t -> let e = insert_after e h in dloop e t dll
;;
let dll_of_list l = 
    let dll = create() in
    match l with
    | []->dll
    | h::t-> let e = insert_first dll h in dloop e t dll
;;

let list_of_dll t = 
let l = ref [] in let _ = iter t (fun e -> l := !l@[e.content]) in !l
;;

let length t = 
let i = ref 0 in let _ = iter t (fun e -> i := !i+1) in !i
;;

let duplicate t = 
iter t (fun e -> insert_after e e.content)
;;

let reverse t = 
iter t (fun e -> remove t e; insert_first t e.content)
;;
(******************** Problem 2 ********************)

module type Serializable = sig
  type t
  type content

  val string_of_t : t -> string

  val fold : ('a -> content -> 'a) -> 'a -> t -> 'a
end

module SerializableList (C : Serializable) = struct
  type t = C.t list
  type content = C.t

  let string_of_t l =
    let rec loop acc l = match l with
      | [] -> acc
      | [x] -> acc ^ (C.string_of_t x)
      | x::xs -> loop (acc ^ (C.string_of_t x) ^ ";") xs
    in
    "[" ^ (loop "" l) ^ "]"

  let fold f accum l = List.fold_left (fun accum x -> C.fold f accum x) accum l

end

module SerializableArray (C : Serializable) = struct
  type t = C.t array
  type content = C.t

  let string_of_t l =
   let acc = "[|" in
     let rec loop acc x=
     if x+1 = Array.length l then (acc ^ (C.string_of_t l.(x)) ^ "|]")
     else
     loop (acc ^ (C.string_of_t l.(x)) ^ ";") (x+1)
     in loop acc 0

  let fold f accum l = Array.fold_left (fun accum x -> C.fold f accum x) accum l
end

module SerializableIntArray = SerializableArray (struct
  type t = int
  type content = int

  let string_of_t x = string_of_int x

  let fold f i res = f i res
end)

module SerializableIntList = SerializableList (struct
  type t = int
  type content = int

  let string_of_t x = string_of_int x

  let fold f i res = f i res
end)

module SerializableIntArrayArray = SerializableArray(SerializableIntArray)

module SerializableIntListArray = SerializableArray(SerializableIntList)

module SerializableIntArrayList = SerializableList(SerializableIntArray)
