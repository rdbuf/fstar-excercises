module Helpme

val foldl : f:('a -> 'b -> 'b) -> list 'a -> 'b -> 'b
let rec foldl f l acc = match l with
	| [] -> acc
	| hd::tl -> foldl f tl (f hd acc)

val rev_acc : list 'a -> list 'a -> list 'a
let rec rev_acc l acc = match l with
    | [] -> acc
	| hd::tl -> rev_acc tl (Cons hd acc)

// fails
let _ = assert (forall (a:Type) (l:list a). foldl Cons l [] == rev_acc l [])