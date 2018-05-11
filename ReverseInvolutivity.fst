module ReverseInvolutivity

val append : list 'a -> list 'a -> list 'a
let rec append l1 l2 = match l1 with
	| [] -> l2
	| hd1 :: tl1 -> hd1 :: (append tl1 l2)

let snoc l x = append l [x]

val reverse : list 'a -> list 'a
let rec reverse l = match l with
	| [] -> []
	| hd :: tl -> snoc (reverse tl) hd

val reverse_snoc_is_cons : l:list 'a -> x:'a -> Lemma (x :: reverse l == reverse (snoc l x))
let rec reverse_snoc_is_cons l x = match l with
	| [] -> ()
	| hd :: tl -> reverse_snoc_is_cons tl x

val reverse_involutivity : l:list 'a -> Lemma (reverse (reverse l) == l)
let rec reverse_involutivity l = match l with
	| [] -> ()
	| hd :: tl ->
		reverse_involutivity tl;
		reverse_snoc_is_cons (reverse tl) hd
