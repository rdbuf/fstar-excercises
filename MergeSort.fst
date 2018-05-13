module MergeSort

type nat = n:int{n>=0}

val length : l:list 'a -> nat
let rec length l = match l with
	| [] -> 0
	| hd :: tl -> 1 + length tl

val count : #a:eqtype -> x:a -> l:list a -> res:nat{res <= length l}
let rec count #a x l = match l with
	| [] -> 0
	| hd :: tl -> (if hd = x then 1 else 0) + count x tl

val mem : #a:eqtype -> a -> list a -> bool
let rec mem #a x l = match l with
	| [] -> false
	| hd :: tl -> x = hd || mem x tl

val pos : #a:eqtype -> x:a -> l:list a{mem x l} -> res:nat{res < length l}
let rec pos #a x l = 
	let (hd :: tl) = l in
	if hd = x then 0 else 1 + pos x tl

val append : l1:list 'a -> l2:list 'a -> res:list 'a{
	length res = length l1 + length l2
	// /\ ('a == eqtype ==> (forall x y. mem x l1 /\ mem y l2 ==> count x l1 = count x res /\ count y l2 = count y res)) // unfortunately, this doesn't typecheck
}
let rec append l1 l2 = match l1 with
	| [] -> l2
	| hd1 :: tl1 -> hd1 :: append tl1 l2

(*
val append_preserves_elements : #a:eqtype -> dec:int{dec == 0 /\ dec == 1} -> l1:list a -> l2:list a
	-> Lemma (forall x. mem x l1 \/ mem x l2 ==> count x l1 + count x l2 == count x (append l1 l2))
let rec append_preserves_elements #a _ l1 l2 = match (l1, l2) with
	| ([], _) -> ()
	| (_, []) -> append_preserves_elements 0 [] l1
	| (hd1 :: tl1, _) -> append_preserves_elements 1 tl1 l2
*)

val splitAt : l:list 'a -> n:nat{n <= length l} -> res:(list 'a * list 'a){let (part1, part2) = res in append part1 part2 == l /\ length part1 == n}
let rec splitAt l n = match l with
	| [] -> ([], [])
	| hd :: tl -> if n = 0 then ([], l) else let (part1, part2) = splitAt tl (n - 1) in (hd :: part1, part2)

type total_order (#a:eqtype) (ord:(a -> a -> bool)) =
	(forall a. ord a a) // reflexivity
	/\ (forall a1 a2. ord a1 a2 /\ ord a2 a1 ==> a1 = a2) // anti-symmetricity
	/\ (forall a1 a2 a3. ord a1 a2 /\ ord a2 a3 ==> ord a1 a3) // transitivity
	/\ (forall a1 a2. ord a1 a2 \/ ord a2 a1) // totality

type ordered (#a:eqtype) (ord:(a -> a -> bool){total_order ord}) = l:list a{
	forall x y. mem x l /\ mem y l /\ pos x l <= pos y l ==> ord x y
}

type permutation (#a:eqtype) (l1:list a) = l2:list a{
	length l1 == length l2
	/\ (forall x. mem x l1 ==> count x l1 == count x l2)
}

val merge_by : #a:eqtype -> ord:(a -> a -> bool){total_order ord} -> l1:list a{l1:ordered ord} -> l2:list a{l2:ordered ord}
	-> Tot (res:list a{res:ordered ord /\ res:permutation (append l1 l2)}) (decreases (length l1 + length l2))
let rec merge_by #a ord l1 l2 = match (l1, l2) with
	| ([], _) -> l2
	| (_, []) -> l1
	| (hd1 :: tl1, hd2 :: tl2) ->
		if ord hd1 hd2 then hd1 :: merge_by ord tl1 l2
		else hd2 :: merge_by ord l1 tl2

val mergesort_by : #a:eqtype -> ord:(a -> a -> bool){total_order ord} -> in_:list a
	-> Tot (out:list a{out:ordered ord /\ out:permutation in_}) (decreases (length in_))
let rec mergesort_by #a ord l =
	if length l <= 1 then l
	else let (part1, part2) = splitAt l (length l / 2) in
	merge_by ord (mergesort_by ord part1) (mergesort_by ord part2)

let result = mergesort_by (<=) [4;3;2]
let _  = assert (result == [2;3;4])
