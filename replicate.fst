module Replicate

open FStar.List.Tot

val replicate : #a:Type -> n:nat -> x:a -> out:list a{
	length out == n
	/\ (forall (y:a{memP y out}). y == x)
}
let rec replicate #a n x =
	if n = 0 then []
	else x :: replicate (n - 1) x // fails