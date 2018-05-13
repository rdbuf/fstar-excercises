module MergeSortTest

open FStar.List // map, map_flatten
open FStar.Int64 // of_string, to_string, op_Less_Equals_Hat
open FStar.String // split
open FStar.IO // input_line, print_string
open MergeSort // mergesort_by

let _ =
	let input = map of_string (split [' '] (input_line ())) in
	let output = mergesort_by (<=^) input in
	print_string (concat " " (map (fun x -> to_string x) output))
