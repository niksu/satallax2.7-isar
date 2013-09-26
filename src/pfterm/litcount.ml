open Flag

(** The module LitCount is a pair of arrays (p,n), 
	where for each literal l  
	p[l]= No. of occurences of l in the set of steps
	n[l]= No. of occurences of -l in the set of steps
	**)
module LitCount =
	struct
	type t = (int array) * (int array)
	let make n = (Array.make n 0,Array.make n 0)
	let copy (p,n) = (Array.copy p ,Array.copy n)
	let get (p,n) l =  if l > 0 then Array.get p l else Array.get n (-l)
	let put (p,n) l x = if l > 0 then Array.set p l x else Array.set n (-l) x
	let incr lc l = put lc l (get lc l + 1)
	let decr lc l = put lc l (if get lc l - 1 < 0 && debug_heuristic then Printf.printf "Literal %d removed too often" l;get lc l - 1  )
	let print (p,n) = Array.iteri (fun pos value ->if value+ Array.get p pos > 2 then Printf.printf "(%d:%d)" pos (value+ Array.get p pos) ) n
	let count (p,n) =  let c = ref 0 in (Array.iteri (fun pos value ->if value+ Array.get p pos > 0 then Pervasives.incr c ) n; !c )
	let get_lits (p,n) =  let lits = ref [] in (Array.iteri (fun pos value -> lits:= (pos,(value+ Array.get p pos))::!lits ) n; !lits)
	end;;
