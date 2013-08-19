open State
open Syntax
open Refutation
open Flag

module OrderedInt =
   struct
     type t = int
     let compare = Pervasives.compare  
   end


module IntSet = Set.Make(OrderedInt)

(** The module Dependency is used to track dependencies of refutations and to enable backjumping**)
module Dependency = struct
	
	(** Dependencies are sets of literals (integers) **)
	type t = IntSet.t
	
	(** Input: a List of literals 
		Output: a dependency containing the literals**)
	let make ls = List.fold_left (fun d l -> IntSet.add l d) IntSet.empty ls 
	
	(** Input: A list of principal formulae h, a list of dependencies ds and a list of alternatives alts
		Invariant: 	h entails alts
					ds and alts have the same length and correspond to each other
		Output: a new dependency: 
				each dependency has the side formulae of its corresponding alternative removed,
				then the union is taken and the principal formulae are added	**)
	let diffunion h ds alts = List.fold_left2 (fun d d2 a -> IntSet.union d (List.fold_left (fun d3 s -> IntSet.remove s d3) d2 a)) (make h) ds alts
	
	(** Input: dependency d and a list of literals ls
		Output: a list of booleans **)
	let check d ls = List.map (fun l -> IntSet.mem l d) ls

	let mem l d = IntSet.mem l d
	let elements d = IntSet.elements d
	let empty = IntSet.empty
	let is_empty d = IntSet.is_empty d
	let filter d ls = List.filter (fun l -> IntSet.mem l d) ls
end

(** The module Branch manages a single branch in a tableau refutation**)
module Branch =
	struct
	exception Closed of refutation * Dependency.t 
	
	(** A history object is either a mark for a ceratin level n or a literal added to the branch **)
	type history = Level of int | Add of int
	
	(** A branch is a set of literals, a history stack and a reference to the current level of the branch**)
	type t = (IntSet.t ref) * (history Stack.t) * (int ref)
	
	(** creates a new empty branch with level 0**)
	let make () = (ref IntSet.empty ,Stack.create (),ref 0) 
	
	(** Input: A branch and a literal l
		Invariant: the branch is open
		Output: if adding l closes the branch Closed with a corresponding refuation and dependency is thrown
				if l is on the branch nothing happens
				otherwise l is added to the set and Add(l) is pushed on the stack**)
	let add (b,h,_) l = 
		let t = literal_to_trm l in  if debug_search then Printf.printf  "adding (%d) to the branch\n" l ;
		if t = False then (if debug_search then Printf.printf  "found False\n";raise (Closed (Fal(t),Dependency.make [l])))
                   else if begin  
                     		match t with 
                     		| Ap(Ap(Imp,Ap(Ap(Eq(_),s),t)),False) ->   s =  t 
                       		| _ -> false end 
                   		then (if debug_search then Printf.printf  "found NRefl\n";raise (Closed (NegRefl(t),Dependency.make[l])))
                   else 
		if IntSet.mem (-l) !b 
			then (if debug_search then Printf.printf  "found Conflict\n";
			raise (Closed (Conflict(literal_to_trm(abs l),literal_to_trm(-(abs l))),Dependency.make [l;-l]) ) )
		else if IntSet.mem l !b then ()
		else Stack.push (Add(l)) h; b:= IntSet.add l !b
		
	(** checks if the given literal l is True or a trivial equation**)	
	let is_taut l = let t = literal_to_trm (-l) in 
		if t = False then true
			else      match t with 
                     		| Ap(Ap(Imp,Ap(Ap(Eq(_),s),t)),False) ->   s =  t 
                       		| _ -> false 
							
	let mem  l (b,_,_) = IntSet.mem l !b
	
	(** increases the level of the branch by one and returns the new level**)
	let next_level (_,h,n) =  incr n ;Stack.push (Level(!n)) h; !n
	
	(** resets the branch to its state when Level(n) was pushed on the stack**)
	let reset (b,h,n') n = 
		let rec reset () = match Stack.pop h with
					| Level(m) -> if m = n then (n':=n; Stack.push (Level(n)) h;(b,h,n')) else reset ()
					| Add(l) ->  b:=IntSet.remove l !b; reset ()
		in reset ()
		
	let elements (b,_,_) = IntSet.elements !b
	end 


(** The module Dgraph is a Dependency graph used for semantic branching of Mating and Decomposition**)
module Dgraph = struct

(** The first list are the nodes of the graph,
	The (Literal* (Literal list)) List encodes the edges, 
	e.g., a pair (l1,[l2;l3]) in the list means that (l1,l2) and (l1,l3) are edges in the graph.
	An edge (l1,l2) means that the refutation of the alternative {-l1} depends on l2 being on the branch.**)
type t = (int list) * ((int * (int list)) list)

(** Invariant: all literals are positive **)

(** Creates a new graph. 
	double is a list of side formulae that occured in more than one alternative.
	This ensures that we later cut on them and save redundant subrefutations **)
let make double sfs = (sfs,[(0,double)])

(** Adds new edges to the graph from node l to the nodes in dfl **)
let update (ls,dg) l dfl = (ls,(l,dfl)::dg)

(** Invariant: |sfs| < |ls|
	reduces the size of the graph by removing nodes.
	Only edges (l,l') are kept where forall l'', (l,l'') -> l'' in sfs **)
let reset (ls,dg) sfs = 
	let dg = List.filter (fun (l,dfl) -> List.mem l sfs && List.for_all (fun l' -> List.mem l' sfs) dfl && l<>0) dg in
	let (ll,_) = List.split dg in
	(ll,(sfs,dg))
	
(** returns all nodes l' where (l',l) is not in the graph**)	
let get_not_smaller (ls,dg) l = 
	let smaller = List.fold_left (fun small (l',dfl) -> if List.mem l dfl then l'::small else small ) [] dg in
	List.filter (fun l' -> not (List.mem l smaller) && l' <> l) ls

(** returns all nodes l where forall l' in ls, (l',l) is not in the graph 
	and removes all edges starting from them**)	
let minimals (ls,dg) = 
	let mins = List.filter (fun l -> List.for_all (fun (_,dfl) -> not (List.mem l dfl)) dg) ls in
	(if debug_semantic then Printf.printf  "Dgraph: mins = [%s]\n" (List.fold_left (fun a sf -> a ^ "," ^string_of_int sf ) "" mins ));
	let dg = List.filter (fun (l,_) -> not (List.mem l mins) && l <> 0) dg in
	let mins = List.filter (fun l -> l <> 0) mins in
	(mins,(ls,dg))

(** Does the same as minimals, but repeats until the graph is empty. **)	
let minlist (_,dg) = 
	let rec min1 minl dg = 
		match dg with
		| [] -> List.rev minl
		| _ -> 
			let (m,_) = try List.find (fun (l,_) -> not (List.exists (fun (_,dfl) -> List.mem l dfl ) dg) ) dg with Not_found -> failwith "no min in Dgraph" in
			let dg = List.remove_assoc m dg in
			min1 (m::minl) dg
	in 
	min1 [] dg
end
