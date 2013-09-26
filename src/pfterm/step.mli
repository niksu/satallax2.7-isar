open State
open Syntax
open Branch
open Litcount

module Step : 
  sig
    	type rule = IMP | NIMP | ALL of stp * trm * trm | NALL of stp * trm * string | MAT | DEC | CON | BE | BQ | FE | FQ | EPS of trm * trm | CUT | KNOWN of trm * string * stp list
    	type step
 
	val trm_free_variable : trm -> string list
	val make_Cut : int -> string list -> step
    	val make : int list -> (clause -> ruleinfo) -> string list -> step list
    	val get_head : step -> int list 
	val get_branches : step -> int list list 
	val get_free : step -> string list 
	val get_rule : step -> rule
	val rule_to_str : rule -> string
	val number_of_branches : step -> int
	val satisfied : step -> Branch.t -> bool
	val suitable : string list -> Branch.t -> step  -> bool
	val get_witness : step -> bool * string
	val heuristic : step -> LitCount.t -> int 
  end;;
