module LitCount : 
  sig
	type t 
	val make : int -> t 
	val copy : t -> t 
	val get : t -> int -> int 
	val put : t -> int -> int -> unit
	val incr : t -> int -> unit
	val decr : t -> int -> unit 
	val print : t ->  unit 
	val count : t -> int
	val get_lits : t -> (int*int) list 
  end;;
