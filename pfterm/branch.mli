open State

module Dependency : sig
 	type t 
	val make : int list -> t 
	val diffunion : int list -> t list -> int list list -> t
	val check : t -> int list -> bool list
	val mem : int -> t -> bool
	val elements : t -> int list
	val empty : t
	val is_empty : t -> bool
  end;;

module Branch : sig
	exception Closed of Refutation.refutation * Dependency.t 
	type t 
	val make : unit -> t 
	val add : t -> int -> unit 
	val is_taut : int -> bool 
	val mem  : int -> t -> bool
	val next_level : t -> int
	val reset : t -> int ->  t 
	val elements : t -> int list
  end;;

module Dgraph : sig
	type t 
	val make : int list -> int list -> t
	val update : t -> int -> int list -> t
	val reset : t -> int list -> int list * t	
	val get_not_smaller : t -> int -> int list
	val minimals : t ->  int list * t
	val minlist : t -> int list 
end;;
