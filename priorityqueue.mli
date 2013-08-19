(*** File: priorityqueue.mli ***)
(*** Author: Chad E Brown, Oct 2010 ***)
(*** Priority Queue Interface ***)

(*** Multiple Implementations, Jan 2011 ***)

module PriorityQueue0 : functor (T : sig type t end) ->
  sig
    type a = T.t
    val reset : unit -> unit
    val insertWithPriority : int -> a -> unit
    val getNext : unit -> a
    val peekAtNext : unit -> int * a

	(*** Just for debugging ***)
    val debug_print : (a -> string) -> unit
  end;;

module PriorityQueue1 : functor (T : sig type t end) ->
  sig
    type a = T.t
    val reset : unit -> unit
    val insertWithPriority : int -> a -> unit
    val getNext : unit -> a
    val peekAtNext : unit -> int * a

	(*** Just for debugging ***)
    val debug_print : (a -> string) -> unit
  end;;

module PriorityQueue2 : functor (T : sig type t end) ->
  sig
    type a = T.t
    val reset : unit -> unit
    val insertWithPriority : int -> a -> unit
    val getNext : unit -> a
    val peekAtNext : unit -> int * a

	(*** Just for debugging ***)
    val debug_print : (a -> string) -> unit
  end;;

module PriorityQueue3 : functor (T : sig type t end) ->
  sig
    type a = T.t
    val reset : unit -> unit
    val insertWithPriority : int -> a -> unit
    val getNext : unit -> a
    val peekAtNext : unit -> int * a

	(*** Just for debugging ***)
    val debug_print : (a -> string) -> unit
  end;;

module PriorityQueue4 : functor (T : sig type t end) ->
  sig
    type a = T.t
    val reset : unit -> unit
    val insertWithPriority : int -> a -> unit
    val getNext : unit -> a
    val peekAtNext : unit -> int * a

	(*** Just for debugging ***)
    val debug_print : (a -> string) -> unit
  end;;

module PriorityQueue5 : functor (T : sig type t end) ->
  sig
    type a = T.t
    val reset : unit -> unit
    val insertWithPriority : int -> a -> unit
    val getNext : unit -> a
    val peekAtNext : unit -> int * a

	(*** Just for debugging ***)
    val debug_print : (a -> string) -> unit
  end;;

module PriorityQueue6 : functor (T : sig type t end) ->
  sig
    type a = T.t
    val reset : unit -> unit
    val insertWithPriority : int -> a -> unit
    val getNext : unit -> a
    val peekAtNext : unit -> int * a

	(*** Just for debugging ***)
    val debug_print : (a -> string) -> unit
  end;;

module PriorityQueue7 : functor (T : sig type t end) ->
  sig
    type a = T.t
    val reset : unit -> unit
    val insertWithPriority : int -> a -> unit
    val getNext : unit -> a
    val peekAtNext : unit -> int * a

	(*** Just for debugging ***)
    val debug_print : (a -> string) -> unit
  end;;

module PriorityQueue8 : functor (T : sig type t end) ->
  sig
    type a = T.t
    val reset : unit -> unit
    val insertWithPriority : int -> a -> unit
    val getNext : unit -> a
    val peekAtNext : unit -> int * a

	(*** Just for debugging ***)
    val debug_print : (a -> string) -> unit
  end;;
