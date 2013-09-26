open Branch

(** Input: List of assumptions and refut 
	Output: a refutation, dependency pair for the assumptions, search time and wether timeout was reached. **)
val search_refutation : int list ->  State.refut -> Refutation.refutation * Dependency.t * int * bool
