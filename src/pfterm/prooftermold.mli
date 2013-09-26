open State
open Search
open Syntax

type refutation =
   Conflict of trm * trm
 | Fal of trm
 | NegRefl of trm
 | Implication of trm * trm * trm * refutation * refutation  
 | Disjunction of trm * trm * trm * refutation * refutation
 | NegConjunction of trm * trm * trm * refutation * refutation  
 | NegImplication of trm * trm * trm * refutation
 | Conjunction of trm * trm * trm * refutation 
 | NegDisjunction of trm * trm * trm * refutation 
 | All of trm * trm * refutation * stp * trm *trm
 | NegAll of trm * trm * refutation * stp * trm * string
 | Exist of trm * trm * refutation * stp * trm * string
 | NegExist of trm * trm * refutation * stp * trm *trm
 | Mating of trm * trm * trm list * refutation list
 | Decomposition of trm * trm list * refutation list 
 | Confront of trm * trm * trm * trm * trm * trm * refutation * refutation 
 | NegEqualProp of trm * trm * trm * refutation * refutation
 | EqualProp of trm * trm * trm * refutation * refutation
 | NegAequivalenz of trm * trm * trm * refutation * refutation
 | Aequivalenz of trm * trm * trm * refutation * refutation
 | NegEqualFunc of trm * trm * refutation
 | EqualFunc of trm * trm * refutation
 | ChoiceR of trm * trm * trm * trm * refutation * refutation (* TODO use choiceop_axiom later *)
 | Cut of trm * refutation * refutation     
 | DoubleNegation of trm * trm * refutation  
 | Rewrite of trm * trm * trm * refutation  (* TODO: handle DB indices + Coq tactic Change*)
 | Delta of trm * trm * string * refutation
 | NYI of trm * trm * refutation   
 | Timeout 

module IntSet : Set.S
module Branch :
    sig
      exception Closed of refutation * IntSet.t * int * int * int
      type history = Level of int | Add of int
      type t = (IntSet.t ref) * (history Stack.t) * (int ref)
      val make : unit -> t
      val add : t -> int -> unit
      val mem : int -> t -> bool
      val next_level : t -> int
      val reset : t -> int -> t
    end
module Step :
    sig
      type rule = IMP | NIMP | ALL of stp * trm * trm | NALL of stp * trm * string | MAT | DEC | CON | BE | BQ | FE | FQ | EPS of trm * trm | CUT
      type step = ((int list) * (int list list) * (string list) * rule) ref
      val get_head : step -> int list
      val get_branches : step -> int list list
      val get_free : step -> string list
      val get_rule : step -> rule
    end

val initialise_literal_array : int list list
  -> int array * int array

val preprocess_clauses : int list list
  -> (int list -> State.ruleinfo)
  -> Step.step list * int list

val apply_clause_check : string list
  -> Branch.t
  -> Step.step
  -> bool

val exists_clause_check : Step.step
  -> bool * string

val remove_satisfied_clauses : Branch.t
  -> Step.step list
  -> Step.step list

val heuristic : Step.step
  -> int array * int array
  -> int

val get_next_clause : string list -> Branch.t
  -> Step.step list
  -> Step.step

val apply_rule1 : Branch.t
  -> Step.step list
  -> int list list
  -> int list
  -> int
  -> refutation list * IntSet.t * int * int * int

val apply_rule : Branch.t
  -> Step.step list ref
  -> int list list
  -> int list
  -> refutation list * IntSet.t * int * int * int

val apply_Imp : Branch.t
  -> int -> int -> int
  -> Step.step list ref
  -> refutation * IntSet.t * int * int * int

val and_search : Branch.t
  -> Step.step
  -> Step.step list ref
  -> refutation * IntSet.t * int * int * int

val or_search1 : Branch.t
  -> Step.step list
  -> refutation * IntSet.t * int * int * int

val or_search : int list -> Branch.t
  -> Step.step list ref
  -> refutation * IntSet.t * int * int * int

val is_an_eqn : trm -> int -> trm * trm * trm * stp
val leibeq_to_primeq2 : trm -> int -> trm * trm * trm * stp

val leibeq_to_primeq : int list -> Branch.t
  -> Step.step list ref
  -> refutation * IntSet.t * int * int * int

val process_refut1 : Branch.t -> State.refut -> refutation * IntSet.t * int * int * int
val process_refut : int list -> Branch.t -> State.refut -> refutation * IntSet.t * int * int * int

val print_proofterm_old : out_channel -> refut -> unit
