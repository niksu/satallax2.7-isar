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
 | Trans of trm * trm * trm * refutation
 | NegEqualProp of trm * trm * trm * refutation * refutation
 | EqualProp of trm * trm * trm * refutation * refutation
 | NegAequivalenz of trm * trm * trm * refutation * refutation
 | Aequivalenz of trm * trm * trm * refutation * refutation
 | NegEqualFunc of trm * trm * refutation
 | EqualFunc of trm * trm * refutation
 | ChoiceR of trm * trm * trm * trm * refutation * refutation 
 | Cut of trm * refutation * refutation     
 | DoubleNegation of trm * trm * refutation  
 | Rewrite of trm * trm * trm * refutation  
 | Delta of trm * trm * string * refutation
 | KnownResult of trm * string * stp list * refutation (* Chad: Aug 2011 *)
 | NYI of trm * trm * refutation   
 | Timeout 

val ref_str : refutation -> string

val is_an_eqn_p : trm -> int -> trm * trm * trm * stp
