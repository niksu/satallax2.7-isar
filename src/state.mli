(* File: state.mli *)
(* Author: Chad E Brown *)
(* Created: October 2010 *)

open String
open Syntax
open Config

exception Redeclaration of string
exception FileNotFound of string
exception GenericError of string
exception CoqProofTooBig of int

val select_axioms_list : int list ref
val select_axioms : unit -> unit
val print_num_axioms : unit -> unit

val useeprover : bool ref
val eeqoequiv : bool ref
val eproverperiod : int ref
val eprovertimeout : int ref
val foffiles : bool ref

val slaveargs : string list ref
val mode : string list ref
val timeout : float option ref
val verbosity : int ref
val nontheorem : bool ref
val coq : bool ref
val coq2 : bool ref
val problemfile : string ref
val coqlocalfile : bool ref
val coqglobalfile : bool ref
val coqinchannel : in_channel ref
val coqoutchannel : out_channel ref
val coqinticks : ((out_channel -> unit) option * int) list ref
val coqoutfn1 : (out_channel -> unit) ref
val coqctx : prectx ref
val coqglobalsectionstack : (string * (out_channel -> unit) * prectx) list ref
val updatecoqglobalsectionstack : prectx -> (string * (out_channel -> unit) * prectx) list -> (prectx -> (out_channel -> unit) -> (out_channel -> unit)) -> (string * (out_channel -> unit) * prectx) list

val conjecturename : string ref
val conjecture : (pretrm * trm * trm) option ref
type proofkind = TSTP | CoqScript | CoqSPfTerm | HOCore | Model | ModelTrue | IsarScript
val mkproofterm : proofkind option ref
val mkprooftermp : unit -> bool
val slave1 : bool ref
val slave : bool ref
val coqsig_base : string list ref
val coqsig_const : (string * stp) list ref
val coqsig_def : (string * pretrm) list ref
val coqsig_hyp : (string * pretrm) list ref
val coqsig_def_trm : (string * trm) list ref
val coqsig_hyp_trm : (string * trm) list ref
val name_base : (string,unit) Hashtbl.t
val name_base_list : string list ref
val name_tp : (string,stp) Hashtbl.t
val name_trm : (string,(trm * stp) * bool ref) Hashtbl.t
val name_trm_list : (string * trm * stp) list ref
val name_def : (string,trm) Hashtbl.t
val name_def_prenorm : (string,trm) Hashtbl.t
val name_hyp : (string,trm) Hashtbl.t
val coqknown : string * string -> string

exception Timeout
val set_timer : float -> unit
val mult_timeout : float -> unit

val required : string ref
val require : string -> unit

val get_fresh_name : stp -> string * trm

val max_atom : unit -> int

val assignedp : trm -> bool

val get_literal : trm -> int
val literal_to_trm : int -> trm

val initial_branch : trm list ref
val initial_branch_prenorm : trm list ref

type clause = int list

val clauses : clause list ref

type searchoption =
 (*** ProcessProp1(m) For rules requiring one formula in the head (most rules) ***)
    ProcessProp1 of trm
 (*** Mating(plit,nlit,pl,nl) where pl,nl and plit = lit (h pl) and nlit = lit ~(h nl) ***)
  | Mating of int * int * trm list * trm list
 (*** Confront(nplit,nnlit,a,u,v,l,r) where u,v,l,r:a and nplit = lit (u = v) and nnlit is lit (l != r) ***)
  | Confront of int * int * stp * trm * trm * trm * trm
 (*** DefaultElt(a) - create a default element of type a ***)
  | DefaultElt of string
 (*** DefaultEltInst(a) - create a default element of type a ***)
  | DefaultEltInst of string
 (*** NewInst(a,m) - put m:a in the set of instantiations ***)
  | NewInst of stp * trm
 (*** EnumIterDeep(d,a) - Enumerate all terms (using the current constants) of depth d ***)
  | EnumIterDeep of int * stp
 (*** EnumTp(d,ar,a) - work on enumerating types that can be used to choose a polymorphic head (Eq, Forall, Choice) ***)
  | EnumTp of int * stp * stp
 (*** EnumAp(d,Gamma,sigmal,h,c) - ***)
  | EnumAp of (int * stp list * stp list * trm * (trm -> unit))
 (*** Enum(d,Gamma,sigma,c) ***)
  | Enum of (int * stp list * stp * (trm -> unit))
 (*** Filter - use Minisat to filter usable sets ***)
  | Filter of int

type ruleinfo =
 (*** NegPropRule(m) For rules requiring one negative formula in the head, except negated forall ***)
    NegPropRule of trm
 (*** PosPropRule(m) For rules requiring one positive formula in the head, except forall ***)
  | PosPropRule of trm
 (*** InstRule(a,m,n) For instantiating a Ap(Forall(a),m) with n:a ***)
  | InstRule of stp * trm * trm
 (*** FreshRule(a,m,x) For producing a witness x for Ap(Neg,Ap(Forall(a),m)) ***)
  | FreshRule of stp * trm * string
 (*** MatingRule(plit,nlit) For mating rule, only save the literals here ***)
  | MatingRule of int * int
 (*** ConfrontationRule(plit,nlit) For confrontation rule, only save the literals here ***)
  | ConfrontationRule of int * int
 (*** ChoiceRule(eps,pred) ***)
  | ChoiceRule of trm * trm
 (*** Known(lit,coqname,stp list) ***)
  | Known of int * string * stp list

val searchoption_str : searchoption -> string
val ruleinfo_str : ruleinfo -> string

type refut =
    NegImpR of trm * trm * refut
  | ImpR of trm * trm * refut * refut
  | FalseR
  | NegReflR
  | NegAllR of stp * trm * string * refut
  | EqFR of stp * stp * trm * trm * refut
  | NegEqFR of stp * stp * trm * trm * refut
  | EqOR of trm * trm * refut * refut
  | NegEqOR of trm * trm * refut * refut
  | SearchR of clause list * (clause -> ruleinfo)
  | AssumptionConflictR

val print_refut : refut -> unit (*** Only for debugging. ***)

val processed : (trm,unit) Hashtbl.t
val clause_ruleinfo : (clause,ruleinfo) Hashtbl.t ref

exception DuplicateClause

val insert_assumption_clause : clause -> unit
val insert_search_clause : clause -> ruleinfo option -> unit

(*** Interface to priority queue of search options ***)
val insertWithPriority : int -> searchoption -> unit
val getNext : unit -> searchoption
val peekAtNext : unit -> int * searchoption

(*** Positive and negative atoms, indexed by the name at the head ***)
val patoms : (string,int * (trm list)) Hashtbl.t
val natoms : (string,int * (trm list)) Hashtbl.t

(*** Positive and negative atoms with Choice(a) at the head, indexed by the type a ***)
val pchoiceatoms : (stp,int * (trm list)) Hashtbl.t
val nchoiceatoms : (stp,int * (trm list)) Hashtbl.t

(*** Positive and negative equations, indexed by the base type at the head ***)
val peqns : (string,int * trm * trm) Hashtbl.t
val neqns : (string,int * trm * trm) Hashtbl.t

val univpreds : (stp,(int * trm)) Hashtbl.t

val filtered : (int,unit) Hashtbl.t

val part_of_conjecture : (trm,unit) Hashtbl.t

val set_default_elt : string -> trm -> unit
val default_elt : string -> trm
val default_elt_p : string -> bool

val get_instantiations : stp -> trm list
val known_instantiation : stp -> trm -> bool
val add_instantiation : stp -> trm -> unit

(*** Hash table associating names of epsilon operators with (a,m) where a is the type and m is the formula giving the choice axiom ***)
val choiceopnames : (string,(stp * trm)) Hashtbl.t

(*** Check if a formula says that a name is a choice operator at some type ***)
val choiceop_axiom : trm -> (string * stp) option

(*** Declare a name to be a choice operator at some type ***)
val declare_choiceop : string -> stp -> trm -> unit

(*** If trm is a choice operator at some type, return the type, otherwise None ***)
val choiceop : trm -> stp option

type namecategory =
    ChoiceOp of int * int * stp list * trm list (*** (i,n,sigmal,tl) where length of sigmal and tl are n, 0 <= i < n, Name has type (sigmal -> o) -> sigmal[i], and for each j:{0,...,n-1} tl[j] is the jth component of the n-ary choice operator (in particular, tl[i] is this one) ***)
   | DescrOp of int * int * stp list * trm list (*** (i,n,sigmal,tl) where length of sigmal and tl are n, 0 <= i < n, Name has type (sigmal -> o) -> sigmal[i], and for each j:{0,...,n-1} tl[j] is the jth component of the n-ary description operator (in particular, tl[i] is this one) ***)
   | IfThenElse of int * int * stp list (*** (i,n,sigmal) where length of sigmal is n, 0 <= i < n, Name has type o -> sigmal -> sigmal -> sigmal[i] ***)
   | ReflexiveBinary
   | IrreflexiveBinary
   | SymmetricBinary
   | ReflexiveSymmetricBinary
   | IrreflexiveSymmetricBinary

val constrainedName : (string,namecategory) Hashtbl.t

val decomposable : string -> bool

exception Unsatisfiable of refut option
exception Satisfiable

val get_timeout_default : float -> float

val st_include_fun : (string -> unit) ref
val st_find_read_thf_fun : (string -> string -> unit) ref

val coq_init : unit -> unit
val print_coqsig : out_channel -> unit

val declare_typed_constant : string -> string -> pretrm -> unit
    
val declare_definition : string -> string -> pretrm -> unit

val declare_thf_logic_formula : string -> string -> pretrm -> unit

(*** Code for enumeration of types and terms ***)
val enum_started : bool ref
val enum_of_started : stp -> bool
val enum_of_start : stp -> unit
val new_type_continuation_rtp : stp -> (stp -> int -> unit) -> unit
val new_type_continuation : (stp -> int -> unit) -> unit
val iter_type_continuations_rtp : stp -> stp -> int -> unit
val iter_type_continuations : stp -> int -> unit
val new_term_continuation_rtp : stp -> (stp list * trm * int -> unit) -> unit
val iter_term_continuations_rtp : stp -> stp list -> trm -> int -> unit
val new_usable_type_rtp : stp -> stp -> int -> unit
val usable_types_rtp : stp -> (stp * int) list
val usable_types : unit -> (stp * stp * int) list
val new_usable_head_rtp : stp -> stp list -> trm -> int -> unit
val usable_heads_rtp : stp -> (stp list * trm * int) list

(*** Search Init ***)
val search_init : unit -> unit

(*** Reset Search ***)
val reset_search : unit -> unit

val print_model : bool -> unit

val onlynegnorm : trm -> trm
val coqnorm : trm -> trm
val normalize : trm -> trm
