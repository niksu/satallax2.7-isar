(* File: syntax.mli *)
(* Author: Chad E Brown *)
(* Created: March 2008/September 2008/September 2010 *)

open String

exception ParsingError of int * int * int * int * string
exception GenericSyntaxError of string
exception DeclareInd

type pretrm =
    PName of string
  | PType | PPropTp | PIndTp | PIntTp | PRealTp | PTrue | PFalse | PIff | PNIff | PImplies | PRevImplies | POr | PNOr | PAnd | PNAnd | PEq | PNEq | PNeg | PForall | PExists
  | PInt of int
  | PReal of float
  | PAp of pretrm * pretrm
  | PULam of string list * pretrm
  | PLam of ((string * pretrm) list) * pretrm
  | PAll of ((string * pretrm) list) * pretrm
  | PEx of ((string * pretrm) list) * pretrm
  | PExU of string * pretrm * pretrm
  | PChoice of (string * pretrm) * pretrm
  | PAr of pretrm * pretrm
  | POf of pretrm * pretrm
  | PDef of pretrm * pretrm
  | PLet of string * pretrm * pretrm
  | PTLet of string * pretrm * pretrm * pretrm

type prectx = (string option * pretrm option * pretrm option) list

val prectx_lam : prectx -> pretrm -> pretrm

val prectx_all : prectx -> pretrm -> pretrm

val prectx_ar : prectx -> pretrm -> pretrm

val pretrm_str:pretrm -> string

type input =
    DeclareTHF of string * string * pretrm
  | Include of string

type stp = Base of string | Prop | Ar of (stp * stp)

exception ExpectedTypeError of pretrm * stp * stp

type ctx = (string * stp) list

type trm =
    Name of string * stp
  | False | Imp | Forall of stp | Eq of stp | Choice of stp
  | True | Neg | Or | And | Iff | Exists of stp (*** These are normalized away. ***)
  | DB of int * stp
  | Lam of stp * trm
  | Ap of trm * trm

val imp:trm -> trm -> trm
val preneg:trm -> trm
val neg:trm -> trm
val normneg:trm -> trm
val disj:trm -> trm -> trm
val conj:trm -> trm -> trm
val iff:trm -> trm -> trm
val eq:stp -> trm -> trm -> trm
val ueq:trm -> trm -> trm
val forall:stp -> trm -> trm
val exists:stp -> trm -> trm
val choice:stp -> trm -> trm

val stp_str:stp -> string
val trm_str:trm -> string

val tpof:trm -> stp

(*** This builds an application after checking the types agree. ***)
val ap:trm * trm -> trm

val coqify_name : string -> (string,string) Hashtbl.t -> (string,unit) Hashtbl.t -> string
val print_stp_coq:out_channel -> stp -> (string,string) Hashtbl.t -> bool -> unit
val print_stp_isar:out_channel -> stp -> (* (string,string) Hashtbl.t -> *) bool -> unit
val print_pretrm_coq:out_channel -> pretrm -> (string,string) Hashtbl.t -> (string,unit) Hashtbl.t -> int -> int -> unit
val print_pretrm_isar:out_channel -> pretrm -> (string,string) Hashtbl.t -> (string,unit) Hashtbl.t -> int -> int -> unit
val print_stp_coq2:out_channel -> stp -> bool -> unit
val print_pretrm_coq2:out_channel -> pretrm -> int -> int -> unit

val shift:trm -> int -> int -> trm
val subst:trm -> int -> trm -> trm
val simulsubst:trm -> trm list -> trm
val namesubst:trm -> string -> trm -> trm
val gen_lam_body:stp -> trm -> trm
val termNotFreeIn:trm -> int -> bool
val termNotFreeInL:trm -> int list -> bool
val termNoDBs:trm -> bool
val norm1:(string,trm) Hashtbl.t -> trm -> trm * bool
val norm:(string,trm) Hashtbl.t -> trm -> trm
val betanorm:(string,trm) Hashtbl.t -> trm -> trm
val onlybetanorm1:trm -> trm * bool
val onlybetanorm:trm -> trm
val logicnorm:trm -> trm

val basetypestobool : bool ref

val to_stp:pretrm -> stp
val to_trm:(string,(trm * stp) * bool ref) Hashtbl.t -> ctx -> pretrm -> stp option -> trm * stp

val neg_p:trm -> bool
val neg_body:trm -> trm option
val eq_body:trm -> (stp * trm * trm) option

val bounded_head_spine: int -> trm -> trm * trm list
val head_spine: trm -> trm * trm list

val rtp : stp -> stp
val argtps_rtp : stp -> stp list * stp

(*** First Order Formulas - Dec 2012 ***)
type fotrm =
    FOVar of string
  | FOFun of string * fotrm list
type foform = (*** assuming a single sort ***)
    FOEq of fotrm * fotrm
  | FOPred of string * fotrm list
  | FOImp of foform * foform
  | FOEqu of foform * foform
  | FOAll of string * foform
  | FOFal

exception NotFO

val trm_to_foform_stp : trm -> bool -> foform * stp option
val trm_to_isar : out_channel -> trm -> int * string list -> unit
val tstpizename : string -> string

val coq_used_names : (string,unit) Hashtbl.t
val coq_names : (string,string) Hashtbl.t
val coq_hyp_names : (string,string) Hashtbl.t
module Variables:
sig
	(** next variable counter and list of used variable names**)
	type t = int * (string list)
	val make : unit -> t
	val push : t -> t
  val top : t -> string
  val get : int -> 'a * 'b list -> 'b
end
