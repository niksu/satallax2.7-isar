(* File: match.mli *)
(* Author: Chad E Brown *)
(* Created: December 2010 *)

open Syntax

exception NotGround
exception PatternMatchFailed

type metatrm =
  | MGround of trm
  | MVar of (int * metatrm option ref) * metatrm list
  | MLam of stp * metatrm
  | MAp of metatrm * metatrm

type ctx = stp list
type dpair = ctx * metatrm * trm * stp
type evar = int * metatrm option ref

val to_meta : trm -> metatrm

val meta_to_ground : (string,trm) Hashtbl.t -> metatrm -> trm

val metatermNotFreeIn : metatrm -> int -> bool
val metashift : metatrm -> int -> int -> metatrm
val metasubst : metatrm -> int -> metatrm -> metatrm
val metanorm : metatrm -> metatrm (** only does beta normalization [and dneg], no eta, no delta **)
val gen_mlam_body:stp -> metatrm -> metatrm

val meta_copy : metatrm -> (int * evar) list -> metatrm

val mem_evar : evar -> evar list -> bool
val pattern_match : dpair list -> dpair list
val update_strict : evar list -> metatrm -> evar list

val new_evar : int -> ctx -> stp -> (evar * metatrm)
val copy_evar : int -> evar -> evar
val string_of_evar : evar -> string
val metatrm_str : metatrm -> string

type udpair = ctx * metatrm * metatrm * stp

val hounif1d : int -> evar list -> metatrm list -> udpair list -> int -> (stp -> trm -> unit) -> unit
val hounif1 : int -> metatrm -> evar list -> metatrm list -> ctx -> int -> bool -> (stp -> trm -> unit) -> unit
