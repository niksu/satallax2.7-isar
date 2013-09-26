(* File: unif.mli *)
(* Author: Chad E Brown *)
(* Created: December 2010 *)

open Syntax

exception NotGround

type metatrm =
  | MGround of trm
  | MVar of metatrm option ref * metatrm list
  | MLam of stp * metatrm
  | MAp of metatrm * metatrm

val to_meta : trm -> metatrm

val meta_to_ground : (string,trm) Hashtbl.t -> metatrm -> trm

type ctx = stp list
type dpair = ctx * metatrm * metatrm * stp

val pattern_unify : dpair list -> dpair list
