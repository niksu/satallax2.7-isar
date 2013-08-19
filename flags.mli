(* File: flags.mli *)
(* Author: Chad E Brown *)
(* Created: September 2010 *)

exception NotFlag of string
exception NotBoolFlag of string
exception NotIntFlag of string

val get_bool_flag : string -> bool
val set_bool_flag : string -> bool -> unit
val get_int_flag : string -> int
val set_int_flag : string -> int -> unit
val print_flags : unit -> unit
val init_flags : unit -> unit
