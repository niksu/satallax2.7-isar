(* File: satallaxmain.mli *)
(* Author: Chad E Brown *)
(* Created: September 2011 *)

exception InputHelpError of string
exception InputError of string
exception UnclassifiedError

val print_help : unit -> unit
val load_mode : string -> unit
val read_coq_file : string -> unit
val read_thf_file : string -> (string -> unit) -> unit
val process_command_line_args : unit -> unit
val search_main : unit -> unit
