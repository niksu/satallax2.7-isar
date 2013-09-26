(* File: satallax.ml *)
(* Author: Chad E Brown *)
(* Created: September 2010 - most code moved to satallaxmain in September 2011 *)

open Satallaxmain
open Flags
open Syntax
open State;;

try
  process_command_line_args ();
  if (!coqglobalfile) then
    read_coq_file !problemfile
  else
    search_main ()
with
| InputHelpError(x) -> if (not (!slave)) then (print_string "% SZS status Error :"; print_newline (); Printf.printf "Input Error: %s" x; print_newline (); print_help ()); exit 1
| InputError(x) -> if (not (!slave)) then (print_string "% SZS status Error :"; print_newline (); Printf.printf "Input Error: %s" x; print_newline ()); exit 1
| FileNotFound(x) -> if (not (!slave)) then (print_string "% SZS status Error :"; print_newline (); Printf.printf "File Not Found: %s" x; print_newline ()); exit 1
| NotFlag(x) -> if (not (!slave)) then (print_string "% SZS status Error :"; print_newline (); Printf.printf "%s is not a flag" x; print_newline ()); exit 2
| NotBoolFlag(x) -> if (not (!slave)) then (print_string "% SZS status Error :"; print_newline (); Printf.printf "%s is an integer flag, not a boolean flag" x; print_newline ()); exit 2
| NotIntFlag(x) -> if (not (!slave)) then (print_string "% SZS status Error :"; print_newline (); Printf.printf "%s is a boolean flag, not an integer flag" x; print_newline ()); exit 2
| Parsing.Parse_error -> if (not (!slave)) then (print_string "% SZS status Error :"; print_newline (); print_string "Syntax Error"; print_newline ()); exit 2
| ParsingError(l1,i1,l2,i2,x) -> if (not (!slave)) then (print_string "% SZS status Error :"; print_newline (); Printf.printf "Parsing Error: %s from line %d char %d to line %d char %d\n" x l1 i1 l2 i2; print_newline ()); exit 2
| ExpectedTypeError(m,a,b) -> if (not (!slave)) then (print_string "% SZS status Error :"; print_newline (); Printf.printf "%s\nhas type\n%s\nexpected type\n%s\n" (pretrm_str m) (stp_str b) (stp_str a); print_newline ()); exit 2
| GenericError(x) -> if (not (!slave)) then (print_string "% SZS status Error :"; print_newline (); Printf.printf "%s\n" x; print_newline ()); exit 2
| GenericSyntaxError(x) -> if (not (!slave)) then (print_string "% SZS status Error :"; print_newline (); Printf.printf "%s\n" x; print_newline ()); exit 2
| Redeclaration(x) -> if (not (!slave)) then (print_string "% SZS status Error :"; print_newline (); Printf.printf "%s cannot be redeclared " x; print_newline ()); exit 2
| UnclassifiedError -> if (not (!slave)) then (print_string "% SZS status Error"; print_newline ()); exit 3
| Timeout -> if (not (!slave)) then (if (!verbosity > 0) then (print_string "% SZS status Timeout"; print_newline ())); exit 5
| e -> if (not (!slave)) then (if (!verbosity > 0) then (print_string "% SZS status Error"; print_newline (); Printf.printf "Exception: %s\n" (Printexc.to_string e))); exit 3
