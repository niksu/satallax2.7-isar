(* File: satallaxcoqtac.ml *)
(* Author: Chad E Brown *)
(* Created: September 2011 [satallaxtop] *)

(* An executable which can be called by Coq's external command. *)

open Satallax;;

let remcoqreq = open_out "/tmp/coqreq" in
try
  while true do
    let l = input_line stdin in
    output_string remcoqreq l;
    Printf.fprintf remcoqreq "\n"
  done
with
|  End_of_file ->
    close_out remcoqreq;;

Printf.printf "<CALL uri=\"exact\">";
Printf.printf "<MUTCONSTRUCT uri=\"cic:/Coq/Init/Logic/True.ind\" noType=\"0\" noConstr=\"1\" id=\"i0\" sort=\"Prop\"/>";
Printf.printf "</CALL>";

