(* File: tptp_config.mli *)
(* tptp_config.mli file with accumulator written by Frank Theiss for Chris Benzmueller's LEO-II *)
(* Postprocess a parsed formula, default is accumulation into a list *)
val accumulator : (Formula.formula -> Formula.formula list -> Formula.formula list) ref

val accumulator2 : (Formula.formula -> Formula.formula list -> Formula.formula list) ref

(*** Chad - Oct 2010 ***)
val process_thf : Formula.formula -> unit
