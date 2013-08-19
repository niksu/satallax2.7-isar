let vold = 2
let vlat = 2

(** Outputs (a lot of) information to standard output.**)
let debug_heuristic = false
let debug_litcount = false
let debug_translation = false (* Should be: false *)
let debug_rewrite = false
let debug_search = false (* Should be: false *)
let debug_add_clauses = false
let debug_free_names = false
let debug_leibeq = false (* Should be: false *)
let debug_Independent_refutation = false (* Should be: false *)
let debug_semantic = false

(** Checks if the witnesses of applied exist steps are still fresh**)
let assert_freshness = false
(** Checks if the last dependency is fulfilled by the initial branch **)
let assert_condition = false

(** Print the refutation after search to standard output**)
let result_print_search = false (* Should be: false *)

(** Print the refutation after translation to standard output**)
let result_print_translation = false (* Should be: false *)

(** Print the refutation as latex code after search and translation at the end of the proof script as a comment**)
let result_latex = false

(** Print additional statistics - mainly preprocess- to standard output**)
let result_statistic = false

(** Print the Coq proof script**)
let result_coq = false (*FIXME was: true *)

(** If a term with a "fun x", "forall x" or "exists x" is printed, the type is added: e.g. "fun (x:tpof(x))" **)
let result_print_coq_type = true

(** The search phase will stop after x seconds 
	and close the remaining open branches with a timeout step **)
let timeout = ref 90.0

(** Activates semantic branching **)
let pftrm_semantic_imp = true
let pftrm_semantic_con = true
let pftrm_semantic_mat_dec = false (** high chance to contain bugs **)

(** The literals in the clauses set are counted. 
	Otherweise litc only contains empty entries**)
let pftrm_litcount = true

(** Activaes Timeout (see timeout)**)
let pftrm_Timeout = true

(** Adds symmetric clauses**)
let pftrm_add_clauses = true

(** Activates Backjumping, necessary for semantic branching **)
let pftrm_Independent_refutation =  true

(* false => lazy rewrite*)
let pftrm_eager_rewrite = false 

let maxcoqproofsize = 800


(** Isabelle/HOL-related flats **)
let result_isabellehol = true
let max_isabellehol_proofsize = 800
