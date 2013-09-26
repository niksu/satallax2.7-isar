(* File: flags.ml *)
(* Author: Chad E Brown *)
(* Created: September 2010 *)

exception NotFlag of string
exception NotBoolFlag of string
exception NotIntFlag of string

let bool_flags : (string,bool) Hashtbl.t = Hashtbl.create 20
let int_flags : (string,int) Hashtbl.t = Hashtbl.create 50

let get_bool_flag flagname = Hashtbl.find bool_flags flagname
let set_bool_flag flagname flagval =
  if (Hashtbl.mem bool_flags flagname) then
    Hashtbl.replace bool_flags flagname flagval
  else if (Hashtbl.mem int_flags flagname) then
    raise (NotBoolFlag flagname)
  else
    raise (NotFlag flagname)
let get_int_flag flagname = Hashtbl.find int_flags flagname
let set_int_flag flagname flagval =
  if (Hashtbl.mem int_flags flagname) then
    Hashtbl.replace int_flags flagname flagval
  else if (Hashtbl.mem bool_flags flagname) then
    raise (NotIntFlag flagname)
  else
    raise (NotFlag flagname)

let print_flags () =
  begin
    Hashtbl.iter (fun x y -> Printf.printf "%s: %B\n" x y) bool_flags;
    Hashtbl.iter (fun x y -> Printf.printf "%s: %d\n" x y) int_flags
  end

let init_flags () =
  begin
(*** The following flags control search. ***)
    Hashtbl.add bool_flags "ENABLE_PATTERN_CLAUSES" false;
    Hashtbl.add bool_flags "PATTERN_CLAUSES_EARLY" false; (*** Dec 2012 - If true, make a pattern clause for the formula when it's assigned a literal instead of when it's processed. ***)
    Hashtbl.add bool_flags "DYNAMIC_PATTERN_CLAUSES" true; (*** Create pattern clauses from universally quantified formulas during search. - Chad, April 6, 2011 ***)
    Hashtbl.add bool_flags "PATTERN_CLAUSES_TRANSITIVITY_EQ" false; (*** Make pattern clauses for transitivity of equality. ***)
    Hashtbl.add bool_flags "PATTERN_CLAUSES_FORALL_AS_LIT" true;
    Hashtbl.add int_flags "PATTERN_CLAUSES_DELAY" 1;
    Hashtbl.add int_flags "PATTERN_CLAUSES_EQN_DELAY" 1;
    Hashtbl.add bool_flags "PATTERN_CLAUSES_ONLYALLSTRICT" false; (*** If true, only apply pattern clauses with a lit that contains all strict variables.  This is the first half of simulating pattern rules from Satallax 1.* ***)
    Hashtbl.add bool_flags "PATTERN_CLAUSES_EQNLITS" false; (*** If true, do rewriting with eqn lits in pattern clauses.  This is the other half of simulating pattern rules from Satallax 1.* ***)
    Hashtbl.add bool_flags "SPLIT_GLOBAL_DISJUNCTIONS" false;
    Hashtbl.add bool_flags "FILTER_UNIV_USABLE" false;
    Hashtbl.add bool_flags "FILTER_UNIV" false;
    Hashtbl.add bool_flags "FILTER_POSATM_USABLE" false;
    Hashtbl.add bool_flags "FILTER_POSATM" false;
    Hashtbl.add bool_flags "FILTER_NEGATM_USABLE" false;
    Hashtbl.add bool_flags "FILTER_NEGATM" false;
    Hashtbl.add bool_flags "FILTER_POSEQ_USABLE" false;
    Hashtbl.add bool_flags "FILTER_POSEQ" false;
    Hashtbl.add bool_flags "FILTER_NEGEQ_USABLE" false;
    Hashtbl.add bool_flags "FILTER_NEGEQ" false;
    Hashtbl.add int_flags "FILTER_START" 5;
    Hashtbl.add int_flags "FILTER_INCR" 5;
    Hashtbl.add bool_flags "SYM_EQ" true;
    Hashtbl.add bool_flags "INSTANTIATE_WITH_FUNC_DISEQN_SIDES" true;
    Hashtbl.add bool_flags "IMITATE_DEFNS" true;
    Hashtbl.add int_flags "EXISTS_DELAY" 1;
    Hashtbl.add int_flags "FORALL_DELAY" 1;
    Hashtbl.add int_flags "DEFAULTELT_DELAY" 30;
    Hashtbl.add int_flags "DEFAULTELTINST_DELAY" 30;
    Hashtbl.add int_flags "CONFR_DIFF_DELAY" 100;
    Hashtbl.add int_flags "CONFR_SAME1_DELAY" 5;
    Hashtbl.add int_flags "CONFR_SAME2_DELAY" 0;
    Hashtbl.add int_flags "ENUM_START" 20;
    Hashtbl.add int_flags "ENUM_ARROW" 10;
    Hashtbl.add int_flags "ENUM_O" 5;
    Hashtbl.add int_flags "ENUM_SORT" 2;
    Hashtbl.add int_flags "ENUM_NEG" 5;
    Hashtbl.add int_flags "ENUM_IMP" 20;
    Hashtbl.add int_flags "ENUM_FALSE" 20;
    Hashtbl.add int_flags "ENUM_CHOICE" 0;
    Hashtbl.add int_flags "ENUM_FORALL" 50; (*** New in Satallax 2.0 ***)
    Hashtbl.add int_flags "ENUM_EQ" 5;
    Hashtbl.add bool_flags "ENUM_ITER_DEEP" false;
    Hashtbl.add int_flags "ENUM_ITER_DEEP_DELAY" 100;
    Hashtbl.add int_flags "ENUM_ITER_DEEP_INIT" 1;
    Hashtbl.add int_flags "ENUM_ITER_DEEP_INCR" 0;
    Hashtbl.add bool_flags "LEIBEQ_TO_PRIMEQ" false;
    Hashtbl.add bool_flags "CHOICE_AS_DEFAULT" false;
    Hashtbl.add int_flags "IMITATE_DEFN_DELAY" 0;
    Hashtbl.add int_flags "IMITATE_DELAY" 10;
    Hashtbl.add int_flags "PROJECT_DELAY" 10;
    Hashtbl.add int_flags "NEW_HEAD_ENUM_DELAY" 10;
    Hashtbl.add int_flags "CHOICE_EMPTY_DELAY" 0;
    Hashtbl.add int_flags "CHOICE_IN_DELAY" 0;
    Hashtbl.add int_flags "POST_OR_L_DELAY" 0;
    Hashtbl.add int_flags "POST_OR_R_DELAY" 0;
    Hashtbl.add int_flags "POST_NOR_L_DELAY" 0;
    Hashtbl.add int_flags "POST_NOR_R_DELAY" 0;
    Hashtbl.add int_flags "POST_EQO_L_DELAY" 0;
    Hashtbl.add int_flags "POST_EQO_R_DELAY" 0;
    Hashtbl.add int_flags "POST_EQO_NL_DELAY" 0;
    Hashtbl.add int_flags "POST_EQO_NR_DELAY" 0;
    Hashtbl.add int_flags "POST_NEQO_L_DELAY" 0;
    Hashtbl.add int_flags "POST_NEQO_R_DELAY" 0;
    Hashtbl.add int_flags "POST_NEQO_NL_DELAY" 0;
    Hashtbl.add int_flags "POST_NEQO_NR_DELAY" 0;
    Hashtbl.add int_flags "POST_DEC_DELAY" 0;
    Hashtbl.add int_flags "PRE_MATING_DELAY_POS" 0;  (*** New in Satallax 2.0 ***)
    Hashtbl.add int_flags "PRE_MATING_DELAY_NEG" 0;  (*** New in Satallax 2.0 ***)
    Hashtbl.add int_flags "PRE_CHOICE_MATING_DELAY_POS" 0;  (*** New in Satallax 2.0 ***)
    Hashtbl.add int_flags "PRE_CHOICE_MATING_DELAY_NEG" 0;  (*** New in Satallax 2.0 ***)
    Hashtbl.add int_flags "POST_MATING_DELAY" 0;
    Hashtbl.add int_flags "POST_FEQ_DELAY" 0;
    Hashtbl.add int_flags "POST_NFEQ_DELAY" 0;
    Hashtbl.add int_flags "POST_CONFRONT1_DELAY" 0;
    Hashtbl.add int_flags "POST_CONFRONT2_DELAY" 0;
    Hashtbl.add int_flags "POST_CONFRONT3_DELAY" 0;
    Hashtbl.add int_flags "POST_CONFRONT4_DELAY" 0;
    Hashtbl.add bool_flags "INITIAL_SUBTERMS_AS_INSTANTIATIONS" false;
    Hashtbl.add int_flags "PRIORITY_QUEUE_IMPL" 0; (*** Which version of priority queue implementation to use ***)
    Hashtbl.add bool_flags "PREPROCESS_BEFORE_SPLIT" false;
    Hashtbl.add bool_flags "TREAT_CONJECTURE_AS_SPECIAL" false;
    Hashtbl.add int_flags "AXIOM_DELAY" 0; (*** Set this to > 0 to work on the negated conjecture first ***)
    Hashtbl.add int_flags "RELEVANCE_DELAY" 0; (*** Set this to > 0 to delay axioms that do not share names with the negated conjecture. Only has an effect if TREAT_CONJECTURE_SPECIAL is true ***)
    Hashtbl.add bool_flags "ALL_DEFS_AS_EQNS" false;

    Hashtbl.add bool_flags "EAGERLY_PROCESS_INSTANTIATIONS" true;
    Hashtbl.add int_flags "INSTANTIATION_DELAY" 1; (*** If EAGERLY_PROCESS_INSTANTIATIONS is false ***)
    Hashtbl.add int_flags "ARTP_WEIGHT" 1; (*** If EAGERLY_PROCESS_INSTANTIATIONS is false ***)
    Hashtbl.add int_flags "BASETP_WEIGHT" 1; (*** If EAGERLY_PROCESS_INSTANTIATIONS is false ***)
    Hashtbl.add int_flags "OTP_WEIGHT" 1; (*** If EAGERLY_PROCESS_INSTANTIATIONS is false ***)
    Hashtbl.add int_flags "AP_WEIGHT" 1; (*** If EAGERLY_PROCESS_INSTANTIATIONS is false ***)
    Hashtbl.add int_flags "LAM_WEIGHT" 1; (*** If EAGERLY_PROCESS_INSTANTIATIONS is false ***)
    Hashtbl.add int_flags "LAM_TP_WEIGHT_FAC" 1; (*** If EAGERLY_PROCESS_INSTANTIATIONS is false ***)
    Hashtbl.add int_flags "NAME_WEIGHT" 1; (*** If EAGERLY_PROCESS_INSTANTIATIONS is false ***)
    Hashtbl.add int_flags "NAME_TP_WEIGHT_FAC" 1; (*** If EAGERLY_PROCESS_INSTANTIATIONS is false ***)
    Hashtbl.add int_flags "DB_WEIGHT" 1; (*** If EAGERLY_PROCESS_INSTANTIATIONS is false ***)
    Hashtbl.add int_flags "DB_TP_WEIGHT_FAC" 1; (*** If EAGERLY_PROCESS_INSTANTIATIONS is false ***)
    Hashtbl.add int_flags "FALSE_WEIGHT" 1; (*** If EAGERLY_PROCESS_INSTANTIATIONS is false ***)
    Hashtbl.add int_flags "IMP_WEIGHT" 1; (*** If EAGERLY_PROCESS_INSTANTIATIONS is false ***)
    Hashtbl.add int_flags "FORALL_WEIGHT" 1; (*** If EAGERLY_PROCESS_INSTANTIATIONS is false ***)
    Hashtbl.add int_flags "FORALL_TP_WEIGHT_FAC" 1; (*** If EAGERLY_PROCESS_INSTANTIATIONS is false ***)
    Hashtbl.add int_flags "EQ_WEIGHT" 1; (*** If EAGERLY_PROCESS_INSTANTIATIONS is false ***)
    Hashtbl.add int_flags "EQ_TP_WEIGHT_FAC" 1; (*** If EAGERLY_PROCESS_INSTANTIATIONS is false ***)
    Hashtbl.add int_flags "CHOICE_WEIGHT" 1; (*** If EAGERLY_PROCESS_INSTANTIATIONS is false ***)
    Hashtbl.add int_flags "CHOICE_TP_WEIGHT_FAC" 1; (*** If EAGERLY_PROCESS_INSTANTIATIONS is false ***)

    Hashtbl.add int_flags "NOT_IN_PROP_MODEL_DELAY" 0; (*** Nov 2011: Use propositional approximation to focus work on those true in the current propositional model. Koen Claessen suggested this at CADE 23. ***)
    Hashtbl.add bool_flags "HOUNIF1" false; (*** Mar 2012 - use HO unification to suggest instantiations during search ***)
    Hashtbl.add bool_flags "HOUNIF1MATE" false;
    Hashtbl.add bool_flags "HOUNIF1MATEBELOWEQUIV" true;
    Hashtbl.add int_flags "HOUNIF1MAXMATES" 1;
    Hashtbl.add int_flags "HOUNIF1BOUND" 4;
    Hashtbl.add int_flags "HOUNIF1PROJECT" 1;
    Hashtbl.add int_flags "HOUNIF1IMITATE" 1;
    Hashtbl.add bool_flags "EXISTSTOCHOICE" false; (*** Mar 2012 - Get rid of existentials during preprocessing ***)

(*** The following flags should only be changed when trying to disprove ***)
    Hashtbl.add bool_flags "BASETYPESTOPROP" false; (*** when true, change all base types to be o -- equivalent to making them all a type with 2 elts. ***)
    Hashtbl.add bool_flags "BASETYPESFINITE" false; (*** when true (and BASETYPESTOPROP false), assume all base types are finite of size <= BASETYPEMAXSIZE and do it. ***)
    Hashtbl.add int_flags "BASETYPESMAXSIZE" 3; (*** Assume all base types have size <= this number ***)

(*** The following flags control translation to proof terms. ***)
    Hashtbl.add bool_flags "PFTRM_ADD_SYM_CLAUSES" true;
    Hashtbl.add bool_flags "PFTRM_PRESORT_CLAUSES" true;
    Hashtbl.add bool_flags "PFTRM_REMOVE_INDEPENDENT" true;

(*** The flag MINISAT_SEARCH_PERIOD controls how often MiniSat asked to search for unsatisfiability.
     Default of 1 means every time a new clause is given to MiniSat. ***)
    Hashtbl.add int_flags "MINISAT_SEARCH_PERIOD" 1;

(*** Send first-order formulas to E with timeout of E_TIMEOUT seconds every E_PERIOD times a first-order formula is encountered. ***)
    Hashtbl.add bool_flags "USE_E" false;
    Hashtbl.add int_flags "E_PERIOD" 100;
    Hashtbl.add int_flags "E_TIMEOUT" 1;
    Hashtbl.add bool_flags "E_EQO_EQUIV" false;

(*** Feb 18 2013
 - INSTANTIATION_ORDER_CYCLE - how long to cycle a stack/queue switching pattern.
 - INSTANTIATION_ORDER_MASK - integer describing the stack/queue switching pattern. ***)
    Hashtbl.add int_flags "INSTANTIATION_ORDER_CYCLE" 1;
    Hashtbl.add int_flags "INSTANTIATION_ORDER_MASK" 0;
  end
