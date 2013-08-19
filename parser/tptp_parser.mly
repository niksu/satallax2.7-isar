/* File: tptp_parser.mly */
/* tptp_parser.mly file written by Frank Theiss for Chris Benzmueller's LEO-II */
/* Added Choice as @+ binder - Chad, Oct 2010 */
%{
open Lexing
open Formula

let print_error startpos endpos msg =
	if startpos.pos_lnum = endpos.pos_lnum then
		Printf.printf "line %d, characters %d-%d: %s\n"
		startpos.pos_lnum (startpos.pos_cnum - startpos.pos_bol)
		(endpos.pos_cnum - endpos.pos_bol)
		msg
	else
		Printf.printf "line %d, character %d - line %d, character %d: %s\n"
		startpos.pos_lnum (startpos.pos_cnum - startpos.pos_bol)
		endpos.pos_lnum (endpos.pos_cnum - endpos.pos_bol)
		msg

%}

%token Unrecognized

%token LBrkt
%token RBrkt
%token LParen
%token RParen
%token Comma
%token Period
%token Colon

%token Ampersand
%token At
%token Vline
%token Star
%token Plus
%token Arrow
%token Tilde
%token Caret
%token Question
%token Exclamation
%token Equal
%token Nequal

%token Iff
%token Implies
%token If
%token Niff
%token Nor
%token Nand

%token Pi
%token Sigma
%token Fforall
%token Eexists
%token Assign
%token Longarrow

%token Thf
%token Fof
%token Cnf

%token Dollar_thf
%token Dollar_fof
%token Dollar_cnf
%token Dollar_fot

%token Choice /* Chad - Oct 2010 */

%token Include

%token <string> Upper_word
%token <string> Lower_word
%token <string> Single_quoted
%token <string> Dollar_word
%token <string> Dollar_dollar_word
%token <string> Distinct_object

%token <string> Real
%token <string> Unsigned_integer
%token <string> Signed_integer

%token EOF

%start tptp_file
%start tptp_input
%start formula_data
%type <Formula.formula list> tptp_file
%type <Formula.formula> tptp_input formula_data

%%
/* Tail recursive, formulae are processed in reverse order */
/* tptp_file :
*    tptp_input tptp_file { (!Tptp_config.accumulator) $1 $2 }
*  | null { [] }
*/

/* Not tail recursive, formulae are processed from first to last */
tptp_file :
    tptp_input { (!Tptp_config.accumulator2) $1 [] }
  | tptp_file tptp_input { (!Tptp_config.accumulator2) $2 $1 }
  | null { [] }

tptp_input :
    annotated_formula {$1}
  | file_include {$1}
  | error { let startpos = Parsing.rhs_start_pos 1 in
	    let endpos = Parsing.rhs_end_pos 1 in
            print_error startpos endpos "syntax error";
            failwith "Syntax Error"}          
;

annotated_formula : 
    thf_annotated {$1}
  | fof_annotated {$1}
  | cnf_annotated {$1}

thf_annotated :
    Thf LParen name Comma formula_role Comma thf_formula annotations RParen Period
    {Appl (Symbol "$$thf",[$3;$5;$7;$8])}

fof_annotated :
    Fof LParen name Comma formula_role Comma fof_formula annotations RParen Period
    {Appl (Symbol "$$fof",[$3;$5;$7;$8])}

cnf_annotated :
    Cnf LParen name Comma formula_role Comma cnf_formula annotations RParen Period
    {Appl (Symbol "$$cnf", [$3;$5;$7;$8])}

annotations :
    Comma source optional_info {Appl (Symbol "$$annotations", [$2;$3])}
  | null {$1}

formula_role :
    Lower_word { Symbol $1 }
  | Thf { Symbol "thf" }
  | Fof { Symbol "fof" }
  | Cnf { Symbol "cnf" }
  | Include { Symbol "include" }

/* THF formulae */

thf_formula :
    thf_logic_formula { $1 }
  | thf_definition { $1 }
  | thf_sequent { $1 }


thf_logic_formula :
    thf_binary_formula { $1 }
  | thf_infix_unary { $1 }
  | thf_unitary_formula { $1 }
  | thf_type_formula { $1 }

thf_binary_formula :
    thf_binary_pair { $1 }
  | thf_binary_tuple { $1 }
  | thf_binary_type { $1 }

thf_binary_pair :
    thf_unitary_formula thf_pair_connective thf_unitary_formula
    {Appl ($2,[$1;$3])}

thf_binary_tuple :
    thf_or_formula { Appl (Symbol "|", $1) }
  | thf_and_formula { Appl (Symbol "&", $1) }
  | thf_apply_formula { Appl (Symbol "@", $1) }

thf_or_formula :
    thf_unitary_formula Vline thf_unitary_formula {[$1;$3]}
  | thf_or_formula Vline thf_unitary_formula {List.append $1 [$3]}

thf_and_formula :
    thf_unitary_formula Ampersand thf_unitary_formula {[$1;$3]}
  | thf_and_formula Ampersand thf_unitary_formula {List.append $1 [$3]}

thf_apply_formula :
    thf_unitary_formula At thf_unitary_formula {[$1;$3]}
  | thf_apply_formula At thf_unitary_formula {List.append $1 [$3]}

thf_unitary_formula :
    thf_quantified_formula { $1 }
  | thf_unary_formula { $1 }
  | thf_atom { $1 }
  | thf_tuple { $1 }
  | thf_letrec { $1 }
  | LParen thf_logic_formula RParen { $2 }

thf_quantified_formula :
    thf_quantifier LBrkt thf_variable_list RBrkt Colon thf_unitary_formula
    {Appl (Symbol "$$quantified", [$1;Appl (Symbol "$$tuple", $3);$6])}

thf_variable_list :
    thf_variable { [ $1 ] }
  | thf_variable Comma thf_variable_list { $1 :: $3 }

thf_variable :
    variable { $1 }
  | thf_typed_variable { $1 }

thf_typed_variable :
    variable Colon thf_top_level_type { Appl (Symbol "$$typed_var", [$1;$3]) }

thf_unary_formula :
    thf_unary_connective LParen thf_logic_formula RParen { Appl ($1, [$3]) }

thf_atom :
    term { $1 }
  | thf_conn_term { $1 }

thf_tuple :
    LBrkt RBrkt { Appl (Symbol "$$tuple", []) }
  | LBrkt thf_tuple_list RBrkt { Appl (Symbol "$$tuple", $2) }

thf_tuple_list :
    thf_unitary_formula {[ $1 ]}
  | thf_unitary_formula Comma thf_tuple_list { $1 :: $3 }

thf_type_formula :
    thf_unitary_formula Colon thf_top_level_type { Appl (Symbol "$$type_formula", [$1;$3]) }
  | constant Colon thf_top_level_type { Appl (Symbol "$$type_formula", [$1;$3]) }

thf_top_level_type :
    thf_logic_formula { $1 }

thf_unitary_type :
    thf_unitary_formula { $1 }

thf_binary_type :
    thf_mapping_type { $1 }
  | thf_xprod_type { $1 }
  | thf_union_type { $1 }

thf_mapping_type :
    thf_unitary_type Arrow thf_unitary_type { Appl (Symbol ">", [$1;$3]) }
  | thf_unitary_type Arrow thf_mapping_type { Appl (Symbol ">", [$1;$3]) }

thf_xprod_type :
    thf_unitary_type Star thf_unitary_type { Appl (Symbol "*", [$1;$3]) }
  | thf_xprod_type Star thf_unitary_type { Appl (Symbol "*", [$1;$3]) }

thf_union_type :
    thf_unitary_type Plus thf_unitary_type { Appl (Symbol "+", [$1;$3]) }
  | thf_union_type Plus thf_unitary_type { Appl (Symbol "+", [$1;$3]) }

thf_letrec :
    Assign LBrkt thf_letrec_list RBrkt Colon thf_unitary_formula { Appl (Symbol "$$letrec", [Appl (Symbol "$$tuple", $3);$6]) }

thf_letrec_list :
    thf_defined_var { [$1] }
  | thf_defined_var Comma thf_letrec_list { $1::$3 }

thf_defined_var :
    thf_variable Assign thf_logic_formula { Appl (Symbol ":=", [$1;$3]) }
  | LParen thf_defined_var RParen { $2 }

thf_definition :
    thf_defn_constant Assign thf_logic_formula { Appl (Symbol ":=", [$1;$3])  }
  | LParen thf_definition RParen { $2 }

thf_defn_constant :
    constant { $1 }
  | thf_type_formula { $1 }

thf_sequent :
    thf_tuple Longarrow thf_tuple { Appl (Symbol "-->", [$1;$3]) }


/* FOF formulae */

fof_formula :
    binary_formula { $1 }
  | unitary_formula { $1 }

binary_formula :
    nonassoc_binary { $1 }
  | assoc_binary { $1 }

nonassoc_binary :
    unitary_formula binary_connective unitary_formula { Appl ($2, [$1;$3]) }

assoc_binary :
    or_formula { Appl (Symbol "|", $1) }
  | and_formula { Appl (Symbol "&", $1) }

or_formula :
    unitary_formula Vline unitary_formula { [$1;$3] }
  | or_formula Vline unitary_formula { List.append $1 [$3] }

and_formula :
    unitary_formula Ampersand unitary_formula { [$1;$3] }
  | and_formula Ampersand unitary_formula { List.append $1 [$3] }

unitary_formula :
    quantified_formula { $1 }
  | unary_formula { $1 }
  | atomic_formula { $1 }
  | LParen fof_formula RParen { $2 }

quantified_formula :
    quantifier LBrkt variable_list RBrkt Colon unitary_formula { Appl (Symbol "$$quantified", [$1;Appl (Symbol "$$tuple", $3);$6]) }

variable_list :
    variable { [ $1 ] }
  | variable Comma variable_list { $1 :: $3 }

unary_formula :
    unary_connective unitary_formula { Appl ($1, [$2]) }
  | fol_infix_unary { $1 }


/* CNF formulae */

cnf_formula :
    LParen disjunction RParen { Appl (Symbol "|", $2) }
  | disjunction { Appl (Symbol "|", $1) }

disjunction :
    literal { [ $1 ] }
  | disjunction Vline literal { List.append $1 [$3] }

literal :
    atomic_formula { Appl (Symbol "$$poslit", [$1]) }
  | Tilde atomic_formula { Appl (Symbol "$$neglit", [$2]) }
  | fol_infix_unary { Appl (Symbol "$$poslit", [$1]) }


/* Special formulae */

thf_infix_unary :
    thf_unitary_formula infix_inequality thf_unitary_formula { Appl ($2, [$1;$3]) }

thf_conn_term :
    thf_pair_connective { $1 }
  | assoc_connective { $1 }
  | thf_unary_connective { $1 }

fol_infix_unary :
    term infix_inequality term { Appl ($2, [$1;$3]) }


/* Connectives - THF */

thf_quantifier :
    quantifier { $1 }
  | Caret { Symbol "^" }
  | Choice { Symbol "@+" } /* Chad - Oct 2010 */
  | Pi { Symbol "!>" }
  | Sigma { Symbol "?*" }

thf_pair_connective :
    infix_equality { $1 }
  | binary_connective { $1 }

thf_unary_connective :
    unary_connective { $1 }
  | Fforall { Symbol "!!" }
  | Eexists { Symbol "??" }


/* Connectives - FOF */

quantifier :
    Question { Symbol "?" }
  | Exclamation { Symbol "!" }

binary_connective :
    Iff { Symbol "<=>" }
  | Implies { Symbol "=>" }
  | If { Symbol "<=" }
  | Niff { Symbol "<~>" }
  | Nor { Symbol "~|" }
  | Nand { Symbol "~&" }

assoc_connective :
    Vline { Symbol "|" }
  | Ampersand { Symbol "&" }

unary_connective :
    Tilde { Symbol "~" }
  

/* Types for THF and TFF */
/* Unused? */

defined_type :
    atomic_defined_word { $1 }

system_type :
    atomic_system_word { $1 }


/* First order atoms */

atomic_formula :
    plain_atomic_formula { $1 }
  | defined_atomic_formula { $1 }
  | system_atomic_formula { $1 }

plain_atomic_formula :
    plain_term { $1 }

defined_atomic_formula :
    defined_plain_formula { $1 }
  | defined_infix_formula { $1 }

defined_plain_formula :
    defined_plain_term { $1 }

defined_infix_formula :
    term defined_infix_pred term { Appl ($2, [$1;$3]) }

defined_infix_pred :
    infix_equality { $1 }

infix_equality :
    Equal { Symbol "=" }

infix_inequality :
    Nequal { Symbol "!=" }

system_atomic_formula :
    system_term { $1 }


/* First order terms */

term :
    function_term { $1 }
  | variable { $1 }

function_term :
    plain_term { $1 }
  | defined_term { $1 }
  | system_term { $1 }

plain_term :
    constant { $1 }
  | fof_functor LParen arguments RParen { Appl ($1, $3) }

constant :
    fof_functor { $1 }

fof_functor :
    atomic_word { $1 }

defined_term :
    defined_atom { $1 }
  | defined_atomic_term { $1 }

defined_atom :
    number { $1 }
  | Distinct_object { Symbol $1 }

defined_atomic_term :
    defined_plain_term { $1 }

defined_plain_term :
    defined_constant { $1 }
  | defined_functor LParen arguments RParen { Appl ($1, $3) }

defined_constant :
    defined_functor { $1 }
  
defined_functor :
    atomic_defined_word { $1 }

system_term :
    system_constant { $1 }
  | system_functor LParen arguments RParen { Appl ($1, $3) }

system_constant :
    system_functor { $1 }
  
system_functor :
    atomic_system_word { $1 }

variable :
    Upper_word { Symbol $1 }

arguments :
    term { [$1] }
  | term Comma arguments { $1::$3 }


/* Formula sources */

source :
    general_term { $1 }

general_term :
    general_data { $1 }
  | general_data Colon general_term { Appl (Symbol ":", [$1;$3]) }
  | general_list { Appl (Symbol "$$tuple", $1) }

general_data :
    atomic_word { $1 }
  | atomic_word LParen general_terms RParen { Appl ($1, $3) }
  | variable { $1 }
  | number { $1 }
  | formula_data { $1 }
  | Distinct_object { Symbol $1 }

formula_data :
    Dollar_thf LParen thf_formula RParen { Appl (Symbol "$thf", [$3]) }
  | Dollar_fof LParen fof_formula RParen { Appl (Symbol "$fof", [$3]) }
  | Dollar_cnf LParen cnf_formula RParen { Appl (Symbol "$cnf", [$3]) }
  | Dollar_fot LParen term RParen { Appl (Symbol "$fot", [$3]) }

general_list :
    LBrkt RBrkt { [] }
  | LBrkt general_terms RBrkt { $2 }

general_terms :
    general_term { [$1] }
  | general_term Comma general_terms {$1::$3 }

optional_info :
    Comma useful_info { Appl (Symbol "$$useful_info", [$2]) }
  | null { $1 }

useful_info :
    general_list { Appl (Symbol "$$tuple", $1) }

/* Include directives */

file_include :
    Include LParen file_name formula_selection RParen Period { Appl (Symbol "$$include", [$3;$4]) }


formula_selection :
    Comma LBrkt name_list RBrkt { Appl (Symbol "$$formula_selection", [Appl (Symbol "$$tuple",$3)]) }
  | null { $1 }

name_list :
    name { [$1] }
  | name Comma name_list { $1::$3 }






name :
    atomic_word {$1}
  | Unsigned_integer {Symbol $1}

atomic_word :
    Lower_word { Symbol $1 }
  | Single_quoted { Symbol $1 }
  | Thf { Symbol "thf" }
  | Fof { Symbol "fof" }
  | Cnf { Symbol "cnf" }
  | Include { Symbol "include" }

atomic_defined_word :
    Dollar_word { Symbol $1 }
  | Dollar_thf { Symbol "$thf" }
  | Dollar_fof { Symbol "$fof" }
  | Dollar_cnf { Symbol "$cnf" }
  | Dollar_fot { Symbol "$fot" }

atomic_system_word :
    Dollar_dollar_word { Symbol $1 }

number :
    Real { Symbol $1 }
  | Signed_integer { Symbol $1 }
  | Unsigned_integer { Symbol $1 }

file_name :
    Single_quoted { Symbol $1 }

null : { Appl (Symbol "$$null",[]) };
