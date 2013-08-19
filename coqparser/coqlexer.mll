(* File: coqlexer.mll *)
(* Author: Chad E Brown *)

{
open Coqparser        (* The type token is defined in coqparser.mli *)
exception Eof
}
rule token = parse
  [' ' '\t' '\n']     { token lexbuf }     (* skip white space *)
| ['(']['*']['*']*[^'*']*['*']+[')'] { token lexbuf }     (* skip comments *)
| '('            { LPAREN }
| ')'            { RPAREN }
| '.'            { DOT(Lexing.lexeme_end lexbuf) }
| ':'            { COLON }
| '='            { EQ }
| "<>"            { NEQ }
| ":e"            { MEM }
| "/:e"            { NMEM }
| "c="            { SUBQ }
| "/c="            { NSUBQ }
| ';'            { SEMICOLON }
| ','            { COMMA }
| "forall"            { ALL }
| "exists"            { EX }
| "exists!"            { EXU }
| "/\\"          { CONJ }
| "\\/"            { DISJ }
| "<->"            { IFF }
| '~'            { NEG }
| "Let"          { BLET }
| "let"          { LLET }
| ":="           { DEQ }
| "in"          { IN }
| "fun"          { LAM }
| "=>"           { DARR }
| "->"           { IMP }
| ">"           { SAR }
| "set"            { INDTYPE}
| "prop"            { PROPTYPE}
| '_'            { BLANK }
| "Require"          { REQUIRE }
| "Export"          { EXPORT }
| "Section"          { SECTION }
| "End"          { END }
| "Variable"          { VAR }
| "Hypothesis"          { HYP }
| "Parameter"        { PARAM }
| "Axiom"        { AXIOM }
| "Lemma"        { THEOREM }
| "Theorem"        { THEOREM }
| "exact"        { EXACT }
| "Qed"        { QED }
| "Conjecture"        { CONJECTURE(Lexing.lexeme_start lexbuf) }
| "Definition"          { DEF }
| "o"            { PROP }
| "Prop"            { PROP }
| "False" { FALSE }
| "True" { TRUE }
| "Eps" as lxm           { POLY1(lxm) }
| "ex" as lxm           { POLY1(lxm) }
| "eq" as lxm           { POLY1(lxm) }
| "exu" as lxm           { POLY1(lxm) }
| "EpsR" as lxm           { POLY1(lxm) }
| "Inh" as lxm           { POLY1(lxm) }
| "exE" as lxm { POLY1(lxm) }
| "exI" as lxm { POLY1(lxm) }
| "eqE" as lxm { POLY1(lxm) }
| "eqI" as lxm { POLY1(lxm) }
| "eq_sym" as lxm { POLY1(lxm) }
| "eqEr" as lxm { POLY1(lxm) }
| "eq_trans" as lxm { POLY1(lxm) }
| "eq_symtrans1" as lxm { POLY1(lxm) }
| "eq_symtrans2" as lxm { POLY1(lxm) }
| "exuE1" as lxm { POLY1(lxm) }
| "exuE2" as lxm { POLY1(lxm) }
| "exuI" as lxm { POLY1(lxm) }
| "exuEa" as lxm { POLY1(lxm) }
| "exuIa" as lxm { POLY1(lxm) }
| "eq_sym_eq" as lxm { POLY1(lxm) }
| "eq_forall_nexists" as lxm { POLY1(lxm) }
| "eq_exists_nforall" as lxm { POLY1(lxm) }
| "eq_leib1" as lxm { POLY1(lxm) }
| "eq_leib2" as lxm { POLY1(lxm) }
| "eq_leib3" as lxm { POLY1(lxm) }
| "eq_leib4" as lxm { POLY1(lxm) }
| "TRef" as lxm { POLY1(lxm) }
| "TAll" as lxm { POLY1(lxm) }
| "TNAll" as lxm { POLY1(lxm) }
| "TEx" as lxm { POLY1(lxm) }
| "TNEx" as lxm { POLY1(lxm) }
| "TCON" as lxm { POLY1(lxm) }
| "Ttrans" as lxm { POLY1(lxm) }
| "TMat" as lxm { POLY1(lxm) }
| "TEps" as lxm { POLY1(lxm) }
| "TEps'" as lxm { POLY1(lxm) }
| "TEps''" as lxm { POLY1(lxm) }
| "TEps'''" as lxm { POLY1(lxm) }
| "TFQ" as lxm { POLY2(lxm) }
| "TFE" as lxm { POLY2(lxm) }
| "TDec" as lxm { POLY2(lxm) }
| "lfp" as lxm { POLY1(lxm) }
| "gfp" as lxm { POLY1(lxm) }
| "lfp_t" as lxm { POLY1(lxm) }
| "gfp_t" as lxm { POLY1(lxm) }
| "fp_t" as lxm { POLY1(lxm) }
| "lfp2" as lxm { POLY2(lxm) }
| "gfp2" as lxm { POLY2(lxm) }
| "lfp2_t" as lxm { POLY2(lxm) }
| "gfp2_t" as lxm { POLY2(lxm) }
| "fp2_t" as lxm { POLY2(lxm) }
| "func_ext" as lxm { POLY2(lxm) }
| "eta_eq" as lxm { POLY2(lxm) }
| ['0'-'9']+ as lxm { INT(int_of_string lxm) }
| ['_''\'''a'-'z''A'-'Z']['_''\'''0'-'9''a'-'z''A'-'Z']* as lxm { ID(lxm) }
| eof            { raise Eof }
