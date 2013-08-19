type token =
  | DEQ
  | COLON
  | SEMICOLON
  | COMMA
  | DARR
  | LPAREN
  | RPAREN
  | EQ
  | NEQ
  | PROP
  | OPENCOM
  | CLOSECOM
  | REQUIRE
  | EXPORT
  | SECTION
  | END
  | ALL
  | EX
  | EXU
  | IMP
  | LAM
  | CONJ
  | DISJ
  | IFF
  | NEG
  | FALSE
  | TRUE
  | BLANK
  | LLET
  | IN
  | SAR
  | INDTYPE
  | PROPTYPE
  | MEM
  | NMEM
  | SUBQ
  | NSUBQ
  | VAR
  | HYP
  | BLET
  | PARAM
  | AXIOM
  | DEF
  | THEOREM
  | EXACT
  | QED
  | CONJECTURE of (int)
  | DOT of (int)
  | POLY1 of (string)
  | POLY2 of (string)
  | NARY1 of (string)
  | NARY2 of (string)
  | INT of (int)
  | ID of (string)

val documentitem :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> unit
