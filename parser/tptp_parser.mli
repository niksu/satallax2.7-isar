type token =
  | Unrecognized
  | LBrkt
  | RBrkt
  | LParen
  | RParen
  | Comma
  | Period
  | Colon
  | Ampersand
  | At
  | Vline
  | Star
  | Plus
  | Arrow
  | Tilde
  | Caret
  | Question
  | Exclamation
  | Equal
  | Nequal
  | Iff
  | Implies
  | If
  | Niff
  | Nor
  | Nand
  | Pi
  | Sigma
  | Fforall
  | Eexists
  | Assign
  | Longarrow
  | Thf
  | Fof
  | Cnf
  | Dollar_thf
  | Dollar_fof
  | Dollar_cnf
  | Dollar_fot
  | Choice
  | Include
  | Upper_word of (string)
  | Lower_word of (string)
  | Single_quoted of (string)
  | Dollar_word of (string)
  | Dollar_dollar_word of (string)
  | Distinct_object of (string)
  | Real of (string)
  | Unsigned_integer of (string)
  | Signed_integer of (string)
  | EOF

val tptp_file :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Formula.formula list
val tptp_input :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Formula.formula
val formula_data :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Formula.formula
