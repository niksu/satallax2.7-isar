(*** File: tptp_lexer.mll ***)
(* tptp_parser.mly file written by Frank Theiss for Chris Benzmueller's LEO-II *)
(* Satallax October 2010 *)
{
  open Tptp_parser
  open Lexing
  exception Eof

  let incr_lineno lexbuf i =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <- { pos with
      pos_lnum = pos.pos_lnum + i;
      pos_bol = pos.pos_cnum;
    }

  (* HACK: newlines are not explicit in multiline comments,
   * so we need to count them. Otherwise any multiline comment
   * counts a one line, which gives wrong line numbers in the
   * parser's error reporting. *)
  open String
  let count_newlines str =
  	let idx i = try (index_from str i '\n') with Not_found -> -1 in
  	let lindex = ref 0 in
  	let count = ref 0 in
  	while (idx !lindex) >= 0 do
  		count := !count + 1;
  		lindex := idx !lindex + 1
  	done;
  	!count
}




let comment_line =            ['%'][^'\n']*
let not_star_slash =          ([^'*']*['*']['*']*[^'/''*'])*[^'*']*
let comment_block =           ['/']['*'](not_star_slash)['*']['*']*['/']
let comment =                 (comment_line)|(comment_block)

let sq_char =                 (['\032'-'\038''\040'-'\091''\093'-'\126']|['\\']['\'''\\'])
let single_quoted =           ['\''](sq_char)(sq_char)*['\'']

let do_char =                 (['\032'-'\033''\035'-'\091''\093'-'\126']|['\\']['"''\\'])
let distinct_object =         ['"'](do_char)(do_char)*['"']


(* character classes *)

let dollar =                  ['$']
let printable_char =          ['\032'-'\126']
let viewable_char =           (printable_char|['\n'])
let upper_alpha =             ['A'-'Z']
let lower_alpha =             ['a'-'z']
let numeric =                 ['0'-'9']
let non_zero_numeric =        ['1'-'9']
let alpha_numeric =           (lower_alpha|upper_alpha|numeric|['_'])


(* numbers *)

let sign =                    ['+''-']
let exponent =                ['E''e']
let dot_decimal =             ['.'](numeric)(numeric)*
let decimal_natural =         (['0']|(non_zero_numeric)(numeric)*)
let signed_decimal =          (sign)(decimal_natural)
let decimal =                 (signed_decimal|decimal_natural)
let decimal_fraction =        (decimal)(dot_decimal)
let decimal_exponent =        (decimal|decimal_fraction)(exponent)(decimal)

let unsigned_integer =        (decimal_natural)
let signed_integer =          (sign)(unsigned_integer)
let real =                    (decimal_fraction|decimal_exponent)

(* misc *)

let sigma =                   ['?']['*']
let pi =                      ['!']['>']
let vline =                   ['|']
let star =                    ['*']
let plus =                    ['+']
let arrow =                   ['>']
let lower_word =              (lower_alpha)(alpha_numeric)*
let upper_word =              (upper_alpha)(alpha_numeric)*
let dollar_word =             (dollar)(lower_word)
let dollar_dollar_word =      (dollar)(dollar)(lower_word)



rule token = parse
  | '[' {LBrkt}
  | ']' {RBrkt}
  | '(' {LParen}
  | ')' {RParen}
  | ',' {Comma}
  | '.' {Period}
  | ':' {Colon}
  | '&' {Ampersand}
  | '@' {At}
  | '~' {Tilde}
  | '^' {Caret}
  | '?' {Question}
  | '!' {Exclamation}
  | '=' {Equal}

  | vline {Vline}
  | star {Star}
  | plus {Plus}
  | arrow {Arrow}

  | ":=" {Assign}
  | "!=" {Nequal}
  | "-->" {Longarrow}
  | "<=>" {Iff}
  | "<=" {If}
  | "=>" {Implies}
  | "<~>" {Niff}
  | "~|" {Nor}
  | "~&" {Nand}
  | sigma {Sigma}
  | pi {Pi}
  | "!!" {Fforall}
  | "??" {Eexists}

  | "$thf" {Dollar_thf}
  | "$fof" {Dollar_fof}
  | "$cnf" {Dollar_cnf}
  | "$fot" {Dollar_fot}

  | "thf" {Thf}
  | "fof" {Fof}
  | "cnf" {Cnf}

  | "include" {Include}
  
  | upper_word as str       { Upper_word str }
  | lower_word as str       { Lower_word str }
  | single_quoted as str    { Single_quoted str }
  | dollar_word as str      { Dollar_word str }
  | dollar_dollar_word as str { Dollar_dollar_word str }
  | distinct_object as str  { Distinct_object str }

  | signed_integer as str   { Signed_integer str }
  | unsigned_integer as str { Unsigned_integer str }
  | real as str             { Real str }

  | comment as str  { incr_lineno lexbuf (count_newlines str); token lexbuf }
  | ['\n'] { incr_lineno lexbuf 1; token lexbuf }
  | [' ' '\t']    { token lexbuf }
  | ['\000'-'\032']|['\127']    { token lexbuf }
  | ['\033'-'\126']    { Unrecognized }

  | "@+" {Choice} (* Chad, Oct 2010 *)

  | eof { EOF }

