open Syntax
open Refutation

exception TranslateFailure

(* eager_rewriting*)
val eager_translate : (trm*trm) list -> refutation -> refutation

(* lazy_rewriting*)
val lazy_translate : (trm*trm) list -> refutation -> refutation

(* safe_translate : Chad - Aug 2011 - Intended to work in every case, but generally gives the worst proof. It's a safety net. *)
val safe_translate : (trm*trm) list -> refutation -> refutation

