open Refutation

val print_stp_tstp : out_channel -> Syntax.stp -> bool -> unit

val ref_coq : out_channel -> refutation -> unit

val ref_tstp : out_channel -> refutation -> unit

val ref_coq_spfterm : out_channel -> refutation -> unit

val ref_isabellehol : out_channel -> refutation -> unit
