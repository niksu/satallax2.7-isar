type formula =
  (* Appl function argument_list: *)
    Appl of formula * formula list
  (* Symbol name: *)
  | Symbol of string

val dictionary : (string,formula list -> string) Hashtbl.t ref

val to_string : formula -> string

val to_string_default : (string -> formula list -> string) ref

val symbol_transform : (string -> string) ref

val set_format : string -> unit
