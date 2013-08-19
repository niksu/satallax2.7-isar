type formula =
  (* Appl function argument_list: *)
    Appl of formula * formula list
  (* Symbol name: *)
  | Symbol of string

let dictionary = ref (Hashtbl.create 0)

let symbol_transform = ref (fun x -> x)

let rec to_string_default = ref (fun func args -> func^"("^(String.concat ", " (List.map to_string args))^")")

and to_string f =
  match f with
    Appl (Symbol func, args)  -> if Hashtbl.mem !dictionary func
                                then (Hashtbl.find !dictionary func) args
                                else (!to_string_default) func args
  | Appl (func, args)         -> "("^(String.concat " " (List.map to_string (func::args)))^")"
  | Symbol s                  -> (!symbol_transform) s

let infix op args = "("^(String.concat op (List.map to_string args))^")"

let make_list args = "["^(String.concat ", " (List.map to_string args))^"]"

let strip_paren lparen rparen s =
  if String.sub s 0 1 = lparen & String.sub s ((String.length s) - 1) 1 = rparen
  then String.sub s 1 ((String.length s) - 2)
  else s

let tptp_special = [
  ("|", infix " | ");
  ("&", infix " & ");
  ("~|", infix " ~| ");
  ("~&", infix " ~& ");
  ("@", infix " @ ");
  ("*", infix " * ");
  ("+", infix " + ");
  (">", infix ">");
  ("=", infix " = ");
  ("!=", infix " != ");
  ("<=>", infix " <=> ");
  ("<~>", infix " <~> ");
  ("=>", infix " => ");
  ("<=", infix " <= ");
  (":=", infix " := ");
  ("-->", infix " --> ");
  ("$$tuple", make_list);
  ("$$null", fun x -> "");
  ("$$thf",fun x ->
             match x with
               [name;role;f;annotations] -> "thf("^(to_string name)^", "^(to_string role)^", "^(to_string f)^(to_string annotations)^")."
             | _ -> failwith "wrong argument number for \"$$thf\"");
  ("$$fof",fun x ->
             match x with
               [name;role;f;annotations] -> "fof("^(to_string name)^", "^(to_string role)^", "^(to_string f)^(to_string annotations)^")."
             | _ -> failwith "wrong argument number for \"$$thf\"");
  ("$$cnf",fun x ->
             match x with
               [name;role;f;annotations] -> "cnf("^(to_string name)^", "^(to_string role)^", "^(to_string f)^(to_string annotations)^")."
             | _ -> failwith "wrong argument number for \"$$cnf\"");
  ("$$typed_var",fun x ->
             match x with
               [var;t] -> (to_string var)^": "^(to_string t)
             | _ -> failwith "wrong argument number for \"$$typed_var\"");
  ("$$type_formula",fun x ->
             match x with
               [f;t] -> (to_string f)^": "^(to_string t)
             | _ -> failwith "wrong argument number for \"$$type_formula\"");
  ("$$annotations",fun x ->
             match x with
               [source;opt] -> ", "^(to_string source)^(to_string opt)
             | _ -> failwith "wrong argument number for \"$$annotations\"");
  ("$$letrec",fun x ->
             match x with
               [lets;f] -> (to_string lets)^(to_string f)
             | _ -> failwith "wrong argument number for \"$$letrec\"");
  ("$$useful_info",fun x ->
             match x with
               [info] -> ", "^(to_string info)
             | _ -> failwith "wrong argument number for \"$$useful_info\""); 
  ("$$poslit",fun x ->
             match x with
               [lit] -> strip_paren "(" ")" (to_string lit)
             | _ -> failwith "wrong argument number for \"$$poslit\"");
  ("$$neglit",fun x ->
             match x with
               [lit] -> "~"^(strip_paren "(" ")" (to_string lit))
             | _ -> failwith "wrong argument number for \"$$neglit\"");
  ("$$formula_selection",fun x ->
             match x with
               [info] -> ", "^(to_string info)
             | _ -> failwith "wrong argument number for \"$$formula_selection\"");
  (":",fun x ->
             match x with
               [t1;t2] -> (to_string t1)^": "^(to_string t2)
             | _ -> failwith "wrong argument number for \":\"");
  ("$$include",fun x ->
             match x with
               [file;select] -> "include("^(to_string file)^(to_string select)^")."
             | _ -> failwith "wrong argument number for \"$$include\"");
  ("$$quantified",fun x ->
             match x with
               [quant;vars;body] -> "("^(to_string quant)^(to_string vars)^":"^(to_string body)^")"
             | _ -> failwith "wrong argument number for \"$$quantified\"");
  ]

let set_format f =
  match String.lowercase f with
    "plain" -> Hashtbl.clear !dictionary
  | "tptp" -> (Hashtbl.clear !dictionary;
               List.iter (fun (name,func) -> Hashtbl.add !dictionary name func) tptp_special)
  | _ -> failwith ("set_format: There's no format \""^f^"\".")

let _ = set_format "tptp"
