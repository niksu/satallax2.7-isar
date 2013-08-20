(* File: syntax.ml *)
(* Author: Chad E Brown *)
(* Created: March 2008/September 2008 *)

open String

exception ParsingError of int * int * int * int * string
exception GenericSyntaxError of string
exception DeclareInd

type pretrm =
    PName of string
  | PType | PPropTp | PIndTp | PIntTp | PRealTp | PTrue | PFalse | PIff | PNIff | PImplies | PRevImplies | POr | PNOr | PAnd | PNAnd | PEq | PNEq | PNeg | PForall | PExists
  | PInt of int
  | PReal of float
  | PAp of pretrm * pretrm
  | PULam of string list * pretrm
  | PLam of ((string * pretrm) list) * pretrm
  | PAll of ((string * pretrm) list) * pretrm
  | PEx of ((string * pretrm) list) * pretrm
  | PExU of string * pretrm * pretrm
  | PChoice of (string * pretrm) * pretrm
  | PAr of pretrm * pretrm
  | POf of pretrm * pretrm
  | PDef of pretrm * pretrm
  | PLet of string * pretrm * pretrm
  | PTLet of string * pretrm * pretrm * pretrm

type prectx = (string option * pretrm option * pretrm option) list

let rec prectx_lam c m =
  match c with
  | (Some x,Some a,None)::c' -> prectx_lam c' (PLam([(x,a)],m))
  | (Some x,_,Some n)::c' -> prectx_lam c' (PLet(x,n,m))
  | (None,Some p,None)::c' -> prectx_lam c' m
  | _::_ -> raise (GenericSyntaxError "Impossible prectx case")
  | [] -> m

let rec prectx_all c m =
  match c with
  | (Some x,Some a,None)::c' -> prectx_all c' (PAll([(x,a)],m))
  | (Some x,_,Some n)::c' -> prectx_all c' (PLet(x,n,m))
  | (None,Some p,None)::c' -> prectx_all c' (PAp(PAp(PImplies,p),m))
  | _::_ -> raise (GenericSyntaxError "Impossible prectx case")
  | [] -> m

let rec prectx_ar c m =
  match c with
  | (Some x,Some a,None)::c' -> prectx_ar c' (PAr(a,m))
  | (Some x,_,Some n)::c' -> prectx_ar c' m
  | (None,Some p,None)::c' -> prectx_ar c' m
  | _::_ -> raise (GenericSyntaxError "Impossible prectx case")
  | [] -> m

let rec pretrm_str m =
  match m with
  | PName x -> x
  | PType -> "$type"
  | PPropTp -> "$o"
  | PIndTp -> "$i"
  | PIntTp -> "$int"
  | PRealTp -> "$real"
  | PTrue -> "$true"
  | PFalse -> "$false"
  | PIff -> "$iff"
  | PNIff -> "$niff"
  | PImplies -> "$implies"
  | PRevImplies -> "$revimplies"
  | POr -> "$or"
  | PNOr -> "$Nor"
  | PAnd -> "$and"
  | PNAnd -> "$Nand"
  | PEq -> "$eq"
  | PNEq -> "$neq"
  | PNeg -> "~"
  | PForall -> "!!"
  | PExists -> "??"
  | PInt i -> string_of_int i
  | PReal z -> string_of_float z
  | PAp(n,p) -> "(" ^ (pretrm_str n) ^ " @ " ^ (pretrm_str p) ^ ")"
  | PULam(xl,m) -> "(^ [" ^ (String.concat "," xl) ^ "] " ^ (pretrm_str m) ^ ")"
  | PLam(xl,m) -> "(^ [" ^ (String.concat "," (List.map (fun (x,a) -> x ^ ":" ^ (pretrm_str a)) xl)) ^ "] " ^ (pretrm_str m) ^ ")"
  | PAll(xl,m) -> "(! [" ^ (String.concat "," (List.map (fun (x,a) -> x ^ ":" ^ (pretrm_str a)) xl)) ^ "] " ^ (pretrm_str m) ^ ")"
  | PEx(xl,m) -> "(? [" ^ (String.concat "," (List.map (fun (x,a) -> x ^ ":" ^ (pretrm_str a)) xl)) ^ "] " ^ (pretrm_str m) ^ ")"
  | PExU(x,a,m) -> "(?! [" ^ x ^ ":" ^ (pretrm_str a) ^ "] " ^ (pretrm_str m) ^ ")"
  | PChoice((x,xa),m) -> "(@+ [" ^ x ^ ":" ^ (pretrm_str xa) ^ "] " ^ (pretrm_str m) ^ ")"
  | PAr(n,p) -> "(" ^ (pretrm_str n) ^ " > " ^ (pretrm_str p) ^ ")"
  | POf(n,p) -> "(" ^ (pretrm_str n) ^ " : " ^ (pretrm_str p) ^ ")"
  | PDef(n,p) -> "(" ^ (pretrm_str n) ^ " := " ^ (pretrm_str p) ^ ")"
  | PLet(x,n,p) -> "(" ^ x ^ " := " ^ (pretrm_str n) ^ " in " ^ (pretrm_str p) ^ ")"
  | PTLet(x,a,n,p) -> "(" ^ x ^ " : " ^ (pretrm_str a) ^ " := " ^ (pretrm_str n) ^ " in " ^ (pretrm_str p) ^ ")"

type input =
    DeclareTHF of string * string * pretrm
  | Include of string

type stp = Base of string | Prop | Ar of (stp * stp)

exception ExpectedTypeError of pretrm * stp * stp

type ctx = (string * stp) list

type trm =
    Name of string * stp
  | False | Imp | Forall of stp | Eq of stp | Choice of stp
  | True | Neg | Or | And | Iff | Exists of stp (*** These are normalized away. ***)
  | DB of int * stp
  | Lam of stp * trm
  | Ap of trm * trm

let oo = Ar(Prop,Prop)
let ooo = Ar(Prop,oo)
let imp x y = Ap(Ap(Imp,x),y)
let preneg x = Ap(Neg,x)
let neg x = imp x False
let normneg m =
  begin
    match m with
    | Ap(Ap(Imp,m1),False) -> m1
    | _ -> neg m
  end
let predisj x y = Ap(Ap(Or,x),y)
let preconj x y = Ap(Ap(And,x),y)
let preiff x y = Ap(Ap(Iff,x),y)
let disj x y = imp (neg x) y
let conj x y = neg (imp x (neg y))
let iff x y = Ap(Ap(Eq(Prop),x),y)
let eq a x y = Ap(Ap(Eq(a),x),y)
let forall a m = Ap(Forall(a),Lam(a,m))
let exists a m = neg (forall a (neg m))
let choice a m = Ap(Choice(a),Lam(a,m))

let existsconst a = let ao = Ar(a,Prop) in Lam(ao,neg (forall a (neg (Ap(DB(1,ao),DB(0,ao))))))

let lpar p = if p then "(" else ""

let rpar p = if p then ")" else ""

let rec stp_str_rec a p =
  match a with
    Base(x) -> x
  | Prop -> "prop"
  | Ar(b,c) -> (lpar p) ^ (stp_str_rec b true) ^ ">" ^ (stp_str_rec c false) ^ (rpar p)

let stp_str a = stp_str_rec a false

let rec church_num_body m =
  match m with
  | DB(0,_) -> true
  | Ap(DB(1,_),m1) -> church_num_body m1
  | _ -> false

let rec church_num_body_val m =
  match m with
  | DB(0,_) -> 0
  | Ap(DB(1,_),m1) -> 1 + (church_num_body_val m1)
  | _ -> raise (GenericSyntaxError("Falsely thought I had the body of a Church numeral. BUG"))

let rec trm_str_rec m p =
  match m with
    Name(x,_) -> x
  | Lam(Ar(a1,a2),DB(0,_)) when (a1 = a2) -> "#1:" ^ (stp_str a1) (*** Church Numeral 1 Printed in a special way. - Chad, Feb 2, 2011 ***)
  | Lam(Ar(a1,a2),Lam(a3,m)) when ((a1 = a2) & (a1 = a3) & (church_num_body m)) -> "#" ^ (string_of_int (church_num_body_val m)) ^ ":" ^ (stp_str a1) (*** Church Numerals Printed in a special way. - Chad, Feb 2, 2011 ***)
  | False -> "False"
  | Imp -> "imp"
  | Forall(a) -> "Pi:" ^ (stp_str a)
  | Eq(a) -> "eq:" ^ (stp_str a)
  | Choice(a) -> "Sepsilon:" ^ (stp_str a)
  | DB(i,_) -> "^" ^ (string_of_int i)
  | Lam(a,m) -> (lpar p) ^ "\\_:" ^ (stp_str a) ^ "." ^ (trm_str_rec m false) ^ (rpar p)
  | Ap(m1,m2) ->
      begin
	match m1 with
	| Lam _ -> (lpar p) ^ (trm_str_rec m1 true) ^ " " ^ (trm_str_rec m2 true) ^ (rpar p)
	| _ -> (lpar p) ^ (trm_str_rec m1 false) ^ " " ^ (trm_str_rec m2 true) ^ (rpar p)
      end
(*** If logic has not been normalized away ***)
  | True -> "True"
  | Neg -> "not"
  | Or -> "or"
  | And -> "and"
  | Iff -> "iff"
  | Exists(_) -> "Sigma"

let trm_str m = trm_str_rec m false

(*** This function assumes m is well-typed. ***)
let rec tpof m =
  match m with
    Name(_,a) -> a
  | False -> Prop
  | Imp -> ooo
  | Forall(a) -> Ar(Ar(a,Prop),Prop)
  | Eq(a) -> Ar(a,Ar(a,Prop))
  | Choice(a) -> Ar(Ar(a,Prop),a)
  | DB(_,a) -> a
  | Lam(a,n) -> Ar(a,tpof n)
  | Ap(f,n) ->
      begin
	match (tpof f) with
	  Ar(a,b) -> b
	| _ -> raise (GenericSyntaxError("Non-function applied: " ^ (trm_str m)))
      end
  | _ -> raise (GenericSyntaxError("Unexpected type case - were logical constants normalized away? " ^ (trm_str m)))

let ueq x y = Ap(Ap(Eq(tpof(x)),x),y)

(*** Call this to check application is well typed ***)
let ap (m,n) =
  match (tpof m,tpof n) with
  | (Ar(a,b),c) when a = c -> Ap(m,n)
  | (a,c) -> raise (GenericSyntaxError("Ill typed application (" ^ (trm_str m) ^ " : " ^ (stp_str a) ^ ") @ (" ^ (trm_str n) ^ " : " ^ (stp_str c) ^ ")"))

(*** Print preterms as Coq ***)
let coqify_name_1 x =
  let r = ref "" in
  if (x = "$i") then r := "i" else
  begin
    let fst = ref true in
    String.iter
      (fun c ->
	let co = Char.code c in
	if (((co >= 65) && (co <= 90)) || ((co >= 97) && (co <= 122))) then
	  begin
	    fst := false;
	    r := (!r) ^ (Char.escaped c)
	  end
	else
	  begin
	    if ((!fst) && (co <> 95)) then r := "_";
	    fst := false;
	    if ((co >= 48) && (co <= 57)) then
	      r := (!r) ^ (Char.escaped c)
	    else if (co = 39) then
	      r := (!r) ^ "'"
	    else if (co = 95) then
	      r := (!r) ^ "_";
	    (*** omit any other characters, relying on coqify_name_0 to ensure it's fresh ***)
	  end
      )
      x;
    if ((!r) = "_") then r := "_X";
  end;
  r

let coqify_name_0 x h =
  let r = coqify_name_1 x in
  while (Hashtbl.mem h (!r)) do
    r := (!r) ^ "'"; (*** add primes until it's fresh ***)
  done;
  (!r)

let coqify_name x h1 h2 =
  let y = coqify_name_0 x h2 in
  Hashtbl.add h1 x y;
  Hashtbl.add h2 y ();
  y
  
let rec print_stp_coq c m h p = (*FIXME this is also defined in coq.ml*)
  match m with
  | Base x ->
      Printf.fprintf c "%s" (Hashtbl.find h x)
  | Prop ->
      Printf.fprintf c "o"
  | Ar(a,b) ->
      begin
	if p then Printf.fprintf c "(";
	print_stp_coq c a h true;
	Printf.fprintf c " --> ";
	print_stp_coq c b h false;
	if p then Printf.fprintf c ")"
      end

(*
let rec print_stp_isar c m h p =
  match m with
    | Base x ->
	      let x = try (Hashtbl.find h x) with Not_found -> failwith("print_stp_isar can't find coqname of "^x) in
          Printf.fprintf c "%s" x
    | Prop ->
        Printf.fprintf c "o"
    | Ar(a,b) ->
        begin
	        if p then Printf.fprintf c "(";
	        print_stp_isar c a h true;
	        Printf.fprintf c " => ";
	        print_stp_isar c b h false;
	        if p then Printf.fprintf c ")"
        end
*)
let rec print_stp_isar c m p =
  match m with
    | Base x ->
        if x <> "$i" then
          Printf.fprintf c "%s_ty"(*FIXME suffix hack*) x
        else
          Printf.fprintf c "i"
    | Prop ->
        Printf.fprintf c "o"
    | Ar(a,b) ->
        begin
	        if p then Printf.fprintf c "(";
	        print_stp_isar c a true;
	        Printf.fprintf c "=>";
	        print_stp_isar c b false;
	        if p then Printf.fprintf c ")";
	        flush c
        end

let rec print_pretrm_coq c m h hu lp rp =
  match m with
  | PName x ->
      Printf.fprintf c "%s" (Hashtbl.find h x)
  | PType -> Printf.fprintf c "SType"
  | PPropTp -> Printf.fprintf c "o"
  | PIndTp ->
      Printf.fprintf c "%s" (Hashtbl.find h "$i")
  | PTrue -> Printf.fprintf c "True"
  | PFalse -> Printf.fprintf c "False"
  | PAp(PNeg,m1) ->
      if ((lp < 0) && (rp < 30)) then
	begin
	  Printf.fprintf c "~ ";
	  print_pretrm_coq c m1 h hu 30 rp;
	end
      else
	begin
	  Printf.fprintf c "(~ ";
	  print_pretrm_coq c m1 h hu 30 (-1);
	  Printf.fprintf c ")";
	end
  | PAp(PForall,m1) ->
      if ((lp < 0) && (rp < 0)) then
	begin
	  Printf.fprintf c "SPi _ ";
	  print_pretrm_coq c m1 h hu (-1) (-1);
	end
      else
	begin
	  Printf.fprintf c "(SPi _ ";
	  print_pretrm_coq c m1 h hu (-1) (-1);
	  Printf.fprintf c ")";
	end
  | PAp(PExists,m1) ->
      if ((lp < 0) && (rp < 0)) then
	begin
	  Printf.fprintf c "SSigma _ ";
	  print_pretrm_coq c m1 h hu (-1) (-1);
	end
      else
	begin
	  Printf.fprintf c "(SSigma _ ";
	  print_pretrm_coq c m1 h hu (-1) (-1);
	  Printf.fprintf c ")";
	end
  | PAp(PAp(PImplies,m1),m2) ->
      if ((lp < 17) && (rp < 16)) then
	begin
	  print_pretrm_coq c m1 h hu lp 17;
	  Printf.fprintf c " -> ";
	  print_pretrm_coq c m2 h hu 16 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  print_pretrm_coq c m1 h hu (-1) 17;
	  Printf.fprintf c " -> ";
	  print_pretrm_coq c m2 h hu 16 (-1);
	  Printf.fprintf c ")";
	end
  | PAp(PAp(PRevImplies,m2),m1) ->
      if ((lp < 17) && (rp < 16)) then
	begin
	  print_pretrm_coq c m1 h hu lp 17;
	  Printf.fprintf c " -> ";
	  print_pretrm_coq c m2 h hu 16 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  print_pretrm_coq c m1 h hu (-1) 17;
	  Printf.fprintf c " -> ";
	  print_pretrm_coq c m2 h hu 16 (-1);
	  Printf.fprintf c ")";
	end
  | PAp(PAp(PAnd,m1),m2) ->
      if ((lp < 21) && (rp < 20)) then
	begin
	  print_pretrm_coq c m1 h hu lp 21;
	  Printf.fprintf c " /\\ ";
	  print_pretrm_coq c m2 h hu 20 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  print_pretrm_coq c m1 h hu (-1) 21;
	  Printf.fprintf c " /\\ ";
	  print_pretrm_coq c m2 h hu 20 (-1);
	  Printf.fprintf c ")";
	end
  | PAp(PAp(POr,m1),m2) ->
      if ((lp < 19) && (rp < 18)) then
	begin
	  print_pretrm_coq c m1 h hu lp 19;
	  Printf.fprintf c " \\/ ";
	  print_pretrm_coq c m2 h hu 18 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  print_pretrm_coq c m1 h hu (-1) 19;
	  Printf.fprintf c " \\/ ";
	  print_pretrm_coq c m2 h hu 18 (-1);
	  Printf.fprintf c ")";
	end
  | PAp(PAp(PIff,m1),m2) ->
      if ((lp < 14) && (rp < 14)) then
	begin
	  print_pretrm_coq c m1 h hu lp 14;
	  Printf.fprintf c " <-> ";
	  print_pretrm_coq c m2 h hu 14 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  print_pretrm_coq c m1 h hu (-1) 14;
	  Printf.fprintf c " <-> ";
	  print_pretrm_coq c m2 h hu 14 (-1);
	  Printf.fprintf c ")";
	end
  | PAp(PAp(PEq,m1),m2) ->
      if ((lp < 40) && (rp < 40)) then
	begin
	  print_pretrm_coq c m1 h hu lp 40;
	  Printf.fprintf c " = ";
	  print_pretrm_coq c m2 h hu 40 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  print_pretrm_coq c m1 h hu (-1) 40;
	  Printf.fprintf c " = ";
	  print_pretrm_coq c m2 h hu 40 (-1);
	  Printf.fprintf c ")";
	end
  | PAp(PAp(PNEq,m1),m2) ->
      if (rp >= 40) then Printf.fprintf c "(";
      Printf.fprintf c "~ (";
      print_pretrm_coq c m1 h hu (-1) 40;
      Printf.fprintf c " = ";
      print_pretrm_coq c m2 h hu 40 (-1);
      Printf.fprintf c ")";
      if (rp >= 40) then Printf.fprintf c ")";
  | PAp(PAp(PNIff,m1),m2) ->
      if (rp >= 30) then Printf.fprintf c "(";
      Printf.fprintf c "~ (";
      print_pretrm_coq c m1 h hu (-1) 14;
      Printf.fprintf c " <-> ";
      print_pretrm_coq c m2 h hu 14 (-1);
      Printf.fprintf c ")";
      if (rp >= 30) then Printf.fprintf c ")";
  | PAp(PAp(PNAnd,m1),m2) ->
      if (rp >= 30) then Printf.fprintf c "(";
      Printf.fprintf c "~ (";
      print_pretrm_coq c m1 h hu (-1) 20;
      Printf.fprintf c " //\ ";
      print_pretrm_coq c m2 h hu 21 (-1);
      Printf.fprintf c ")";
      if (rp >= 30) then Printf.fprintf c ")";
  | PAp(PAp(PNOr,m1),m2) ->
      if (rp >= 30) then Printf.fprintf c "(";
      Printf.fprintf c "~ (";
      print_pretrm_coq c m1 h hu (-1) 18;
      Printf.fprintf c " \\/ ";
      print_pretrm_coq c m2 h hu 19 (-1);
      Printf.fprintf c ")";
      if (rp >= 30) then Printf.fprintf c ")";
  | PIff -> Printf.fprintf c "Siff"
  | POr -> Printf.fprintf c "Sor"
  | PAnd -> Printf.fprintf c "Sand"
  | PNeg -> Printf.fprintf c "Snot"
  | PForall ->
      Printf.fprintf c "(SPi _)";
  | PExists ->
      Printf.fprintf c "(SSigma _)";
  | PEq ->
      Printf.fprintf c "(Seq _)";
  | PAp(m1,m2) ->
      if ((lp < 5000) && (rp < 5001)) then
	begin
	  print_pretrm_coq c m1 h hu lp 5000;
	  Printf.fprintf c " ";
	  print_pretrm_coq c m2 h hu 5001 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  print_pretrm_coq c m1 h hu (-1) 5000;
	  Printf.fprintf c " ";
	  print_pretrm_coq c m2 h hu 5001 (-1);
	  Printf.fprintf c ")";
	end
  | PAr(m1,m2) ->
      if ((lp < 71) && (rp < 70)) then
	begin
	  print_pretrm_coq c m1 h hu lp 71;
	  Printf.fprintf c " --> ";
	  print_pretrm_coq c m2 h hu 70 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  print_pretrm_coq c m1 h hu (-1) 71;
	  Printf.fprintf c " --> ";
	  print_pretrm_coq c m2 h hu 70 (-1);
	  Printf.fprintf c ")";
	end
  | POf(n,p) -> print_pretrm_coq c n h hu lp rp
(***  | PDef(n,p) -> print_pretrm_coq c n h hu lp rp ***)
  | PULam(xl,m) ->
      begin
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c "(";
	begin
	  Printf.fprintf c "fun";
	  print_ulam_coq c xl m h hu
	end;
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c ")";
      end
  | PLam(xl,m) ->
      begin
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c "(";
	begin
	  Printf.fprintf c "fun";
	  print_lam_coq c xl m h hu
	end;
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c ")";
      end
  | PAll(xl,m) ->
      begin
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c "(";
	begin
	  Printf.fprintf c "forall";
	  print_all_coq c xl m h hu
	end;
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c ")";
      end
  | PEx(xl,m) ->
      begin
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c "(";
	begin
	  print_ex_coq c xl m h hu
	end;
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c ")";
      end
  | PChoice((x,xa),m) ->
      begin
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c "(";
	begin
	  let y = coqify_name x h hu in
	  Hashtbl.remove h x; (*** pops y from the values of x to print domain ***)
	  Hashtbl.remove hu y; (*** free y to print the domain ***)
	  Printf.fprintf c "Sepsilon (fun ";
	  Printf.fprintf c " %s" y;
	  Printf.fprintf c ":";
	  print_pretrm_coq c xa h hu (-1) (-1);
	  Hashtbl.add h x y; (*** put y back on ***)
	  Hashtbl.add hu y (); (*** put y back on ***)
	  Printf.fprintf c " => ";
	  print_pretrm_coq c m h hu (-1) (-1);
	  Hashtbl.remove h x; (*** pops y from the values of x ***)
	  Hashtbl.remove hu y; (*** free y to be used later ***)
	  Printf.fprintf c ")";
	end;
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c ")";
      end
  | _ -> raise (GenericSyntaxError ("Unknown pretrm case print Coq version : " ^ (pretrm_str m)))
and print_ulam_coq c xl m h hu =
  match xl with
    (x::xr) ->
      begin
	let y = coqify_name x h hu in
	Hashtbl.remove h x; (*** pops y from the values of x to print domain ***)
	Hashtbl.remove hu y; (*** free y to print the domain ***)
	Printf.fprintf c " ";
	Printf.fprintf c "%s" y;
	Hashtbl.add h x y; (*** put y back on ***)
	Hashtbl.add hu y (); (*** put y back on ***)
	print_ulam_coq c xr m h hu;
	Hashtbl.remove h x; (*** pops y from the values of x ***)
	Hashtbl.remove hu y; (*** free y to be used later ***)
      end
  | [] ->
      begin
	Printf.fprintf c " => ";
	print_pretrm_coq c m h hu (-1) (-1)
      end
and print_lam_coq c xl m h hu =
  match xl with
    ((x,a)::xr) ->
      begin
	let y = coqify_name x h hu in
	Hashtbl.remove h x; (*** pops y from the values of x to print domain ***)
	Hashtbl.remove hu y; (*** free y to print the domain ***)
	Printf.fprintf c " ("; Printf.fprintf c "%s" y; Printf.fprintf c ":"; print_pretrm_coq c a h hu (-1) (-1); Printf.fprintf c ")";
	Hashtbl.add h x y; (*** put y back on ***)
	Hashtbl.add hu y (); (*** put y back on ***)
	print_lam_coq c xr m h hu;
	Hashtbl.remove h x; (*** pops y from the values of x ***)
	Hashtbl.remove hu y; (*** free y to be used later ***)
      end
  | [] ->
      begin
	Printf.fprintf c " => ";
	print_pretrm_coq c m h hu (-1) (-1)
      end
and print_all_coq c xl m h hu =
  match xl with
    ((x,a)::xr) ->
      begin
	let y = coqify_name x h hu in
	Hashtbl.remove h x; (*** pops y from the values of x to print domain ***)
	Hashtbl.remove hu y; (*** free y to print the domain ***)
	Printf.fprintf c " ("; Printf.fprintf c "%s" y; Printf.fprintf c ":"; print_pretrm_coq c a h hu (-1) (-1); Printf.fprintf c ")";
	Hashtbl.add h x y; (*** put y back on ***)
	Hashtbl.add hu y (); (*** put y back on ***)
	print_all_coq c xr m h hu;
	Hashtbl.remove h x; (*** pops y from the values of x ***)
	Hashtbl.remove hu y; (*** free y to be used later ***)
      end
  | [] ->
      begin
	Printf.fprintf c ", ";
	print_pretrm_coq c m h hu (-1) (-1)
      end
and print_ex_coq c xl m h hu =
  match xl with
    ((x,a)::xr) ->
      begin
	let y = coqify_name x h hu in
	Hashtbl.remove h x; (*** pops y from the values of x to print domain ***)
	Hashtbl.remove hu y; (*** free y to print the domain ***)
	Printf.fprintf c "exists"; Printf.fprintf c " %s" y; Printf.fprintf c ":"; print_pretrm_coq c a h hu (-1) (-1); Printf.fprintf c ", ";
	Hashtbl.add h x y; (*** put y back on ***)
	Hashtbl.add hu y (); (*** put y back on ***)
	print_ex_coq c xr m h hu;
	Hashtbl.remove h x; (*** pops y from the values of x ***)
	Hashtbl.remove hu y; (*** free y to be used later ***)
      end
  | [] ->
      begin
	print_pretrm_coq c m h hu (-1) (-1)
      end

(*FIXME repeating the code is a bad idea. this is repeated from print_pretrm_coq*)
let rec print_pretrm_isar c m h hu lp rp =
  match m with
    | PName x ->
        Printf.fprintf c "%s" (Hashtbl.find h x)
    | PType -> (* Printf.fprintf c "SType" *) ()
    | PPropTp -> Printf.fprintf c "o"
    | PIndTp ->
        Printf.fprintf c "%s" (Hashtbl.find h "$i") (*FIXME what's set as $i? where is this set?*)  
    | PTrue -> Printf.fprintf c "True"
    | PFalse -> Printf.fprintf c "False"
    | PAp(PNeg,m1) ->
        if ((lp < 0) && (rp < 30)) then
	        begin
	          Printf.fprintf c "~ ";
	          print_pretrm_isar c m1 h hu 30 rp;
	        end
        else
	        begin
	          Printf.fprintf c "(~ ";
	          print_pretrm_isar c m1 h hu 30 (-1);
	          Printf.fprintf c ")";
	        end
    | PAp(PForall,m1) ->
        if ((lp < 0) && (rp < 0)) then
	        begin
	          (* Printf.fprintf c "SPi _ "; *)
	          Printf.fprintf c "All";
	          print_pretrm_isar c m1 h hu (-1) (-1);
	        end
        else
	        begin
	          (* Printf.fprintf c "(SPi _ "; *)
	          Printf.fprintf c "(All ";
	          print_pretrm_isar c m1 h hu (-1) (-1);
	          Printf.fprintf c ")";
	        end
    | PAp(PExists,m1) ->
        if ((lp < 0) && (rp < 0)) then
	        begin
	          (* Printf.fprintf c "SSigma _ "; *)
	          Printf.fprintf c "Ex ";
	          print_pretrm_isar c m1 h hu (-1) (-1);
	        end
        else
	        begin
	          (* Printf.fprintf c "(SSigma _ "; *)
	          Printf.fprintf c "(Ex ";
	          print_pretrm_isar c m1 h hu (-1) (-1);
	          Printf.fprintf c ")";
	        end
    | PAp(PAp(PImplies,m1),m2) ->
        if ((lp < 17) && (rp < 16)) then
	        begin
	          print_pretrm_isar c m1 h hu lp 17;
	          Printf.fprintf c " --> ";
	          print_pretrm_isar c m2 h hu 16 rp;
	        end
        else
	        begin
	          Printf.fprintf c "(";
	          print_pretrm_isar c m1 h hu (-1) 17;
	          Printf.fprintf c " --> ";
	          print_pretrm_isar c m2 h hu 16 (-1);
	          Printf.fprintf c ")";
	        end
    | PAp(PAp(PRevImplies,m2),m1) ->
        if ((lp < 17) && (rp < 16)) then
	        begin
	          print_pretrm_isar c m1 h hu lp 17;
	          Printf.fprintf c " --> ";
	          print_pretrm_isar c m2 h hu 16 rp;
	        end
        else
	        begin
	          Printf.fprintf c "(";
	          print_pretrm_isar c m1 h hu (-1) 17;
	          Printf.fprintf c " --> ";
	          print_pretrm_isar c m2 h hu 16 (-1);
	          Printf.fprintf c ")";
	        end
    | PAp(PAp(PAnd,m1),m2) ->
        if ((lp < 21) && (rp < 20)) then
	        begin
	          print_pretrm_isar c m1 h hu lp 21;
	          Printf.fprintf c " & ";
	          print_pretrm_isar c m2 h hu 20 rp;
	        end
        else
	        begin
	          Printf.fprintf c "(";
	          print_pretrm_isar c m1 h hu (-1) 21;
	          Printf.fprintf c " & ";
	          print_pretrm_isar c m2 h hu 20 (-1);
	          Printf.fprintf c ")";
	        end
    | PAp(PAp(POr,m1),m2) ->
(*FIXME excluding parentheses can lead to parse problems on the Isabelle side
        if ((lp < 19) && (rp < 18)) then
	        begin
	          print_pretrm_isar c m1 h hu lp 19;
	          Printf.fprintf c " | ";
	          print_pretrm_isar c m2 h hu 18 rp;
	        end
        else
*)
	        begin
	          Printf.fprintf c "(";
	          print_pretrm_isar c m1 h hu (-1) 19;
	          Printf.fprintf c " | ";
	          print_pretrm_isar c m2 h hu 18 (-1);
	          Printf.fprintf c ")";
	        end
    | PAp(PAp(PIff,m1),m2) ->
        if ((lp < 14) && (rp < 14)) then
	        begin
	          print_pretrm_isar c m1 h hu lp 14;
	          Printf.fprintf c " = ";
	          print_pretrm_isar c m2 h hu 14 rp;
	        end
        else
	        begin
	          Printf.fprintf c "(";
	          print_pretrm_isar c m1 h hu (-1) 14;
	          Printf.fprintf c " = ";
	          print_pretrm_isar c m2 h hu 14 (-1);
	          Printf.fprintf c ")";
	        end
    | PAp(PAp(PEq,m1),m2) ->
        if ((lp < 40) && (rp < 40)) then
	        begin
	          print_pretrm_isar c m1 h hu lp 40;
	          Printf.fprintf c " = ";
	          print_pretrm_isar c m2 h hu 40 rp;
	        end
        else
	        begin
	          Printf.fprintf c "(";
	          print_pretrm_isar c m1 h hu (-1) 40;
	          Printf.fprintf c " = ";
	          print_pretrm_isar c m2 h hu 40 (-1);
	          Printf.fprintf c ")";
	        end
    | PAp(PAp(PNEq,m1),m2) ->
        if (rp >= 40) then Printf.fprintf c "(";
        Printf.fprintf c "~ (";
        print_pretrm_isar c m1 h hu (-1) 40;
        Printf.fprintf c " = ";
        print_pretrm_isar c m2 h hu 40 (-1);
        Printf.fprintf c ")";
        if (rp >= 40) then Printf.fprintf c ")";
    | PAp(PAp(PNIff,m1),m2) ->
        if (rp >= 30) then Printf.fprintf c "(";
        Printf.fprintf c "~ (";
        print_pretrm_isar c m1 h hu (-1) 14;
        Printf.fprintf c " = ";
        print_pretrm_isar c m2 h hu 14 (-1);
        Printf.fprintf c ")";
        if (rp >= 30) then Printf.fprintf c ")";
    | PAp(PAp(PNAnd,m1),m2) ->
        if (rp >= 30) then Printf.fprintf c "(";
        Printf.fprintf c "~ (";
        print_pretrm_isar c m1 h hu (-1) 20;
        Printf.fprintf c " & ";
        print_pretrm_isar c m2 h hu 21 (-1);
        Printf.fprintf c ")";
        if (rp >= 30) then Printf.fprintf c ")";
    | PAp(PAp(PNOr,m1),m2) ->
        if (rp >= 30) then Printf.fprintf c "(";
        Printf.fprintf c "~ (";
        print_pretrm_isar c m1 h hu (-1) 18;
        Printf.fprintf c " | ";
        print_pretrm_isar c m2 h hu 19 (-1);
        Printf.fprintf c ")";
        if (rp >= 30) then Printf.fprintf c ")";
    | PIff -> Printf.fprintf c "(op =)"
    | POr -> Printf.fprintf c "(op |)"
    | PAnd -> Printf.fprintf c "(op &)"
    | PNeg -> Printf.fprintf c "Not"
    | PForall ->
        Printf.fprintf c "All";
    | PExists ->
        Printf.fprintf c "Ex";
    | PEq ->
        Printf.fprintf c "(op =)";
    | PAp(m1,m2) ->
        if ((lp < 5000) && (rp < 5001)) then
	        begin
	          print_pretrm_isar c m1 h hu lp 5000;
	          Printf.fprintf c " ";
	          print_pretrm_isar c m2 h hu 5001 rp;
	        end
        else
	        begin
	          Printf.fprintf c "(";
	          print_pretrm_isar c m1 h hu (-1) 5000;
	          Printf.fprintf c " ";
	          print_pretrm_isar c m2 h hu 5001 (-1);
	          Printf.fprintf c ")";
	        end
    | PAr(m1,m2) ->
        if ((lp < 71) && (rp < 70)) then
	        begin
	          print_pretrm_isar c m1 h hu lp 71;
	          Printf.fprintf c " => ";
	          print_pretrm_isar c m2 h hu 70 rp;
	        end
        else
	        begin
	          Printf.fprintf c "(";
	          print_pretrm_isar c m1 h hu (-1) 71;
	          Printf.fprintf c " => ";
	          print_pretrm_isar c m2 h hu 70 (-1);
	          Printf.fprintf c ")";
	        end
    | POf(n,p) -> print_pretrm_isar c n h hu lp rp
(***  | PDef(n,p) -> print_pretrm_isar c n h hu lp rp ***)
    | PULam(xl,m) ->
        begin
	        if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c "(";
	        begin
	          Printf.fprintf c "%% ";
	          print_ulam_isar c xl m h hu
	        end;
	        if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c ")";
        end
    | PLam(xl,m) ->
        begin
	        if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c "(";
	        begin
	          Printf.fprintf c "%% ";
	          print_lam_isar c xl m h hu
	        end;
	        if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c ")";
        end
    | PAll(xl,m) ->
        begin
	        if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c "(";
	        begin
	          Printf.fprintf c "!";
	          print_all_isar c xl m h hu
	        end;
	        if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c ")";
        end
    | PEx(xl,m) ->
        begin
	        if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c "(";
	        begin
	          print_ex_isar c xl m h hu
	        end;
	        if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c ")";
        end
    | PChoice((x,xa),m) ->
        begin
	        if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c "(";
	        begin
	          let y = coqify_name x h hu in
	            Hashtbl.remove h x; (*** pops y from the values of x to print domain ***)
	            Hashtbl.remove hu y; (*** free y to print the domain ***)
	            Printf.fprintf c "Eps (%% ";
	            Printf.fprintf c " %s" y;
	            Printf.fprintf c "::";
	            print_pretrm_isar c xa h hu (-1) (-1);
	            Hashtbl.add h x y; (*** put y back on ***)
	            Hashtbl.add hu y (); (*** put y back on ***)
	            Printf.fprintf c " . ";
	            print_pretrm_isar c m h hu (-1) (-1);
	            Hashtbl.remove h x; (*** pops y from the values of x ***)
	            Hashtbl.remove hu y; (*** free y to be used later ***)
	            Printf.fprintf c ")";
	        end;
	        if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c ")";
        end
    | _ -> raise (GenericSyntaxError ("Unknown pretrm case print Coq version : " ^ (pretrm_str m))) (*FIXME this wasnt changed from the original function*)
and print_ulam_isar c xl m h hu =
  match xl with
      (x::xr) ->
        begin
	        let y = coqify_name x h hu in
	          Hashtbl.remove h x; (*** pops y from the values of x to print domain ***)
	          Hashtbl.remove hu y; (*** free y to print the domain ***)
	          Printf.fprintf c " ";
	          Printf.fprintf c "%s" y;
	          Hashtbl.add h x y; (*** put y back on ***)
	          Hashtbl.add hu y (); (*** put y back on ***)
	          print_ulam_isar c xr m h hu;
	          Hashtbl.remove h x; (*** pops y from the values of x ***)
	          Hashtbl.remove hu y; (*** free y to be used later ***)
        end
    | [] ->
        begin
	        Printf.fprintf c " . ";
	        print_pretrm_isar c m h hu (-1) (-1)
        end
and print_lam_isar c xl m h hu =
  match xl with
      ((x,a)::xr) ->
        begin
	        let y = coqify_name x h hu in
	          Hashtbl.remove h x; (*** pops y from the values of x to print domain ***)
	          Hashtbl.remove hu y; (*** free y to print the domain ***)
	          Printf.fprintf c " ("; Printf.fprintf c "%s" y; Printf.fprintf c "::"; print_pretrm_isar c a h hu (-1) (-1); Printf.fprintf c ")";
	          Hashtbl.add h x y; (*** put y back on ***)
	          Hashtbl.add hu y (); (*** put y back on ***)
	          print_lam_isar c xr m h hu;
	          Hashtbl.remove h x; (*** pops y from the values of x ***)
	          Hashtbl.remove hu y; (*** free y to be used later ***)
        end
    | [] ->
        begin
	        Printf.fprintf c " . ";
	        print_pretrm_isar c m h hu (-1) (-1)
        end
and print_all_isar c xl m h hu =
  match xl with
      ((x,a)::xr) ->
        begin
	        let y = coqify_name x h hu in
	          Hashtbl.remove h x; (*** pops y from the values of x to print domain ***)
	          Hashtbl.remove hu y; (*** free y to print the domain ***)
	          Printf.fprintf c " ("; Printf.fprintf c "%s" y; Printf.fprintf c "::"; print_pretrm_isar c a h hu (-1) (-1); Printf.fprintf c ")";
	          Hashtbl.add h x y; (*** put y back on ***)
	          Hashtbl.add hu y (); (*** put y back on ***)
	          print_all_isar c xr m h hu;
	          Hashtbl.remove h x; (*** pops y from the values of x ***)
	          Hashtbl.remove hu y; (*** free y to be used later ***)
        end
    | [] ->
        begin
	        Printf.fprintf c ". ";
	        print_pretrm_isar c m h hu (-1) (-1)
        end
and print_ex_isar c xl m h hu =
  match xl with
      ((x,a)::xr) ->
        begin
	        let y = coqify_name x h hu in
	          Hashtbl.remove h x; (*** pops y from the values of x to print domain ***)
	          Hashtbl.remove hu y; (*** free y to print the domain ***)
	          Printf.fprintf c "?"; Printf.fprintf c " %s" y; Printf.fprintf c "::"; print_pretrm_isar c a h hu (-1) (-1); Printf.fprintf c ". ";
	          Hashtbl.add h x y; (*** put y back on ***)
	          Hashtbl.add hu y (); (*** put y back on ***)
	          print_ex_isar c xr m h hu;
	          Hashtbl.remove h x; (*** pops y from the values of x ***)
	          Hashtbl.remove hu y; (*** free y to be used later ***)
        end
    | [] ->
        begin
	        print_pretrm_isar c m h hu (-1) (-1)
        end

let rec print_stp_coq2 c m p =
  match m with
  | Base _ ->
      Printf.fprintf c "set"
  | Prop ->
      Printf.fprintf c "prop"
  | Ar(a,b) ->
      begin
	if p then Printf.fprintf c "(";
	print_stp_coq2 c a true;
	Printf.fprintf c " > ";
	print_stp_coq2 c b false;
	if p then Printf.fprintf c ")"
      end

let rec print_pretrm_coq2 c m lp rp =
  match m with
  | PName x ->
      Printf.fprintf c "%s" x
  | PType -> Printf.fprintf c "Type"
  | PPropTp -> Printf.fprintf c "prop"
  | PIndTp ->
      Printf.fprintf c "set"
  | PTrue -> Printf.fprintf c "True"
  | PFalse -> Printf.fprintf c "False"
  | PAp(PNeg,m1) ->
      if ((lp < 0) && (rp < 30)) then
	begin
	  Printf.fprintf c "~ ";
	  print_pretrm_coq2 c m1 30 rp;
	end
      else
	begin
	  Printf.fprintf c "(~ ";
	  print_pretrm_coq2 c m1 30 (-1);
	  Printf.fprintf c ")";
	end
  | PAp(PForall,m1) ->
      if ((lp < 0) && (rp < 0)) then
	begin
	  Printf.fprintf c "(fun p => forall x, p x) ";
	  print_pretrm_coq2 c m1 (-1) (-1);
	end
      else
	begin
	  Printf.fprintf c "((fun p => forall x, p x) ";
	  print_pretrm_coq2 c m1 (-1) (-1);
	  Printf.fprintf c ")";
	end
  | PAp(PExists,m1) ->
      if ((lp < 0) && (rp < 0)) then
	begin
	  Printf.fprintf c "ex _ ";
	  print_pretrm_coq2 c m1 (-1) (-1);
	end
      else
	begin
	  Printf.fprintf c "(ex _ ";
	  print_pretrm_coq2 c m1 (-1) (-1);
	  Printf.fprintf c ")";
	end
  | PAp(PAp(PImplies,m1),m2) ->
      if ((lp < 17) && (rp < 16)) then
	begin
	  print_pretrm_coq2 c m1 lp 17;
	  Printf.fprintf c " -> ";
	  print_pretrm_coq2 c m2 16 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  print_pretrm_coq2 c m1 (-1) 17;
	  Printf.fprintf c " -> ";
	  print_pretrm_coq2 c m2 16 (-1);
	  Printf.fprintf c ")";
	end
  | PAp(PAp(PRevImplies,m2),m1) ->
      if ((lp < 17) && (rp < 16)) then
	begin
	  print_pretrm_coq2 c m1 lp 17;
	  Printf.fprintf c " -> ";
	  print_pretrm_coq2 c m2 16 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  print_pretrm_coq2 c m1 (-1) 17;
	  Printf.fprintf c " -> ";
	  print_pretrm_coq2 c m2 16 (-1);
	  Printf.fprintf c ")";
	end
  | PAp(PAp(PAnd,m1),m2) ->
      if ((lp < 21) && (rp < 20)) then
	begin
	  print_pretrm_coq2 c m1 lp 21;
	  Printf.fprintf c " /\\ ";
	  print_pretrm_coq2 c m2 20 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  print_pretrm_coq2 c m1 (-1) 21;
	  Printf.fprintf c " /\\ ";
	  print_pretrm_coq2 c m2 20 (-1);
	  Printf.fprintf c ")";
	end
  | PAp(PAp(POr,m1),m2) ->
      if ((lp < 19) && (rp < 18)) then
	begin
	  print_pretrm_coq2 c m1 lp 19;
	  Printf.fprintf c " \\/ ";
	  print_pretrm_coq2 c m2 18 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  print_pretrm_coq2 c m1 (-1) 19;
	  Printf.fprintf c " \\/ ";
	  print_pretrm_coq2 c m2 18 (-1);
	  Printf.fprintf c ")";
	end
  | PAp(PAp(PIff,m1),m2) ->
      if ((lp < 14) && (rp < 14)) then
	begin
	  print_pretrm_coq2 c m1 lp 14;
	  Printf.fprintf c " <-> ";
	  print_pretrm_coq2 c m2 14 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  print_pretrm_coq2 c m1 (-1) 14;
	  Printf.fprintf c " <-> ";
	  print_pretrm_coq2 c m2 14 (-1);
	  Printf.fprintf c ")";
	end
  | PAp(PAp(PEq,m1),m2) ->
      if ((lp < 40) && (rp < 40)) then
	begin
	  print_pretrm_coq2 c m1 lp 40;
	  Printf.fprintf c " = ";
	  print_pretrm_coq2 c m2 40 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  print_pretrm_coq2 c m1 (-1) 40;
	  Printf.fprintf c " = ";
	  print_pretrm_coq2 c m2 40 (-1);
	  Printf.fprintf c ")";
	end
  | PAp(PAp(PNEq,m1),m2) ->
      if (rp >= 40) then Printf.fprintf c "(";
      Printf.fprintf c "~ (";
      print_pretrm_coq2 c m1 (-1) 40;
      Printf.fprintf c " = ";
      print_pretrm_coq2 c m2 40 (-1);
      Printf.fprintf c ")";
      if (rp >= 40) then Printf.fprintf c ")";
  | PAp(PAp(PNIff,m1),m2) ->
      if (rp >= 30) then Printf.fprintf c "(";
      Printf.fprintf c "~ (";
      print_pretrm_coq2 c m1 (-1) 14;
      Printf.fprintf c " <-> ";
      print_pretrm_coq2 c m2 14 (-1);
      Printf.fprintf c ")";
      if (rp >= 30) then Printf.fprintf c ")";
  | PAp(PAp(PNAnd,m1),m2) ->
      if (rp >= 30) then Printf.fprintf c "(";
      Printf.fprintf c "~ (";
      print_pretrm_coq2 c m1 (-1) 20;
      Printf.fprintf c " //\ ";
      print_pretrm_coq2 c m2 21 (-1);
      Printf.fprintf c ")";
      if (rp >= 30) then Printf.fprintf c ")";
  | PAp(PAp(PNOr,m1),m2) ->
      if (rp >= 30) then Printf.fprintf c "(";
      Printf.fprintf c "~ (";
      print_pretrm_coq2 c m1 (-1) 18;
      Printf.fprintf c " \\/ ";
      print_pretrm_coq2 c m2 19 (-1);
      Printf.fprintf c ")";
      if (rp >= 30) then Printf.fprintf c ")";
  | PIff -> Printf.fprintf c "iff"
  | POr -> Printf.fprintf c "or"
  | PAnd -> Printf.fprintf c "and"
  | PNeg -> Printf.fprintf c "not"
  | PForall ->
      Printf.fprintf c "(fun p => forall x, p x)";
  | PExists ->
      Printf.fprintf c "(ex _)";
  | PEq ->
      Printf.fprintf c "(eq _)";
  | PAp(m1,m2) ->
      if ((lp < 5000) && (rp < 5001)) then
	begin
	  print_pretrm_coq2 c m1 lp 5000;
	  Printf.fprintf c " ";
	  print_pretrm_coq2 c m2 5001 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  print_pretrm_coq2 c m1 (-1) 5000;
	  Printf.fprintf c " ";
	  print_pretrm_coq2 c m2 5001 (-1);
	  Printf.fprintf c ")";
	end
  | PAr(m1,m2) ->
      if ((lp < 71) && (rp < 70)) then
	begin
	  print_pretrm_coq2 c m1 lp 71;
	  Printf.fprintf c " > ";
	  print_pretrm_coq2 c m2 70 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  print_pretrm_coq2 c m1 (-1) 71;
	  Printf.fprintf c " > ";
	  print_pretrm_coq2 c m2 70 (-1);
	  Printf.fprintf c ")";
	end
  | POf(n,p) -> print_pretrm_coq2 c n lp rp
(***  | PDef(n,p) -> print_pretrm_coq2 c n lp rp ***)
  | PULam(xl,m) ->
      begin
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c "(";
	begin
	  Printf.fprintf c "fun";
	  print_ulam_coq2 c xl m
	end;
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c ")";
      end
  | PLam(xl,m) ->
      begin
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c "(";
	begin
	  Printf.fprintf c "fun";
	  print_lam_coq2 c xl m
	end;
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c ")";
      end
  | PAll(xl,m) ->
      begin
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c "(";
	begin
	  Printf.fprintf c "forall";
	  print_all_coq2 c xl m
	end;
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c ")";
      end
  | PEx(xl,m) ->
      begin
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c "(";
	begin
	  print_ex_coq2 c xl m
	end;
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c ")";
      end
  | PChoice((x,xa),m) ->
      begin
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c "(";
	begin
	  Printf.fprintf c "Eps _ (fun ";
	  Printf.fprintf c " %s" x;
	  Printf.fprintf c ":";
	  print_pretrm_coq2 c xa (-1) (-1);
	  Printf.fprintf c " => ";
	  print_pretrm_coq2 c m (-1) (-1);
	  Printf.fprintf c ")";
	end;
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c ")";
      end
  | PLet(x,m1,m2) ->
      begin
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c "(";
	Printf.fprintf c "let %s := " (if (x = "") then "_" else x);
	print_pretrm_coq2 c m1 (-1) (-1);
	Printf.fprintf c " in ";
	print_pretrm_coq2 c m2 (-1) (-1);
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c ")";
      end
  | PTLet(x,a1,m1,m2) ->
      begin
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c "(";
	Printf.fprintf c "let %s : " (if (x = "") then "_" else x);
	print_pretrm_coq2 c a1 (-1) (-1);
	Printf.fprintf c " := ";
	print_pretrm_coq2 c m1 (-1) (-1);
	Printf.fprintf c " in ";
	print_pretrm_coq2 c m2 (-1) (-1);
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c ")";
      end
  | _ -> raise (GenericSyntaxError ("Unknown pretrm case print Coq version : " ^ (pretrm_str m)))
and print_ulam_coq2 c xl m =
  match xl with
  | (x::xr) when x = "" ->
      begin
	Printf.fprintf c " _";
	print_ulam_coq2 c xr m;
      end
  | (x::xr) ->
      begin
	let y = x in
	Printf.fprintf c " "; Printf.fprintf c "%s" y;
	print_ulam_coq2 c xr m;
      end
  | [] ->
      begin
	Printf.fprintf c " => ";
	print_pretrm_coq2 c m (-1) (-1)
      end
and print_lam_coq2 c xl m =
  match xl with
  | ((x,a)::xr) when x = "" ->
      begin
	Printf.fprintf c " (_"; Printf.fprintf c ":"; print_pretrm_coq2 c a (-1) (-1); Printf.fprintf c ")";
	print_lam_coq2 c xr m;
      end
  | ((x,a)::xr) ->
      begin
	let y = x in
	Printf.fprintf c " ("; Printf.fprintf c "%s" y; Printf.fprintf c ":"; print_pretrm_coq2 c a (-1) (-1); Printf.fprintf c ")";
	print_lam_coq2 c xr m;
      end
  | [] ->
      begin
	Printf.fprintf c " => ";
	print_pretrm_coq2 c m (-1) (-1)
      end
and print_all_coq2 c xl m =
  match xl with
  | ((x,a)::xr) when x = "" ->
      begin
	Printf.fprintf c " (_"; Printf.fprintf c ":"; print_pretrm_coq2 c a (-1) (-1); Printf.fprintf c ")";
	print_all_coq2 c xr m;
      end
  | ((x,a)::xr) ->
      begin
	let y = x in
	Printf.fprintf c " ("; Printf.fprintf c "%s" y; Printf.fprintf c ":"; print_pretrm_coq2 c a (-1) (-1); Printf.fprintf c ")";
	print_all_coq2 c xr m;
      end
  | [] ->
      begin
	Printf.fprintf c ", ";
	print_pretrm_coq2 c m (-1) (-1)
      end
and print_ex_coq2 c xl m =
  match xl with
  | ((x,a)::xr) when x = "" ->
      begin
	Printf.fprintf c "exists _:"; print_pretrm_coq2 c a (-1) (-1); Printf.fprintf c ", ";
	print_ex_coq2 c xr m;
      end
  | ((x,a)::xr) ->
      begin
	let y = x in
	Printf.fprintf c "exists"; Printf.fprintf c " %s" y; Printf.fprintf c ":"; print_pretrm_coq2 c a (-1) (-1); Printf.fprintf c ", ";
	print_ex_coq2 c xr m;
      end
  | [] ->
      begin
	print_pretrm_coq2 c m (-1) (-1)
      end

(*** Shifting, Substitution, Normalization ***)

let rec shift m i j =
  match m with
    DB(k,_) when k < i -> m
  | DB(k,a) -> DB(k + j,a)
  | Lam(a1,m2) -> Lam(a1,shift m2 (i + 1) j)
  | Ap(m1,m2) -> Ap(shift m1 i j,shift m2 i j)
  | _ -> m

let rec subst m i n =
  match m with
    DB(k,_) when k < i -> m
  | DB(k,_) when k = i -> n
  | DB(k,a) -> DB(k - 1,a)
  | Lam(a1,m2) -> Lam(a1,subst m2 (i + 1) (shift n 0 1))
  | Ap(m1,m2) -> Ap(subst m1 i n,subst m2 i n)
  | _ -> m

(*** Simultaneous Substitution ***)
(*** Assumes no dangling deBruijn indices. ***)
let rec simulsubst m s =
  match m with
    DB(k,_) ->
      let n = List.nth s k in
      if (m = n) then m else n
  | Lam(a1,m1) ->
      let n1 = simulsubst m1 ((DB(0,a1))::(List.map (fun n -> shift n 0 1) s)) in
      if (m1 = n1) then m else Lam(a1,n1)
  | Ap(m1,m2) ->
      let n1 = simulsubst m1 s in
      let n2 = simulsubst m2 s in
      if ((m1 = n1) && (m2 = n2)) then m else Ap(n1,n2)
  | _ -> m

let rec namesubst m x n =
  match m with
    Name(y,a) when (x = y) -> n
  | Lam(a1,m1) -> Lam(a1,namesubst m1 x n)
  | Ap(m1,m2) -> Ap(namesubst m1 x n,namesubst m2 x n)
  | _ -> m

let gen_lam_body a m =
  match m with
  | Lam(_,m1) -> m1
  | _ -> Ap(shift m 0 1,DB(0,a))

let rec termNotFreeIn m i =
  match m with
    DB(j,_) when i = j -> false
  | Ap(m1,m2) -> (termNotFreeIn m1 i) && (termNotFreeIn m2 i)
  | Lam(a,m1) -> termNotFreeIn m1 (i + 1)
  | _ -> true

let rec termNotFreeInL m il =
  match m with
    DB(j,_) when (List.mem j il) -> false
  | Ap(m1,m2) -> (termNotFreeInL m1 il) && (termNotFreeInL m2 il)
  | Lam(a,m1) -> termNotFreeInL m1 (List.map (fun i -> i + 1) il)
  | _ -> true

let rec termNoDBs_rec m i =
  match m with
    DB(j,_) -> if (j < i) then true else false
  | Ap(m1,m2) -> (termNoDBs_rec m1 i) && (termNoDBs_rec m2 i)
  | Lam(a,m1) -> termNoDBs_rec m1 (i + 1)
  | _ -> true

let termNoDBs m = termNoDBs_rec m 0

let rec norm1 d m =
  match m with
    Ap(Lam(a,m1),m2) -> (* beta *)
      let (n1,_) = norm1 d m1 in
      let (n2,_) = norm1 d m2 in
      (subst n1 0 n2,true)
  | Lam(_,Ap(m1,DB(0,_))) when (termNotFreeIn m1 0) -> (* eta *)
      (shift m1 0 (- 1),true)
	(*** dneg ***)
  | Ap(Ap(Imp,Ap(Ap(Imp,m1),False)),False) -> (* double negation reduce *)
      let (n1,_) = norm1 d m1 in
      (n1,true)
  | Name(x,_) ->
      begin
	try
	  (Hashtbl.find d x,true)
	with
	| Not_found -> (m,false)
      end
  | Ap(m1,m2) ->
      let (n1,b1) = norm1 d m1 in
      let (n2,b2) = norm1 d m2 in
      if (b1 || b2) then
	(Ap(n1,n2),true)
      else
	(m,false)
  | Lam(a1,m1) ->
      let (n1,b1) = norm1 d m1 in
      if b1 then
	(Lam(a1,n1),true)
      else
	(m,false)
  | _ -> (m,false)

(* beta-eta-delta-dneg *)    
let rec norm d m =
  let (m1,reduced) = norm1 d m in
  if reduced then (norm d m1) else m

let rec betanorm1 d m =
  match m with
    Ap(Lam(a,m1),m2) -> (* beta *)
      let (n1,_) = betanorm1 d m1 in
      let (n2,_) = betanorm1 d m2 in
      (subst n1 0 n2,true)
  | Name(x,_) ->
      begin
	try
	  (Hashtbl.find d x,true)
	with
	| Not_found -> (m,false)
      end
  | Ap(m1,m2) ->
      let (n1,b1) = betanorm1 d m1 in
      let (n2,b2) = betanorm1 d m2 in
      if (b1 || b2) then
	(Ap(n1,n2),true)
      else
	(m,false)
  | Lam(a1,m1) ->
      let (n1,b1) = betanorm1 d m1 in
      if b1 then
	(Lam(a1,n1),true)
      else
	(m,false)
  | _ -> (m,false)
    
(* beta-delta *)    
let rec betanorm d m =
  let (m1,reduced) = betanorm1 d m in
  if reduced then (betanorm d m1) else m

let rec onlybetanorm1 m =
  match m with
    Ap(Lam(a,m1),m2) -> (* onlybeta *)
      let (n1,_) = onlybetanorm1 m1 in
      let (n2,_) = onlybetanorm1 m2 in
      (subst n1 0 n2,true)
  | Ap(m1,m2) ->
      let (n1,b1) = onlybetanorm1 m1 in
      let (n2,b2) = onlybetanorm1 m2 in
      if (b1 || b2) then
	(Ap(n1,n2),true)
      else
	(m,false)
  | Lam(a1,m1) ->
      let (n1,b1) = onlybetanorm1 m1 in
      if b1 then
	(Lam(a1,n1),true)
      else
	(m,false)
  | _ -> (m,false)
    
(* beta (no delta) *)
let rec onlybetanorm m =
  let (m1,reduced) = onlybetanorm1 m in
  if reduced then (onlybetanorm m1) else m

let rec logicnorm1 m =
  match m with
  | True -> (imp False False,true)
  | Ap(Neg,m1) ->
      let (n1,_) = logicnorm1 m1 in
      (imp n1 False,true)
  | Neg -> (Lam(Prop,imp (DB(0,Prop)) False),true)
  | Ap(Ap(Or,m1),m2) ->
      let (n1,_) = logicnorm1 m1 in
      let (n2,_) = logicnorm1 m2 in
      (disj n1 n2,true)
  | Or -> (Lam(Prop,Lam(Prop,disj (DB(1,Prop)) (DB(0,Prop)))),true)
  | Ap(Ap(And,m1),m2) ->
      let (n1,_) = logicnorm1 m1 in
      let (n2,_) = logicnorm1 m2 in
      (conj n1 n2,true)
  | And -> (Lam(Prop,Lam(Prop,conj (DB(1,Prop)) (DB(0,Prop)))),true)
  | Ap(Ap(Iff,m1),m2) ->
      let (n1,_) = logicnorm1 m1 in
      let (n2,_) = logicnorm1 m2 in
      (iff n1 n2,true)
  | Iff -> (Lam(Prop,Lam(Prop,iff (DB(1,Prop)) (DB(0,Prop)))),true)
  | Ap(Exists(a),Lam(_,m1)) ->
      let (n1,_) = logicnorm1 m1 in
      (exists a n1,true)
  | Exists(a) ->
      let ao = Ar(a,Prop) in
      (Lam(ao,exists a (Ap(DB(1,ao),DB(0,a)))),true)
  | Ap(m1,m2) ->
      let (n1,b1) = logicnorm1 m1 in
      let (n2,b2) = logicnorm1 m2 in
      if (b1 || b2) then
	(Ap(n1,n2),true)
      else
	(m,false)
  | Lam(a1,m1) ->
      let (n1,b1) = logicnorm1 m1 in
      if b1 then
	(Lam(a1,n1),true)
      else
	(m,false)
  | _ -> (m,false)

(* Reduce logical constants to ->, False, forall, =, choice *)
let rec logicnorm m =
  let (n,_) = logicnorm1 m in n

let ideclared = ref false
let basetypestobool = ref false

(*** conversion of pretrm ***)
let rec to_stp (m:pretrm) =
  match m with
    PPropTp -> Prop
  | PIndTp when !basetypestobool -> Prop
  | PName _ when !basetypestobool -> Prop
  | PIndTp ->
      if (!ideclared) then Base("$i")
      else
       begin
        ideclared := true;
        raise DeclareInd
       end
  | PName x ->
     begin
       Base x
     end
  | PAr(a,b) -> Ar(to_stp a,to_stp b)
  | _ -> raise (GenericSyntaxError ((pretrm_str m) ^ "is not a simple type"))

let expected_tp m a b =
  match a with
    Some(aa) ->
      if (aa = b) then () else raise (ExpectedTypeError(m,aa,b))
  | _ -> ()

let rec to_trm (h:(string,(trm * stp) * bool ref) Hashtbl.t) (g:ctx) (m:pretrm) (a:stp option) =
  match m with
  | PAp(PName "Eps",a) -> let b = to_stp a in (Choice b,Ar(Ar(b,Prop),b))
  | PName "In" -> let a = Base "set" in (Name("In",Ar(a,Ar(a,Prop))),Ar(a,Ar(a,Prop)))
  | PName "Subq" -> let a = Base "set" in (Lam(a,Lam(a,Ap(Forall(a),Lam(a,Ap(Ap(Imp,Ap(Ap(Name("In",Ar(a,Ar(a,Prop))),DB(0,a)),DB(2,a))),Ap(Ap(Name("In",Ar(a,Ar(a,Prop))),DB(0,a)),DB(1,a))))))),Ar(a,Ar(a,Prop)))
  | PName x ->
      begin(*** look in g, then in h, then fail ***)
	try
	  to_db m x g a 0
	with
	| Not_found ->
	    try
	      let (zz,o) = Hashtbl.find h x in
	      begin
		(match zz with (_,b) -> expected_tp m a b);
		o := true; (** Mark that it's occurred. - Chad, March 31, 2011 **)
		zz
	      end
	    with
	    | Not_found -> raise (GenericSyntaxError ("Unknown Name " ^ x))
      end
  | PTrue ->
      expected_tp m a Prop;
      (True,Prop)
  | PFalse ->
      expected_tp m a Prop;
      (False,Prop)
  | PNeg -> (Neg,oo)
  | POr ->
      expected_tp m a ooo;
      (Or,ooo)
  | PAnd ->
      expected_tp m a ooo;
      (And,ooo)
  | PIff ->
      expected_tp m a ooo;
      (Iff,ooo)
  | PAp(PExists,m1) ->
      begin
	expected_tp m a Prop;
	let (n1,a1) = to_trm h g m1 None in
	match a1 with
	  Ar(a1a,Prop) -> (Ap(Exists(a1a),n1),Prop)
	| _ ->
	    raise (ExpectedTypeError(m1,a1,Ar(Base("*"),Prop)))
      end
  | PAp(PAp(PNIff,m1),m2) ->
      expected_tp m a Prop;
      (preneg (preiff (to_trm_1 h g m1 (Some Prop)) (to_trm_1 h g m2 (Some Prop))),Prop)
  | PNIff ->
      expected_tp m a ooo;
      (Lam(Prop,Lam(Prop,preneg (preiff (DB(1,Prop)) (DB(0,Prop))))),ooo)
  | PImplies ->
      expected_tp m a ooo;
      (Lam(Prop,Lam(Prop,imp (DB(1,Prop)) (DB(0,Prop)))),ooo)
  | PRevImplies ->
      expected_tp m a ooo;
      (Lam(Prop,Lam(Prop,imp (DB(0,Prop)) (DB(1,Prop)))),ooo)
  | PNOr ->
      expected_tp m a ooo;
      (Lam(Prop,Lam(Prop,preneg (predisj (DB(1,Prop)) (DB(0,Prop))))),ooo)
  | PNAnd ->
      expected_tp m a ooo;
      (Lam(Prop,Lam(Prop,preneg (preconj (DB(1,Prop)) (DB(0,Prop))))),ooo)
  | PAp(PAp(PEq,m1),m2) ->
      expected_tp m a Prop;
      let (n1,b1) = to_trm h g m1 None in
      let n2 = to_trm_1 h g m2 (Some b1) in
      ((eq b1 n1 n2),Prop)
  | PEq ->
      begin
	match a with
	  Some(Ar(b1,Ar(b2,Prop)) as aa) when (b1 = b2) ->
	    (Lam(b1,Lam(b1,eq b1 (DB(1,Prop)) (DB(0,Prop)))),aa)
	| Some(aa) ->
	    raise (ExpectedTypeError(m,aa,Ar(Base("*"),Ar(Base("*"),Prop))))
	| None ->
	    raise (GenericSyntaxError ("Cannot determine type of unapplied equality"));
      end
  | PAp(PAp(PNEq,m1),m2) ->
      expected_tp m a Prop;
      let (n1,b1) = to_trm h g m1 None in
      let n2 = to_trm_1 h g m2 (Some b1) in
      (preneg (eq b1 n1 n2),Prop)
  | PNEq ->
      begin
	match a with
	  Some(Ar(b1,Ar(b2,Prop)) as aa) when (b1 = b2) ->
	    (Lam(b1,Lam(b1,preneg (eq b1 (DB(1,Prop)) (DB(0,Prop))))),aa)
	| Some(aa) ->
	    raise (ExpectedTypeError(m,aa,Ar(Base("*"),Ar(Base("*"),Prop))))
	| None ->
	    raise (GenericSyntaxError ("Cannot determine type of unapplied negated equality"));
      end
  | PAp(PForall,m1) ->
      begin
	expected_tp m a Prop;
	let (n1,a1) = to_trm h g m1 None in
	match a1 with
	  Ar(a1a,Prop) -> (Ap(Forall(a1a),n1),Prop)
	| _ ->
	    raise (ExpectedTypeError(m1,a1,Ar(Base("*"),Prop)))
      end
  | PAp(m1,m2) ->
      begin
	let (n1,a1) = to_trm h g m1 None in
	match a1 with
	  Ar(a1a,a1b) ->
	    expected_tp m a a1b;
	    let n2 = to_trm_1 h g m2 (Some a1a) in
	    (Ap(n1,n2),a1b)
	| _ -> raise (GenericSyntaxError("Non-function applied: " ^ (trm_str n1)))
      end
  | PULam(xl,m1) ->
      begin
	match a with
	| Some(aa) -> to_ulam h g xl m1 aa
	| None -> raise (GenericSyntaxError("Cannot infer type omitted from lambda"))
      end
  | PLam(xl,m1) ->
      to_lam h g xl m1 a
  | PAll(xl,m1) ->
      expected_tp m a Prop;
      (to_all h g xl m1,Prop)
  | PEx(xl,m1) ->
      expected_tp m a Prop;
      (to_exists h g xl m1,Prop)
  | PExU(x,a1,m1) ->
      expected_tp m a Prop;
      begin
	let atp = to_stp a1 in
	match to_trm h ((x,atp)::g) m1 (Some Prop) with
	| (m1a,_) -> (Ap(Lam(Ar(atp,Prop),Ap(Exists(atp),Lam(atp,Ap(Ap(And,Ap(DB(1,Ar(atp,Prop)),DB(0,atp))),Ap(Forall(atp),Lam(atp,Ap(Ap(Imp,Ap(DB(2,Ar(atp,Prop)),DB(0,atp))),Ap(Ap(Eq(atp),DB(0,atp)),DB(1,atp))))))))),Lam(atp,m1a)),Prop)
      end
  | PChoice((x,xa),m1) ->
      let xaa = to_stp xa in
      let n1 = to_trm_1 h ((x,xaa)::g) m1 (Some Prop) in
      (choice xaa n1,xaa)
  | POf(m1,m2) ->
      let b = to_stp m2 in
      expected_tp m1 a b;
      to_trm h g m1 (Some b)
  | PDef(m1,_) ->
      to_trm h g m1 a
  | PLet(x,m1,m2) ->
      begin
	let (m1a,aa) = to_trm h g m1 None in
	let (m2b,bb) = to_trm h ((x,aa)::g) m2 a in
	(Ap(Lam(aa,m2b),m1a),bb)
      end
  | PTLet(x,a1,m1,m2) ->
      begin
	let (m1a,aa) = to_trm h g m1 (Some (to_stp a1)) in
	let (m2b,bb) = to_trm h ((x,aa)::g) m2 a in
	(Ap(Lam(aa,m2b),m1a),bb)
      end
  | _ -> raise (GenericSyntaxError ("Ill-formed term " ^ (pretrm_str m)))
and to_trm_1 h g m a = let (n,_) = to_trm h g m a in n
and to_ulam h (g:ctx) xl m a =
  match xl with
    (x::xr) ->
      begin
	match a with
	  Ar(a1,a2) ->
	    let (n1,_) = to_ulam h ((x,a1)::g) xr m a2 in
	    (Lam(a1,n1),a)
	| _ ->
	    raise (ExpectedTypeError(m,a,Ar(Base("_"),Base("*"))))
      end
  | [] -> to_trm h g m (Some a)
and to_lam h (g:ctx) xl m a =
  match xl with
    ((x,xa)::xr) ->
      begin
	let xaa = to_stp xa in
	match a with
	  Some(Ar(a1,a2) as aa) when (a1 = xaa) ->
	    let (n1,_) = to_lam h ((x,xaa)::g) xr m (Some a2) in
	    (Lam(xaa,n1),aa)
	| Some(aa) ->
	    raise (ExpectedTypeError(m,aa,Ar(xaa,Base("*"))))
	| None ->
	    let (n1,b) = to_lam h ((x,xaa)::g) xr m None in
	    (Lam(xaa,n1),Ar(xaa,b))
      end
  | [] -> to_trm h g m a
and to_all h (g:ctx) xl m =
  match xl with
    ((x,xa)::xr) ->
      begin
	let xaa = to_stp xa in
	let n1 = to_all h ((x,xaa)::g) xr m in
	forall xaa n1
      end
  | [] -> to_trm_1 h g m (Some Prop)
and to_exists h (g:ctx) xl m =
  match xl with
    ((x,xa)::xr) ->
      begin
	let xaa = to_stp xa in
	let n1 = to_exists h ((x,xaa)::g) xr m in
	Ap(Exists(xaa),Lam(xaa,n1))
      end
  | [] ->
      to_trm_1 h g m (Some Prop)
and to_db m x g a i =
  match g with
    ((y,b)::gr) -> 
      if (x = y) then
	begin
	  expected_tp m a b;
	  (DB(i,b),b)
	end
      else
	to_db m x gr a (i + 1)
  | [] -> raise Not_found

let neg_body m =
  match m with
    Ap(Ap(Imp,n),False) -> Some n
  | _ -> None

let eq_body m =
  match m with
      Ap (Ap (Eq a, x), y) -> Some (a, x, y)
    | _ -> None

let neg_p m =
  match (neg_body m) with Some _ -> true | None -> false

(*This is like "head_spine" below, but accepts
  a bound to the number of "Ap"s it is to go
  through before stopping.*)
let bounded_head_spine n m =
  let rec head_spine_aux n m args =
    if n = 0 then (m, args)
    else
      match m with
          Ap (f, a) -> head_spine_aux (n - 1) f (a :: args)
        | _ -> (m, args)
  in
    head_spine_aux n m []

(*Unbounded form of "bounded_head_spine": it
  fully unfolds a term into the head (a non-applicative term)
  and the spine of terms it is applied to.*)
let head_spine m = bounded_head_spine (-1) m

let rec rtp a =
  match a with
    Ar(a1,a2) -> rtp a2
  | _ -> a

let rec argtps_rtp_rec a =
  match a with
  | Ar(a1,a2) ->
      let (al,r) = argtps_rtp_rec a2 in
      (a1::al,r)
  | _ -> ([],a)

let argtps_rtp a = argtps_rtp_rec a

(*** First Order Formulas - Dec 2012 ***)
type fotrm =
    FOVar of string
  | FOFun of string * fotrm list
type foform = (*** assuming a single sort ***)
    FOEq of fotrm * fotrm
  | FOPred of string * fotrm list
  | FOImp of foform * foform
  | FOEqu of foform * foform
  | FOAll of string * foform
  | FOFal

exception NotFO

(*** These functions assume the type i which will act as the first order type is given. ***)
let rec foftp_p a i : int =
  match a with
  | Ar(b,c) when b = i -> 1 + foftp_p c i
  | _ when a = i -> 0
  | _ -> raise NotFO

let rec foptp_p a i : int =
  match a with
  | Ar(b,c) when b = i -> 1 + foptp_p c i
  | _ when a = Prop -> 0
  | _ -> raise NotFO

let rec trm_to_fotrm_rec m (ml:trm list) i vl =
  match m with
  | Name(x,a) when foftp_p a i = List.length ml ->
    FOFun(x,List.map (fun m' -> trm_to_fotrm_rec m' [] i vl) ml)
  | DB(j,a) when a = i -> FOVar(List.nth vl j)
  | Ap(m1,m2) -> trm_to_fotrm_rec m1 (m2::ml) i vl
  | _ -> raise NotFO

let rec trm_to_foatom_rec m ml i vl =
  match m with
  | Name(x,a) when foptp_p a i = List.length ml ->
    FOPred(x,List.map (fun m' -> trm_to_fotrm_rec m' [] i vl) ml)
  | Ap(m1,m2) -> trm_to_foatom_rec m1 (m2::ml) i vl
  | _ -> raise NotFO

let rec trm_to_foform_rec p i vl eqoequiv =
  match p with
  | False -> FOFal
  | Ap(Ap(Imp,p1),p2) -> FOImp(trm_to_foform_rec p1 i vl eqoequiv,trm_to_foform_rec p2 i vl eqoequiv)
  | Ap(Forall(a),Lam(_,p1)) when a = i ->
      let x = "X" ^ (string_of_int (List.length vl)) in
      FOAll(x,trm_to_foform_rec p1 i (x::vl) eqoequiv)
  | Ap(Ap(Eq(Prop),p1),p2) when eqoequiv -> FOEqu(trm_to_foform_rec p1 i vl eqoequiv,trm_to_foform_rec p2 i vl eqoequiv)
  | Ap(Ap(Eq(a),m1),m2) when a = i -> FOEq(trm_to_fotrm_rec m1 [] i vl,trm_to_fotrm_rec m2 [] i vl)
  | _ -> trm_to_foatom_rec p [] i vl

(*** These functions try to determine if there is a type from which the formula can be viewed as first order ***)
(*** 'None' means it is propositional -- so no type is required. ***)
let rec trm_to_foatom_stp_rec m ml vl =
  match m with
  | Name(x,Ar(i,b)) when 1 + foptp_p b i = List.length ml -> (*** Must be an arrow type because we handle propositional constants below ***)
      (FOPred(x,List.map (fun m' -> trm_to_fotrm_rec m' [] i vl) ml),Some i)
  | Ap(m1,m2) -> trm_to_foatom_stp_rec m1 (m2::ml) vl
  | _ -> raise NotFO

let rec trm_to_foform_stp_rec p vl eqoequiv =
  match p with
  | False -> (FOFal,None)
  | Ap(Ap(Imp,p1),p2) ->
    begin
      match (trm_to_foform_stp_rec p1 vl eqoequiv) with
      | (p1',Some i) -> (FOImp(p1',trm_to_foform_rec p2 i vl eqoequiv),Some i)
      | (p1',None) ->
	  begin
	    match (trm_to_foform_stp_rec p2 vl eqoequiv) with
	    | (p2',Some i) -> (FOImp(p1',p2'),Some i)
	    | (p2',None) -> (FOImp(p1',p2'),None)
	  end
    end
  | Ap(Forall(i),Lam(_,p1)) -> (*** a quantifier determines the type ***)
      let x = "X" ^ (string_of_int (List.length vl)) in
      (FOAll(x,trm_to_foform_rec p1 i (x::vl) eqoequiv),Some i)
  | Ap(Ap(Eq(Prop),p1),p2) when eqoequiv -> (*** Treat eq(o) as equivalence ***)
    begin
      match (trm_to_foform_stp_rec p1 vl eqoequiv) with
      | (p1',Some i) -> (FOEqu(p1',trm_to_foform_rec p2 i vl eqoequiv),Some i)
      | (p1',None) ->
	  begin
	    match (trm_to_foform_stp_rec p2 vl eqoequiv) with
	    | (p2',Some i) -> (FOEqu(p1',p2'),Some i)
	    | (p2',None) -> (FOEqu(p1',p2'),None)
	  end
    end
  | Ap(Ap(Eq(i),m1),m2) -> (*** an equation determines the type ***)
      (FOEq(trm_to_fotrm_rec m1 [] i vl,trm_to_fotrm_rec m2 [] i vl),Some i)
  | Name(x,Prop) -> (*** Propositional constants don't determine the type ***)
      (FOPred(x,[]),None)
  | Ap(m1,m2) -> (*** This will necessarily determine the type ***)
      trm_to_foatom_stp_rec m1 [m2] vl
  | _ -> raise NotFO

(*** Takes a trm p and either returns a pair of a foform with optionally a simple type
     or raises NotFO ***)
let trm_to_foform_stp p eqoequiv = trm_to_foform_stp_rec p [] eqoequiv
