(* File: state.ml *)
(* Author: Chad E Brown *)
(* Created: October 2010 *)

open String
open Flags
open Syntax
open Priorityqueue
open Minisatinterface

exception Redeclaration of string
exception FileNotFound of string
exception GenericError of string
exception CoqProofTooBig of int

let useeprover = ref false;;
let eeqoequiv = ref false;;
let eproverperiod = ref 10;;
let eprovertimeout = ref 1;;
let foffiles = ref false;;

type clause = int list
let clauses : clause list ref = ref []
let clausesTable : (clause,unit) Hashtbl.t = Hashtbl.create 10

let slaveargs = ref [Sys.argv.(0)];;
let mode : string list ref = ref []
let timeout : float option ref = ref None
let verbosity : int ref = ref 1 (*** Default to 1; 0 should mean print nothing (-verb 0 command line option) ***)
let nontheorem : bool ref = ref false (*** March 2012 - Know if you're explicitly trying to determine Satisfiable/CounterSatisfiable ***)
let coq = ref false
let coq2 = ref false
let problemfile = ref ""
let coqlocalfile = ref false
let coqglobalfile = ref false
let coqinchannel : in_channel ref = ref stdin
let coqoutchannel : out_channel ref = ref stdout
let coqinticks : ((out_channel -> unit) option * int) list ref = ref []
let coqoutfn1 = ref (fun c -> ())
let coqctx : (string option * pretrm option * pretrm option) list ref = ref []
let coqglobalsectionstack : (string * (out_channel -> unit) * (string option * pretrm option * pretrm option) list) list ref = ref []

let rec updatecoqglobalsectionstack cx cgss co =
  match cgss with
  | ((secname,cfn,lcx)::cgss') -> ((secname,co cx cfn,lcx)::(updatecoqglobalsectionstack (List.append cx lcx) cgss' co))
  | [] -> []

let conjecturename : string ref = ref "claim"
let conjecture : (pretrm * trm * trm) option ref = ref None
type proofkind = TSTP | CoqScript | CoqSPfTerm | HOCore | Model | ModelTrue | IsarScript
let mkproofterm = ref None
let mkprooftermp () = match !mkproofterm with Some _ -> true | None -> false
let slave1 = ref false
let slave = ref false
let coqsig_base : string list ref = ref []
let coqsig_const : (string * stp) list ref = ref []
let coqsig_def : (string * pretrm) list ref = ref []
let coqsig_hyp : (string * pretrm) list ref = ref []
let coqsig_def_trm : (string * trm) list ref = ref []
let coqsig_hyp_trm : (string * trm) list ref = ref []
let name_base : (string,unit) Hashtbl.t = Hashtbl.create 10
let name_base_list : string list ref = ref []
let name_tp : (string,stp) Hashtbl.t = Hashtbl.create 100
let name_trm : (string,(trm * stp) * bool ref) Hashtbl.t = Hashtbl.create 100
let name_trm_list : (string * trm * stp) list ref = ref []
let name_def : (string,trm) Hashtbl.t = Hashtbl.create 100
let name_def_prenorm : (string,trm) Hashtbl.t = Hashtbl.create 100
let name_hyp : (string,trm) Hashtbl.t = Hashtbl.create 100

(** Replaces all occurences of 'Neg' by 'implies False' **)
let rec negnorm1 m =
  match m with
  | Ap(Neg,m1) ->
      let (n1,_) = negnorm1 m1 in
      (imp n1 False,true)
  | Neg -> (Lam(Prop,imp (DB(0,Prop)) False),true)
  | Ap(m1,m2) ->
      let (n1,b1) = negnorm1 m1 in
      let (n2,b2) = negnorm1 m2 in
      if (b1 || b2) then
	(Ap(n1,n2),true)
      else
	(m,false)
  | Lam(a1,m1) ->
      let (n1,b1) = negnorm1 m1 in
      if b1 then
	(Lam(a1,n1),true)
      else
	(m,false)
  | _ -> (m,false)
(** applies neg- and betanormalization**)
let onlynegnorm m =
  let (n,_) = negnorm1 m in onlybetanorm n
(** applies neg-, beta- and delta-normalization**)
let coqnorm m =
  let m = betanorm name_def_prenorm m in
  let (n,_) = negnorm1 m in n
(** applies full satallax normalization**)
let normalize pt = norm name_def (logicnorm pt)

let coqknown (x,y) =
  if (!coq2) then y else x

exception Timeout

(*** set_timer for timeout signal, see http://alan.petitepomme.net/cwn/2006.01.03.html#2 ***)
let set_timer s =
  ignore (Sys.signal Sys.sigalrm (Sys.Signal_handle (fun signo -> raise Timeout)));
  ignore (Unix.setitimer Unix.ITIMER_REAL { Unix.it_interval = 0.0; Unix.it_value = s });;

let remaining_time () =
  let a = Unix.getitimer Unix.ITIMER_REAL in
  a.Unix.it_value

let mult_timeout f =
  match (!timeout) with
  | Some tm -> timeout := Some (tm *. f)
  | None -> ()

let requireSet0a () =
  let a = Base "set" in
  let b = PName "set" in
  Hashtbl.add coq_used_names "In" ();
  Hashtbl.add coq_used_names "Subq" ();
  Hashtbl.add coq_names "In" "In";
  Hashtbl.add coq_names "Subq" "Subq";
  coqsig_const := ("In",Ar(a,Ar(a,Prop)))::!coqsig_const;
  coqsig_const := ("Subq",Ar(a,Ar(a,Prop)))::!coqsig_const;
  coqsig_def := ("Subq",PLam([("x",b);("y",b)],PAll(["z",b],PAp(PAp(PImplies,PAp(PAp(PName "In",PName "z"),PName "x")),PAp(PAp(PName "In",PName "z"),PName "y")))))::!coqsig_def;
  coqsig_def_trm := ("Subq",Lam(a,Lam(a,Ap(Forall(a),Lam(a,Ap(Ap(Imp,Ap(Ap(Name("In",Ar(a,Ar(a,Prop))),DB(0,a)),DB(2,a))),Ap(Ap(Name("In",Ar(a,Ar(a,Prop))),DB(0,a)),DB(1,a))))))))::!coqsig_def_trm;
  ()

let required : string ref = ref ""

let require x =
  if (!verbosity > 5) then Printf.printf "Requiring %s\n" x;
  required := x;
  let f = !coqoutfn1 in
  begin
    coqoutfn1 := (fun c -> f c; Printf.fprintf c "Require Export %s.\n" x);
    match x with
    | "set0a" -> requireSet0a()
    | "set0" -> raise (GenericError "set0 is not yet supported.")
    | "set1" -> raise (GenericError "set1 is not yet supported.")
    | _ -> ()
  end

(*** March 31, 2011 - Chad - THF policy regarding definitions. (See comments before declare_definition_real below. ***)
exception TreatAsAssumption

let next_fresh_name : int ref = ref 0

let rec get_fresh_name a =
  let x = "__" ^ (string_of_int (!next_fresh_name)) in
  incr next_fresh_name;
  if (!coq) then
    begin
      ignore (coqify_name x coq_names coq_used_names)
    end;
  if ((Hashtbl.mem name_base x) || (Hashtbl.mem name_tp x)) then
    get_fresh_name a
  else
    let xa = Name(x,a) in
    begin
      Hashtbl.add name_tp x a;
      Hashtbl.add name_trm x ((xa,a), ref false);
      name_trm_list := (x,xa,a)::!name_trm_list;
      (x,xa)
    end

type ruleinfo =
 (*** NegPropRule(m) For rules requiring one negative formula in the head, except negated forall ***)
    NegPropRule of trm
 (*** PosPropRule(m) For rules requiring one positive formula in the head, except forall ***)
  | PosPropRule of trm
 (*** InstRule(a,m,n) For instantiating a Ap(Forall(a),m) with n:a ***)
  | InstRule of stp * trm * trm
 (*** FreshRule(a,m,x) For producing a witness x for Ap(Neg,Ap(Forall(a),m)) ***)
  | FreshRule of stp * trm * string
 (*** MatingRule(plit,nlit) For mating rule, only save the literals here ***)
  | MatingRule of int * int
 (*** ConfrontationRule(plit,nlit) For confrontation rule, only save the literals here ***)
  | ConfrontationRule of int * int
 (*** ChoiceRule(eps,pred) ***)
  | ChoiceRule of trm * trm
 (*** Known(lit,coqname,stp list) ***)
  | Known of int * string * stp list

type refut =
    NegImpR of trm * trm * refut
  | ImpR of trm * trm * refut * refut
  | FalseR
  | NegReflR
  | NegAllR of stp * trm * string * refut
  | EqFR of stp * stp * trm * trm * refut
  | NegEqFR of stp * stp * trm * trm * refut
  | EqOR of trm * trm * refut * refut
  | NegEqOR of trm * trm * refut * refut
  | SearchR of clause list * (clause -> ruleinfo)
  | AssumptionConflictR

exception Unsatisfiable of refut option
exception Satisfiable

let next_atom = ref 1
let atom_hash : (trm,int) Hashtbl.t = Hashtbl.create 1000
let atom_hash_rev : (int,trm) Hashtbl.t = Hashtbl.create 1000

let max_atom () = (!next_atom) - 1

let prop_fo_forms : (int * foform) list ref = ref []
let stp_fo_forms : (stp,int * foform) Hashtbl.t = Hashtbl.create 10
let fo_types_h : (stp,unit) Hashtbl.t = Hashtbl.create 10
let fo_types : stp list ref = ref []
let fo_ecounter : (stp,int ref) Hashtbl.t = Hashtbl.create 10

let plit_fo_str a =
  if a > 0 then
    "p" ^ (string_of_int a)
  else
    "~ p" ^ (string_of_int (- a))

let rec printf_fotrm s m =
  match m with
  | FOVar(x) -> Printf.fprintf s "%s" x
  | FOFun(f,[]) -> Printf.fprintf s "c%s" f
  | FOFun(f,(a::al)) ->
      begin
	Printf.fprintf s "f%s(" f;
	printf_fotrm s a;
	List.iter (fun t -> Printf.fprintf s ","; printf_fotrm s t) al;
	Printf.fprintf s ")";
      end

let rec printf_fof s m =
  match m with
  | FOEq(t1,t2) ->
      Printf.fprintf s "(";
      printf_fotrm s t1;
      Printf.fprintf s " = ";
      printf_fotrm s t2;
      Printf.fprintf s ")";
  | FOPred(p,[]) ->
      Printf.fprintf s "q%s" p;
  | FOPred(p,(a::al)) ->
      Printf.fprintf s "r%s(" p;
      printf_fotrm s a;
      List.iter (fun t -> Printf.fprintf s ","; printf_fotrm s t) al;
      Printf.fprintf s ")";
  | FOImp(m1,m2) ->
      Printf.fprintf s "(";
      printf_fof s m1;
      Printf.fprintf s " => ";
      printf_fof s m2;
      Printf.fprintf s ")";
  | FOEqu(m1,m2) ->
      Printf.fprintf s "(";
      printf_fof s m1;
      Printf.fprintf s " <=> ";
      printf_fof s m2;
      Printf.fprintf s ")";
  | FOAll(x,m1) ->
      Printf.fprintf s "( ! [%s] : " x;
      printf_fof s m1;
      Printf.fprintf s ")";
  | FOFal ->
      Printf.fprintf s "$false"

let printf_fof_file s b =
  let axc = ref 0 in
	   (*** Send all propositional clauses we've sent to MiniSat. This contains the propositional structure of the problem. ***)
  List.iter (fun c ->
    match c with
    | (l1::ll) ->
	incr axc;
	Printf.fprintf s "fof(ax%d,axiom,( %s " (!axc) (plit_fo_str l1);
	List.iter (fun l2 -> Printf.fprintf s " | %s" (plit_fo_str l2)) ll;
	Printf.fprintf s ")).\n";
    | [] -> () (*** should never happen ***)
	  )
    !clauses;
	   (*** Relate Some propositional literals to first order formulas. ***)
	   (*** First the ones that are really propositional. ***)
  List.iter (fun (p,fof) ->
    incr axc;
    Printf.fprintf s "fof(ax%d,axiom,( %s <=> " (!axc) (plit_fo_str p);
    printf_fof s fof;
    Printf.fprintf s ")).\n"
      )
    (!prop_fo_forms);
	   (*** Finally the ones that are specifically viewed as first order via the current type b. ***)
  List.iter (fun (p,fof) ->
    incr axc;
    Printf.fprintf s "fof(ax%d,axiom,( %s <=> " (!axc) (plit_fo_str p);
    printf_fof s fof;
    Printf.fprintf s ")).\n"
      )
    (Hashtbl.find_all stp_fo_forms b)

(*** Output FOF as Sexpr -- just for debugging BEGIN ***)
let rec printf_fstrm s m =
  match m with
  | FOVar(x) -> Printf.fprintf s "|%s|" x
  | FOFun(f,[]) -> Printf.fprintf s "|%s|" f
  | FOFun(f,(a::al)) ->
      begin
	Printf.fprintf s "(|%s| " f;
	printf_fstrm s a;
	List.iter (fun t -> Printf.fprintf s " "; printf_fstrm s t) al;
	Printf.fprintf s ")";
      end

let rec printf_fs s m =
  match m with
  | FOEq(t1,t2) ->
      Printf.fprintf s "(= ";
      printf_fstrm s t1;
      Printf.fprintf s " ";
      printf_fstrm s t2;
      Printf.fprintf s ")";
  | FOPred(p,[]) ->
      Printf.fprintf s "|%s|" p;
  | FOPred(p,(a::al)) ->
      Printf.fprintf s "(|%s| " p;
      printf_fstrm s a;
      List.iter (fun t -> Printf.fprintf s " "; printf_fstrm s t) al;
      Printf.fprintf s ")";
  | FOImp(m1,m2) ->
      Printf.fprintf s "(=> ";
      printf_fs s m1;
      Printf.fprintf s " ";
      printf_fs s m2;
      Printf.fprintf s ")";
  | FOEqu(m1,m2) ->
      Printf.fprintf s "(<=> ";
      printf_fs s m1;
      Printf.fprintf s " ";
      printf_fs s m2;
      Printf.fprintf s ")";
  | FOAll(x,m1) ->
      Printf.fprintf s "(ALL |%s| " x;
      printf_fs s m1;
      Printf.fprintf s ")";
  | FOFal ->
      Printf.fprintf s "FALSE"

let printf_fs_file s b =
  let axc = ref 0 in
	   (*** Send all propositional clauses we've sent to MiniSat. This contains the propositional structure of the problem. ***)
  List.iter (fun c ->
    match c with
    | (l1::ll) ->
	incr axc;
	Printf.fprintf s "(AXIOM %d (|%s|" (!axc) (plit_fo_str l1);
	List.iter (fun l2 -> Printf.fprintf s " |%s|" (plit_fo_str l2)) ll;
	Printf.fprintf s "))\n";
    | [] -> () (*** should never happen ***)
	  )
    !clauses;
	   (*** Relate Some propositional literals to first order formulas. ***)
	   (*** First the ones that are really propositional. ***)
  List.iter (fun (p,fof) ->
    incr axc;
    Printf.fprintf s "(EAXIOM %d |%s| " (!axc) (plit_fo_str p);
    printf_fs s fof;
    Printf.fprintf s ")\n"
      )
    (!prop_fo_forms);
	   (*** Finally the ones that are specifically viewed as first order via the current type b. ***)
  List.iter (fun (p,fof) ->
    incr axc;
    Printf.fprintf s "(EAXIOM %d |%s| " (!axc) (plit_fo_str p);
    printf_fs s fof;
    Printf.fprintf s ")\n"
      )
    (Hashtbl.find_all stp_fo_forms b)
(*** Output FOF as Sexpr -- just for debugging END ***)

(*** Remember if a is FO, so I can send this to E. Send it to E every E_PERIOD times. ***)
let new_possible_fo_formula m a =
 try
   match trm_to_foform_stp m (!eeqoequiv) with
   | (fof,Some b) ->
       if (not (Hashtbl.mem fo_types_h b)) then
	 begin
	   if (!verbosity > 4) then (Printf.printf "New FO type: %s\n" (stp_str b); flush stdout);
	   Hashtbl.add fo_types_h b ();
	   fo_types := b::!fo_types;
	   Hashtbl.add fo_ecounter b (ref 0);
	 end;
       if (!verbosity > 4) then (Printf.printf "Adding FOF for type %s: %s\n" (stp_str b) (trm_str m); flush stdout);
       Hashtbl.add stp_fo_forms b (a,fof);
       let r = Hashtbl.find fo_ecounter b in
       incr r;
       if (!r >= !eproverperiod) then
	 begin
	   r := 0;
	   if (!verbosity > 4) then (Printf.printf "Calling E on FOF for type %s\n" (stp_str b); flush stdout);
	   if (!foffiles) then
	     begin
	       let foffilename = "/tmp/fof" ^ (string_of_float (Unix.time ())) ^ "p" in
	       let foffile = open_out foffilename in
	       printf_fof_file foffile b;
	       close_out foffile;
	       Printf.printf "./E/PROVER/eprover -s --auto --cpu-limit=1 --tptp3-in < %s\n" foffilename;
	       Unix.sleep 1; (*** sleep for a second so the names will be unique ***)
	     end;
(***
 ***)
	   let etimeoutnow =
             match (!timeout) with
             | Some _ -> min (int_of_float (remaining_time ())) (!eprovertimeout)
             | None -> !eprovertimeout
           in
	   if (etimeoutnow > 0) then
	     begin
	       if (!verbosity > 4) then Printf.printf "Calling E for %d seconds.\n" etimeoutnow;
	       let (myout,myin,myerr) = Unix.open_process_full ((!Config.eprover) ^ " -s --auto --cpu-limit=" ^ (string_of_int etimeoutnow) ^ "  --tptp3-in") [| |] in
               printf_fof_file myin b;
	       close_out myin;
	       if (!verbosity > 4) then (Printf.printf "About to read result from eprover\n"; flush stdout);
	       try
		 while true do
		   match (input_line myout) with
		   | "# SZS status Unsatisfiable" ->
                       if (!foffiles) then
			 begin
			   let foffilename = "/tmp/fof" ^ (string_of_float (Unix.time ())) ^ "p" in
			   let foffile = open_out foffilename in
			   printf_fof_file foffile b;
			   close_out foffile;
			   let fsfilename = "/tmp/fs" ^ (string_of_float (Unix.time ())) ^ ".lisp" in
			   let fsfile = open_out fsfilename in
			   printf_fs_file fsfile b;
			   close_out fsfile;
			   Printf.printf "./E/PROVER/eprover -s --auto --cpu-limit=1 --tptp3-in < %s\n" foffilename;
			 end;
                       ignore(Unix.close_process_full(myout,myin,myerr));
		       raise (Unsatisfiable None)
		   | _ -> ()
		 done
	       with End_of_file -> ignore(Unix.close_process_full(myout,myin,myerr))
	     end
	 end
   | (fof,None) ->
       if (!verbosity > 4) then (Printf.printf "Adding prop FOF: %s\n" (trm_str m); flush stdout);
       prop_fo_forms := ((a,fof)::!prop_fo_forms)
 with NotFO -> ()

let new_atom m =
  let a = (!next_atom) in
  incr next_atom;
  Hashtbl.add atom_hash m a;
  Hashtbl.add atom_hash_rev a m;
  if (!verbosity > 4) then if (!verbosity > 8) then (Printf.printf "Atom %d: %s\n" a (trm_str m)) else (Printf.printf "Atom %d\n" a);
  if (!useeprover) then new_possible_fo_formula m a;
  a

let get_atom m =
  try
    Hashtbl.find atom_hash m
  with
  | Not_found -> new_atom m

let get_literal m =
  match (neg_body m) with
    Some n ->
      (- (get_atom n))
  | None -> (get_atom m)

let literal_to_trm l =
  if (l < 0) then
    (neg (Hashtbl.find atom_hash_rev (- l)))
  else
    (Hashtbl.find atom_hash_rev l)

let assignedp m =
  match (neg_body m) with
    Some n -> Hashtbl.mem atom_hash n
  | None -> Hashtbl.mem atom_hash m

let initial_branch : trm list ref = ref []
let initial_branch_prenorm : trm list ref = ref []

type searchoption =
 (*** ProcessProp1(m) For rules requiring one formula in the head (most rules) ***)
    ProcessProp1 of trm
 (*** Mating(plit,nlit,pl,nl) where pl,nl and plit = lit (h pl) and nlit = lit ~(h nl) ***)
  | Mating of int * int * trm list * trm list
 (*** Confront(nplit,nnlit,a,s,t,u,v) where s,t,u,v:a and nplit = lit (s = t) and nnlit is lit (u != v) ***)
  | Confront of int * int * stp * trm * trm * trm * trm
 (*** DefaultElt(a) - create a default element of type a ***)
  | DefaultElt of string
 (*** DefaultEltInst(a) - create a default element of type a ***)
  | DefaultEltInst of string
 (*** NewInst(a,m) - put m:a in the set of instantiations ***)
  | NewInst of stp * trm
 (*** EnumIterDeep(d,a) - Enumerate all terms (using the current constants) of depth d ***)
  | EnumIterDeep of int * stp
 (*** EnumTp(d,ar,a) - work on enumerating types that can be used to choose a polymorphic head (Eq, Forall, Choice) ***)
  | EnumTp of int * stp * stp
 (*** EnumAp(d,Gamma,sigmal,h,c) - ***)
  | EnumAp of (int * stp list * stp list * trm * (trm -> unit))
 (*** Enum(d,Gamma,sigma,c) ***)
  | Enum of (int * stp list * stp * (trm -> unit))
 (*** Filter - use Minisat to filter usable sets ***)
  | Filter of int

(*** For printing a searchoption - helpful for debugging. - Chad, Oct 2010 ***)
let searchoption_str s =
  match s with
  | ProcessProp1(m) -> ("ProcessProp1(" ^ (trm_str m) ^ ")")
  | Mating(plit,nlit,pl,nl) -> "Mating(" ^ (string_of_int plit) ^ "," ^ (string_of_int nlit) ^ " -- " ^ (String.concat "," (List.map trm_str pl)) ^ " -- " ^ (String.concat "," (List.map trm_str nl)) ^  ")"
  | Confront(plit,nlit,a,s,t,u,v) -> "Confront(" ^ (string_of_int plit) ^ "," ^ (string_of_int nlit) ^ ")"
  | DefaultElt(a) -> "DefaultElt(" ^ a ^ ")"
  | DefaultEltInst(a) -> "DefaultEltInst(" ^ a ^ ")"
  | EnumIterDeep(d,a) -> "EnumIterDeep(" ^ (string_of_int d) ^ "," ^ (stp_str a) ^ ")"
  | EnumTp(d,_,a) -> "EnumTp(" ^ (string_of_int d) ^ "," ^ (stp_str a) ^ ")"
  | EnumAp(d,gamma,sigmal,h,_) -> "EnumAp(" ^ (string_of_int d) ^ "," ^ (String.concat ";" (List.map stp_str gamma)) ^ "," ^ (String.concat ";" (List.map stp_str sigmal)) ^ "," ^ (trm_str h) ^ ")"
  | Enum(d,gamma,sigma,_) -> "Enum(" ^ (string_of_int d) ^ "," ^ (String.concat ";" (List.map stp_str gamma)) ^ "," ^ (stp_str sigma) ^ ")"
  | NewInst(_,m) -> "NewInst(" ^ (trm_str m) ^ ")"
  | Filter(d) -> "Filter(" ^ (string_of_int d) ^ ")"
(***  | _ -> "OtherSearchOption" (*** to do: the rest if we need them ***) ***)

(*** For printing a ruleinfo - helpful for debugging. - Chad, Oct 2010 ***)
let ruleinfo_str s =
  match s with
  | NegPropRule(m) -> ("NegPropRule(" ^ (trm_str m) ^ ")")
  | PosPropRule(m) -> ("PosPropRule(" ^ (trm_str m) ^ ")")
  | InstRule(a,m,n) -> ("InstRule(" ^ (stp_str a) ^ "," ^ (trm_str m) ^ "," ^ (trm_str n) ^ ")")
  | FreshRule(a,m,x) -> ("FreshRule(" ^ (stp_str a) ^ "," ^ (trm_str m) ^ "," ^ x ^ ")")
  | MatingRule(plit,nlit) -> "MatingRule(" ^ (string_of_int plit) ^ "," ^ (string_of_int nlit) ^ ")"
  | ConfrontationRule(plit,nlit) -> "ConfrontationRule(" ^ (string_of_int plit) ^ "," ^ (string_of_int nlit) ^ ")"
  | ChoiceRule(eps,pred) -> "ChoiceRule(" ^ (trm_str eps) ^ "," ^ (trm_str pred) ^ ")"
  | Known(l,cname,al) -> "Known(" ^ (string_of_int l) ^ "," ^ cname ^ ")"

(*** For printing the refutation - helpful for debugging. - Chad, Oct 2010 ***)
let rec print_refut r =
  match r with
  | NegImpR(m,n,r1) ->
      Printf.printf "NegImpR\n  left: %s\n  right: %s\n" (trm_str m) (trm_str n);
      print_refut r1
  | ImpR(m,n,r1,r2) ->
      Printf.printf "ImpR\n  left: %s\n  right: %s\n" (trm_str m) (trm_str n);
      print_refut r1;
      print_refut r2
  | FalseR ->
      Printf.printf "FalseR\n"
  | NegReflR ->
      Printf.printf "NegReflR\n"
  | NegAllR(a,m,x,r) ->
      Printf.printf "NegAllR\n  fresh var:%s\n  stp: %s\n   body: %s\n" x (stp_str a) (trm_str m);
      print_refut r
  | EqFR(a,b,m,n,r) ->
      Printf.printf "EqFR\n  stp: (%s)   ->   (%s)\nleft: %s\n  right: %s\n" (stp_str a) (stp_str b) (trm_str m) (trm_str n);
  | NegEqFR(a,b,m,n,r) ->
      Printf.printf "NegEqFR\n  stp: (%s)   ->   (%s)\nleft: %s\n  right: %s\n" (stp_str a) (stp_str b) (trm_str m) (trm_str n);
  | EqOR(m,n,r1,r2) ->
      Printf.printf "EqOR\n  left: %s\n  right: %s\n" (trm_str m) (trm_str n);
      print_refut r1;
      print_refut r2
  | NegEqOR(m,n,r1,r2) ->
      Printf.printf "NegEqOR\n  left: %s\n  right: %s\n" (trm_str m) (trm_str n);
      print_refut r1;
      print_refut r2
  | AssumptionConflictR ->
      Printf.printf "AssumptionConflictR\n";
  | SearchR(cl,cr) ->
      Printf.printf "SearchR\n  clauses with search options:\n";
      List.iter
	(fun c ->
	  Printf.printf "%s\n" (String.concat " " (List.map string_of_int c));
	  List.iter
	    (fun z -> (Printf.printf "Atom %d: %s\n" (abs z) (trm_str (Hashtbl.find atom_hash_rev (abs z)))))
	    c;
	  try
	    Printf.printf "associated rule: %s\n" (ruleinfo_str (cr c))
	  with
	  | Not_found ->
	      Printf.printf "no associated rule\n"
	)
	cl

let processed : (trm,unit) Hashtbl.t = Hashtbl.create 100
let clause_ruleinfo : (clause,ruleinfo) Hashtbl.t ref = ref (Hashtbl.create 100)

exception DuplicateClause

let insert_assumption_clause c =
  if (Hashtbl.mem clausesTable c) then
    raise DuplicateClause
  else
    begin
      Hashtbl.add clausesTable c ();
      clauses := (c::!clauses)
    end

let insert_search_clause c r = 
(***  (Printf.printf "inserting search clause %s: %s\n" (List.fold_left (fun x y -> if ((String.length x) == 0) then (string_of_int y) else (x ^ " " ^ (string_of_int y))) "" c) (match r with (Some r) -> (ruleinfo_str r) | _ -> "None"); flush stdout); ***)
  if (Hashtbl.mem clausesTable c) then
    (*** Chad: April 4, 2011: Check if the clause has already been added before.  If it has, raise DuplicateClause. (Otherwise, we may end up with bad rule info -- e.g., a later rule which will violate freshness) ***)
(***    Printf.printf "duplicate clause %s: %s\n" (List.fold_left (fun x y -> if ((String.length x) == 0) then (string_of_int y) else (x ^ " " ^ (string_of_int y))) "" c) (match r with (Some r) -> (ruleinfo_str r) | _ -> "None"); flush stdout; ***)
     raise DuplicateClause
  else
    begin
      Hashtbl.add clausesTable c ();
      clauses := (c::!clauses);
      match r with
      | Some(r) ->
	  Hashtbl.add (!clause_ruleinfo) c r;
      | None -> ()
    end

(*** Different Implementations of Fair Priority Queues ***)
module PQueue0 = PriorityQueue0 (struct type t = searchoption end)
module PQueue1 = PriorityQueue1 (struct type t = searchoption end)
module PQueue2 = PriorityQueue2 (struct type t = searchoption end)
module PQueue3 = PriorityQueue3 (struct type t = searchoption end)
module PQueue4 = PriorityQueue4 (struct type t = searchoption end)
module PQueue5 = PriorityQueue5 (struct type t = searchoption end)
module PQueue6 = PriorityQueue6 (struct type t = searchoption end)
module PQueue7 = PriorityQueue7 (struct type t = searchoption end)
module PQueue8 = PriorityQueue8 (struct type t = searchoption end)

let insertWithPriority n o =
  let (ins,dp) =
    begin
      match (get_int_flag "PRIORITY_QUEUE_IMPL") with
      | 0 -> (PQueue0.insertWithPriority,PQueue0.debug_print)
      | 1 -> (PQueue1.insertWithPriority,PQueue1.debug_print)
      | 2 -> (PQueue2.insertWithPriority,PQueue2.debug_print)
      |	3 -> (PQueue3.insertWithPriority,PQueue3.debug_print)
      |	4 -> (PQueue4.insertWithPriority,PQueue4.debug_print)
      |	5 -> (PQueue5.insertWithPriority,PQueue5.debug_print)
      |	6 -> (PQueue6.insertWithPriority,PQueue6.debug_print)
      |	7 -> (PQueue7.insertWithPriority,PQueue7.debug_print)
      |	8 -> (PQueue8.insertWithPriority,PQueue8.debug_print)
      | n -> (raise (GenericError("Invalid value of PRIORITY_QUEUE_IMPL: " ^ (string_of_int n))))
    end
  in
  begin
    if (!verbosity > 8) then Printf.printf "Inserting option with priority %d: %s\n" n (searchoption_str o);
    ins n o;
    if (!verbosity > 49) then dp searchoption_str
  end

let getNext () =
  let (gn,dp) =
    begin
      match (get_int_flag "PRIORITY_QUEUE_IMPL") with
      | 0 -> (PQueue0.getNext,PQueue0.debug_print)
      | 1 -> (PQueue1.getNext,PQueue1.debug_print)
      | 2 -> (PQueue2.getNext,PQueue2.debug_print)
      |	3 -> (PQueue3.getNext,PQueue3.debug_print)
      |	4 -> (PQueue4.getNext,PQueue4.debug_print)
      |	5 -> (PQueue5.getNext,PQueue5.debug_print)
      |	6 -> (PQueue6.getNext,PQueue6.debug_print)
      |	7 -> (PQueue7.getNext,PQueue7.debug_print)
      |	8 -> (PQueue8.getNext,PQueue8.debug_print)
      | n -> (raise (GenericError("Invalid value of PRIORITY_QUEUE_IMPL: " ^ (string_of_int n))))
    end
  in
  if (!verbosity > 49) then (Printf.printf "About to get next option:\n"; dp searchoption_str);
  let o = gn()
  in
  if (!verbosity > 49) then (Printf.printf "After removing option:\n"; dp searchoption_str);
  o

let peekAtNext() =
  begin
    match (get_int_flag "PRIORITY_QUEUE_IMPL") with
    | 0 -> PQueue0.peekAtNext()
    | 1 -> PQueue1.peekAtNext()
    | 2 -> PQueue2.peekAtNext()
    | 3 -> PQueue3.peekAtNext()
    | 4 -> PQueue4.peekAtNext()
    | 5 -> PQueue5.peekAtNext()
    | 6 -> PQueue6.peekAtNext()
    | 7 -> PQueue7.peekAtNext()
    | 8 -> PQueue8.peekAtNext()
    | n -> (raise (GenericError("Invalid value of PRIORITY_QUEUE_IMPL: " ^ (string_of_int n))))
  end

let testPriorityQueue() =
  let v = (!verbosity) in
(***  verbosity := 50; ***)
  for i = 0 to 2000
  do
    let p = (Random.int 10) in
    Printf.printf "Inserting %d with priority %d\n" i p;
    Printf.printf "(ins %d %d)\n" i p;
    insertWithPriority p (Filter i);
    if ((Random.int 3) = 0) then
      begin
	let (q,o1) = peekAtNext() in
	Printf.printf "Peeking at %s of priority %d\n" (searchoption_str o1) q;
	Printf.printf "(unless (equal (getnext) (list %d %d)) (error \"\"))\n" (match o1 with (Filter z) -> z | _ -> 0) q;
	let o2 = getNext() in
	if (not (o1 = o2)) then
	  Printf.printf "Got something different: %s\n" (searchoption_str o2);
      end;
  done;
  verbosity := v

let patoms : (string,int * (trm list)) Hashtbl.t = Hashtbl.create 10
let natoms : (string,int * (trm list)) Hashtbl.t = Hashtbl.create 10

let pchoiceatoms : (stp,int * (trm list)) Hashtbl.t = Hashtbl.create 10
let nchoiceatoms : (stp,int * (trm list)) Hashtbl.t = Hashtbl.create 10

let peqns : (string,int * trm * trm) Hashtbl.t = Hashtbl.create 10
let neqns : (string,int * trm * trm) Hashtbl.t = Hashtbl.create 10

let univpreds : (stp,(int * trm)) Hashtbl.t = Hashtbl.create 10
let instantiations : (stp,(trm,unit) Hashtbl.t) Hashtbl.t = Hashtbl.create 10
let instantiationslist : (stp,trm list) Hashtbl.t = Hashtbl.create 10
let default_elts : (string,trm) Hashtbl.t = Hashtbl.create 10

let set_default_elt aname x =
  Hashtbl.add default_elts aname x

let set_default_elt_if_needed a x =
  match a with
  | Base(aname) ->
      if (not (Hashtbl.mem default_elts aname)) then set_default_elt aname x
  | _ -> ()

let default_elt aname =
  try
    Hashtbl.find default_elts aname
  with
  | Not_found ->
      let a = Base aname in
      let (_,x) = get_fresh_name a in
      begin
	set_default_elt aname x;
	x
      end

let default_elt_p aname =
  Hashtbl.mem default_elts aname

let get_instantiations a =
  try
    Hashtbl.find instantiationslist a
  with Not_found -> []

let known_instantiation a m =
  try
    let h = Hashtbl.find instantiations a in
    Hashtbl.find h m;
    true
  with Not_found -> false

let cons_instantiation m ml =
    let iordcyc = get_int_flag "INSTANTIATION_ORDER_CYCLE" in
    let iordmask = get_int_flag "INSTANTIATION_ORDER_MASK" in
    if (iordcyc < 2) then
      begin
	if (iordmask mod 2 = 0) then
	  (m::ml)
	else
	  (ml @ [m])
      end
    else
      let j = List.length ml mod iordcyc in
      begin
	if ((iordmask lsr j) mod 2 = 0) then
	  (m::ml)
	else
	  (ml @ [m])
      end

let add_instantiation_2 a m =
  try
    let ml = Hashtbl.find instantiationslist a in
    Hashtbl.replace instantiationslist a (cons_instantiation m ml)
  with Not_found ->
    Hashtbl.add instantiationslist a [m]

let add_instantiation a m =
  try
    let h = Hashtbl.find instantiations a in
    Hashtbl.add h m ();
    add_instantiation_2 a m;
    set_default_elt_if_needed a m
  with Not_found ->
    let h : (trm,unit) Hashtbl.t = Hashtbl.create 10 in
    Hashtbl.add instantiations a h;
    Hashtbl.add h m ();
    add_instantiation_2 a m;
    set_default_elt_if_needed a m

let choiceopnames : (string,(stp * trm)) Hashtbl.t = Hashtbl.create 10

let choiceop_axiom m =
  match m with
  | Ap (Forall (Ar (a, Prop)),
	Lam (Ar (_, Prop),
	     Ap (Forall _,
		 Lam (_,
		      Ap (Ap (Imp, Ap (DB (1, Ar (_, Prop)), DB (0, _))),
			  Ap (DB (1, Ar (_, Prop)),
			      Ap (Name (x, Ar (Ar (_, Prop), _)),
				  DB (1, Ar (_, Prop)))))))))
    -> Some(x,a)
  | Ap (Forall (Ar (a, Prop)),
	Lam (Ar (_, Prop),
	     Ap
	       (Ap (Imp,
		    Ap
		      (Ap (Imp,
			   Ap (Forall _,
			       Lam (_,
				    Ap (Ap (Imp, Ap (DB (1, Ar (_, Prop)), DB (0, _))),
					False)))),
		       False)),
		Ap (DB (0, Ar (_, Prop)),
		    Ap (Name (x, Ar (Ar (_, Prop), _)),
			DB (0, Ar (_, Prop)))))))
    -> Some(x,a)
  | _ -> None

let declare_choiceop x a m = Hashtbl.add choiceopnames x (a,m)

let choiceop m =
  match m with
  | Choice(a) -> Some(a)
  | Name(x,_) ->
      begin
	try
	  let (a,_) = Hashtbl.find choiceopnames x in
	  Some(a)
	with
	| Not_found -> None
      end
  | _ -> None

let filtered : (int,unit) Hashtbl.t = Hashtbl.create 10

let part_of_conjecture : (trm,unit) Hashtbl.t = Hashtbl.create 10

type namecategory =
    ChoiceOp of int * int * stp list * trm list (*** (i,n,sigmal,tl) where length of sigmal and tl are n, 0 <= i < n, Name has type (sigmal -> o) -> sigmal[i], and for each j:{0,...,n-1} tl[j] is the jth component of the n-ary choice operator (in particular, tl[i] is this one) ***)
   | DescrOp of int * int * stp list * trm list (*** (i,n,sigmal,tl) where length of sigmal and tl are n, 0 <= i < n, Name has type (sigmal -> o) -> sigmal[i], and for each j:{0,...,n-1} tl[j] is the jth component of the n-ary description operator (in particular, tl[i] is this one) ***)
   | IfThenElse of int * int * stp list (*** (i,n,sigmal) where length of sigmal is n, 0 <= i < n, Name has type o -> sigmal -> sigmal -> sigmal[i] ***)
   | ReflexiveBinary
   | IrreflexiveBinary
   | SymmetricBinary
   | ReflexiveSymmetricBinary
   | IrreflexiveSymmetricBinary

let constrainedName : (string,namecategory) Hashtbl.t = Hashtbl.create 10

let decomposable x =
   try
   let c = Hashtbl.find constrainedName x in (*** Some categorized names are decomposable and some are not ***)
   match c with
   | IfThenElse _ -> false (*** TO DO: Check that n-ary if-then-else need not be decomposable ***)
   (*** TO DO: Should *Binary cases be decomposable? ***)
   | _ -> true
   with Not_found -> true (*** A name is decomposable by default ***)

(*** Set completep to false if I use a mode that makes the search incomplete, so that failure does not imply satisfiability.
     Currently there is no such mode. - Chad, Oct 2010 ***)
let completep = ref true

let get_timeout_default x = match (!timeout) with Some y -> y | None -> x

let st_include_fun : (string -> unit) ref = ref (fun x -> raise (GenericError("Bug when including file " ^ x)))
let st_find_read_thf_fun : (string -> string -> unit) ref = ref (fun d x -> raise (GenericError("Bug when including file " ^ x)))

let coq_init () =
  begin
    Hashtbl.add coq_used_names "as" ();
    Hashtbl.add coq_used_names "at" ();
    Hashtbl.add coq_used_names "cofix" ();
    Hashtbl.add coq_used_names "else" ();
    Hashtbl.add coq_used_names "end" ();
    Hashtbl.add coq_used_names "exists2" ();
    Hashtbl.add coq_used_names "fix" ();
    Hashtbl.add coq_used_names "for" ();
    Hashtbl.add coq_used_names "forall" ();
    Hashtbl.add coq_used_names "fun" ();
    Hashtbl.add coq_used_names "if" ();
    Hashtbl.add coq_used_names "IF" ();
    Hashtbl.add coq_used_names "in" ();
    Hashtbl.add coq_used_names "let" ();
    Hashtbl.add coq_used_names "match" ();
    Hashtbl.add coq_used_names "mod" ();
    Hashtbl.add coq_used_names "Prop" ();
    Hashtbl.add coq_used_names "return" ();
    Hashtbl.add coq_used_names "Set" ();
    Hashtbl.add coq_used_names "then" ();
    Hashtbl.add coq_used_names "Type" ();
    Hashtbl.add coq_used_names "using" ();
    Hashtbl.add coq_used_names "where" ();
    Hashtbl.add coq_used_names "with" ();
    (*** Avoid certain names used by stt in Coq ***)
    Hashtbl.add coq_used_names "SType" ();
    Hashtbl.add coq_used_names "Sar" ();
    Hashtbl.add coq_used_names "o" ();
    Hashtbl.add coq_used_names "prop" ();
    Hashtbl.add coq_used_names "Sepsilon" ();
    Hashtbl.add coq_used_names "forall" ();
    Hashtbl.add coq_used_names "exists" ();
    Hashtbl.add coq_used_names "False" ();
    Hashtbl.add coq_used_names "True" ();
    Hashtbl.add coq_used_names "not" ();
    Hashtbl.add coq_used_names "Snot" ();
    Hashtbl.add coq_used_names "and" ();
    Hashtbl.add coq_used_names "Sand" ();
    Hashtbl.add coq_used_names "or" ();
    Hashtbl.add coq_used_names "Sor" ();
    Hashtbl.add coq_used_names "iff" ();
    Hashtbl.add coq_used_names "Siff" ();
    Hashtbl.add coq_used_names "ex" ();
    Hashtbl.add coq_used_names "SSigma" ();
    Hashtbl.add coq_used_names "SPi" ();
    Hashtbl.add coq_used_names "eq" ();
    Hashtbl.add coq_used_names "Seq" ();
    Hashtbl.add coq_used_names "I" ();
    Hashtbl.add coq_used_names "FalseE" ();
    Hashtbl.add coq_used_names "conj" ();
    Hashtbl.add coq_used_names "proj1" ();
    Hashtbl.add coq_used_names "proj2" ();
    Hashtbl.add coq_used_names "and_ind" ();
    Hashtbl.add coq_used_names "or_introl" ();
    Hashtbl.add coq_used_names "or_intror" ();
    Hashtbl.add coq_used_names "or_ind" ();
    Hashtbl.add coq_used_names "ex_intro" ();
    Hashtbl.add coq_used_names "ex_ind" ();
    Hashtbl.add coq_used_names "refl_equal" ();
    Hashtbl.add coq_used_names "eq_ind" ();
    Hashtbl.add coq_used_names "SinhE" ();
    Hashtbl.add coq_used_names "classic" ();
    Hashtbl.add coq_used_names "NNPP" ();
    Hashtbl.add coq_used_names "prop_ext" ();
    Hashtbl.add coq_used_names "functional_extensionality" ();
    Hashtbl.add coq_used_names "Sepsilon_spec" ();
    (*** Other names to avoid ***)
    Hashtbl.add coq_used_names "claim" ();

    (*FIXME add isar keywords*)
  end

let print_coqsig c =
  let rec print_coqsig_base l =
    match l with
        (x :: r) ->
	        print_coqsig_base r;
          if !mkproofterm = Some IsarScript then
            if x <> "i" (*FIXME "$i"="i"*) then
              (*there's no need to redeclare $i*)
              (*FIXME to avoid name clashes, could suffix names with something*)
              Printf.fprintf c "typedecl %s\n" x
            else ()
          else
	          if (not (!coq2)) then Printf.fprintf c "Variable %s:SType.\n" x
      | [] -> ()
  in
  let rec print_coqsig_const l =
    match l with
        ((x, a) :: r) ->
	        begin
	          print_coqsig_const r;
	          try
	            ignore (List.assoc x (!coqsig_def));
	          with
	            | Not_found ->
	                begin
		                try
                      if !mkproofterm = Some IsarScript then
                        begin
		                      Printf.fprintf c "consts %s :: \"" x;
		                      print_stp_isar c a (* coq_names *) false;
		                      Printf.fprintf c "\"\n"
                        end
                      else
                        begin
		                      Printf.fprintf c "Variable %s : " x;
		                      if (!coq2) then print_stp_coq2 c a false else print_stp_coq c a coq_names false;
		                      Printf.fprintf c ".\n"
                        end
		                with
		                  | Not_found ->
		                      begin
		                        if (c != stdout) then close_out c;
		                        raise (GenericError("A Satallax bug caused a problem creating the Coq/Isar file."))
		                      end
	                end
	        end
      | [] -> ()
  in
  let rec print_coqsig_def l =
    match l with
        ((x,a)::r) ->
	        begin
	          print_coqsig_def r;
	          try
	            let m = List.assoc x (!coqsig_def) in
                if !mkproofterm = Some IsarScript then
	                begin
	                  Printf.fprintf c "definition %s :: \"" x;
	                  print_stp_isar c a (* coq_names *) false;
	                  Printf.fprintf c "\"\n where \"%s == (" x;
	                  print_pretrm_isar c m coq_names coq_used_names (-1) (-1);
	                  Printf.fprintf c ")\"\n"
	                end
                else
	                begin
	                  Printf.fprintf c "Definition %s : " x;
	                  if (!coq2) then print_stp_coq2 c a false else print_stp_coq c a coq_names false;
	                  Printf.fprintf c "\n := ";
	                  if (!coq2) then print_pretrm_coq2 c m (-1) (-1) else print_pretrm_coq c m coq_names coq_used_names (-1) (-1);
	                  Printf.fprintf c ".\n"
	                end
	          with
	            | Not_found -> ()
	        end
      | [] -> ()
  in
  let rec print_coqsig_hyp l =
    match l with
        ((x,m)::r) ->
	        begin
	          try
              if !mkproofterm = Some IsarScript then
	              begin
	                print_coqsig_hyp r;
	                Printf.fprintf c "assumes %s : \"" x;
	                print_pretrm_isar c m coq_names coq_used_names (-1) (-1);
	                Printf.fprintf c "\"\n"
                end
              else
	              begin
	                print_coqsig_hyp r;
	                Printf.fprintf c "Hypothesis %s : " x;
	                if (!coq2) then print_pretrm_coq2 c m (-1) (-1) else print_pretrm_coq c m coq_names coq_used_names (-1) (-1);
	                Printf.fprintf c ".\n"
                end
	          with
	            | Not_found ->
	                begin
		                if (c != stdout) then close_out c;
		                raise (GenericError("A Satallax bug caused a problem creating the Coq file."))
	                end
	        end
      | [] -> ()
  in
    if (not (!coqlocalfile)) then
      begin
        begin
          match (!mkproofterm) with
            |	Some CoqSPfTerm ->
	              begin
	                Printf.fprintf c "Require Export stt3.\n";
	              end
            |	Some CoqScript ->
	              begin
	                Printf.fprintf c "Add LoadPath \"%s/coq\".\n" Config.satallaxdir;
	                Printf.fprintf c "Require Import stttab.\n";
	                Printf.fprintf c "Section SatallaxProblem.\n"
	              end
            |	Some IsarScript ->
	              begin
	                Printf.fprintf c "theory SatallaxProblem\n";
	                Printf.fprintf c "imports Satallax\n";
	                Printf.fprintf c "begin\n"
	              end
            |	_ -> ()
        end;
        print_coqsig_base !coqsig_base;
        print_coqsig_const !coqsig_const;
        print_coqsig_def !coqsig_const;
        if !mkproofterm = Some IsarScript then
	        Printf.fprintf c "\nlemma\n";
        print_coqsig_hyp !coqsig_hyp;
        match (!conjecture) with
          | Some (m,t,_) ->
              if !mkproofterm = Some IsarScript then
	              begin
	                Printf.fprintf c "shows %s : \"" (Hashtbl.find coq_hyp_names (!conjecturename));
	                (* print_pretrm_isar c m coq_names coq_used_names (-1) (-1); *)
	                trm_to_isar c (coqnorm t) (Syntax.Variables.make ());
	                Printf.fprintf c "\"\n";

                  (*FIXME currently all definitions are unfolded, irrespective of whether when they're used. This seems to reflect Satallax's usage anyway.*)
                  if List.length !coqsig_def > 0 then
	                  Printf.fprintf c "unfolding %s\n" (String.concat " " (List.map (fun (s, _) -> s ^ "_def") !coqsig_def))
	              end
              else
	              begin
	                Printf.fprintf c "Theorem %s : " (Hashtbl.find coq_hyp_names (!conjecturename));
	                if (!coq2) then print_pretrm_coq2 c m (-1) (-1) else print_pretrm_coq c m coq_names coq_used_names (-1) (-1);
	                Printf.fprintf c ".\n"
	              end
          | None ->
              if !mkproofterm = Some IsarScript then
                Printf.fprintf c "shows claim : \"False\"\n"
              else
                Printf.fprintf c "Theorem claim : False.\n"
      end

let declare_base_type a =
  if (!coq) then
    begin 
      let y = coqify_name a coq_names coq_used_names in
      coqsig_base := (y::!coqsig_base)
    end;
  Hashtbl.add name_base a ();
  name_base_list := (a::!name_base_list);
  if (get_bool_flag "CHOICE_AS_DEFAULT") then
    set_default_elt a (norm name_def (ap(Choice (Base a),Lam(Base a,False))))

let st_to_stp m =
  begin
    try
      to_stp m
    with
    | DeclareInd ->
	begin (*** Declare the base type i the first time it's seen.  Use a different name if an 'i' has already been used. ***)
	  declare_base_type "$i";
	  to_stp m
	end
  end

let st_to_trm_given_stp m tp =
  begin
    try
      let (n,_) = to_trm name_trm [] m (Some tp) in n
    with
    | DeclareInd ->
	begin (*** Declare the base type i the first time it's seen.  Use a different name if an 'i' has already been used. ***)
	  declare_base_type "$i";
	  let (n,_) = to_trm name_trm [] m (Some tp) in n
	end
  end

let st_to_trm m =
  begin
    try
      to_trm name_trm [] m None
    with
    | DeclareInd ->
	begin (*** Declare the base type i the first time it's seen.  Use a different name if an 'i' has already been used. ***)
	  declare_base_type "$i";
	  to_trm name_trm [] m None
	end
  end

let declare_typed_constant (name:string) (role:string) (m:pretrm) =
  begin
    if (!verbosity > 4) then (Printf.printf "declare_typed_constant %s %s\n%s\n" name role (pretrm_str m); flush stdout);
    match m with
      POf(PName(x),m) ->
	begin
	  match m with
	    PType -> (*** Actually unused. - April 20 2012 ***)
	      if (Hashtbl.mem name_base x) then raise (Redeclaration x);
	      if (Hashtbl.mem name_tp x) then raise (Redeclaration x);
	      declare_base_type x
	  | PName "$type" -> (*** The case that's used. Added April 20 2012 ***)
	      if (Hashtbl.mem name_base x) then raise (Redeclaration x);
	      if (Hashtbl.mem name_tp x) then raise (Redeclaration x);
	      declare_base_type x
	  | _ ->
	      let tp = (st_to_stp m) in
	      if (Hashtbl.mem name_base x) then raise (Redeclaration x);
	      if (Hashtbl.mem name_tp x) then raise (Redeclaration x);
	      if (!coq) then
		begin
		  let y = coqify_name x coq_names coq_used_names in
		  coqsig_const := (y,tp)::!coqsig_const
		end;
	      Hashtbl.add name_tp x tp;
	      Hashtbl.add name_trm x ((Name(x,tp),tp),ref false);
	      name_trm_list := (x,Name(x,tp),tp)::!name_trm_list
	end
    | _ -> raise (GenericError ("Incorrect format for type declaration " ^ name))
  end
    
(***
 THF official policy requires that all names are given a type before use,
 that definitions can be circular (in which case they must be treated as equations),
 and that definitions may appear *after* it's already been used in an assumption.
 In order to comply with this policy *and* do something reasonable in the 'usual' case,
 I do the following:

 1. I keep a hashtable (occurred_names) of typed names that have been used in an assumption.
 2. When I encounter a definition, if it's of the form (x = t), I first parse t.  If x has been used,
    then I include the equation as an axiom.  Otherwise, x is treated as a definition and expanded away.

 NOTE: If I wanted to be strict, I would exit if the definition is given without the name being given a type,
 but I will not require the type to be given.  I will print a warning if the verbosity is > 0.
 ***)
let declare_definition_real x m =
  if (Hashtbl.mem name_base x) then raise (Redeclaration x);
  if (Hashtbl.mem name_def x) then raise TreatAsAssumption; (*** treat it as an assumption per THF policy. - Mar 31, 2011 - Chad ***)
(*** raise (Redeclaration x); ***)
  try
    let tp = Hashtbl.find name_tp x in
    let tm = st_to_trm_given_stp m tp in
    try 
      let (_,r) = Hashtbl.find name_trm x in
      if (!r) then
	raise TreatAsAssumption (*** It's already been used, treat 'definition' as an assumption. ***)
      else
	raise Not_found
    with
    | Not_found ->
	begin
	  if (!coq) then
	    begin (*** The name was coqified when the type was declared. ***)
	      try
		let y = Hashtbl.find coq_names x in
		coqsig_def := (y,m)::!coqsig_def;
		coqsig_def_trm := (y,tm)::!coqsig_def_trm
	      with
	      | Not_found -> raise (GenericError("Could not find Coq version of name " ^ x))
	    end;
	  Hashtbl.add name_def_prenorm x tm;
	  Hashtbl.add name_def x (norm name_def (logicnorm tm))
	end
  with
  | Not_found ->
      begin (*** Giving a definition without giving it's type isn't allowed in THF anymore.  I'm still allowing it.  ***)
	if ((!verbosity > 0) && (not (!coqglobalfile)) && (not (!coqlocalfile))) then Printf.printf "WARNING: %s defined without giving type first.\n" x;
	let (tm,tp) = st_to_trm m in
	if (!coq) then
	  begin
	    let y = coqify_name x coq_names coq_used_names in
	    coqsig_const := (y,tp)::!coqsig_const;
	    coqsig_def := (y,m)::!coqsig_def;
	    coqsig_def_trm := (y,tm)::!coqsig_def_trm
	  end;
	Hashtbl.add name_tp x tp;
	Hashtbl.add name_trm x ((Name(x,tp),tp),ref false);
	name_trm_list := (x,Name(x,tp),tp)::!name_trm_list;
	Hashtbl.add name_def_prenorm x tm;
	Hashtbl.add name_def x (norm name_def (logicnorm tm))
      end

let rec declare_thf_logic_formula (name:string) (role:string) (m:pretrm) =
  begin
    if !verbosity > 4 then (Printf.printf "declare_thf_logic_formula %s %s\n" name role; flush stdout);
    if ((role = "axiom") || (role = "hypothesis") || (role = "lemma")) then
      begin
	if (Hashtbl.mem name_hyp name) then raise (Redeclaration name);
	let tm = st_to_trm_given_stp m Prop in
	if (!coq) then
	  begin
	    let y = coqify_name name coq_hyp_names coq_used_names in
	    coqsig_hyp := ((y,m)::!coqsig_hyp);
	    coqsig_hyp_trm := ((y,tm)::!coqsig_hyp_trm)
	  end;
	let tmn = norm name_def (logicnorm tm) in
	Hashtbl.add name_hyp name tmn;
	if (!verbosity > 20) then Printf.printf "name_hyp %s %s\n" name (trm_str tmn);
	initial_branch_prenorm := (tm::(!initial_branch_prenorm));
	initial_branch := (tmn::(!initial_branch))
      end
    else if ((role = "conjecture") || (role = "theorem")) then
      begin
	match (!conjecture) with
	| Some _ -> raise (GenericError "Problem file has more than one conjecture.")
	| None ->
	    let tm = st_to_trm_given_stp m Prop in
	    begin
	      conjecturename := name;
	      if (name != "claim") then
		ignore (coqify_name name coq_hyp_names coq_used_names);
	      let ntm = Ap(Neg,tm) in
	      let ntmn = norm name_def (logicnorm ntm) in
	      initial_branch_prenorm := (ntm::(!initial_branch_prenorm));
	      initial_branch := (ntmn::(!initial_branch));
	      conjecture := Some (m,tm,ntmn);
	      Hashtbl.add part_of_conjecture ntmn ()
	    end
      end
    else
      raise (GenericError ("Unknown role " ^ role))
  end
and declare_definition (name:string) (role:string) (m:pretrm) =
  try
    begin
      if (get_bool_flag "ALL_DEFS_AS_EQNS") then raise TreatAsAssumption;
      if !verbosity > 4 then (Printf.printf "declare_definition %s %s\n" name role; flush stdout);
      match m with
	PDef(PName(x),m) -> (*** No longer THF syntax. ***)
	  declare_definition_real x m
      | PAp(PAp(PEq,PName(x)),m) ->
	  declare_definition_real x m
      | _ -> (*** Treat as an assumption, now matter how it looks. Odd, but OK. This may be too liberal; we haven't decided yet. ***)
	  raise TreatAsAssumption
(*** raise (GenericError ("Incorrect format for definition " ^ name)) ***)
    end
  with
  | TreatAsAssumption ->
      declare_thf_logic_formula name "hypothesis" m

(*** Code for enumeration of types and terms - Dec 10, 2010 - Chad ***)
let enum_started = ref false
let enum_of_started_ : (stp,unit) Hashtbl.t = Hashtbl.create 5
let enum_of_started a =
  Hashtbl.mem enum_of_started_ a
let enum_of_start a =
  Hashtbl.add enum_of_started_ a ()
let type_continuations_rtp : (stp option,(stp -> int -> unit)) Hashtbl.t = Hashtbl.create 5
let term_continuations_rtp : (stp,(stp list * trm * int -> unit)) Hashtbl.t = Hashtbl.create 5
let usableTypes_rtp : (stp,(stp * int)) Hashtbl.t = Hashtbl.create 5
let usableTypes : (stp * stp * int) list ref = ref []
let usableHeads_rtp : (stp,(stp list * trm * int)) Hashtbl.t = Hashtbl.create 5

let new_type_continuation_rtp ar f =
  Hashtbl.add type_continuations_rtp (Some ar) f

let new_type_continuation f =
  Hashtbl.add type_continuations_rtp None f

let iter_type_continuations_rtp ar a d =
  List.iter (fun f -> f a d) (Hashtbl.find_all type_continuations_rtp (Some ar))

let iter_type_continuations a d =
  List.iter (fun f -> f a d) (Hashtbl.find_all type_continuations_rtp None)

let new_term_continuation_rtp ar f =
  Hashtbl.add term_continuations_rtp ar f

let iter_term_continuations_rtp ar sigmal m p =
  List.iter (fun f -> f (sigmal,m,p)) (Hashtbl.find_all term_continuations_rtp ar)

let new_usable_type_rtp ar a d =
  Hashtbl.add usableTypes_rtp ar (a,d);
  usableTypes := ((ar,a,d)::(!usableTypes))

let usable_types_rtp ar = Hashtbl.find_all usableTypes_rtp ar

let usable_types () = !usableTypes

let new_usable_head_rtp ar sigmal m n = Hashtbl.add usableHeads_rtp ar (sigmal,m,n)

let usable_heads_rtp ar = Hashtbl.find_all usableHeads_rtp ar

(*** search init ***)
let search_init () =
  (*** Add initial instantiations: true and false for o ***)
  add_instantiation Prop False;
  add_instantiation Prop (neg False)
  
(*** reset search ***)
let reset_search () =
  begin
    Hashtbl.clear clausesTable;
    clauses := [];
    clause_ruleinfo := Hashtbl.create 100;
    PQueue0.reset();
    PQueue1.reset();
    PQueue2.reset();
    Hashtbl.clear patoms;
    Hashtbl.clear natoms;
    Hashtbl.clear pchoiceatoms;
    Hashtbl.clear nchoiceatoms;
    Hashtbl.clear peqns;
    Hashtbl.clear neqns;
    Hashtbl.clear univpreds;
    Hashtbl.clear instantiations;
    Hashtbl.clear processed;
    enum_started := false;
    Hashtbl.clear enum_of_started_;
    Hashtbl.clear type_continuations_rtp;
    Hashtbl.clear term_continuations_rtp;
    Hashtbl.clear usableTypes_rtp;
    usableTypes := [];
    Hashtbl.clear usableHeads_rtp;
    Hashtbl.clear choiceopnames;
    Hashtbl.clear filtered;
    prop_fo_forms := [];
    Hashtbl.clear stp_fo_forms;
    Hashtbl.clear fo_types_h;
    fo_types := [];
    Hashtbl.clear fo_ecounter;
    search_init()
  end

let print_model b =
  Hashtbl.iter
    (fun m i ->
      let v = minisat_modelValue i in
      if (b) then
	begin
	  if (v = 0) then (*** 0 means true ***)
	    Printf.printf "%d %s\n" i (trm_str m);
	end
      else
	if (v < 2) then
	  Printf.printf "%d%s %s\n" i (if (v = 0) then "+" else "-") (trm_str m)
      )
    atom_hash

let rec select_list_rec l sl rl =
  match sl with
  | (j::sr) -> select_list_rec l sr (List.nth l j::rl)
  | [] -> rl

let select_axioms_list : int list ref = ref [];;

let select_axioms () =
  (*** I should select the prenorm branch too, but that's only needed for proof reconstruction. ***)
  initial_branch := select_list_rec (!initial_branch) (!select_axioms_list) [];
  if (!verbosity > 4) then
    let i = ref 0 in
    begin
      Printf.printf "Initial branch after selection:\n";
      incr i;
      List.iter (fun m -> Printf.printf "%d %s\n" (!i) (trm_str m)) (!initial_branch)
    end;;

let print_num_axioms () =
  let n = List.length (!initial_branch) in
  Printf.printf "(NUMAXIOMS \"%s\" %d)\n" (!problemfile) n;
  exit 123
  
