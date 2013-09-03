open State
open String
open Syntax
open Refutation
open Flag

(** Prints type m as a Coq-formatted string on the out_channel c  **)
let rec print_stp_coq c m h p =
  match m with
  | Base x ->
	let x = try (Hashtbl.find h x) with Not_found -> failwith("print_stp_coq can't find coqname of "^x) in
      Printf.fprintf c "%s" x
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
(* FIXME moved to Syntax
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

(** Input: out_channel c, term m, list of bound variables 
	Invariant: m is closed, if  it is enclosed in quantifiers for the bound variables 
	Prints the term m on the channel c**)
let rec trm_to_coq c m bound lp rp =
  match m with
    Name(x,_) -> (* Definitions *)
	let x = try (Hashtbl.find coq_names x) with Not_found -> x in
      Printf.fprintf c "%s" x
  | False -> (* Bottom *)
	Printf.fprintf c "False"
  | Ap(Ap(Imp,m1),False) ->  (* Negation *)
	if ((lp < 0) && (rp < 30)) then
	begin
	  Printf.fprintf c "~ ";
	  trm_to_coq c m1 bound 30 rp;
	end
      else
	begin
	  Printf.fprintf c "(~ ";
	  trm_to_coq c m1 bound 30 (-1);
	  Printf.fprintf c ")";
	end
   | Ap(Ap(Imp,m1),m2) -> (* Implication *)
      if ((lp < 17) && (rp < 16)) then
	begin
	  trm_to_coq c m1 bound lp 17;
	  Printf.fprintf c " -> ";
	  trm_to_coq c m2 bound 16 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  trm_to_coq c m1 bound (-1) 17;
	  Printf.fprintf c " -> ";
	  trm_to_coq c m2 bound 16 (-1);
	  Printf.fprintf c ")";
	end
  | Ap(Imp,m1) -> trm_to_coq c (Lam(Prop,Ap(Ap(Imp,shift m1 0 1),DB(0,Prop)))) bound lp rp;
  | Imp -> trm_to_coq c (Lam(Prop,Lam(Prop,Ap(Ap(Imp,DB(1,Prop)),DB(0,Prop))))) bound lp rp; 
  | Ap(Forall(a),Lam(_,m1)) -> (* forall with Lam *)
      begin
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c "(";
	begin
	  Printf.fprintf c "forall";
	  print_all_coq c a m1 bound
	end;
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c ")";
      end
  | Forall(a) ->
      begin
	if ((lp >= 5000) || (rp >= 5001)) then Printf.fprintf c "(";
	Printf.fprintf c "SPi "; print_stp_coq c a coq_names true;
	if ((lp >= 5000) || (rp >= 5001)) then Printf.fprintf c ")";
      end
  | Ap(Ap(Eq(a),m1),m2) -> (* Equality *)
      if ((lp < 40) && (rp < 40)) then
	begin
	  trm_to_coq c m1 bound lp 40;
	  Printf.fprintf c " = ";
	  trm_to_coq c m2 bound 40 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  trm_to_coq c m1 bound (-1) 40;
	  Printf.fprintf c " = ";
	  trm_to_coq c m2 bound 40 (-1);
	  Printf.fprintf c ")";
	end
  | Eq(a) ->     
	if ((lp < 5000) && (rp < 5001)) then
	begin
	  Printf.fprintf c "Seq ";
	  print_stp_coq c a coq_names true;
	end
      else
	begin
	  Printf.fprintf c "(Seq ";
	  print_stp_coq c a coq_names true;
	  Printf.fprintf c ")";
	end      
(*** I'm now always explicitly giving the Stype
  | Ap(Choice(a),m) ->   (* Choice *)  
	if ((lp < 5000) && (rp < 5001)) then
	begin
	  Printf.fprintf c "@Sepsilon ";
	  trm_to_coq c m bound 5001 rp;
	end
      else
	begin
	  Printf.fprintf c "(@Sepsilon ";
	  
	  trm_to_coq c m bound 5001 (-1);
	  Printf.fprintf c ")";
	end      
***)
  | Choice(a) ->
      if ((lp < 5000) && (rp < 5001)) then
	begin
	  Printf.fprintf c "@Sepsilon ";
	  print_stp_coq c a coq_names true
	end
      else
	begin
	  Printf.fprintf c "(@Sepsilon ";
	  print_stp_coq c a coq_names true;
	  Printf.fprintf c ")"
	end
  | True -> (* Top *)
	Printf.fprintf c "True"
  | Ap(Ap(And,m1),m2) -> (* conjunction *)
      if ((lp < 21) && (rp < 20)) then
	begin
	  trm_to_coq c m1 bound lp 21;
	  Printf.fprintf c " /\\ ";
	  trm_to_coq c m2 bound 20 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  trm_to_coq c m1 bound (-1) 21;
	  Printf.fprintf c " /\\ ";
	  trm_to_coq c m2 bound 20 (-1);
	  Printf.fprintf c ")";
	end
  | And ->Printf.fprintf c "and"
  | Ap(Ap(Or,m1),m2) -> (* disjunction *)
      if ((lp < 19) && (rp < 18)) then
	begin
	  trm_to_coq c m1 bound lp 19;
	  Printf.fprintf c " \\/ ";
	  trm_to_coq c m2 bound 18 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  trm_to_coq c m1 bound (-1) 19;
	  Printf.fprintf c " \\/ ";
	  trm_to_coq c m2 bound 18 (-1);
	  Printf.fprintf c ")";
	end
  | Or -> Printf.fprintf c "or"
  | Ap(Ap(Iff,m1),m2) -> (* equivalenz *)
      if ((lp < 14) && (rp < 14)) then
	begin
	  trm_to_coq c m1 bound lp 14;
	  Printf.fprintf c " <-> ";
	  trm_to_coq c m2 bound 14 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  trm_to_coq c m1 bound (-1) 14;
	  Printf.fprintf c " <-> ";
	  trm_to_coq c m2 bound 14 (-1);
	  Printf.fprintf c ")";
	end
  | Iff -> Printf.fprintf c "iff"
  | Neg -> Printf.fprintf c "not"
  | Ap(Exists(a),Lam(_,m1)) -> (* exist *)
      begin
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c "(";
	begin
	  print_ex_coq c a m1 bound
	end;
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c ")";
      end
  | Exists(a) ->
      begin
	if ((lp >= 5000) || (rp >= 5001)) then Printf.fprintf c "(";
	Printf.fprintf c "SSigma "; print_stp_coq c a coq_names true;
	if ((lp >= 5000) || (rp >= 5001)) then Printf.fprintf c ")";
      end
  | DB(i,a) -> (* Bound variable *)
	Printf.fprintf c "%s" (Variables.get i bound)
  | Lam(a,m) ->
      begin
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c "(";
	begin
	  Printf.fprintf c "fun";
	  print_lam_coq c a m bound
	end;
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c ")";
      end
  | Ap(m1,m2) ->     
	if ((lp < 5000) && (rp < 5001)) then
	begin
	  trm_to_coq c m1 bound lp 5000;
	  Printf.fprintf c " ";
	  trm_to_coq c m2 bound 5001 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  trm_to_coq c m1 bound (-1) 5000;
	  Printf.fprintf c " ";
	  trm_to_coq c m2 bound 5001 (-1);
	  Printf.fprintf c ")";
	end      
  | _ -> raise (GenericSyntaxError ("Unknown case in trm_to_coq version : " ^ (trm_str m)))

 (* Prints consecutive lambda-terms as a single fun in Coq. *) 
and print_lam_coq c a m bound =
	let bound = Variables.push bound in
	Printf.fprintf c " ("; Printf.fprintf c "%s" (Variables.top bound); Printf.fprintf c ":"; print_stp_coq c a coq_names false; Printf.fprintf c ")";
	match m with
		| Lam(b,m') -> print_lam_coq c b m' bound
		| _ -> Printf.fprintf c " => "; trm_to_coq c m bound (-1) (-1)

(* Prints consecutive forall-terms together with the corresponding lambda-terms as a single forall in Coq. *) 		
and print_all_coq c a m bound =
  let bound = Variables.push bound in
  Printf.fprintf c " ("; Printf.fprintf c "%s" (Variables.top bound); Printf.fprintf c ":"; print_stp_coq c a coq_names false; Printf.fprintf c ")";
  match m with
  | Ap(Forall(a'),Lam(_,m'))-> print_all_coq c a' m' bound
  | _ -> Printf.fprintf c ", "; trm_to_coq c m bound (-1) (-1)

(* Prints an exist-term together with the corresponding lambda-term as an exists in Coq. *) 		
and print_ex_coq c a m bound =
 	let bound = Variables.push bound in
	Printf.fprintf c "exists"; Printf.fprintf c " %s" (Variables.top bound); 
	Printf.fprintf c ":"; print_stp_coq c a coq_names false; 
        Printf.fprintf c ", ";
	trm_to_coq c m bound (-1) (-1)

(** Input: Name x, Type a, association list (term -> hypothesis name) hyp 
	Output: name of the hypothesis that defines x as a choice operator **)
let get_Choicop_axiom x a hyp = 
let ao = Ar(a,Prop) in
let m1 = Ap (Forall (ao),Lam (ao,Ap (Forall a,Lam (a,Ap (Ap (Imp, Ap (DB (1, ao), DB (0, a))),
	 Ap (DB (1, ao),Ap (Name (x, Ar (ao, a)), DB (1, ao)))))))) in
let m2 = Ap (Forall (ao),Lam (ao,Ap(Ap (Imp,Ap(Ap (Imp,Ap (Forall a,Lam (a,
	Ap (Ap (Imp, Ap (DB (1, ao), DB (0, a))),False)))),False)),Ap (DB (0, ao),
	Ap (Name (x, Ar (ao, a)),DB (0, ao))))))in
let m3 = Ap (Forall (ao),Lam (ao,Ap(Ap (Imp,Ap (Exists a,Lam (a,
	Ap (DB (1, ao), DB (0, a))))),Ap (DB (0, ao),
	Ap (Name (x, Ar (ao, a)),DB (0, ao))))))in
try
let (m,h)= List.find (fun (m,h) -> m = m1 || m = m2 || m = m3 ) hyp in h
with Not_found -> "missing_choice_axiom_for"^x


let next_fresh_hyp : int ref = ref 0

let next_fresh_trm : int ref = ref 0

(** Input: unit
	Output: returns next fresh hypothesis name **)
let rec get_hyp_name hyp =
	let x = "H" ^ (string_of_int (!next_fresh_hyp)) in
	incr next_fresh_hyp;
	if (Hashtbl.mem coq_used_names x) 
	then get_hyp_name hyp
  	else x 

let rec find_fresh_consts n const =
  begin
    match n with 
    | Name(x,a) ->
	let x =try Hashtbl.find coq_names x with
	  Not_found
	  ->
	    failwith ("add_fresh_const can't find "^x^" in coq_names") in
	if List.mem_assoc x const then [] else [(x,a)] 
    | Ap(m1,m2) -> find_fresh_consts m1 const @ find_fresh_consts m2 const
    | Lam(_,m) -> find_fresh_consts m const
    | _ -> []
  end

(** Input: out_channel c, association list (constant name -> type) const, term n, Space string sp 
	Output: prints inhabitation tactic for fresh constants on c and returns an updated list const **)	
let add_fresh_const is_isar c const n sp =
  let add_fresh_const' cons (x, a) =
    if List.mem (x, a) cons then cons
    else
      begin
        if is_isar then
          begin
            Printf.fprintf c "%sfixes (%s :: " sp x;
            print_stp_isar c a false;
            Printf.fprintf c ")\n";
          end
        else
          begin
            Printf.fprintf c "%stab_inh (" sp;
            print_stp_coq c a coq_names false;
            Printf.fprintf c ") %s.\n" x;
          end;
        (x, a) :: cons
      end
  in
    List.fold_left add_fresh_const'
      const (find_fresh_consts (coqnorm n) const)

let rec lookup w s hyp =
  try
    List.assoc s hyp
  with
  | Not_found ->
      Printf.printf "%s: Could not find hyp name\ns = %s\nhyp:\n" w (trm_str s);
      List.iter (fun (m,h) -> Printf.printf "%s: %s\n" h (trm_str m)) hyp;
      failwith ("Could not find hyp name")
 
(** Input: out_channel c, refutation r, association list (term -> hypothesis name) hyp, association list (constant name -> type) const, Space string sp 
	Output: unit, prints refutation r to c **)
let rec ref_coq1 c r hyp const sp=
	match r with
 | Conflict(s,ns) -> 			
	Printf.fprintf c "%stab_conflict %s %s.\n" sp (lookup "0" (coqnorm s) hyp) (lookup "1" (coqnorm ns) hyp)
 | Fal(_) -> 				
	Printf.fprintf c "%stab_false %s.\n" sp (lookup "2" False hyp) 
 | NegRefl(s) -> 			
	Printf.fprintf c "%stab_refl %s.\n" sp (lookup "3" (coqnorm s) hyp)
 | Implication(h,s,t,r1,r2) -> 	
	let h1 = get_hyp_name() in	
	Printf.fprintf c "%stab_imp %s %s.\n" sp (lookup "4" (coqnorm h) hyp) h1;
	ref_coq1 c r1 ((coqnorm s,h1)::hyp) const (sp^" ");
	ref_coq1 c r2 ((coqnorm t,h1)::hyp) const (sp^" ");
 | Disjunction(h,s,t,r1,r2) ->
	let h1 = get_hyp_name() in	
	Printf.fprintf c "%stab_or %s %s.\n" sp (lookup "5" (coqnorm h) hyp) h1;
	ref_coq1 c r1 ((coqnorm s,h1)::hyp) const (sp^" ");
	ref_coq1 c r2 ((coqnorm t,h1)::hyp) const (sp^" "); 	
 | NegConjunction(h,s,t,r1,r2) ->
	let h1 = get_hyp_name() in	
	Printf.fprintf c "%stab_nand %s %s.\n" sp (lookup "6" (coqnorm h) hyp) h1;
	ref_coq1 c r1 ((coqnorm s,h1)::hyp) const (sp^" ");
	ref_coq1 c r2 ((coqnorm t,h1)::hyp) const (sp^" ");  
 | NegImplication(h,s,t,r1) ->
	let h1 = get_hyp_name() in
	let h2 = get_hyp_name() in	
	Printf.fprintf c "%stab_negimp %s %s %s.\n" sp (lookup "7" (coqnorm h) hyp) h1 h2;
	ref_coq1 c r1 ((coqnorm s,h1)::(coqnorm t,h2)::hyp) const sp
 | Conjunction(h,s,t,r1) ->
	let h1 = get_hyp_name() in
	let h2 = get_hyp_name() in	
	Printf.fprintf c "%stab_and %s %s %s.\n" sp (lookup "8" (coqnorm h) hyp) h1 h2;
	ref_coq1 c r1 ((coqnorm s,h1)::(coqnorm t,h2)::hyp) const sp
 | NegDisjunction(h,s,t,r1) ->
	let h1 = get_hyp_name() in
	let h2 = get_hyp_name() in	
	Printf.fprintf c "%stab_nor %s %s %s.\n" sp (lookup "9" (coqnorm h) hyp) h1 h2;
	ref_coq1 c r1 ((coqnorm s,h1)::(coqnorm t,h2)::hyp) const sp
 | All(h,s,r1,a,m,n) ->
	let const = add_fresh_const false c const n sp in
	let h1 = get_hyp_name() in	
	Printf.fprintf c "%stab_all %s (" sp (lookup "10" (coqnorm h) hyp); 
	(trm_to_coq c n (Variables.make ()) (-1) (-1));
	Printf.fprintf c ") %s.\n" h1;
	ref_coq1 c r1 ((coqnorm s,h1)::hyp) const sp
 | NegAll(h,s,r1,a,m,x) ->
	let h1 = get_hyp_name() in
	let x = ( Hashtbl.find coq_names x ) in
	Printf.fprintf c "%stab_negall %s %s %s.\n" sp (lookup "11" (coqnorm h) hyp) x h1;
	ref_coq1 c r1 ((coqnorm s,h1)::hyp) ((x,a)::const) sp
 | Exist(h,s,r1,a,m,x) ->
	let h1 = get_hyp_name() in
	let x = ( Hashtbl.find coq_names x ) in
	Printf.fprintf c "%stab_ex %s %s %s.\n" sp (lookup "12" (coqnorm h) hyp) x h1;
	ref_coq1 c r1 ((coqnorm s,h1)::hyp) ((x,a)::const) sp
 | NegExist(h,s,r1,a,m,n) ->
	let const = add_fresh_const false c const n sp in
	let h1 = get_hyp_name() in	
	Printf.fprintf c "%stab_negex %s (" sp (lookup "13" (coqnorm h) hyp); 
	(trm_to_coq c n (Variables.make ()) (-1) (-1));
	Printf.fprintf c ") %s.\n" h1;
	ref_coq1 c r1 ((coqnorm s,h1)::hyp) const sp	
 | Mating(h1,h2, ss, rs) ->
	let h3 = get_hyp_name() in	
	Printf.fprintf c "%stab_mat %s %s %s.\n" sp (lookup "14" (coqnorm h1) hyp) (lookup "15" (coqnorm h2) hyp) h3;
	List.iter (fun (s,r) -> ref_coq1 c r ((coqnorm s,h3)::hyp) const (sp^" ")) (List.combine ss rs)
 | Decomposition(h1, ss, rs) ->
	let h3 = get_hyp_name() in	
	Printf.fprintf c "%stab_dec %s %s.\n" sp (lookup "16" (coqnorm h1) hyp) h3;
	List.iter (fun (s,r) -> ref_coq1 c r ((coqnorm s,h3)::hyp) const (sp^" ")) (List.combine ss rs) 	
 | Confront(h1,h2,su,tu,sv,tv,r1,r2) ->
	let h3 = get_hyp_name() in
	let h4 = get_hyp_name() in	
	Printf.fprintf c "%stab_con %s %s %s %s.\n" sp (lookup "17" (coqnorm h1) hyp) (lookup "18" (coqnorm h2) hyp) h3 h4;
	ref_coq1 c r1 ((coqnorm su,h3)::(coqnorm tu,h4)::hyp) const (sp^" ");
	ref_coq1 c r2 ((coqnorm sv,h3)::(coqnorm tv,h4)::hyp) const (sp^" ");	
 | Trans(h1,h2,su,r1) ->
	let h3 = get_hyp_name() in	
	Printf.fprintf c "%stab_trans %s %s %s.\n" sp (lookup "19" (coqnorm h1) hyp) (lookup "20" (coqnorm h2) hyp) h3;
	ref_coq1 c r1 ((coqnorm su,h3)::hyp) const (sp^" ");
 | NegEqualProp(h,s,t,r1,r2) -> 
	let h1 = get_hyp_name() in
	let h2 = get_hyp_name() in	
	Printf.fprintf c "%stab_be %s %s %s.\n" sp (lookup "21" (coqnorm h) hyp) h1 h2;
	ref_coq1 c r1 ((coqnorm s,h1)::(coqnorm (neg t),h2)::hyp) const (sp^" ");
	ref_coq1 c r2 ((coqnorm (neg s),h1)::(coqnorm t,h2)::hyp) const (sp^" ");
 | EqualProp(h,s,t,r1,r2) -> 
	let h1 = get_hyp_name() in
	let h2 = get_hyp_name() in	
	Printf.fprintf c "%stab_bq %s %s %s.\n" sp (lookup "22" (coqnorm h) hyp) h1 h2;
	ref_coq1 c r1 ((coqnorm s,h1)::(coqnorm t,h2)::hyp) const (sp^" ");
	ref_coq1 c r2 ((coqnorm (neg s),h1)::(coqnorm (neg t),h2)::hyp) const (sp^" ");
 | NegAequivalenz(h,s,t,r1,r2) -> 
	let h1 = get_hyp_name() in
	let h2 = get_hyp_name() in	
	Printf.fprintf c "%stab_negiff %s %s %s.\n" sp (lookup "23" (coqnorm h) hyp) h1 h2;
	ref_coq1 c r1 ((coqnorm s,h1)::(coqnorm (neg t),h2)::hyp) const (sp^" ");
	ref_coq1 c r2 ((coqnorm (neg s),h1)::(coqnorm t,h2)::hyp) const (sp^" ");
 | Aequivalenz(h,s,t,r1,r2) -> 
	let h1 = get_hyp_name() in
	let h2 = get_hyp_name() in	
	Printf.fprintf c "%stab_iff %s %s %s.\n" sp (lookup "24" (coqnorm h) hyp) h1 h2;
	ref_coq1 c r1 ((coqnorm s,h1)::(coqnorm t,h2)::hyp) const (sp^" ");
	ref_coq1 c r2 ((coqnorm (neg s),h1)::(coqnorm (neg t),h2)::hyp) const (sp^" ");
 | NegEqualFunc(h,s,r1) ->
	let h1 = get_hyp_name() in	
	Printf.fprintf c "%stab_fe %s %s.\n" sp (lookup "25" (coqnorm h) hyp) h1;
	ref_coq1 c r1 ((coqnorm s,h1)::hyp) const sp
 | EqualFunc(h,s,r1) ->
	let h1 = get_hyp_name() in	
	Printf.fprintf c "%stab_fq %s %s.\n" sp (lookup "26" (coqnorm h) hyp) h1;
	ref_coq1 c r1 ((coqnorm s,h1)::hyp) const  sp
 | ChoiceR(eps,pred,s,t,r1,r2) -> 
     let const = add_fresh_const false c const pred sp in
     let h1 = get_hyp_name() in
     begin
       match eps with
       | Choice(a) -> 
	   Printf.fprintf c "%stab_choice " sp;
	   print_stp_coq c a coq_names true;
	   Printf.fprintf c " (";
	   (trm_to_coq c pred (Variables.make ()) (-1) (-1));
	   Printf.fprintf c ") %s.\n" h1;
	   ref_coq1 c r1 ((coqnorm s,h1)::hyp) const (sp^" ");
	   ref_coq1 c r2 ((coqnorm t,h1)::hyp) const (sp^" ");
       | Name(x,Ar(Ar(a,Prop),_)) ->
	   Printf.fprintf c "%stab_choice' " sp;
	   print_stp_coq c a coq_names true;
	   Printf.fprintf c " (";
	   (trm_to_coq c eps (Variables.make ()) (-1) (-1));
	   Printf.fprintf c ") (";
	   (trm_to_coq c pred (Variables.make ()) (-1) (-1));
	   Printf.fprintf c ") %s %s.\n" (get_Choicop_axiom x a hyp) h1;
	   ref_coq1 c r1 ((coqnorm s,h1)::hyp) const (sp^" ");
	   ref_coq1 c r2 ((coqnorm t,h1)::hyp) const (sp^" ");
       | _ -> failwith "eps is not a valid epsilon"
     end
 | Cut(s,r1,r2) -> 
	let const = add_fresh_const false c const s sp in
	let h1 = get_hyp_name() in	
	Printf.fprintf c "%stab_cut (" sp;
	(trm_to_coq c s (Variables.make ()) (-1) (-1));
	Printf.fprintf c ") %s.\n" h1;
	ref_coq1 c r2 ((coqnorm (neg s),h1)::hyp) const (sp^" ");
	ref_coq1 c r1 ((coqnorm s,h1)::hyp) const (sp^" ");
 | DoubleNegation(h,s,r1) ->
	let h1 = get_hyp_name() in	
	Printf.fprintf c "%stab_dn %s %s.\n" sp (lookup "27" (coqnorm h) hyp) h1;
	ref_coq1 c r1 ((coqnorm s,h1)::hyp) const sp;
 | Rewrite(prefix,pt,pt',r1) ->
	let h =  coqnorm (Ap(prefix,pt)) in
	let h1 = lookup "28" h hyp in	
	let s =  coqnorm (Ap(prefix,pt')) in 
	let h2 = get_hyp_name() in
	begin
	match pt with
		| True -> 	Printf.fprintf c "%stab_rew_true %s %s (" sp h1 h2;
				(trm_to_coq c prefix (Variables.make ()) (-1) (-1));  Printf.fprintf c ") .\n"; 
		| And -> 	Printf.fprintf c "%stab_rew_and %s %s (" sp h1 h2;
				(trm_to_coq c prefix (Variables.make ()) (-1) (-1));  Printf.fprintf c ") .\n"; 
		| Or -> 	Printf.fprintf c "%stab_rew_or %s %s (" sp h1 h2;
				(trm_to_coq c prefix (Variables.make ()) (-1) (-1));  Printf.fprintf c ") .\n";
		| Iff -> 	Printf.fprintf c "%stab_rew_iff %s %s (" sp h1 h2;
				(trm_to_coq c prefix (Variables.make ()) (-1) (-1));  Printf.fprintf c ") .\n";
		| Exists(_) -> 	Printf.fprintf c "%stab_rew_ex %s %s (" sp h1 h2;
				(trm_to_coq c prefix (Variables.make ()) (-1) (-1));  Printf.fprintf c ") .\n";
		| Eq(_) -> 	Printf.fprintf c "%stab_rew_sym %s %s (" sp h1 h2;
				(trm_to_coq c prefix (Variables.make ()) (-1) (-1));  Printf.fprintf c ") .\n";
		| Lam(_,Lam(_,Ap(DB(1,_),DB(0,_)))) -> 
				Printf.fprintf c "%stab_rew_eta %s %s (" sp h1 h2;
				(trm_to_coq c prefix (Variables.make ()) (-1) (-1));  Printf.fprintf c ") .\n";
		| Lam(Ar(Prop,Prop),Ap(Ap(Imp,Ap(Ap(Imp,DB(0,Prop)),False)),False)) -> 
				Printf.fprintf c "%stab_rew_dn %s %s (" sp h1 h2;
				(trm_to_coq c prefix (Variables.make ()) (-1) (-1));  Printf.fprintf c ") .\n";
		| Lam(_,Lam(_,Ap(Forall(_),Lam(_,(Ap(Ap(Imp,(Ap(DB(0,_),DB(2,_)))),(Ap(DB(0,_),DB(1,_)))) ))) )) -> 
				Printf.fprintf c "%stab_rew_leib1 %s %s (" sp h1 h2;
				(trm_to_coq c prefix (Variables.make ()) (-1) (-1));  Printf.fprintf c ") .\n";
		| Lam(_,Lam(_,Ap(Forall(_),Lam(_,(Ap(Ap(Imp,Ap(Ap(Imp,(Ap(DB(0,_),DB(2,_)))),False)),Ap(Ap(Imp,(Ap(DB(0,_),DB(1,_)))),False)) ))) )) -> 
				Printf.fprintf c "%stab_rew_leib2 %s %s (" sp h1 h2;
				(trm_to_coq c prefix (Variables.make ()) (-1) (-1));  Printf.fprintf c ") .\n";
		| Lam(_,Lam(_,Ap(Forall(_),Lam(_,(Ap(Ap(Imp,(Ap(Forall(_),Lam(_,(Ap(Ap(DB(1,_),DB(0,_)),DB(0,_)))))) ),(Ap(Ap(DB(0,_),DB(2,_)),DB(1,_)))) ) )) )) -> 
				Printf.fprintf c "%stab_rew_leib3 %s %s (" sp h1 h2;
				(trm_to_coq c prefix (Variables.make ()) (-1) (-1));  Printf.fprintf c ") .\n";
		| Lam(_,Lam(_, Ap(Forall(_),Lam(_,(Ap(Ap(Imp,(Ap(Ap(Imp,(Ap(Ap(DB(0,_),DB(2,_)),DB(1,_)))),False) )),(Ap(Ap(Imp,(Ap(Forall(_),Lam(_,(Ap(Ap(DB(1,_),DB(0,_)),DB(0,_))))) )),False) )) ) )) )) -> 
				Printf.fprintf c "%stab_rew_leib4 %s %s (" sp h1 h2;
				(trm_to_coq c prefix (Variables.make ()) (-1) (-1));  Printf.fprintf c ") .\n";
		| _ -> failwith("unknown rewrite step found in ref_coq" ^ (trm_str pt))
	end;
	ref_coq1 c r1 ((s,h2)::hyp) const sp
 | Delta(h,s,x,r1) ->
	let h1 = (lookup "29" (coqnorm h) hyp) in	
	Printf.fprintf c "%sunfold %s in %s.\n" sp ( Hashtbl.find coq_names x ) h1;
	ref_coq1 c r1 ((coqnorm s,h1)::hyp) const sp;
 | KnownResult(s,name,al,r1) ->
     begin
       match al with
       | (_::_) ->
	   let h1 = get_hyp_name() in
	   Printf.fprintf c "%sset (%s := (%s" sp h1 name;
	   List.iter
	     (fun a ->
	       Printf.fprintf c " ";
	       print_stp_coq c a coq_names true)
	     al;
	   Printf.fprintf c ")).\n";
	   ref_coq1 c r1 ((coqnorm s,h1)::hyp) const sp
       | [] ->
	   ref_coq1 c r1 ((coqnorm s,name)::hyp) const sp
     end;
 | NYI(h,s,r1) -> failwith("NYI step found in ref_coq" )
 | Timeout -> failwith("Timeout step found in ref_coq" )
 | _ -> failwith("unknown refutation case in ref_coq" )    

 (** Prints refutation r to out_channel c **)
let ref_coq c r = 
	(* get conjecture *)
	let con =match !conjecture with Some(_,con,_)->coqnorm con | None-> False in
	(* initialise hypotheses *)
	let hyp = List.fold_left (fun l (s,pt) -> (coqnorm pt,s)::l ) [] !coqsig_hyp_trm in
	let h1 = get_hyp_name() in
  Printf.fprintf c "\ntab_start %s.\n" h1;
  ref_coq1 c r ((neg con,h1)::hyp) (!coqsig_const) ""; 
  Printf.fprintf c "Qed.\n";
  Printf.fprintf c "End SatallaxProblem.\n" 

let forallbvarnames : (string,string) Hashtbl.t = Hashtbl.create 100;;
let nexistsbvarnames : (string,string) Hashtbl.t = Hashtbl.create 100;;

let next_fresh_name : int ref = ref 0
let get_fresh_name () =
  next_fresh_name := 1 + !next_fresh_name;
  "SOMENAME__" ^ (string_of_int (!next_fresh_name)) (*FIXME check for name collisions*)

let rec countup from for_many acc : int list =
  if for_many = 0 then List.rev acc
  else countup (from + 1) (for_many - 1) (from :: acc)

let trm_to_isar_rembvar x c m bound =
  match m with
    | Ap(Forall(a),Lam(_,m1)) ->
        let bound = Variables.push bound in
        let y = Variables.top bound in
          Hashtbl.add forallbvarnames x y;
          Printf.fprintf c "(! "; Printf.fprintf c "%s" y; Printf.fprintf c "::"; print_stp_isar c a (*Hashtbl.create 0(*FIXME*)*) false; Printf.fprintf c ". ";
          trm_to_isar c m1 bound; Printf.fprintf c ")"
    | Ap(Neg,Ap(Exists(a),Lam(_,m1))) ->
        let bound = Variables.push bound in
        let y = Variables.top bound in
          Hashtbl.add nexistsbvarnames x y;
          Printf.fprintf c "(~(? "; Printf.fprintf c "%s" y; Printf.fprintf c "::"; print_stp_isar c a (*Hashtbl.create 0(*FIXME*)*) false; Printf.fprintf c ". ";
          trm_to_isar c m1 bound; Printf.fprintf c "))"
    | Ap(Ap(Imp,Ap(Exists(a),Lam(_,m1))),False) ->
        let bound = Variables.push bound in
        let y = Variables.top bound in
          Hashtbl.add nexistsbvarnames x y;
          Printf.fprintf c "(~(? "; Printf.fprintf c "%s" y; Printf.fprintf c "::"; print_stp_isar c a (*Hashtbl.create 0(*FIXME*)*) false; Printf.fprintf c ". ";
          trm_to_isar c m1 bound; Printf.fprintf c "))"
    | _ ->
        trm_to_isar c m bound


let rec ref_isabellehol1 c r hyp const sp=
  (*c is channel,
    hyp is shared hypotheses,
    h1 is new hypothesis' name,
    s and t are the new hypothesis terms,
    r1 and r2 are the remainder refutations*)
  let sp' = sp ^ "  " in
  let sp'' = sp' ^ "  " in
  let tab_disj c hyp h1 s t r1 r2 =
    Printf.fprintf c "%sfrom %s have False\n" sp h1;
    Printf.fprintf c "%sproof\n" sp';
    Printf.fprintf c "%sassume %s : \"" sp'' h1;
    trm_to_isar c (coqnorm s) (Variables.make ());
    Printf.fprintf c "\"\n";
    ref_isabellehol1 c r1 ((coqnorm s, h1) :: hyp) const sp'';
    Printf.fprintf c "%snext\n" sp';
    Printf.fprintf c "%sassume %s : \"" sp'' h1;
    trm_to_isar c (coqnorm t) (Variables.make ());
    Printf.fprintf c "\"\n";
    ref_isabellehol1 c r2 ((coqnorm t, h1) :: hyp) const sp'';
    Printf.fprintf c "%sqed\n" sp';
    Printf.fprintf c "%sthus ?thesis by blast\n" sp' in
  (*like tab_disj, but with two hypotheses*)
  let tab_disj2 c hyp h1 h2 (s1, s2) (t1, t2) r1 r2 =
	  Printf.fprintf c "%sfrom %s have False\n" sp h1;
	  Printf.fprintf c "%sproof\n" sp;
	  Printf.fprintf c "%sassume %s : \"" sp' h1;
	  trm_to_isar c (coqnorm s1) (Variables.make ());
	  Printf.fprintf c "\"\n";
	  Printf.fprintf c "%s and %s : \"" sp' h2;
	  trm_to_isar c (coqnorm s2) (Variables.make ());
	  Printf.fprintf c "\"\n";
	  ref_isabellehol1 c r1 ((coqnorm s1, h1) :: (coqnorm s2, h2) :: hyp) const sp'';

	  Printf.fprintf c "%snext\n" sp';
	  Printf.fprintf c "%sassume %s : \"" sp' h1;
	  trm_to_isar c (coqnorm t1) (Variables.make ());
	  Printf.fprintf c "\"\n";
	  Printf.fprintf c "%s and %s : \"" sp' h2;
	  trm_to_isar c (coqnorm t2) (Variables.make ());
	  Printf.fprintf c "\"\n";
	  ref_isabellehol1 c r2 ((coqnorm t1, h1) :: (coqnorm t2, h2) :: hyp) const sp'';
    Printf.fprintf c "%sqed\n" sp';
    Printf.fprintf c "%sthus ?thesis by blast\n" sp'
  in
	match r with
    | Conflict(s,ns) ->
	      (* Printf.fprintf c "%stab_conflict %s %s.\n" sp (lookup "0" (coqnorm s) hyp) (lookup "1" (coqnorm ns) hyp) *)
	      Printf.fprintf c "%sfrom %s %s show ?thesis by blast\n" sp (lookup "0" (coqnorm s) hyp) (lookup "1" (coqnorm ns) hyp)
    | Fal(_) ->
	      (* Printf.fprintf c "%stab_false %s.\n" sp (lookup "2" False hyp) *)
        Printf.fprintf c "%sfrom %s show False by blast\n" sp (lookup "2" False hyp);
    | NegRefl(s) ->
	      (* Printf.fprintf c "%stab_refl %s.\n" sp (lookup "3" (coqnorm s) hyp) *)
	      Printf.fprintf c "%sfrom %s have False by blast (*tab_refl*)\n" sp (lookup "3" (coqnorm s) hyp);
	      Printf.fprintf c "%sthus ?thesis by blast\n" sp
    | Implication(h,s,t,r1,r2) ->
	      let h1 = get_hyp_name() in
(*
	        Printf.fprintf c "%stab_imp %s %s.\n" sp (lookup "4" (coqnorm h) hyp) h1;
	        ref_isabellehol1 c r1 ((coqnorm s,h1)::hyp) const (sp^" ");
	        ref_isabellehol1 c r2 ((coqnorm t,h1)::hyp) const (sp^" ");
*)
	        Printf.fprintf c "%snote %s = %s[THEN TImp[THEN mp]](*tab_imp*)\n" sp h1 (lookup "4" (coqnorm h) hyp);
          tab_disj c hyp h1 s t r1 r2
    | Disjunction(h,s,t,r1,r2) ->
	      let h1 = get_hyp_name() in
          (*
	        Printf.fprintf c "%stab_or %s %s.\n" sp (lookup "5" (coqnorm h) hyp) h1;
	        ref_isabellehol1 c r1 ((coqnorm s,h1)::hyp) const (sp^" ");
	        ref_isabellehol1 c r2 ((coqnorm t,h1)::hyp) const (sp^" ");
          *)
	        Printf.fprintf c "%snote %s = %s(*tab_or*)\n" sp h1 (lookup "5" (coqnorm h) hyp);
          tab_disj c hyp h1 s t r1 r2
    | NegConjunction(h,s,t,r1,r2) ->
	      let h1 = get_hyp_name() in
	        (* Printf.fprintf c "%stab_nand %s %s.\n" sp (lookup "6" (coqnorm h) hyp) h1; *)
	        (* ref_isabellehol1 c r1 ((coqnorm s,h1)::hyp) const (sp^" "); *)
	        (* ref_isabellehol1 c r2 ((coqnorm t,h1)::hyp) const (sp^" "); *)
	        Printf.fprintf c "%snote %s = %s(*tab_nand*)\n" sp h1 (lookup "6" (coqnorm h) hyp);
          tab_disj c hyp h1 s t r1 r2
    | NegImplication(h,s,t,r1) ->
	      let h1 = get_hyp_name() in
	      let h2 = get_hyp_name() in
	        Printf.fprintf c "%snote %s = %s[THEN TNegImp1]\n" sp h1 (lookup "7" (coqnorm h) hyp);
	        Printf.fprintf c "%snote %s = %s[THEN TNegImp2]\n" sp h2 (lookup "7" (coqnorm h) hyp);
	        ref_isabellehol1 c r1 ((coqnorm s, h1) :: (coqnorm t, h2) :: hyp) const sp
    | Conjunction(h,s,t,r1) ->
	      let h1 = get_hyp_name() in
	      let h2 = get_hyp_name() in
	        Printf.fprintf c "%snote %s = %s[THEN TAnd1]\n" sp h1 (lookup "8" (coqnorm h) hyp);
	        Printf.fprintf c "%snote %s = %s[THEN TAnd2]\n" sp h2 (lookup "8" (coqnorm h) hyp);
	        ref_isabellehol1 c r1 ((coqnorm s, h1) :: (coqnorm t, h2) :: hyp) const sp
    | NegDisjunction(h,s,t,r1) ->
	      let h1 = get_hyp_name() in
	      let h2 = get_hyp_name() in
          (*
	        Printf.fprintf c "%stab_nor %s %s %s.\n" sp (lookup "9" (coqnorm h) hyp) h1 h2;
	        ref_isabellehol1 c r1 ((coqnorm s,h1)::(coqnorm t,h2)::hyp) const sp
          *)
	        Printf.fprintf c "%snote %s = TNor1[rule_format, OF %s]\n" sp h1 (lookup "9" (coqnorm h) hyp);
	        Printf.fprintf c "%snote %s = TNor2[rule_format, OF %s]\n" sp h2 (lookup "9" (coqnorm h) hyp);
	        ref_isabellehol1 c r1 ((coqnorm s, h1) :: (coqnorm t, h2) :: hyp) const sp
    | All(h,s,r1,a,m,n) ->
	      let const = add_fresh_const true c const n sp in
	      let h1 = get_hyp_name() in
(*
	        Printf.fprintf c "%stab_all %s (" sp (lookup "10" (coqnorm h) hyp);
	        (trm_to_coq c n (Variables.make ()) (-1) (-1));
	        Printf.fprintf c ") %s.\n" h1;
*)
(* note H17 = H16[THEN spec, of "eigen__0 (eigen__2 eigen__5 eigen__6)"] *)
	        Printf.fprintf c "%snote %s = %s[THEN spec, of \"" sp h1 (lookup "10" (coqnorm h) hyp);
	        trm_to_isar c n (Variables.make ());
	        Printf.fprintf c "\"]\n";
	        ref_isabellehol1 c r1 ((coqnorm s, h1) :: hyp) const sp
    | NegAll(h,s,r1,a,m,x) ->
	      let h1 = get_hyp_name() in
	      let x = Hashtbl.find coq_names x in
	        (* Printf.fprintf c "%stab_negall %s %s %s.\n" sp (lookup "11" (coqnorm h) hyp) x h1; *)
	        Printf.fprintf c "%sfrom %s obtain eigen%s where %s : \"" sp (lookup "11" (coqnorm h) hyp) x h1;
	        trm_to_isar c (coqnorm s) (Variables.make ());
	        (* Printf.fprintf c "\" by (erule TNegAll'[rule_format])\n"; *)
	        Printf.fprintf c "\" by blast\n";
	        ref_isabellehol1 c r1 ((coqnorm s, h1) :: hyp) ((x, a) :: const) sp
    | Exist(h,s,r1,a,m,x) ->
	      let h1 = get_hyp_name() in
	      let x = ( Hashtbl.find coq_names x ) in
	        (* Printf.fprintf c "%stab_ex %s %s %s.\n" sp (lookup "12" (coqnorm h) hyp) x h1; *)
	        (* ref_isabellehol1 c r1 ((coqnorm s,h1)::hyp) ((x,a)::const) sp *)

    (* from H4 obtain eigen__1 where H5 : "rel_d eigen__0 eigen__1" by (erule TEx)   *)

	        Printf.fprintf c "%sfrom %s obtain eigen%s where %s : \"" sp (lookup "12" (coqnorm h) hyp) x h1;
	        trm_to_isar c (coqnorm s) (Variables.make ());
	        Printf.fprintf c "\" by (erule TEx)\n";
	        ref_isabellehol1 c r1 ((coqnorm s, h1) :: hyp) ((x, a) :: const) sp
    | NegExist(h,s,r1,a,m,n) ->
	      let const = add_fresh_const true c const n sp in
	      let h1 = get_hyp_name() in
	        (* Printf.fprintf c "%stab_negex %s (" sp (lookup "13" (coqnorm h) hyp); *)
	        (* (trm_to_coq c n (Variables.make ()) (-1) (-1)); *)
	        (* Printf.fprintf c ") %s.\n" h1; *)

          (* tab_negex H0 (forall (X1:o), ~ X1) H1. *)
	        Printf.fprintf c "%snote %s = TNegEx[OF %s, where y = \"" sp h1 (lookup "13" (coqnorm h) hyp);
	        trm_to_isar c (coqnorm n) (Variables.make ());
	        Printf.fprintf c "\"]\n";
	        ref_isabellehol1 c r1 ((coqnorm s, h1) :: hyp) const sp
    | Mating(h1,h2, ss, rs) ->
        assert ( ((neg_p h1) || (neg_p h2)) && not ((neg_p h1) && (neg_p h2)));
	      let h3 = get_hyp_name() in
	        (* Printf.fprintf c "%stab_mat %s %s %s.\n" sp (lookup "14" (coqnorm h1) hyp) (lookup "15" (coqnorm h2) hyp) h3; *)
	        (* List.iter (fun (s,r) -> ref_isabellehol1 c r ((coqnorm s,h3)::hyp) const (sp^" ")) (List.combine ss rs) *)

          (*
            This rule seems to combine resolution with decomposition. It takes two facts "p s1 sn" and "~ q t1 tn"
            then we obtain a refutation by showing that "p = q" and "si = ti" for all i.
            Satallax's Coq reconstruction reduces this to decomposition (see the ltac definition for tab_mat) but
            we treat the whole mating here (mainly because we cannot rely on the compositionality of Satallax's approach
            in Coq for the time being).
          *)

        let (neg_hyp, pos_hyp) =
          if neg_p h1 then (h1, h2) else (h2, h1) in

    (*FIXME mostly duplicated from tab_dec*)
        let card = List.length ss in
        let proof_step_str =
          if card > 1 then
            "proof"
          else
            "proof -" in
        let fresh_fact_name = get_fresh_name () in
        let head = (*NOTE this was changed from tab_dec*)
          match neg_body neg_hyp(*this was h1 in tab_dec*) with
              Some h1' -> fst (bounded_head_spine card h1')
            | _ -> failwith "Could not determine head expression during Isar translation.2" in
        let indices = countup 0 card [] in
        let (custom_dec_prefix, custom_dec_suffix) =
          let (prefix, diseqs) =
            List.split (List.map (fun i ->
              ("s" ^ string_of_int i ^ " t" ^ string_of_int i,
               "(s" ^ string_of_int i ^ " ~= t" ^ string_of_int i ^ ")"))
              indices)
          in
            ("have " ^ fresh_fact_name ^ " : \"!! " ^ String.concat " " prefix ^ ". [|",
             "|] ==> " ^ String.concat " | " diseqs ^ "\" by blast") in
        (*FIXME this bit would be less of a mess if we use sprintf instead of printf*)
        let print_diseq () = (*NOTE this function was changed from that in the tab_dec handler*)
          let side v = " " ^ String.concat " " (List.map (fun i -> v ^ string_of_int i) indices)
          in
            trm_to_isar c head (Variables.make ());
	          Printf.fprintf c "%s" (side "s");
	          Printf.fprintf c "; ~ "; (*NOTE interesting that in Leo2 resolution covers the functionality of mating*)
            trm_to_isar c head (Variables.make ());
	          Printf.fprintf c "%s" (side "t");
        in
	        Printf.fprintf c "%s%s" sp custom_dec_prefix;
          print_diseq ();
	        Printf.fprintf c "%s\n" custom_dec_suffix;
	        Printf.fprintf c "%snote %s = %s[OF %s, OF %s]\n" sp h3 fresh_fact_name (lookup "14" (coqnorm pos_hyp) hyp) (lookup "15" (coqnorm neg_hyp) hyp); (*NOTE this line of the tab_dec handler was changed*)
	        Printf.fprintf c "%sfrom %s have False\n" sp h3;
          Printf.fprintf c "%s%s\n" sp' proof_step_str;

	        ignore(List.fold_right
            (fun (s, r) remaining ->
               Printf.fprintf c "%sassume %s : \"" sp'' h3;
	             trm_to_isar c (coqnorm s) (Variables.make ());
               Printf.fprintf c "\"\n";
               ref_isabellehol1 c r ((coqnorm s,h3)::hyp) const sp'';

               if remaining > 1 then Printf.fprintf c "%snext\n" sp';

               remaining - 1)
            (List.combine ss rs)
            card);

          Printf.fprintf c "%sqed\n" sp';
          Printf.fprintf c "%sthus ?thesis by blast\n" sp';
    | Decomposition(h1, ss, rs) ->
	      let h3 = get_hyp_name() in
	        (* Printf.fprintf c "%stab_dec %s %s.\n" sp (lookup "16" (coqnorm h1) hyp) h3; *)
	        (* List.iter (fun (s,r) -> ref_isabellehol1 c r ((coqnorm s,h3)::hyp) const (sp^" ")) (List.combine ss rs) *)

        let card = List.length ss in
        let proof_step_str =
          if card > 1 then
            "proof"
          else
            "proof -" in
        let fresh_fact_name = get_fresh_name () in
        let head =
          match neg_body h1 with
            Some h1' ->
              begin
                match eq_body h1' with
                    Some (_, m, _) -> fst (bounded_head_spine card m)
                  | _ -> failwith "Could not determine head expression during Isar translation."
              end
            | _ -> failwith "Could not determine head expression during Isar translation." in
        let indices = countup 0 card [] in
        let (custom_dec_prefix, custom_dec_suffix) =
          let (prefix, diseqs) =
            List.split (List.map (fun i ->
              ("s" ^ string_of_int i ^ " t" ^ string_of_int i,
               "(s" ^ string_of_int i ^ " ~= t" ^ string_of_int i ^ ")"))
              indices)
          in
            ("have " ^ fresh_fact_name ^ " : \"!! " ^ String.concat " " prefix ^ ". ",
             " ==> " ^ String.concat " | " diseqs ^ "\" by blast") in
        (*FIXME this bit would be less of a mess if we use sprintf instead of printf*)
        let print_diseq () =
          let side v = " " ^ String.concat " " (List.map (fun i -> v ^ string_of_int i) indices)
          in
            trm_to_isar c head (Variables.make ());
	          Printf.fprintf c "%s" (side "s");
	          Printf.fprintf c " ~= ";
            trm_to_isar c head (Variables.make ());
	          Printf.fprintf c "%s" (side "t");
        in

      (* have custom_tac : "\<And> s1 t1. eigen__1 s1 \<noteq> eigen__1 t1 ==> s1 \<noteq> t1" by blast *)
      (* note H22 = custom_tac[OF H20] *)
      (* from H22 have False *)

	        Printf.fprintf c "%s%s" sp custom_dec_prefix;
          print_diseq ();
	        Printf.fprintf c "%s\n" custom_dec_suffix;
	        Printf.fprintf c "%snote %s = %s[OF %s]\n" sp h3 fresh_fact_name (lookup "16" (coqnorm h1) hyp);
	        Printf.fprintf c "%sfrom %s have False\n" sp h3;
          Printf.fprintf c "%s%s\n" sp' proof_step_str;

	        (* List.iter *)
          (*   (fun (s, r) -> *)
          (*      ref_isabellehol1 c r ((coqnorm s,h3)::hyp) const (sp^" ")) *)
          (*   (List.combine ss rs) *)

	        ignore(List.fold_right
            (fun (s, r) remaining ->
               Printf.fprintf c "%sassume %s : \"" sp'' h3;
	             trm_to_isar c (coqnorm s) (Variables.make ());
               Printf.fprintf c "\"\n";
               ref_isabellehol1 c r ((coqnorm s,h3)::hyp) const sp'';

               if remaining > 1 then Printf.fprintf c "%snext\n" sp';

               remaining - 1)
            (List.combine ss rs)
            card);

          Printf.fprintf c "%sqed\n" sp';
          Printf.fprintf c "%sthus ?thesis by blast\n" sp';
    | Confront(h1,h2,su,tu,sv,tv,r1,r2) ->
	      let h3 = get_hyp_name() in
	      let h4 = get_hyp_name() in
	        (* Printf.fprintf c "%stab_con %s %s %s %s.\n" sp (lookup "17" (coqnorm h1) hyp) (lookup "18" (coqnorm h2) hyp) h3 h4; *)
	        (* ref_isabellehol1 c r1 ((coqnorm su,h3)::(coqnorm tu,h4)::hyp) const (sp^" "); *)
	        (* ref_isabellehol1 c r2 ((coqnorm sv,h3)::(coqnorm tv,h4)::hyp) const (sp^" "); *)

        let fresh_fact_name = get_fresh_name () in
          (*FIXME should also try symmetric equation*)
	        Printf.fprintf c "%snote %s = TCON[OF %s, OF %s](*tab_con*)\n" sp fresh_fact_name (lookup "17" (coqnorm h1) hyp) (lookup "18" (coqnorm h2) hyp);

          (*FIXME this next bit is dirty -- might be better to adapt tab_disj2*)
          Printf.fprintf c "%sfrom %s have False\n" sp fresh_fact_name;
          Printf.fprintf c "%sproof\n" sp;
          Printf.fprintf c "%sassume %s : \"" sp' fresh_fact_name;
          Printf.fprintf c "(";
          trm_to_isar c (coqnorm su) (Variables.make ());
          Printf.fprintf c ") & (";
          trm_to_isar c (coqnorm tu) (Variables.make ());
          Printf.fprintf c ")";
          Printf.fprintf c "\"\n";
          Printf.fprintf c "%sfrom %s have %s : \"" sp' fresh_fact_name h3;
          trm_to_isar c (coqnorm su) (Variables.make ());
          Printf.fprintf c "\" by blast\n";
          Printf.fprintf c "%sfrom %s have %s : \"" sp' fresh_fact_name h4;
          trm_to_isar c (coqnorm tu) (Variables.make ());
          Printf.fprintf c "\" by blast\n";
          ref_isabellehol1 c r1 ((coqnorm su, h3) :: (coqnorm tu, h4) :: hyp) const sp'';

          Printf.fprintf c "%snext\n" sp';
          Printf.fprintf c "%sassume %s : \"" sp' fresh_fact_name;
          Printf.fprintf c "(";
          trm_to_isar c (coqnorm sv) (Variables.make ());
          Printf.fprintf c ") & (";
          trm_to_isar c (coqnorm tv) (Variables.make ());
          Printf.fprintf c ")";
          Printf.fprintf c "\"\n";
          Printf.fprintf c "%sfrom %s have %s : \"" sp' fresh_fact_name h3;
          trm_to_isar c (coqnorm sv) (Variables.make ());
          Printf.fprintf c "\" by blast\n";
          Printf.fprintf c "%sfrom %s have %s : \"" sp' fresh_fact_name h4;
          trm_to_isar c (coqnorm tv) (Variables.make ());
          Printf.fprintf c "\" by blast\n";
          ref_isabellehol1 c r2 ((coqnorm sv, h3) :: (coqnorm tv, h4) :: hyp) const sp'';
          Printf.fprintf c "%sqed\n" sp';
          Printf.fprintf c "%sthus ?thesis by blast\n" sp'
    | Trans(h1,h2,su,r1) -> (*TODO*) 
	      let h3 = get_hyp_name() in
	        Printf.fprintf c "%stab_trans %s %s %s.\n" sp (lookup "19" (coqnorm h1) hyp) (lookup "20" (coqnorm h2) hyp) h3;
	        ref_isabellehol1 c r1 ((coqnorm su,h3)::hyp) const (sp^" ");
    | NegEqualProp(h,s,t,r1,r2) ->
	      let h1 = get_hyp_name() in
	      let h2 = get_hyp_name() in
          (*
	        Printf.fprintf c "%stab_be %s %s %s.\n" sp (lookup "21" (coqnorm h) hyp) h1 h2;
	        ref_isabellehol1 c r1 ((coqnorm s,h1)::(coqnorm (neg t),h2)::hyp) const (sp^" ");
	        ref_isabellehol1 c r2 ((coqnorm (neg s),h1)::(coqnorm t,h2)::hyp) const (sp^" ");
          *)
	        Printf.fprintf c "%snote %s = TBE[rule_format, OF %s](*tab_be*)\n" sp h1 (lookup "21" (coqnorm h) hyp);
          tab_disj2 c hyp h1 h2 (s, neg t) (neg s, t) r1 r2
    | EqualProp(h,s,t,r1,r2) ->
	      let h1 = get_hyp_name() in
	      let h2 = get_hyp_name() in
	        (* Printf.fprintf c "%stab_bq %s %s %s.\n" sp (lookup "22" (coqnorm h) hyp) h1 h2; *)
	        (* ref_isabellehol1 c r1 ((coqnorm s,h1)::(coqnorm t,h2)::hyp) const (sp^" "); *)
	        (* ref_isabellehol1 c r2 ((coqnorm (neg s),h1)::(coqnorm (neg t),h2)::hyp) const (sp^" "); *)
	        Printf.fprintf c "%snote %s = TBQ[rule_format, OF %s](*tab_bq*)\n" sp h1 (lookup "22" (coqnorm h) hyp);
          tab_disj2 c hyp h1 h2 (s, t) (neg s, neg t) r1 r2
    | NegAequivalenz(h,s,t,r1,r2) ->
        (*
	      let h1 = get_hyp_name() in
	      let h2 = get_hyp_name() in
	        Printf.fprintf c "%stab_negiff %s %s %s.\n" sp (lookup "23" (coqnorm h) hyp) h1 h2;
	        ref_isabellehol1 c r1 ((coqnorm s,h1)::(coqnorm (neg t),h2)::hyp) const (sp^" ");
	        ref_isabellehol1 c r2 ((coqnorm (neg s),h1)::(coqnorm t,h2)::hyp) const (sp^" ");
          *)
	      let h1 = get_hyp_name() in
	      let h2 = get_hyp_name() in
	        Printf.fprintf c "%snote %s = TNIff[rule_format, OF %s](*tab_negiff*)\n" sp h1 (lookup "23" (coqnorm h) hyp);
          tab_disj2 c hyp h1 h2 (s, neg t) (neg s, t) r1 r2
    | Aequivalenz(h,s,t,r1,r2) ->
	      let h1 = get_hyp_name() in
	      let h2 = get_hyp_name() in
	        (* Printf.fprintf c "%stab_iff %s %s %s.\n" sp (lookup "24" (coqnorm h) hyp) h1 h2; *)
	        (* ref_isabellehol1 c r1 ((coqnorm s,h1)::(coqnorm t,h2)::hyp) const (sp^" "); *)
	        (* ref_isabellehol1 c r2 ((coqnorm (neg s),h1)::(coqnorm (neg t),h2)::hyp) const (sp^" "); *)
	        Printf.fprintf c "%snote %s = TIff[rule_format, OF %s](*tab_iff*)\n" sp h1 (lookup "24" (coqnorm h) hyp);
          tab_disj2 c hyp h1 h2 (s, t) (neg s, neg t) r1 r2
    | NegEqualFunc(h,s,r1) ->
	      let h1 = get_hyp_name() in
	        (* Printf.fprintf c "%stab_fe %s %s.\n" sp (lookup "25" (coqnorm h) hyp) h1; *)
	        Printf.fprintf c "%snote %s = TFE[THEN mp, OF %s]\n" sp h1 (lookup "25" (coqnorm h) hyp);
	        ref_isabellehol1 c r1 ((coqnorm s, h1) :: hyp) const sp
    | EqualFunc(h,s,r1) ->
	      let h1 = get_hyp_name() in
	        (* Printf.fprintf c "%stab_fq %s %s.\n" sp (lookup "26" (coqnorm h) hyp) h1; *)
	        Printf.fprintf c "%snote %s = TFQ[THEN mp, OF %s]\n" sp h1 (lookup "26" (coqnorm h) hyp);
	        ref_isabellehol1 c r1 ((coqnorm s, h1) :: hyp) const  sp
    | ChoiceR(eps,pred,s,t,r1,r2) ->
        let const = add_fresh_const true c const pred sp in
        let h1 = get_hyp_name() in
          begin
            match eps with
              | Choice(a) ->
(*
	                Printf.fprintf c "%stab_choice " sp;
	                print_stp_coq c a coq_names true;
	                Printf.fprintf c " (";
	                (trm_to_coq c pred (Variables.make ()) (-1) (-1));
	                Printf.fprintf c ") %s.\n" h1;
	                ref_isabellehol1 c r1 ((coqnorm s,h1)::hyp) const (sp^" ");
	                ref_isabellehol1 c r2 ((coqnorm t,h1)::hyp) const (sp^" ");
*)

(*
    let ?p = "% (X1 :: i). f X1 = eigen__11"
    have H4 : "(! x. ~ ?p x)" by (rule TSeps[where 'A = "i" and p = ?p, THEN mp], rule impI, insert H2, blast)
*)
                  let termname = "?" ^ get_fresh_name ()
                  in
	                  Printf.fprintf c "%slet %s = \"" sp termname;
	                  trm_to_isar c pred (Variables.make ());
	                  Printf.fprintf c "\"\n";
	                  Printf.fprintf c "%shave %s : \"! x. ~ %s x\" " sp h1 termname;
	                  Printf.fprintf c "by (rule TSeps[where 'A = \"";
	                  print_stp_isar c a true;
                    Printf.fprintf c "\" and p = %s, THEN mp], rule impI, insert %s, blast)\n" termname (String.concat " " (List.map snd hyp));
	                  ref_isabellehol1 c r1 ((coqnorm s,h1)::hyp) const (sp ^ " ");
              | Name(x,Ar(Ar(a,Prop),_)) -> (*TODO*) 
	                Printf.fprintf c "%stab_choice' " sp;
	                print_stp_coq c a coq_names true;
	                Printf.fprintf c " (";
	                (trm_to_coq c eps (Variables.make ()) (-1) (-1));
	                Printf.fprintf c ") (";
	                (trm_to_coq c pred (Variables.make ()) (-1) (-1));
	                Printf.fprintf c ") %s %s.\n" (get_Choicop_axiom x a hyp) h1;
	                ref_isabellehol1 c r1 ((coqnorm s,h1)::hyp) const (sp^" ");
	                ref_isabellehol1 c r2 ((coqnorm t,h1)::hyp) const (sp^" ");
              | _ -> failwith "eps is not a valid epsilon"
          end
    | Cut(s,r1,r2) ->
	      let const = add_fresh_const true c const s sp in
	      let h1 = get_hyp_name() in
	        (* Printf.fprintf c "%stab_cut (" sp; *)
	        (* (trm_to_coq c s (Variables.make ()) (-1) (-1)); *)
	        (* Printf.fprintf c ") %s.\n" h1; *)
	        (* ref_isabellehol1 c r2 ((coqnorm (neg s),h1)::hyp) const (sp^" "); *)
	        (* ref_isabellehol1 c r1 ((coqnorm s,h1)::hyp) const (sp^" "); *)
        let termname = "?" ^ get_fresh_name ()
        in
	        Printf.fprintf c "%slet %s = \"" sp termname;
	        trm_to_isar c s (Variables.make ());
	        Printf.fprintf c "\"\n";
	        Printf.fprintf c "%shave %s : \"~ %s | %s\" by blast (*tab_cut*)\n" sp h1 termname termname;
          tab_disj c (((coqnorm (disj (neg s) s)), h1) :: hyp) h1 (neg s) s r2 r1
    | DoubleNegation(h,s,r1) ->
	      let h1 = get_hyp_name() in
	        (* Printf.fprintf c "%stab_dn %s %s.\n" sp (lookup "27" (coqnorm h) hyp) h1; *)
	        (* ref_isabellehol1 c r1 ((coqnorm s,h1)::hyp) const sp; *)
	        Printf.fprintf c "%snote %s = notnotD[OF %s]\n" sp h1 (lookup "27" (coqnorm h) hyp);
	        ref_isabellehol1 c r1 ((coqnorm s,h1)::hyp) const sp;
    | Rewrite(prefix,pt,pt',r1) ->
	      let h =  coqnorm (Ap(prefix,pt)) in
	      let h1 = lookup "28" h hyp in
	      let s =  coqnorm (Ap(prefix,pt')) in
	      let h2 = get_hyp_name() in
	        begin
	          match pt with
		          | True ->
                  (* Printf.fprintf c "%stab_rew_true %s %s (" sp h1 h2; *)
				          (* (trm_to_coq c prefix (Variables.make ()) (-1) (-1));  Printf.fprintf c ") .\n"; *)
                  Printf.fprintf c "%snote %s = eq_ind[THEN spec, of \"True\", THEN spec, of \"" sp h2;
				          trm_to_isar c prefix (Variables.make ());
                  Printf.fprintf c "\", THEN mp, OF %s, THEN spec, of \"~ False\", THEN mp, OF eq_true]\n" h1;
		          | And ->
                  (*
                  Printf.fprintf c "%stab_rew_and %s %s (" sp h1 h2;
				          (trm_to_coq c prefix (Variables.make ()) (-1) (-1));  Printf.fprintf c ") .\n";
                  *)
                  Printf.fprintf c "%snote %s = eq_ind[THEN spec, of \"(op &)\", THEN spec, of \"" sp h2;
				          trm_to_isar c prefix (Variables.make ());
                  Printf.fprintf c "\", THEN mp, OF %s, THEN spec, of \"%% x y. ~ (x --> ~ y)\", THEN mp, OF eq_and_imp]\n" h1;
		          | Or ->
                  (*
 	                  Printf.fprintf c "%stab_rew_or %s %s (" sp h1 h2;
				            (trm_to_coq c prefix (Variables.make ()) (-1) (-1));  Printf.fprintf c ") .\n";
                  *)
                  Printf.fprintf c "%snote %s = eq_ind[THEN spec, of \"(op |)\", THEN spec, of \"" sp h2;
				          trm_to_isar c prefix (Variables.make ());
                  Printf.fprintf c "\", THEN mp, OF %s, THEN spec, of \"%% x y. ((~ x) --> y)\", THEN mp, OF eq_or_imp]\n" h1;

		          | Iff -> (*TODO*) 
                  Printf.fprintf c "%stab_rew_iff %s %s (" sp h1 h2;
				          (trm_to_coq c prefix (Variables.make ()) (-1) (-1));  Printf.fprintf c ") .\n";
		          | Exists(_) ->
                  (* Printf.fprintf c "%stab_rew_ex %s %s (" sp h1 h2; *)
				          (* (trm_to_coq c prefix (Variables.make ()) (-1) (-1));  Printf.fprintf c ") .\n"; *)

(* note H2 = eq_ind[THEN spec, of "% p. ? x. p x", THEN spec, of "% (X1::(bool=>bool)=>bool). ~ X1 (% X2::bool. X2)", THEN mp, OF H0, THEN spec, of "% p. ~ (! x. ~ p x)", THEN mp, OF eq_exists_nforall] *)

                  (*FIXME horrible hardcoding*)
                    Printf.fprintf c "%snote %s = eq_ind[THEN spec, of \"%% p. ? x. p x\", THEN spec, of \"" sp h2;
				            trm_to_isar c prefix (Variables.make ());
                    Printf.fprintf c "\", THEN mp, OF %s, THEN spec, of \"%% p. ~ (! x. ~ p x)\", THEN mp, OF eq_exists_nforall]\n" h1;
		          | Eq(_) -> (*TODO*) 
                  Printf.fprintf c "%stab_rew_sym %s %s (" sp h1 h2;
				          (trm_to_coq c prefix (Variables.make ()) (-1) (-1));  Printf.fprintf c ") .\n";
		          | Lam(_,Lam(_,Ap(DB(1,_),DB(0,_)))) -> (*TODO*) 
				          Printf.fprintf c "%stab_rew_eta %s %s (" sp h1 h2;
				          (trm_to_coq c prefix (Variables.make ()) (-1) (-1));  Printf.fprintf c ") .\n";
		          | Lam(Ar(Prop,Prop),Ap(Ap(Imp,Ap(Ap(Imp,DB(0,Prop)),False)),False)) ->
                  (*
				          Printf.fprintf c "%stab_rew_dn %s %s (" sp h1 h2;
				          (trm_to_coq c prefix (Variables.make ()) (-1) (-1));  Printf.fprintf c ") .\n";
                  *)
                  Printf.fprintf c "%snote %s = eq_ind[THEN spec, of \"%% x. ~ ~ x\", THEN spec, of \"" sp h2;
				          trm_to_isar c prefix (Variables.make ());
                  Printf.fprintf c "\", THEN mp, OF %s, THEN spec, of \"%% x . x\", THEN mp, OF eq_neg_neg_id]\n" h1;
		          | Lam(_,Lam(_,Ap(Forall(_),Lam(_,(Ap(Ap(Imp,(Ap(DB(0,_),DB(2,_)))),(Ap(DB(0,_),DB(1,_)))) ))) )) -> (*TODO*) 
				          Printf.fprintf c "%stab_rew_leib1 %s %s (" sp h1 h2;
				          (trm_to_coq c prefix (Variables.make ()) (-1) (-1));  Printf.fprintf c ") .\n";
		          | Lam(_,Lam(_,Ap(Forall(_),Lam(_,(Ap(Ap(Imp,Ap(Ap(Imp,(Ap(DB(0,_),DB(2,_)))),False)),Ap(Ap(Imp,(Ap(DB(0,_),DB(1,_)))),False)) ))) )) -> (*TODO*) 
				          Printf.fprintf c "%stab_rew_leib2 %s %s (" sp h1 h2;
				          (trm_to_coq c prefix (Variables.make ()) (-1) (-1));  Printf.fprintf c ") .\n";
		          | Lam(_,Lam(_,Ap(Forall(_),Lam(_,(Ap(Ap(Imp,(Ap(Forall(_),Lam(_,(Ap(Ap(DB(1,_),DB(0,_)),DB(0,_)))))) ),(Ap(Ap(DB(0,_),DB(2,_)),DB(1,_)))) ) )) )) -> (*TODO*) 
				          Printf.fprintf c "%stab_rew_leib3 %s %s (" sp h1 h2;
				          (trm_to_coq c prefix (Variables.make ()) (-1) (-1));  Printf.fprintf c ") .\n";
		          | Lam(_,Lam(_, Ap(Forall(_),Lam(_,(Ap(Ap(Imp,(Ap(Ap(Imp,(Ap(Ap(DB(0,_),DB(2,_)),DB(1,_)))),False) )),(Ap(Ap(Imp,(Ap(Forall(_),Lam(_,(Ap(Ap(DB(1,_),DB(0,_)),DB(0,_))))) )),False) )) ) )) )) -> (*TODO*) 
				          Printf.fprintf c "%stab_rew_leib4 %s %s (" sp h1 h2;
				          (trm_to_coq c prefix (Variables.make ()) (-1) (-1));  Printf.fprintf c ") .\n";
		          | _ -> failwith("unknown rewrite step found in ref_coq" ^ (trm_str pt))
	        end;
	        ref_isabellehol1 c r1 ((s,h2)::hyp) const sp
    | Delta(h,s,x,r1) ->
	      let h1 = (lookup "29" (coqnorm h) hyp) in
	        (* Printf.fprintf c "%sunfold %s in %s.\n" sp ( Hashtbl.find coq_names x ) h1; *)
	        Printf.fprintf c "%snote %s = %s[unfolded %s_def]\n" sp h1 h1 (Hashtbl.find coq_names x);
	        ref_isabellehol1 c r1 ((coqnorm s,h1)::hyp) const sp;
    | KnownResult(s,name,al,r1) ->
        begin
          match al with
            | (_::_) ->
	              let h1 = get_hyp_name() in
(*
	                Printf.fprintf c "%sset (%s := (%s" sp h1 name;
	                List.iter
	                  (fun a ->
	                     Printf.fprintf c " ";
	                     print_stp_coq c a coq_names true)
	                  al;
	                Printf.fprintf c ")).\n";
*)
                let name = (*remove "@" prefix. note sure why Satallax puts it there.*)
                  if String.sub name 0 1 = "@" then String.sub name 1 (String.length name - 1)
                  else name
                in
	                Printf.fprintf c "%snote %s = %s" sp h1 name;
                  let length_al = List.length al
                  in
                    if length_al > 0 then
                      begin
	                      Printf.fprintf c "[where ";
                        let ty_names =
                          List.combine (countup 1 length_al []) al
                        in
	                        ignore(List.fold_right
                            (*"ty" is the name of the schematic type variable;
                              "a" is the object-level type it's being instantiate to*)
	                          (fun (ty, a) remaining -> (
	                             Printf.fprintf c "'ty%s_ = " (string_of_int ty); (*FIXME const*) (*the typename is suffixed with "_" otherwise isabelle will have trouble matching the intended schematic variable.. this is hackish*)
	                             print_stp_coq c a coq_names true;
                               if remaining > 1 then Printf.fprintf c " and "; (*FIXME const*)
                               remaining - 1))
	                          ty_names length_al);
	                        Printf.fprintf c "]"
                      end;
	                  Printf.fprintf c "\n";
	                  ref_isabellehol1 c r1 ((coqnorm s,h1)::hyp) const sp
            | [] ->
	              ref_isabellehol1 c r1 ((coqnorm s,name)::hyp) const sp
        end;
    | NYI(h,s,r1) -> failwith("NYI step found in ref_coq" )
    | Timeout -> failwith("Timeout step found in ref_coq" )
    | _ -> failwith("unknown refutation case in ref_coq" )

let ref_isabellehol c r =
(*FIXME where is the header + signature + lemma definition printed?*)  
	(* get conjecture *)
	let con =
    match !conjecture with
        Some(_, con, _) -> (* coqnorm *) con (*FIXME rename coqnorm?*)  
      | None -> False in
	(* initialise hypotheses *)
	let hyp =
    List.fold_left
      (fun l (s, pt) ->
         (coqnorm pt, s) :: l ) [] !coqsig_hyp_trm in (*FIXME coqnorm?, coqsig_hyp_trm?*)  
	let h1 = get_hyp_name() in
  Printf.fprintf c "\nproof (rule ccontr)\n";
  Printf.fprintf c "  assume %s : \"" h1;
(* (List.assoc h1 !coqsig_hyp) *)
(*to_trm name_trm [] (neg con) None*)
  (* print_pretrm_isar c precon coq_names coq_used_names (-1) (-1); *)

  trm_to_isar c (coqnorm (neg con)) (Variables.make ());

  Printf.fprintf c "\"\n";
  Printf.fprintf c "  show False\n";
  Printf.fprintf c "    proof (rule ccontr)\n";

  ref_isabellehol1 c r ((neg (coqnorm con), h1) :: hyp) (!coqsig_const) "    ";  (*FIXME what are the parameters?*)
  (* Printf.fprintf c "  thus False .\n"; *)
  Printf.fprintf c "    qed\n";
  Printf.fprintf c "  qed\n";
  Printf.fprintf c "end\n"

(*** July 2012 (Chad) : TSTP ***)
(** Prints type m as a Tstp-formatted string on the out_channel c  **)
let rec print_stp_tstp c m p =
  match m with
  | Base x ->
      Printf.fprintf c "%s" x
  | Prop ->
      Printf.fprintf c "$o"
  | Ar(a,b) ->
      begin
	if p then Printf.fprintf c "(";
	print_stp_tstp c a true;
	Printf.fprintf c ">";
	print_stp_tstp c b false;
	if p then Printf.fprintf c ")";
	flush c
      end

(*
(*FIXME duplicated from TSTP function*) (*FIXME there's another function, with a slightly different signature, in Syntax*)
let rec print_stp_isar c m p =
  match m with
    | Base x ->
        Printf.fprintf c "%s" x
    | Prop ->
        Printf.fprintf c "o"
    | Ar(a,b) ->
        begin
	        if p then Printf.fprintf c "(";
	        print_stp_tstp c a true;
	        Printf.fprintf c "=>";
	        print_stp_tstp c b false;
	        if p then Printf.fprintf c ")";
	        flush c
        end
*)

(** Input: out_channel c, term m, list of bound variables 
	Invariant: m is closed, if  it is enclosed in quantifiers for the bound variables 
	Prints the term m on the channel c**)
let rec trm_to_tstp c m bound =
  match m with
    Name(x,_) -> (* Definitions *)
      Printf.fprintf c "%s" (tstpizename x)
  | False -> (* Bottom *)
	Printf.fprintf c "$false"
  | Ap(Ap(Imp,m1),False) ->  (* Negation *)
	begin
	  Printf.fprintf c "(~(";
	  trm_to_tstp c m1 bound;
	  Printf.fprintf c "))";
	end
   | Ap(Ap(Imp,m1),m2) -> (* Implication *)
	begin
	  Printf.fprintf c "(";
	  trm_to_tstp c m1 bound;
	  Printf.fprintf c " => ";
	  trm_to_tstp c m2 bound;
	  Printf.fprintf c ")";
	end
  | Ap(Imp,m1) -> trm_to_tstp c (Lam(Prop,Ap(Ap(Imp,shift m1 0 1),DB(0,Prop)))) bound
  | Imp -> trm_to_tstp c (Lam(Prop,Lam(Prop,Ap(Ap(Imp,DB(1,Prop)),DB(0,Prop))))) bound
  | Ap(Forall(a),Lam(_,m1)) -> (* forall with Lam *)
      begin
	print_all_tstp c a m1 bound
      end
  | Forall(a) ->
      begin
	Printf.fprintf c "(!!)";
      end
  | Ap(Ap(Eq(a),m1),m2) -> (* Equality *)
	begin
	  Printf.fprintf c "(";
	  trm_to_tstp c m1 bound;
	  Printf.fprintf c " = ";
	  trm_to_tstp c m2 bound;
	  Printf.fprintf c ")"
	end
  | Eq(a) ->     
      Printf.fprintf c "(=)"
  | Ap(Choice(a),Lam(_,m1)) ->
      let bound = Variables.push bound in
      Printf.fprintf c "(@+["; Printf.fprintf c "%s" (Variables.top bound); 
      Printf.fprintf c ":"; print_stp_tstp c a false; 
      Printf.fprintf c "]:";
      trm_to_tstp c m1 bound; Printf.fprintf c ")"
  | Choice(a) ->
      Printf.fprintf c "(@+)";
  | True -> (* Top *)
	Printf.fprintf c "$true"
  | Ap(Ap(And,m1),m2) -> (* conjunction *)
	begin
	  Printf.fprintf c "(";
	  trm_to_tstp c m1 bound;
	  Printf.fprintf c " & ";
	  trm_to_tstp c m2 bound;
	  Printf.fprintf c ")";
	end
  | And ->Printf.fprintf c "(&)"
  | Ap(Ap(Or,m1),m2) -> (* disjunction *)
	begin
	  Printf.fprintf c "(";
	  trm_to_tstp c m1 bound;
	  Printf.fprintf c " | ";
	  trm_to_tstp c m2 bound;
	  Printf.fprintf c ")";
	end
  | Or -> Printf.fprintf c "(|)"
  | Ap(Ap(Iff,m1),m2) -> (* equivalenz *)
	begin
	  Printf.fprintf c "(";
	  trm_to_tstp c m1 bound;
	  Printf.fprintf c " <=> ";
	  trm_to_tstp c m2 bound;
	  Printf.fprintf c ")";
	end
  | Iff -> Printf.fprintf c "(<=>)"
  | Neg -> Printf.fprintf c "(~)"
  | Ap(Exists(a),Lam(_,m1)) -> (* exist *)
      begin
	print_ex_tstp c a m1 bound
      end
  | Exists(a) ->
      begin
	Printf.fprintf c "(??)";
      end
  | DB(i,a) -> (* Bound variable *)
	Printf.fprintf c "%s" (Variables.get i bound)
  | Lam(a,m) ->
      begin
	print_lam_tstp c a m bound
      end
  | Ap(m1,m2) ->     
	begin
	  Printf.fprintf c "(";
	  trm_to_tstp c m1 bound;
	  Printf.fprintf c " @ ";
	  trm_to_tstp c m2 bound;
	  Printf.fprintf c ")";
	end      
  | _ -> raise (GenericSyntaxError ("Unknown case in trm_to_tstp version : " ^ (trm_str m)))

 (* Prints consecutive lambda-terms as a single fun in Tstp. *) 
and print_lam_tstp c a m bound =
	let bound = Variables.push bound in
	Printf.fprintf c "(^["; Printf.fprintf c "%s" (Variables.top bound); Printf.fprintf c ":"; print_stp_tstp c a false; Printf.fprintf c "]:";
	match m with
		| Lam(b,m') -> print_lam_tstp c b m' bound; Printf.fprintf c ")"
		| _ -> trm_to_tstp c m bound; Printf.fprintf c ")"

(* Prints consecutive forall-terms together with the corresponding lambda-terms as a single forall in Tstp. *) 		
and print_all_tstp c a m bound =
  let bound = Variables.push bound in
  Printf.fprintf c "(!["; Printf.fprintf c "%s" (Variables.top bound); Printf.fprintf c ":"; print_stp_tstp c a false; Printf.fprintf c "]:";
  match m with
  | Ap(Forall(a'),Lam(_,m')) -> print_all_tstp c a' m' bound; Printf.fprintf c ")"
  | _ -> trm_to_tstp c m bound; Printf.fprintf c ")"

(* Prints an exist-term together with the corresponding lambda-term as an exists in Tstp. *) 		
and print_ex_tstp c a m bound =
 	let bound = Variables.push bound in
	Printf.fprintf c "(?["; Printf.fprintf c "%s" (Variables.top bound); 
	Printf.fprintf c ":"; print_stp_tstp c a false; 
        Printf.fprintf c "]:";
	trm_to_tstp c m bound; Printf.fprintf c ")"

let tstp_axioms : (trm,string * trm * out_channel * (bool ref)) Hashtbl.t = Hashtbl.create 100;;

let trm_to_tstp_rembvar x c m bound =
  match m with
  | Ap(Forall(a),Lam(_,m1)) ->
      let bound = Variables.push bound in
      let y = Variables.top bound in
      Hashtbl.add forallbvarnames x y;
      Printf.fprintf c "(!["; Printf.fprintf c "%s" y; Printf.fprintf c ":"; print_stp_tstp c a false; Printf.fprintf c "]:";
      trm_to_tstp c m1 bound; Printf.fprintf c ")"
  | Ap(Neg,Ap(Exists(a),Lam(_,m1))) ->
      let bound = Variables.push bound in
      let y = Variables.top bound in
      Hashtbl.add nexistsbvarnames x y;
      Printf.fprintf c "(~(?["; Printf.fprintf c "%s" y; Printf.fprintf c ":"; print_stp_tstp c a false; Printf.fprintf c "]:";
      trm_to_tstp c m1 bound; Printf.fprintf c "))"
  | Ap(Ap(Imp,Ap(Exists(a),Lam(_,m1))),False) ->
      let bound = Variables.push bound in
      let y = Variables.top bound in
      Hashtbl.add nexistsbvarnames x y;
      Printf.fprintf c "(~(?["; Printf.fprintf c "%s" y; Printf.fprintf c ":"; print_stp_tstp c a false; Printf.fprintf c "]:";
      trm_to_tstp c m1 bound; Printf.fprintf c "))"
  | _ ->
      trm_to_tstp c m bound

let rec lookup_tstp w s hyp =
  try
    List.assoc s hyp
  with
  | Not_found ->
      begin
	try
	  let (x,m,c,f) = Hashtbl.find tstp_axioms s in
	  if (!f) then
	    begin
	      f := false;
	      Printf.fprintf c "thf(%s,axiom," x;
	      trm_to_tstp_rembvar x c m (Variables.make ());
	      Printf.fprintf c ").\n";
	      flush c
	    end;
	  x
	with
	| Not_found ->
	  Printf.printf "%s: Could not find hyp name\ns = %s\nhyp:\n" w (trm_str s);
	  List.iter (fun (m,h) -> Printf.printf "%s: %s\n" h (trm_str m)) hyp;
	  failwith ("Could not find hyp name")
      end

let tstpline : int ref = ref 1;;

let tstphyp : (trm,string) Hashtbl.t = Hashtbl.create 100

(**
 Input: unit
	Output: returns next fresh hypothesis name **)
let rec get_thyp_name () =
  let x = "h" ^ (string_of_int (!next_fresh_hyp)) in
  incr next_fresh_hyp;
  if (Hashtbl.mem coq_used_names x) 
  then get_thyp_name ()
  else
    x

let rec get_tstp_hyp_name c s =
  try
    Hashtbl.find tstphyp s
  with Not_found ->
    let x = "h" ^ (string_of_int (!next_fresh_hyp)) in
    Hashtbl.add tstphyp s x;
    incr next_fresh_hyp;
    if (Hashtbl.mem coq_used_names x) 
    then get_tstp_hyp_name c s
    else
      begin
	Printf.fprintf c "thf(%s,assumption," x;
	trm_to_tstp_rembvar x c s (Variables.make ());
	Printf.fprintf c ",introduced(assumption,[])).\n";
	flush c;
	x
      end

let rec as_str2 al =
  match al with
  | (a::ar) -> "," ^ a ^ (as_str2 ar)
  | [] -> ""

let as_str al =
  match al with
  | (a::ar) -> "[" ^ a ^ (as_str2 ar) ^ "]"
  | [] -> "[]"

let rec disch_str2 d =
  match d with
  | (x::r) -> "," ^ x ^ (disch_str2 r)
  | [] -> ""

let disch_str d =
  match d with
  | (x::r) -> x ^ (disch_str2 r)
  | [] -> ""

let rec info_str2 r dl =
  match dl with
  | (d::dr) -> "," ^ r ^ "(discharge,[" ^ (disch_str d) ^ "])" ^ (info_str2 r dr)
  | [] -> ""

let info_str r hyp dl =
  match hyp with
  | [] -> info_str2 r dl
  | _ -> ",assumptions(" ^ (as_str (List.map (fun (_,h) -> h) hyp)) ^ ")" ^ (info_str2 r dl)

(** Input: out_channel c, refutation r, association list (term -> hypothesis name) hyp, association list (constant name -> type) const, Space string sp 
	Output: unit, prints refutation r to c **)
let rec ref_tstp1 c r hyp const =
  let l = !tstpline in
  incr tstpline;
  begin
    match r with
    | Conflict(s,ns) ->
	let p1 = (lookup_tstp "0" (coqnorm s) hyp) in
	let p2 = (lookup_tstp "1" (coqnorm ns) hyp) in
	Printf.fprintf c "thf(%d,plain,$false,inference(tab_conflict,[status(thm)%s],[%s,%s])).\n" l (info_str "tab_conflict" hyp []) p1 p2
    | Fal(_) -> 				
	let p1 = (lookup_tstp "2" False hyp) in
	Printf.fprintf c "thf(%d,plain,$false,inference(tab_false,[status(thm)%s],[%s])).\n" l (info_str "tab_false" hyp []) p1
    | NegRefl(s) -> 			
	let p1 = (lookup_tstp "3" (coqnorm s) hyp) in
	Printf.fprintf c "thf(%d,plain,$false,inference(tab_refl,[status(thm)%s],[%s])).\n" l (info_str "tab_refl" hyp []) p1;
    | Implication(h,s,t,r1,r2) -> 	
	let h1 = get_tstp_hyp_name c (coqnorm s) in	
	let h2 = get_tstp_hyp_name c (coqnorm t) in	
	let l1 = ref_tstp1 c r1 ((coqnorm s,h1)::hyp) const in
	let l2 = ref_tstp1 c r2 ((coqnorm t,h2)::hyp) const in
	let p1 = (lookup_tstp "4" (coqnorm h) hyp) in
	Printf.fprintf c "thf(%d,plain,$false,inference(tab_imp,[status(thm)%s],[%s,%d,%d%s])).\n" l (info_str "tab_imp" hyp [[h1];[h2]]) p1 l1 l2 (disch_str2 [h1;h2]);
    | Disjunction(h,s,t,r1,r2) ->
	let h1 = get_tstp_hyp_name c (coqnorm s) in	
	let h2 = get_tstp_hyp_name c (coqnorm t) in	
	let l1 = ref_tstp1 c r1 ((coqnorm s,h1)::hyp) const in
	let l2 = ref_tstp1 c r2 ((coqnorm t,h2)::hyp) const in
	let p1 = (lookup_tstp "5" (coqnorm h) hyp) in
	Printf.fprintf c "thf(%d,plain,$false,inference(tab_or,[status(thm)%s],[%s,%d,%d%s])).\n" l (info_str "tab_or" hyp [[h1];[h2]]) p1 l1 l2 (disch_str2 [h1;h2]);
    | NegConjunction(h,s,t,r1,r2) ->
	let h1 = get_tstp_hyp_name c (coqnorm s) in	
	let h2 = get_tstp_hyp_name c (coqnorm t) in	
	let l1 = ref_tstp1 c r1 ((coqnorm s,h1)::hyp) const in
	let l2 = ref_tstp1 c r2 ((coqnorm t,h2)::hyp) const in
	let p1 = (lookup_tstp "6" (coqnorm h) hyp) in
	Printf.fprintf c "thf(%d,plain,$false,inference(tab_nand,[status(thm)%s],[%s,%d,%d%s])).\n" l (info_str "tab_nand" hyp [[h1];[h2]]) p1 l1 l2 (disch_str2 [h1;h2]);
    | NegImplication(h,s,t,r1) ->
	let h1 = get_tstp_hyp_name c (coqnorm s) in
	let h2 = get_tstp_hyp_name c (coqnorm t) in	
	let l1 = ref_tstp1 c r1 ((coqnorm s,h1)::(coqnorm t,h2)::hyp) const in
	let p1 = (lookup_tstp "7" (coqnorm h) hyp) in
	Printf.fprintf c "thf(%d,plain,$false,inference(tab_negimp,[status(thm)%s],[%s,%d%s])).\n" l (info_str "tab_negimp" hyp [[h1;h2]]) p1 l1 (disch_str2 [h1;h2]);
    | Conjunction(h,s,t,r1) ->
	let h1 = get_tstp_hyp_name c (coqnorm s) in
	let h2 = get_tstp_hyp_name c (coqnorm t) in	
	let l1 = ref_tstp1 c r1 ((coqnorm s,h1)::(coqnorm t,h2)::hyp) const in
	let p1 = (lookup_tstp "8" (coqnorm h) hyp) in
	Printf.fprintf c "thf(%d,plain,$false,inference(tab_and,[status(thm)%s],[%s,%d%s])).\n" l (info_str "tab_and" hyp [[h1;h2]]) p1 l1 (disch_str2 [h1;h2]);
    | NegDisjunction(h,s,t,r1) ->
	let h1 = get_tstp_hyp_name c (coqnorm s) in
	let h2 = get_tstp_hyp_name c (coqnorm t) in	
	let l1 = ref_tstp1 c r1 ((coqnorm s,h1)::(coqnorm t,h2)::hyp) const in
	let p1 = (lookup_tstp "9" (coqnorm h) hyp) in
	Printf.fprintf c "thf(%d,plain,$false,inference(tab_nor,[status(thm)%s],[%s,%d%s])).\n" l (info_str "tab_nor" hyp [[h1;h2]]) p1 l1 (disch_str2 [h1;h2]);
    | All(h,s,r1,a,m,n) ->
	let const = add_fresh_const false c const n "" in
	let h1 = get_tstp_hyp_name c (coqnorm s) in
	let l1 = ref_tstp1 c r1 ((coqnorm s,h1)::hyp) const in
	let p1 = (lookup_tstp "9" (coqnorm h) hyp) in
	begin
	  try
	    let x = Hashtbl.find forallbvarnames p1 in
	    Printf.fprintf c "thf(%d,plain,$false,inference(tab_all,[status(thm)%s],[%s:[bind(%s,$thf(" l (info_str "tab_all" hyp [[h1]]) p1 x;
	    trm_to_tstp c n (Variables.make ());
	    Printf.fprintf c "))],%d%s])).\n" l1 (disch_str2 [h1])
	  with Not_found ->
	    Printf.fprintf c "thf(%d,plain,$false,inference(tab_all,[status(thm)%s],[%s:[bind(Xnoname,$thf(" l (info_str "tab_all" hyp [[h1]]) p1;
	    trm_to_tstp c n (Variables.make ());
	    Printf.fprintf c "))],%d%s])).\n" l1 (disch_str2 [h1])
	end
    | NegAll(h,s,r1,a,m,x) ->
	let h1 = get_tstp_hyp_name c (coqnorm s) in
	let l1 = ref_tstp1 c r1 ((coqnorm s,h1)::hyp) ((x,a)::const) in
	let p1 = (lookup_tstp "11" (coqnorm h) hyp) in
	Printf.fprintf c "thf(%d,plain,$false,inference(tab_negall,[status(thm)%s,tab_negall(eigenvar,%s)],[%s,%d%s])).\n" l (info_str "tab_negall" hyp [[h1]]) (tstpizename x) p1 l1 (disch_str2 [h1])
    | Exist(h,s,r1,a,m,x) ->
	let h1 = get_tstp_hyp_name c (coqnorm s) in
	let l1 = ref_tstp1 c r1 ((coqnorm s,h1)::hyp) ((x,a)::const) in
	let p1 = (lookup_tstp "11" (coqnorm h) hyp) in
	Printf.fprintf c "thf(%d,plain,$false,inference(tab_ex,[status(thm)%s,tab_ex(eigenvar,%s)],[%s,%d%s])).\n" l (info_str "tab_ex" hyp [[h1]]) (tstpizename x) p1 l1 (disch_str2 [h1])
    | NegExist(h,s,r1,a,m,n) ->
	let const = add_fresh_const false c const n "" in
	let h1 = get_tstp_hyp_name c (coqnorm s) in	
	let l1 = ref_tstp1 c r1 ((coqnorm s,h1)::hyp) const in
	let p1 = (lookup_tstp "12" (coqnorm h) hyp) in
	begin
	  try
	    let x = Hashtbl.find nexistsbvarnames p1 in
	    Printf.fprintf c "thf(%d,plain,$false,inference(tab_negex,[status(thm)%s],[%s:[bind(%s,$thf(" l (info_str "tab_negex" hyp [[h1]]) p1 x;
	    trm_to_tstp c n (Variables.make ());
	    Printf.fprintf c "))],%d%s])).\n" l1 (disch_str2 [h1])
	  with Not_found ->
	    Printf.fprintf c "thf(%d,plain,$false,inference(tab_negex,[status(thm)%s],[%s:[bind(Xnoname,$thf(" l (info_str "tab_negex" hyp [[h1]]) p1;
	    trm_to_tstp c n (Variables.make ());
	    Printf.fprintf c "))],%d%s])).\n" l1 (disch_str2 [h1])
	end
    | Mating(h1,h2, ss, rs) ->
	let hl = ref [] in
	let ll = ref [] in
	let fst = ref true in
	List.iter (fun (s,r) ->
	  let h' = get_tstp_hyp_name c (coqnorm s) in
	  let l' = ref_tstp1 c r ((coqnorm s,h')::hyp) const in
	  hl := h'::!hl;
	  ll := l'::!ll)
	  (List.combine ss rs);
	let p1 = (lookup_tstp "14" (coqnorm h1) hyp) in
	let p2 = (lookup_tstp "15" (coqnorm h2) hyp) in
	Printf.fprintf c "thf(%d,plain,$false,inference(tab_mat,[status(thm)%s],[%s,%s" l (info_str "tab_mat" hyp (List.map (fun h -> [h]) (!hl))) p1 p2;
	flush c;
	Printf.fprintf c "],[%s,%s" p1 p2;
	flush c;
	List.iter (fun l' ->
	  Printf.fprintf c ",%d" l'; flush c
	      ) !ll;
	Printf.fprintf c "%s])).\n" (disch_str2 !hl)
    | Decomposition(h1, ss, rs) ->
	let hl = ref [] in
	let ll = ref [] in
	let fst = ref true in
	List.iter (fun (s,r) ->
	  let h' = get_tstp_hyp_name c (coqnorm s) in
	  let l' = ref_tstp1 c r ((coqnorm s,h')::hyp) const in
	  hl := h'::!hl;
	  ll := l'::!ll)
	  (List.combine ss rs);
	let p1 = (lookup_tstp "16" (coqnorm h1) hyp) in
	Printf.fprintf c "thf(%d,plain,$false,inference(tab_dec,[status(thm)%s],[%s" l (info_str "tab_dec" hyp (List.map (fun h -> [h]) (!hl))) p1;
	flush c;
	List.iter (fun l' ->
	    Printf.fprintf c ",%d" l'; flush c
	      ) !ll;
	Printf.fprintf c "%s])).\n" (disch_str2 !hl)
    | Confront(h1,h2,su,tu,sv,tv,r1,r2) ->
	let h3 = get_tstp_hyp_name c (coqnorm su) in
	let h4 = get_tstp_hyp_name c (coqnorm tu) in
	let h5 = get_tstp_hyp_name c (coqnorm sv) in
	let h6 = get_tstp_hyp_name c (coqnorm tv) in
	let l1 = ref_tstp1 c r1 ((coqnorm su,h3)::(coqnorm tu,h4)::hyp) const in
	let l2 = ref_tstp1 c r2 ((coqnorm sv,h5)::(coqnorm tv,h6)::hyp) const in
	let p1 = (lookup_tstp "17" (coqnorm h1) hyp) in
	let p2 = (lookup_tstp "18" (coqnorm h2) hyp) in
	Printf.fprintf c "thf(%d,plain,$false,inference(tab_con,[status(thm)%s],[%s,%s,%d,%d%s])).\n" l (info_str "tab_con" hyp [[h3;h4];[h5;h6]]) p1 p2 l1 l2 (disch_str2 [h3;h4;h5;h6])
    | Trans(h1,h2,su,r1) ->
	let h3 = get_tstp_hyp_name c (coqnorm su) in	
	let l1 = ref_tstp1 c r1 ((coqnorm su,h3)::hyp) const in
	let p1 = (lookup_tstp "17" (coqnorm h1) hyp) in
	let p2 = (lookup_tstp "18" (coqnorm h2) hyp) in
	Printf.fprintf c "thf(%d,plain,$false,inference(tab_trans,[status(thm)%s],[%s,%s,%d%s])).\n" l (info_str "tab_trans" hyp [[h3]]) p1 p2 l1 (disch_str2 [h3])
    | NegEqualProp(h,s,t,r1,r2) -> 
	let h1 = get_tstp_hyp_name c (coqnorm s) in
	let h2 = get_tstp_hyp_name c (coqnorm (neg t)) in
	let h3 = get_tstp_hyp_name c (coqnorm (neg s)) in
	let h4 = get_tstp_hyp_name c (coqnorm t) in
	let l1 = ref_tstp1 c r1 ((coqnorm s,h1)::(coqnorm (neg t),h2)::hyp) const in
	let l2 = ref_tstp1 c r2 ((coqnorm (neg s),h3)::(coqnorm t,h4)::hyp) const in
	let p1 = (lookup_tstp "21" (coqnorm h) hyp) in
	Printf.fprintf c "thf(%d,plain,$false,inference(tab_be,[status(thm)%s],[%s,%d,%d%s])).\n" l (info_str "tab_be" hyp [[h1;h2];[h3;h4]]) p1 l1 l2 (disch_str2 [h1;h2;h3;h4])
    | EqualProp(h,s,t,r1,r2) -> 
	let h1 = get_tstp_hyp_name c (coqnorm s) in
	let h2 = get_tstp_hyp_name c (coqnorm t) in	
	let h3 = get_tstp_hyp_name c (coqnorm (neg s)) in
	let h4 = get_tstp_hyp_name c (coqnorm (neg t)) in
	let l1 = ref_tstp1 c r1 ((coqnorm s,h1)::(coqnorm t,h2)::hyp) const in
	let l2 = ref_tstp1 c r2 ((coqnorm (neg s),h3)::(coqnorm (neg t),h4)::hyp) const in
	let p1 = (lookup_tstp "22" (coqnorm h) hyp) in
	Printf.fprintf c "thf(%d,plain,$false,inference(tab_bq,[status(thm)%s],[%s,%d,%d%s])).\n" l (info_str "tab_bq" hyp [[h1;h2];[h3;h4]]) p1 l1 l2 (disch_str2 [h1;h2;h3;h4])
    | NegAequivalenz(h,s,t,r1,r2) -> 
	let h1 = get_tstp_hyp_name c (coqnorm s) in
	let h2 = get_tstp_hyp_name c (coqnorm (neg t)) in
	let h3 = get_tstp_hyp_name c (coqnorm (neg s)) in
	let h4 = get_tstp_hyp_name c (coqnorm t) in
	let l1 = ref_tstp1 c r1 ((coqnorm s,h1)::(coqnorm (neg t),h2)::hyp) const in
	let l2 = ref_tstp1 c r2 ((coqnorm (neg s),h3)::(coqnorm t,h4)::hyp) const in
	let p1 = (lookup_tstp "23" (coqnorm h) hyp) in
	Printf.fprintf c "thf(%d,plain,$false,inference(tab_negiff,[status(thm)%s],[%s,%d,%d%s])).\n" l (info_str "tab_negiff" hyp [[h1;h2];[h3;h4]]) p1 l1 l2 (disch_str2 [h1;h2;h3;h4])
    | Aequivalenz(h,s,t,r1,r2) -> 
	let h1 = get_tstp_hyp_name c (coqnorm s) in
	let h2 = get_tstp_hyp_name c (coqnorm t) in	
	let h3 = get_tstp_hyp_name c (coqnorm (neg s)) in
	let h4 = get_tstp_hyp_name c (coqnorm (neg t)) in
	let l1 = ref_tstp1 c r1 ((coqnorm s,h1)::(coqnorm t,h2)::hyp) const in
	let l2 = ref_tstp1 c r2 ((coqnorm (neg s),h3)::(coqnorm (neg t),h4)::hyp) const in
	let p1 = (lookup_tstp "24" (coqnorm h) hyp) in
	Printf.fprintf c "thf(%d,plain,$false,inference(tab_iff,[status(thm)%s],[%s,%d,%d%s])).\n" l (info_str "tab_iff" hyp [[h1;h2];[h3;h4]]) p1 l1 l2 (disch_str2 [h1;h2;h3;h4])
    | NegEqualFunc(h,s,r1) ->
	let h1 = get_tstp_hyp_name c (coqnorm s) in	
	let l1 = ref_tstp1 c r1 ((coqnorm s,h1)::hyp) const in
	let p1 = (lookup_tstp "25" (coqnorm h) hyp) in
	Printf.fprintf c "thf(%d,plain,$false,inference(tab_fe,[status(thm)%s],[%s,%d%s])).\n" l (info_str "tab_fe" hyp [[h1]]) p1 l1 (disch_str2 [h1])
    | EqualFunc(h,s,r1) ->
	let h1 = get_tstp_hyp_name c (coqnorm s) in	
	let l1 = ref_tstp1 c r1 ((coqnorm s,h1)::hyp) const in
	let p1 = (lookup_tstp "26" (coqnorm h) hyp) in
	Printf.fprintf c "thf(%d,plain,$false,inference(tab_fq,[status(thm)%s],[%s,%d%s])).\n" l (info_str "tab_fq" hyp [[h1]]) p1 l1 (disch_str2 [h1])
    | ChoiceR(eps,pred,s,t,r1,r2) -> 
	let const = add_fresh_const false c const pred "" in
	let h1 = get_tstp_hyp_name c (coqnorm s) in
	let h2 = get_tstp_hyp_name c (coqnorm t) in
	begin
	  match eps with
	  | Choice(a) -> 
	      let l1 = ref_tstp1 c r1 ((coqnorm s,h1)::hyp) const in
	      let l2 = ref_tstp1 c r2 ((coqnorm t,h2)::hyp) const in
	      Printf.fprintf c "thf(%d,plain,$false,inference(tab_choice,[status(thm)%s],[%d,%d%s])).\n" l (info_str "tab_choice" hyp [[h1];[h2]]) l1 l2 (disch_str2 [h1;h2])
	  | Name(x,Ar(Ar(a,Prop),_)) ->
	      let l1 = ref_tstp1 c r1 ((coqnorm s,h1)::hyp) const in
	      let l2 = ref_tstp1 c r2 ((coqnorm t,h2)::hyp) const in
	      Printf.fprintf c "thf(%d,plain,$false,inference(tab_choiceop,[status(thm),%s,%s%s],[%d,%d%s])).\n" l x (get_Choicop_axiom x a hyp) (info_str "tab_choiceop" hyp [[h1];[h2]]) l1 l2 (disch_str2 [h1;h2])
	  | _ -> failwith "eps is not a valid epsilon"
	end
    | Cut(s,r1,r2) -> 
	let const = add_fresh_const false c const s "" in
	let h1 = get_tstp_hyp_name c (coqnorm s) in
	let h2 = get_tstp_hyp_name c (coqnorm (neg s)) in
	let l1 = ref_tstp1 c r1 ((coqnorm s,h1)::hyp) const in
	let l2 = ref_tstp1 c r2 ((coqnorm (neg s),h2)::hyp) const in
	Printf.fprintf c "thf(%d,plain,$false,inference(tab_cut,[status(thm)%s],[%d,%d%s])).\n" l (info_str "tab_cut" hyp [[h1];[h2]]) l1 l2 (disch_str2 [h1;h2])
    | DoubleNegation(h,s,r1) ->
	let h1 = get_tstp_hyp_name c (coqnorm s) in
	let l1 = ref_tstp1 c r1 ((coqnorm s,h1)::hyp) const in
	let p1 = (lookup_tstp "27" (coqnorm h) hyp) in
	Printf.fprintf c "thf(%d,plain,$false,inference(tab_dn,[status(thm)%s],[%s,%d%s])).\n" l (info_str "tab_dn" hyp [[h1]]) p1 l1 (disch_str2 [h1])
    | Rewrite(prefix,pt,pt',r1) ->
	let h =  coqnorm (Ap(prefix,pt)) in
	let h1 = lookup_tstp "28" h hyp in	
	let s =  coqnorm (Ap(prefix,pt')) in 
	let h2 = get_tstp_hyp_name c s in
	let l2 = ref_tstp1 c r1 ((s,h2)::hyp) const in
	let rewout rname =
	  Printf.fprintf c "thf(%d,plain,$false,inference(%s,[status(thm)%s,%s(leibnizp,$thf(" l rname (info_str rname hyp [[h2]]) rname;
	  trm_to_tstp c prefix (Variables.make ());
	  Printf.fprintf c "))],[%s,%d%s])).\n" h1 l2 (disch_str2 [h2])
	in
	begin
	  match pt with
	  | True -> rewout "tab_rew_true"
	  | And -> rewout "tab_rew_and"
	  | Or -> rewout "tab_rew_or"
	  | Iff -> rewout "tab_rew_iff"
	  | Exists(_) -> rewout "tab_rew_ex"
	  | Eq(_) -> rewout "tab_rew_sym"
	  | Lam(_,Lam(_,Ap(DB(1,_),DB(0,_)))) ->  rewout "tab_rew_eta"
	  | Lam(Ar(Prop,Prop),Ap(Ap(Imp,Ap(Ap(Imp,DB(0,Prop)),False)),False)) ->  rewout "tab_rew_dn"
	  | Lam(_,Lam(_,Ap(Forall(_),Lam(_,(Ap(Ap(Imp,(Ap(DB(0,_),DB(2,_)))),(Ap(DB(0,_),DB(1,_)))) ))) )) ->  rewout "tab_rew_leib1"
	  | Lam(_,Lam(_,Ap(Forall(_),Lam(_,(Ap(Ap(Imp,Ap(Ap(Imp,(Ap(DB(0,_),DB(2,_)))),False)),Ap(Ap(Imp,(Ap(DB(0,_),DB(1,_)))),False)) ))) )) ->  rewout "tab_rew_leib2"
	  | Lam(_,Lam(_,Ap(Forall(_),Lam(_,(Ap(Ap(Imp,(Ap(Forall(_),Lam(_,(Ap(Ap(DB(1,_),DB(0,_)),DB(0,_)))))) ),(Ap(Ap(DB(0,_),DB(2,_)),DB(1,_)))) ) )) )) ->  rewout "tab_rew_leib3"
	  | Lam(_,Lam(_, Ap(Forall(_),Lam(_,(Ap(Ap(Imp,(Ap(Ap(Imp,(Ap(Ap(DB(0,_),DB(2,_)),DB(1,_)))),False) )),(Ap(Ap(Imp,(Ap(Forall(_),Lam(_,(Ap(Ap(DB(1,_),DB(0,_)),DB(0,_))))) )),False) )) ) )) )) ->  rewout "tab_rew_leib4"
	  | _ -> failwith("unknown rewrite step found in ref_tstp" ^ (trm_str pt))
	end
    | Delta(h,s,x,r1) ->
	let h1 = (lookup_tstp "29" (coqnorm h) hyp) in
	let h2 = get_tstp_hyp_name c (coqnorm s) in
	let l1 = ref_tstp1 c r1 ((coqnorm s,h2)::hyp) const in
	Printf.fprintf c "thf(%d,plain,$false,inference(tab_delta,[status(thm),%s%s],[%s,%d%s])).\n" l x (info_str "tab_delta" hyp [[h2]]) h1 l1 (disch_str2 [h2])
    | KnownResult(s,name,al,r1) ->
	let h1 = get_tstp_hyp_name c (coqnorm s) in
	let l1 = ref_tstp1 c r1 ((coqnorm s,h1)::hyp) const in
	begin
	  Printf.fprintf c "thf(%d,plain,$false,inference(tab_known,[status(thm)%s" l (info_str "tab_known" hyp [[h1]]);
	  flush c;
	  List.iter (fun a ->
	    Printf.fprintf c ",$thf(";
	    flush c;
	    print_stp_tstp c a false;
	    Printf.fprintf c ")";
	    flush c;
	    )
	    al;
	  Printf.fprintf c "],[%s,%d%s])).\n" (tstpizename name) l1 (disch_str2 [h1])
	end
    | NYI(h,s,r1) -> failwith("NYI step found in ref_tstp" )
    | Timeout -> failwith("Timeout step found in ref_tstp" )
    | _ -> failwith("unknown refutation case in ref_tstp" )    
  end; flush c; l

 (** Prints refutation r to out_channel c **)
let ref_tstp c r = 
  List.iter
    (fun (s,pt) ->
      let m = coqnorm pt in
      Hashtbl.add tstp_axioms m (s,m,c,ref true))
    (!coqsig_hyp_trm);
  match !conjecture with
  | Some(_,con,_) ->
    let ccon = coqnorm con in
    let ncon = neg ccon in
    let h1 = get_thyp_name() in
    Printf.fprintf c "thf(%s,conjecture," (!conjecturename);
    flush c;
    trm_to_tstp c ccon (Variables.make ());
    flush c;
    Printf.fprintf c ").\n";
    flush c;
    Printf.fprintf c "thf(%s,negated_conjecture," h1;
    flush c;
    trm_to_tstp_rembvar h1 c ncon (Variables.make ());
    flush c;
    Printf.fprintf c ",inference(assume_negation,[status(cth)],[%s])).\n" (!conjecturename);
    flush c;
    let ll = ref_tstp1 c r [(ncon,h1)] (!coqsig_const) in
    Printf.fprintf c "thf(0,theorem,";
    flush c;
    trm_to_tstp c ccon (Variables.make ());
    flush c;
    Printf.fprintf c ",inference(contra,[status(thm),contra(discharge,[%s])],[%d,%s])).\n" h1 ll h1;
    flush c;
  | None ->
    ignore (ref_tstp1 c r [] (!coqsig_const))

(*** Oct 2011 (Chad): A version for simply typed version in Coq. ***)

(** Input: stp a ***)
let rec coq_stp c a p =
  begin
    match a with
    | Prop ->
	Printf.fprintf c "prop"
    | Base(_) ->
	Printf.fprintf c "set" (*** Only allow set as a base type here ***)
    | Ar(a1,a2) ->
	if p then Printf.fprintf c "(";
	coq_stp c a1 true;
	Printf.fprintf c ">";
	coq_stp c a2 false;
	if p then Printf.fprintf c ")";
  end

let rec coq_sterm c m bound lp rp =
  match m with
    Name(x,_) -> (* Definitions *)
      let x = try (Hashtbl.find coq_names x) with Not_found -> x in
      Printf.fprintf c "%s" x
  | False -> (* Bottom *)
      Printf.fprintf c "False"
  | Ap(Ap(Imp,m1),False) ->  (* Negation *)
      if ((lp < 0) && (rp < 30)) then
	begin
	  Printf.fprintf c "~ ";
	  coq_sterm c m1 bound 30 rp;
	end
      else
	begin
	  Printf.fprintf c "(~ ";
	  coq_sterm c m1 bound 30 (-1);
	  Printf.fprintf c ")";
	end
   | Ap(Ap(Imp,m1),m2) -> (* Implication *)
      if ((lp < 17) && (rp < 16)) then
	begin
	  coq_sterm c m1 bound lp 17;
	  Printf.fprintf c " -> ";
	  coq_sterm c m2 bound 16 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  coq_sterm c m1 bound (-1) 17;
	  Printf.fprintf c " -> ";
	  coq_sterm c m2 bound 16 (-1);
	  Printf.fprintf c ")";
	end
  | Ap(Imp,m1) -> coq_sterm c (Lam(Prop,Ap(Ap(Imp,shift m1 0 1),DB(0,Prop)))) bound lp rp;
  | Imp -> coq_sterm c (Lam(Prop,Lam(Prop,Ap(Ap(Imp,DB(1,Prop)),DB(0,Prop))))) bound lp rp; 
  | Ap(Forall(a),Lam(_,m1)) -> (* forall with Lam *)
      begin
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c "(";
	begin
	  Printf.fprintf c "forall";
	  coq_sall c a m1 bound
	end;
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c ")";
      end
  | Forall(a) -> coq_sterm c (Lam(Ar(a,Prop),Ap(Forall(a),Lam(a,Ap(DB(1,Ar(a,Prop)),DB(0,a)))))) bound lp rp
  | Ap(Ap(Eq(Base(_)),m1),m2) -> (* Equality *)
      if ((lp < 40) && (rp < 40)) then
	begin
	  coq_sterm c m1 bound lp 40;
	  Printf.fprintf c " = ";
	  coq_sterm c m2 bound 40 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  coq_sterm c m1 bound (-1) 40;
	  Printf.fprintf c " = ";
	  coq_sterm c m2 bound 40 (-1);
	  Printf.fprintf c ")";
	end
  | Eq(a) ->
      if ((lp < 5000) && (rp < 5001)) then
	begin
	  Printf.fprintf c "eq ";
	  coq_stp c a true;
	end
      else
	begin
	  Printf.fprintf c "(eq ";
	  coq_stp c a true;
	  Printf.fprintf c ")";
	end      
  | Choice(a) ->
      if ((lp < 5000) && (rp < 5001)) then
	begin
	  Printf.fprintf c "Eps ";
	  coq_stp c a true;
	end
      else
	begin
	  Printf.fprintf c "(Eps ";
	  coq_stp c a true;
	  Printf.fprintf c ")"
	end
  | True -> (* Top *)
      Printf.fprintf c "True"
  | Ap(Ap(And,m1),m2) -> (* conjunction *)
      if ((lp < 21) && (rp < 20)) then
	begin
	  coq_sterm c m1 bound lp 21;
	  Printf.fprintf c " /\\ ";
	  coq_sterm c m2 bound 20 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  coq_sterm c m1 bound (-1) 21;
	  Printf.fprintf c " /\\ ";
	  coq_sterm c m2 bound 20 (-1);
	  Printf.fprintf c ")";
	end
  | And ->Printf.fprintf c "and"
  | Ap(Ap(Or,m1),m2) -> (* disjunction *)
      if ((lp < 19) && (rp < 18)) then
	begin
	  coq_sterm c m1 bound lp 19;
	  Printf.fprintf c " \\/ ";
	  coq_sterm c m2 bound 18 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  coq_sterm c m1 bound (-1) 19;
	  Printf.fprintf c " \\/ ";
	  coq_sterm c m2 bound 18 (-1);
	  Printf.fprintf c ")";
	end
  | Or -> Printf.fprintf c "or"
  | Ap(Ap(Iff,m1),m2) -> (* equivalenz *)
      if ((lp < 14) && (rp < 14)) then
	begin
	  coq_sterm c m1 bound lp 14;
	  Printf.fprintf c " <-> ";
	  coq_sterm c m2 bound 14 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  coq_sterm c m1 bound (-1) 14;
	  Printf.fprintf c " <-> ";
	  coq_sterm c m2 bound 14 (-1);
	  Printf.fprintf c ")";
	end
  | Iff -> Printf.fprintf c "iff"
  | Neg -> Printf.fprintf c "not"
  | Ap(Exists(a),Lam(_,m1)) -> (* exist *)
      begin
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c "(";
	coq_sex c a m1 bound;
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c ")";
      end
  | Exists(a) ->
      begin
	if ((lp >= 5000) || (rp >= 5001)) then Printf.fprintf c "(";
	Printf.fprintf c "ex "; coq_stp c a true;
	if ((lp >= 5000) || (rp >= 5001)) then Printf.fprintf c ")";
      end
  | DB(i,a) -> (* Bound variable *)
	Printf.fprintf c "%s" (Variables.get i bound)
  | Lam(a,m) ->
      begin
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c "(";
	begin
	  Printf.fprintf c "fun";
	  coq_slam c a m bound
	end;
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c ")";
      end
  | Ap(m1,m2) ->     
	if ((lp < 5000) && (rp < 5001)) then
	begin
	  coq_sterm c m1 bound lp 5000;
	  Printf.fprintf c " ";
	  coq_sterm c m2 bound 5001 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  coq_sterm c m1 bound (-1) 5000;
	  Printf.fprintf c " ";
	  coq_sterm c m2 bound 5001 (-1);
	  Printf.fprintf c ")";
	end      
  | _ -> raise (GenericSyntaxError ("Unknown case in coq_sterm version : " ^ (trm_str m)))

 (* Prints consecutive lambda-terms as a single fun in Coq. *) 
and coq_slam c a m bound =
	let bound = Variables.push bound in
	Printf.fprintf c " ("; Printf.fprintf c "%s" (Variables.top bound); Printf.fprintf c ":"; coq_stp c a false; Printf.fprintf c ")";
	match m with
		| Lam(b,m') -> coq_slam c b m' bound
		| _ -> Printf.fprintf c " => "; coq_sterm c m bound (-1) (-1)

(* Prints consecutive forall-terms together with the corresponding lambda-terms as a single forall in Coq. *) 		
and coq_sall c a m bound =
  let bound = Variables.push bound in
  Printf.fprintf c " ("; Printf.fprintf c "%s" (Variables.top bound); Printf.fprintf c ":"; coq_stp c a false; Printf.fprintf c ")";
  match m with
  | Ap(Forall(a'),Lam(_,m'))-> coq_sall c a' m' bound
  | _ -> Printf.fprintf c ", "; coq_sterm c m bound (-1) (-1)

(* Prints an exist-term together with the corresponding lambda-term as an exists in Coq. *) 		
and coq_sex c a m bound =
 	let bound = Variables.push bound in
	Printf.fprintf c "exists"; Printf.fprintf c " %s" (Variables.top bound); 
	Printf.fprintf c ":"; coq_stp c a false; 
        Printf.fprintf c ", ";
	coq_sterm c m bound (-1) (-1)

(** Input: refutation r, association list (term -> hypothesis name) hyp, association list (constant name -> type) const
	Output: unit, prints refutation r to c **)
let rec coq_spfterm c r hyp const bound =
  match r with
 | Conflict(s,ns) ->
     let s2 = coqnorm s in
     let ns2 = coqnorm ns in
     begin
       match (s2,ns2) with
       | (Ap(Ap(Eq(a),s21),s22),Ap(Ap(Imp,Ap(Ap(Eq(_),ns22),ns21)),False)) when s21 = ns21 && s22 = ns22 ->
	   begin
	     try
	       let h1 = List.assoc (Ap(Ap(Eq(a),s22),s21)) hyp in
	       Printf.fprintf c "%s %s" (lookup "1" ns2 hyp) h1
	     with
	     | Not_found ->
		 begin
		   try
		     let h2 = List.assoc (Ap(Ap(Imp,(Ap(Ap(Eq(a),s21),s22))),False)) hyp in
		     Printf.fprintf c "%s %s" h2 (lookup "1" s2 hyp)
		   with
		   | Not_found ->
		       Printf.fprintf c "%s (eq_sym " (lookup "1" ns2 hyp);
		       coq_stp c a true;
		       Printf.fprintf c " ";
		       coq_sterm c s21 bound 5001 5000;
		       Printf.fprintf c " ";
		       coq_sterm c s22 bound 5001 5000;
		       Printf.fprintf c " %s)" (lookup "0" s2 hyp)
		 end
	   end
       | _ -> Printf.fprintf c "%s %s" (lookup "1" ns2 hyp) (lookup "0" s2 hyp)
     end
 | Fal(_) ->
     Printf.fprintf c "%s" (lookup "2" False hyp) 
 | NegRefl(Ap(Ap(Imp,Ap(Ap(Eq(a),s),_)),False) as h) ->
     Printf.fprintf c "TRef ";
     coq_stp c a true;
     Printf.fprintf c " ";
     coq_sterm c s bound 5001 5000;
     Printf.fprintf c " %s" (lookup "3" (coqnorm h) hyp);
 | DoubleNegation(h,s,r1) ->
     let h1 = get_hyp_name() in	
     Printf.fprintf c "%s (fun %s => " (lookup "27" (coqnorm h) hyp) h1;
     coq_spfterm c r1 ((coqnorm s,h1)::hyp) const bound;
     Printf.fprintf c ")"
 | Implication(h,((Ap(Ap(Imp,s),False)) as s'),t,r1,r2) -> 	
     let h1 = get_hyp_name() in
     Printf.fprintf c "TImp ";
     coq_sterm c s bound 5001 5000;
     Printf.fprintf c " ";
     coq_sterm c t bound 5001 5000;
     Printf.fprintf c " %s (fun %s => " (lookup "4" (coqnorm h) hyp) h1;
     coq_spfterm c r1 ((coqnorm s',h1)::hyp) const bound;
     Printf.fprintf c ") (fun %s => " h1;
     coq_spfterm c r2 ((coqnorm t,h1)::hyp) const bound;
     Printf.fprintf c ")"
 | NegImplication(h,s,((Ap(Ap(Imp,t),False)) as t'),r1) ->
     let h1 = get_hyp_name() in
     let h2 = get_hyp_name() in	
     Printf.fprintf c "TNImp ";
     coq_sterm c s bound 5001 5000;
     Printf.fprintf c " ";
     coq_sterm c t bound 5001 5000;
     Printf.fprintf c " %s (fun %s %s => " (lookup "7" (coqnorm h) hyp) h1 h2;
     coq_spfterm c r1 ((coqnorm s,h1)::(coqnorm t',h2)::hyp) const bound;
     Printf.fprintf c ")"
 | Disjunction(h,s,t,r1,r2) ->
     let h1 = get_hyp_name() in
     Printf.fprintf c "TOr ";
     coq_sterm c s bound 5001 5000;
     Printf.fprintf c " ";
     coq_sterm c t bound 5001 5000;
     Printf.fprintf c " %s (fun %s => " (lookup "4" (coqnorm h) hyp) h1;
     coq_spfterm c r1 ((coqnorm s,h1)::hyp) const bound;
     Printf.fprintf c ") (fun %s => " h1;
     coq_spfterm c r2 ((coqnorm t,h1)::hyp) const bound;
     Printf.fprintf c ")"
 | NegConjunction(h,((Ap(Ap(Imp,s),False)) as s'),((Ap(Ap(Imp,t),False)) as t'),r1,r2) ->
     let h1 = get_hyp_name() in
     Printf.fprintf c "TNAnd ";
     coq_sterm c s bound 5001 5000;
     Printf.fprintf c " ";
     coq_sterm c t bound 5001 5000;
     Printf.fprintf c " %s (fun %s => " (lookup "4" (coqnorm h) hyp) h1;
     coq_spfterm c r1 ((coqnorm s',h1)::hyp) const bound;
     Printf.fprintf c ") (fun %s => " h1;
     coq_spfterm c r2 ((coqnorm t',h1)::hyp) const bound;
     Printf.fprintf c ")"
 | Conjunction(h,s,t,r1) ->
     let h1 = get_hyp_name() in
     let h2 = get_hyp_name() in	
     Printf.fprintf c "TAnd ";
     coq_sterm c s bound 5001 5000;
     Printf.fprintf c " ";
     coq_sterm c t bound 5001 5000;
     Printf.fprintf c " %s (fun %s %s => " (lookup "7" (coqnorm h) hyp) h1 h2;
     coq_spfterm c r1 ((coqnorm s,h1)::(coqnorm t,h2)::hyp) const bound;
     Printf.fprintf c ")"
 | NegDisjunction(h,((Ap(Ap(Imp,s),False)) as s'),((Ap(Ap(Imp,t),False)) as t'),r1) ->
     let h1 = get_hyp_name() in
     let h2 = get_hyp_name() in	
     Printf.fprintf c "TNOr ";
     coq_sterm c s bound 5001 5000;
     Printf.fprintf c " ";
     coq_sterm c t bound 5001 5000;
     Printf.fprintf c " %s (fun %s %s => " (lookup "7" (coqnorm h) hyp) h1 h2;
     coq_spfterm c r1 ((coqnorm s',h1)::(coqnorm t',h2)::hyp) const bound;
     Printf.fprintf c ")"
 | All((Ap(Forall(_),m1) as h),s,r1,a,m,n) ->
     let xl = find_fresh_consts n const in
     let const = List.fold_left
       (fun cons (x,b) ->
	 Printf.fprintf c "Inh ";
	 coq_stp c b true;
	 Printf.fprintf c " False (fun %s => " x;
	 (x,b)::cons
	 )
       const xl in
     let h1 = get_hyp_name() in	
     Printf.fprintf c "TAll ";
     coq_stp c a true;
     Printf.fprintf c " ";
     coq_sterm c m1 bound 5001 5000;
     Printf.fprintf c " %s " (lookup "10" (coqnorm h) hyp);
     coq_sterm c n bound 5001 5000;
     Printf.fprintf c " (fun %s => " h1;
     coq_spfterm c r1 ((coqnorm s,h1)::hyp) const bound;
     Printf.fprintf c ")";
     List.iter
       (fun (x,b) ->
	 Printf.fprintf c ")";
	 )
       xl;
 | NegExist(((Ap(Ap(Imp,Ap(Exists(_),m1)),False)) as h),s,r1,a,m,n) ->
     let xl = find_fresh_consts n const in
     let const = List.fold_left
       (fun cons (x,b) ->
	 Printf.fprintf c "Inh ";
	 coq_stp c b true;
	 Printf.fprintf c " False (fun %s => " x;
	 (x,b)::cons
	 )
       const xl in
     let h1 = get_hyp_name() in	
     Printf.fprintf c "TNEx ";
     coq_stp c a true;
     Printf.fprintf c " ";
     coq_sterm c m1 bound 5001 5000;
     Printf.fprintf c " %s " (lookup "10" (coqnorm h) hyp);
     coq_sterm c n bound 5001 5000;
     Printf.fprintf c " (fun %s => " h1;
     coq_spfterm c r1 ((coqnorm s,h1)::hyp) const bound;
     Printf.fprintf c ")";
     List.iter
       (fun (x,b) ->
	 Printf.fprintf c ")";
	 )
       xl;
 | Exist(((Ap(Exists(_),m1)) as h),s,r1,a,m,x) ->
     let h1 = get_hyp_name() in
     let x = ( Hashtbl.find coq_names x ) in
     Printf.fprintf c "TEx ";
     coq_stp c a true;
     Printf.fprintf c " ";
     coq_sterm c m1 bound 5001 5000;
     Printf.fprintf c " %s (fun %s %s => " (lookup "10" (coqnorm h) hyp) x h1;
     coq_spfterm c r1 ((coqnorm s,h1)::hyp) ((x,a)::const) bound;
     Printf.fprintf c ")";
 | NegAll(((Ap(Ap(Imp,Ap(Forall(_),m1)),False)) as h),s,r1,a,m,x) ->
     let h1 = get_hyp_name() in
     let x = ( Hashtbl.find coq_names x ) in
     Printf.fprintf c "TNAll ";
     coq_stp c a true;
     Printf.fprintf c " ";
     coq_sterm c m1 bound 5001 5000;
     Printf.fprintf c " %s (fun %s %s => " (lookup "10" (coqnorm h) hyp) x h1;
     coq_spfterm c r1 ((coqnorm s,h1)::hyp) ((x,a)::const) bound;
     Printf.fprintf c ")";
 | Cut(s,r1,r2) -> 
     let xl = find_fresh_consts s const in
     let const = List.fold_left
	 (fun cons (x,b) ->
	 Printf.fprintf c "Inh ";
	 coq_stp c b true;
	 Printf.fprintf c " False (fun %s => " x;
	   (x,b)::cons
	 )
       const xl in
     let h1 = get_hyp_name() in	
     Printf.fprintf c "((fun %s => " h1;
     coq_spfterm c r2 ((coqnorm (neg s),h1)::hyp) const bound;
     Printf.fprintf c ") (fun %s => " h1;
     coq_spfterm c r1 ((coqnorm s,h1)::hyp) const bound;
     Printf.fprintf c "))";
     List.iter
       (fun (x,b) ->
	 Printf.fprintf c ")";
	 )
       xl;
 | Trans(((Ap(Ap(Eq(a),w),z)) as h1),((Ap(Ap(Eq(_),v),u)) as h2),(Ap(Ap(Eq(_),s),t) as st),r1) ->
     begin
     let h3 = get_hyp_name() in
     Printf.fprintf c "Ttrans ";
     coq_stp c a true;
     Printf.fprintf c " ";
     coq_sterm c s bound 5001 5000;
     Printf.fprintf c " ";
     coq_sterm c t bound 5001 5000;
     Printf.fprintf c " ";
     if (coqnorm w = coqnorm s) then
       begin
	 if (coqnorm v = coqnorm t) then
	   begin
   coq_sterm c z bound 5001 5000;
   Printf.fprintf c " %s (eq_sym " (lookup "10" (coqnorm h1) hyp);
   coq_stp c a true;
   Printf.fprintf c " ";
   coq_sterm c v bound 5001 5000;
   Printf.fprintf c " ";
   coq_sterm c u bound 5001 5000;
   Printf.fprintf c " %s) " (lookup "10" (coqnorm h2) hyp)
           end
         else if (coqnorm u = coqnorm t) then
	   begin
   coq_sterm c z bound 5001 5000;
   Printf.fprintf c " %s %s " (lookup "10" (coqnorm h1) hyp) (lookup "10" (coqnorm h2) hyp)
	   end
	 else
	   Printf.fprintf c "<TRANS-ERROR>"
       end
     else if (coqnorm z = coqnorm s) then
       begin
	 if (coqnorm v = coqnorm t) then
	   begin
   coq_sterm c w bound 5001 5000;
   Printf.fprintf c " (eq_sym ";
   coq_stp c a true;
   Printf.fprintf c " ";
   coq_sterm c w bound 5001 5000;
   Printf.fprintf c " ";
   coq_sterm c z bound 5001 5000;
   Printf.fprintf c " %s) (eq_sym " (lookup "10" (coqnorm h1) hyp);
   coq_stp c a true;
   Printf.fprintf c " ";
   coq_sterm c v bound 5001 5000;
   Printf.fprintf c " ";
   coq_sterm c u bound 5001 5000;
   Printf.fprintf c " %s) " (lookup "10" (coqnorm h2) hyp)
	   end
	 else if (coqnorm u = coqnorm t) then
	   begin
   coq_sterm c w bound 5001 5000;
   Printf.fprintf c " (eq_sym ";
   coq_stp c a true;
   Printf.fprintf c " ";
   coq_sterm c w bound 5001 5000;
   Printf.fprintf c " ";
   coq_sterm c z bound 5001 5000;
   Printf.fprintf c " %s) %s " (lookup "10" (coqnorm h1) hyp) (lookup "10" (coqnorm h2) hyp)
	   end
	 else
	   Printf.fprintf c "<TRANS-ERROR>"
       end
     else if (coqnorm w = coqnorm t) then
       begin
	 if (coqnorm v = coqnorm s) then
	   begin
   coq_sterm c z bound 5001 5000;
   Printf.fprintf c " (eq_sym ";
   coq_stp c a true;
   Printf.fprintf c " ";
   coq_sterm c v bound 5001 5000;
   Printf.fprintf c " ";
   coq_sterm c u bound 5001 5000;
   Printf.fprintf c " %s) %s " (lookup "10" (coqnorm h2) hyp) (lookup "10" (coqnorm h1) hyp)
	   end
	 else if (coqnorm u = coqnorm s) then
	   begin
   coq_sterm c z bound 5001 5000;
   Printf.fprintf c " (eq_sym ";
   coq_stp c a true;
   Printf.fprintf c " ";
   coq_sterm c v bound 5001 5000;
   Printf.fprintf c " ";
   coq_sterm c u bound 5001 5000;
   Printf.fprintf c " %s) (eq_sym " (lookup "10" (coqnorm h2) hyp);
   coq_stp c a true;
   Printf.fprintf c " ";
   coq_sterm c w bound 5001 5000;
   Printf.fprintf c " ";
   coq_sterm c z bound 5001 5000;
   Printf.fprintf c " %s) " (lookup "10" (coqnorm h1) hyp)
	   end
	 else
	   Printf.fprintf c "<TRANS-ERROR>"
       end
     else if (coqnorm z = coqnorm t) then
       begin
	 if (coqnorm v = coqnorm s) then
	   begin
   coq_sterm c w bound 5001 5000;
   Printf.fprintf c " %s %s " (lookup "10" (coqnorm h2) hyp) (lookup "10" (coqnorm h1) hyp);
	   end
	 else if (coqnorm u = coqnorm s) then
	   begin
   coq_sterm c w bound 5001 5000;
   Printf.fprintf c " %s (eq_sym " (lookup "10" (coqnorm h2) hyp);
   coq_stp c a true;
   Printf.fprintf c " ";
   coq_sterm c w bound 5001 5000;
   Printf.fprintf c " ";
   coq_sterm c z bound 5001 5000;
   Printf.fprintf c " %s) " (lookup "10" (coqnorm h1) hyp)
	   end
	 else
	   Printf.fprintf c "<TRANS-ERROR>"
       end
     else
       Printf.fprintf c "<TRANS-ERROR>";
     Printf.fprintf c "(fun %s => " h3;
     coq_spfterm c r1 ((coqnorm st,h3)::hyp) const bound;
     Printf.fprintf c ")";
     end
 | Delta(h,s,x,r1) ->
   let h1 = (lookup "29" (coqnorm h) hyp) in	
   coq_spfterm c r1 ((coqnorm s,h1)::hyp) const bound;
 | ChoiceR(eps,pred,s,t,r1,r2) -> 
     let xl = find_fresh_consts s const in
     let const = List.fold_left
       (fun cons (x,b) ->
	 Printf.fprintf c "Inh ";
	 coq_stp c b true;
	 Printf.fprintf c " False (fun %s => " x;
   (x,b)::cons
	 )
       const xl in
     let h1 = get_hyp_name() in
     begin
       match eps with
       | Choice(a) -> 
	   Printf.fprintf c "TEps ";
           coq_stp c a true;
	   Printf.fprintf c " ";
           coq_sterm c pred bound 5001 5000;
	   Printf.fprintf c " (fun %s => " h1;
	   coq_spfterm c r1 ((coqnorm s,h1)::hyp) const bound;
	   Printf.fprintf c ") (fun %s => " h1;
	   coq_spfterm c r2 ((coqnorm t,h1)::hyp) const bound;
	   Printf.fprintf c ")";
       | Name(x,Ar(Ar(a,Prop),_)) ->
	   Printf.fprintf c "CHOICE-TODO";
       | _ -> failwith "eps is not a valid epsilon"
     end;
     List.iter
       (fun (x,b) ->
	 Printf.fprintf c ")";
	 )
       xl;
 | NegEqualProp(h,s,t,r1,r2) -> 
	let h1 = get_hyp_name() in
	let h2 = get_hyp_name() in
	Printf.fprintf c "TBE ";
	coq_sterm c s bound 5001 5000;
	Printf.fprintf c " ";
	coq_sterm c t bound 5001 5000;
	Printf.fprintf c " %s (fun %s %s => " (lookup "21" (coqnorm h) hyp) h1 h2;
	coq_spfterm c r1 ((coqnorm s,h1)::(coqnorm (neg t),h2)::hyp) const bound;
	Printf.fprintf c ") (fun %s %s => " h1 h2;
	coq_spfterm c r2 ((coqnorm (neg s),h1)::(coqnorm t,h2)::hyp) const bound;
	Printf.fprintf c ")";
 | EqualProp(h,s,t,r1,r2) -> 
	let h1 = get_hyp_name() in
	let h2 = get_hyp_name() in	
	Printf.fprintf c "TBQ ";
	coq_sterm c s bound 5001 5000;
	Printf.fprintf c " ";
	coq_sterm c t bound 5001 5000;
	Printf.fprintf c " %s (fun %s %s => " (lookup "21" (coqnorm h) hyp) h1 h2;
	coq_spfterm c r1 ((coqnorm s,h1)::(coqnorm t,h2)::hyp) const bound;
	Printf.fprintf c ") (fun %s %s => " h1 h2;
	coq_spfterm c r2 ((coqnorm (neg s),h1)::(coqnorm (neg t),h2)::hyp) const bound;
	Printf.fprintf c ")";
 | NegAequivalenz(h,s,t,r1,r2) -> 
	let h1 = get_hyp_name() in
	let h2 = get_hyp_name() in
	Printf.fprintf c "TNIff ";
	coq_sterm c s bound 5001 5000;
	Printf.fprintf c " ";
	coq_sterm c t bound 5001 5000;
	Printf.fprintf c " %s (fun %s %s => " (lookup "21" (coqnorm h) hyp) h1 h2;
	coq_spfterm c r1 ((coqnorm s,h1)::(coqnorm (neg t),h2)::hyp) const bound;
	Printf.fprintf c ") (fun %s %s => " h1 h2;
	coq_spfterm c r2 ((coqnorm (neg s),h1)::(coqnorm t,h2)::hyp) const bound;
	Printf.fprintf c ")";
 | Aequivalenz(h,s,t,r1,r2) -> 
	let h1 = get_hyp_name() in
	let h2 = get_hyp_name() in	
	Printf.fprintf c "TIff ";
	coq_sterm c s bound 5001 5000;
	Printf.fprintf c " ";
	coq_sterm c t bound 5001 5000;
	Printf.fprintf c " %s (fun %s %s => " (lookup "21" (coqnorm h) hyp) h1 h2;
	coq_spfterm c r1 ((coqnorm s,h1)::(coqnorm t,h2)::hyp) const bound;
	Printf.fprintf c ") (fun %s %s => " h1 h2;
	coq_spfterm c r2 ((coqnorm (neg s),h1)::(coqnorm (neg t),h2)::hyp) const bound;
	Printf.fprintf c ")";
 | Rewrite(prefix,pt,pt',r1) ->
   let h =  coqnorm (Ap(prefix,pt)) in
   let h1 = lookup "28" h hyp in	
   let s =  coqnorm (Ap(prefix,pt')) in 
   begin
     match pt with
     | True ->
	 let h2 = get_hyp_name() in
	 Printf.fprintf c "TRew prop True (~ False) ";
	 coq_sterm c prefix bound 5001 5000;
	 Printf.fprintf c " eq_true %s (fun %s => " h1 h2;
	 coq_spfterm c r1 ((s,h2)::hyp) const bound;
	 Printf.fprintf c ")"
     | And ->
	 let h2 = get_hyp_name() in
	 Printf.fprintf c "TRew (prop>prop>prop) and (fun x y:prop => ~(x -> ~y)) ";
	 coq_sterm c prefix bound 5001 5000;
	 Printf.fprintf c " eq_and_imp %s (fun %s => " h1 h2;
	 coq_spfterm c r1 ((s,h2)::hyp) const bound;
	 Printf.fprintf c ")"
     | Or ->
	 let h2 = get_hyp_name() in
	 Printf.fprintf c "TRew (prop>prop>prop) or (fun x y:prop => ~x -> y) ";
	 coq_sterm c prefix bound 5001 5000;
	 Printf.fprintf c " eq_or_imp %s (fun %s => " h1 h2;
	 coq_spfterm c r1 ((s,h2)::hyp) const bound;
	 Printf.fprintf c ")"
     | Iff ->
	 let h2 = get_hyp_name() in
	 Printf.fprintf c "TRew (prop>prop>prop) iff (eq prop) ";
	 coq_sterm c prefix bound 5001 5000;
	 Printf.fprintf c " eq_iff %s (fun %s => " h1 h2;
	 coq_spfterm c r1 ((s,h2)::hyp) const bound;
	 Printf.fprintf c ")"
     | Lam(Ar(Prop,Prop),Ap(Ap(Imp,Ap(Ap(Imp,DB(0,Prop)),False)),False)) -> 
	 let h2 = get_hyp_name() in
	 Printf.fprintf c "TRew (prop>prop) (fun x:prop => ~~x) (fun x:prop => x) ";
	 coq_sterm c prefix bound 5001 5000;
	 Printf.fprintf c " eq_neg_neg_id %s (fun %s => " h1 h2;
	 coq_spfterm c r1 ((s,h2)::hyp) const bound;
	 Printf.fprintf c ")"
     | Exists(a) ->
	 let h2 = get_hyp_name() in
	 Printf.fprintf c "TRew ((";
         coq_stp c a true;
	 Printf.fprintf c ">prop)>prop) (fun f => exists x, f x) (fun f => ~forall x, ~f x) ";
	 coq_sterm c prefix bound 5001 5000;
	 Printf.fprintf c " (eq_exists_nforall ";
         coq_stp c a true;
	 Printf.fprintf c ") %s (fun %s => " h1 h2;
	 coq_spfterm c r1 ((s,h2)::hyp) const bound;
	 Printf.fprintf c ")"
     | Eq(_) -> failwith("unexpected rewrite step with Eq") (*** symmetry handled by known now ***)
     | Lam((Ar(a,b) as ab),Lam(_,Ap(DB(1,_),DB(0,_)))) ->
(*** Skip etas - Mar 2012 ***)
	 coq_spfterm c r1 ((s,h1)::hyp) const bound;
(***
       (*** Could Skip etas, but don't for now so Coq can type check the result. ***)
       (*** But mark it with a comment ***)
	 let h2 = h1 ^ "_e" in
	 Printf.fprintf c "\n(** eta 1 **) TRew ((";
         coq_stp c ab true;
	 Printf.fprintf c ")>";
         coq_stp c ab true;
	 Printf.fprintf c ") (fun f x => f x) (fun f => f) ";
	 coq_sterm c prefix bound 5001 5000;
	 Printf.fprintf c " (eq_eta2 ";
         coq_stp c a true;
	 Printf.fprintf c " ";
         coq_stp c b true;
	 Printf.fprintf c ") %s (fun %s =>\n" h1 h2;
	 coq_spfterm c r1 ((s,h2)::hyp) const bound;
	 Printf.fprintf c "\n) (** eta 2 **)\n"
***)
     | Lam(a,Lam(_,Ap(Forall(_),Lam(_,(Ap(Ap(Imp,(Ap(DB(0,_),DB(2,_)))),(Ap(DB(0,_),DB(1,_)))) ))) )) -> 
	 let h2 = get_hyp_name() in
	 Printf.fprintf c "TRew (";
         coq_stp c a true;
	 Printf.fprintf c ">";
         coq_stp c a true;
	 Printf.fprintf c ">prop) (fun s t => forall p:";
         coq_stp c a true;
	 Printf.fprintf c ">prop, p s -> p t) (fun s t => s = t) ";
	 coq_sterm c prefix bound 5001 5000;
	 Printf.fprintf c " (eq_leib1 ";
         coq_stp c a true;
	 Printf.fprintf c ") %s (fun %s => " h1 h2;
	 coq_spfterm c r1 ((s,h2)::hyp) const bound;
	 Printf.fprintf c ")"
     | Lam(a,Lam(_,Ap(Forall(_),Lam(_,(Ap(Ap(Imp,Ap(Ap(Imp,(Ap(DB(0,_),DB(2,_)))),False)),Ap(Ap(Imp,(Ap(DB(0,_),DB(1,_)))),False)) ))) )) -> 
	 let h2 = get_hyp_name() in
	 Printf.fprintf c "TRew (";
         coq_stp c a true;
	 Printf.fprintf c ">";
         coq_stp c a true;
	 Printf.fprintf c ">prop) (fun s t => forall p:";
         coq_stp c a true;
	 Printf.fprintf c ">prop, ~ p s -> ~ p t) (fun s t => s = t) ";
	 coq_sterm c prefix bound 5001 5000;
	 Printf.fprintf c " (eq_leib2 ";
         coq_stp c a true;
	 Printf.fprintf c ") %s (fun %s => " h1 h2;
	 coq_spfterm c r1 ((s,h2)::hyp) const bound;
	 Printf.fprintf c ")"
     | Lam(a,Lam(_,Ap(Forall(_),Lam(_,(Ap(Ap(Imp,(Ap(Forall(_),Lam(_,(Ap(Ap(DB(1,_),DB(0,_)),DB(0,_)))))) ),(Ap(Ap(DB(0,_),DB(2,_)),DB(1,_)))) ) )) )) -> 
	 let h2 = get_hyp_name() in
	 Printf.fprintf c "TRew (";
         coq_stp c a true;
	 Printf.fprintf c ">";
         coq_stp c a true;
	 Printf.fprintf c ">prop) (fun s t => forall r:";
         coq_stp c a true;
	 Printf.fprintf c ">";
         coq_stp c a true;
	 Printf.fprintf c ">prop, (forall x, r x x) -> r s t) (fun s t => s = t) ";
	 coq_sterm c prefix bound 5001 5000;
	 Printf.fprintf c " (eq_leib3 ";
         coq_stp c a true;
	 Printf.fprintf c ") %s (fun %s => " h1 h2;
	 coq_spfterm c r1 ((s,h2)::hyp) const bound;
	 Printf.fprintf c ")"
     | Lam(a,Lam(_, Ap(Forall(_),Lam(_,(Ap(Ap(Imp,(Ap(Ap(Imp,(Ap(Ap(DB(0,_),DB(2,_)),DB(1,_)))),False) )),(Ap(Ap(Imp,(Ap(Forall(_),Lam(_,(Ap(Ap(DB(1,_),DB(0,_)),DB(0,_))))) )),False) )) ) )) )) -> 
	 let h2 = get_hyp_name() in
	 Printf.fprintf c "TRew (";
         coq_stp c a true;
	 Printf.fprintf c ">";
         coq_stp c a true;
	 Printf.fprintf c ">prop) (fun s t => forall r:";
         coq_stp c a true;
	 Printf.fprintf c ">";
         coq_stp c a true;
	 Printf.fprintf c ">prop, ~ r s t -> ~ (forall x, r x x)) (fun s t => s = t) ";
	 coq_sterm c prefix bound 5001 5000;
	 Printf.fprintf c " (eq_leib4 ";
         coq_stp c a true;
	 Printf.fprintf c ") %s (fun %s => " h1 h2;
	 coq_spfterm c r1 ((s,h2)::hyp) const bound;
	 Printf.fprintf c ")"
     | _ -> failwith("unknown rewrite step found in ref_coq" ^ (trm_str pt))
   end;
 | NegEqualFunc(((Ap(Ap(Imp,Ap(Ap(Eq(Ar(a,b)),s1),s2)),False)) as h),s,r1) ->
     let h1 = get_hyp_name() in
     Printf.fprintf c "TFE ";
     coq_stp c a true;
     Printf.fprintf c " ";
     coq_stp c b true;
     Printf.fprintf c " ";
     coq_sterm c s1 bound 5001 5000;
     Printf.fprintf c " ";
     coq_sterm c s2 bound 5001 5000;
     Printf.fprintf c " %s (fun %s => " (lookup "90" (coqnorm h) hyp) h1;
     coq_spfterm c r1 ((coqnorm s,h1)::hyp) const bound;
     Printf.fprintf c ")";
 | EqualFunc(((Ap(Ap(Eq(Ar(a,b)),s1),s2)) as h),s,r1) ->
     let h1 = get_hyp_name() in
     Printf.fprintf c "TFQ ";
     coq_stp c a true;
     Printf.fprintf c " ";
     coq_stp c b true;
     Printf.fprintf c " ";
     coq_sterm c s1 bound 5001 5000;
     Printf.fprintf c " ";
     coq_sterm c s2 bound 5001 5000;
     Printf.fprintf c " %s (fun %s => " (lookup "90" (coqnorm h) hyp) h1;
     coq_spfterm c r1 ((coqnorm s,h1)::hyp) const bound;
     Printf.fprintf c ")";
 | KnownResult(s,name,al,r1) ->
     begin
       match al with
       | (_::_) ->
	   let h1 = get_hyp_name() in
	   Printf.fprintf c "let %s := %s" h1 name;
	   List.iter
	     (fun a ->
	       Printf.fprintf c " ";
	       coq_stp c a true)
	     al;
	   Printf.fprintf c " in ";
	   coq_spfterm c r1 ((coqnorm s,h1)::hyp) const bound
       | [] ->
	   coq_spfterm c r1 ((coqnorm s,name)::hyp) const bound
     end
 | Decomposition(((Ap(Ap(Imp,Ap(Ap(Eq(b),tl),tr)),False)) as h1),ss, rs) ->
     coq_spfterm_dec c (lookup "91" (coqnorm h1) hyp) b tl tr (List.rev ss) (List.rev rs) hyp const bound
 | Mating(h1,h2, ss, rs) ->
     let h1c = coqnorm h1 in
     let h2c = coqnorm h2 in
     let h3 = get_hyp_name() in
     begin
       match (h1,h2,List.rev ss,List.rev rs) with (*** ss and rs **)
       | (Ap(Ap(Imp,Ap(h1p,h1s)),False),Ap(h2q,h2t),(((Ap(Ap(Imp,Ap(Ap(Eq(a),s11),s12)),False)) as s1)::sr),(r1::rr)) when h1s = s11 && h2t = s12 ->
	   Printf.fprintf c "TMat ";
	   coq_stp c (tpof h1s) true;
	   Printf.fprintf c " ";
	   coq_sterm c h2t bound 5001 5000;
	   Printf.fprintf c " ";
	   coq_sterm c h1s bound 5001 5000;
	   Printf.fprintf c " ";
	   coq_sterm c h2q bound 5001 5000;
	   Printf.fprintf c " ";
	   coq_sterm c h1p bound 5001 5000;
	   Printf.fprintf c " %s %s (fun %s => " (lookup "91" h2c hyp) (lookup "92" h1c hyp) h3;
	   coq_spfterm_dec c h3 (Ar(a,Prop)) h2q h1p sr rr ((coqnorm (Ap(Ap(Imp,Ap(Ap(Eq(Ar(a,Prop)),h1p),h2q)),False)),h3)::hyp) const bound; (** fix **)
	   Printf.fprintf c ") (fun %s => " h3;
	   coq_spfterm c r1 ((coqnorm s1,h3)::hyp) const bound;
	   Printf.fprintf c ")";
       | (Ap(Ap(Imp,Ap(h1p,h1s)),False),Ap(h2q,h2t),(((Ap(Ap(Imp,Ap(Ap(Eq(a),s11),s12)),False)) as s1)::sr),(r1::rr)) ->
	   let h4 = get_hyp_name() in
	   Printf.fprintf c "TMat ";
	   coq_stp c (tpof h1s) true;
	   Printf.fprintf c " ";
	   coq_sterm c h2t bound 5001 5000;
	   Printf.fprintf c " ";
	   coq_sterm c h1s bound 5001 5000;
	   Printf.fprintf c " ";
	   coq_sterm c h2q bound 5001 5000;
	   Printf.fprintf c " ";
	   coq_sterm c h1p bound 5001 5000;
	   Printf.fprintf c " %s %s (fun %s => let %s = eq_sym " (lookup "91" h2c hyp) (lookup "92" h1c hyp) h4 h3;
	   coq_stp c a true;
	   Printf.fprintf c " ";
	   coq_sterm c h1p bound 5001 5000;
	   Printf.fprintf c " ";
	   coq_sterm c h2q bound 5001 5000;
	   Printf.fprintf c " in ";
	   coq_spfterm_dec c h3 (Ar(a,Prop)) h2q h1p sr rr ((coqnorm (Ap(Ap(Imp,Ap(Ap(Eq(Ar(a,Prop)),h1p),h2q)),False)),h3)::(coqnorm (Ap(Ap(Imp,Ap(Ap(Eq(Ar(a,Prop)),h2q),h1p)),False)),h4)::hyp) const bound;
	   Printf.fprintf c ") (fun %s => " h3;
	   coq_spfterm c r1 ((coqnorm s1,h3)::hyp) const bound;
	   Printf.fprintf c ")";
       | (Ap(h1p,h1s),Ap(Ap(Imp,Ap(h2q,h2t)),False),(((Ap(Ap(Imp,Ap(Ap(Eq(a),s11),s12)),False)) as s1)::sr),(r1::rr)) ->
	   Printf.fprintf c "TMat ";
	   coq_stp c a true;
	   Printf.fprintf c " ";
	   coq_sterm c h1s bound 5001 5000;
	   Printf.fprintf c " ";
	   coq_sterm c h2t bound 5001 5000;
	   Printf.fprintf c " ";
	   coq_sterm c h1p bound 5001 5000;
	   Printf.fprintf c " ";
	   coq_sterm c h2q bound 5001 5000;
	   Printf.fprintf c " %s %s (fun %s => " (lookup "91" h1c hyp) (lookup "92" h2c hyp) h3;
	   coq_spfterm_dec c h3 (Ar(a,Prop)) h1p h2q sr rr ((coqnorm (Ap(Ap(Imp,Ap(Ap(Eq(Ar(a,Prop)),h1p),h2q)),False)),h3)::hyp) const bound;
	   Printf.fprintf c ") (fun %s => " h3;
	   coq_spfterm c r1 ((coqnorm s1,h3)::hyp) const bound;
	   Printf.fprintf c ")";
       | _ -> failwith("mating step did not match expected in ref_coq::" ^ (trm_str h1) ^ "::" ^ (trm_str h2))
     end
 | Confront(h1,h2,su,tu,sv,tv,r1,r2) ->
     let h1c = coqnorm h1 in
     let h2c = coqnorm h2 in
     let sun = coqnorm su in
     let tvn = coqnorm tv in
     begin
       match (sun,tvn) with
       | (Ap(Ap(Imp,Ap(Ap(Eq(a),s),u)),False),Ap(Ap(Imp,Ap(Ap(Eq(_),t),v)),False)) ->
	   let h3 = get_hyp_name() in
	   let h4 = get_hyp_name() in	
	   Printf.fprintf c "TCon ";
	   coq_stp c a true;
	   Printf.fprintf c " ";
	   coq_sterm c s bound 5001 5000;
	   Printf.fprintf c " ";
	   coq_sterm c t bound 5001 5000;
	   Printf.fprintf c " ";
	   coq_sterm c u bound 5001 5000;
	   Printf.fprintf c " ";
	   coq_sterm c v bound 5001 5000;
	   (*** h1 and h2 may be reversed ***)
	   begin
	     match h1c with
	     | (Ap(Ap(Eq(_),_),_)) ->
		 Printf.fprintf c " %s %s (fun %s %s => " (lookup "81" (coqnorm h1) hyp) (lookup "82" (coqnorm h2) hyp) h3 h4
	     | _ ->
		 Printf.fprintf c " %s %s (fun %s %s => " (lookup "81" (coqnorm h2) hyp) (lookup "82" (coqnorm h1) hyp) h3 h4
	   end;
	   coq_spfterm c r1 ((sun,h3)::(coqnorm tu,h4)::hyp) const bound;
	   Printf.fprintf c ") (fun %s %s => " h3 h4;
	   coq_spfterm c r2 ((coqnorm sv,h3)::(tvn,h4)::hyp) const bound;
	   Printf.fprintf c ")";
       | _ -> failwith("confront does not match")
     end
 | NYI(h,s,r1) -> failwith("NYI step found in ref_coq" )
 | Timeout -> failwith("Timeout step found in ref_coq" )
 | _ -> failwith("unknown refutation case in ref_coq" )    
and coq_spfterm_dec c h1n b tl tr ss rs hyp const bound =
  if ((coqnorm tl) = (coqnorm tr)) then
    begin
      Printf.fprintf c "TRef ";
      coq_stp c b true;
      Printf.fprintf c " ";
      coq_sterm c tl bound 5001 5000;
      Printf.fprintf c " %s" h1n
    end
  else
    begin
      match (ss,rs,tl,tr) with
	((((Ap(Ap(Imp,Ap(Ap(Eq(a),s11),s12)),False)) as s1)::sr),(r1::rr),Ap(tl1,_),Ap(tr1,_)) ->
	  let h2 = get_hyp_name() in
	  begin
	    Printf.fprintf c "TDec ";
	    coq_stp c a true;
	    Printf.fprintf c " ";
	    coq_stp c b true;
	    Printf.fprintf c " ";
	    coq_sterm c s11 bound 5001 5000;
	    Printf.fprintf c " ";
	    coq_sterm c s12 bound 5001 5000;
	    Printf.fprintf c " ";
	    coq_sterm c tl1 bound 5001 5000;
	    Printf.fprintf c " ";
	    coq_sterm c tr1 bound 5001 5000;
	    Printf.fprintf c " %s (fun %s => " h1n h2;
	    coq_spfterm_dec c h2 (Ar(a,b)) tl1 tr1 sr rr ((coqnorm (Ap(Ap(Imp,Ap(Ap(Eq(Ar(a,b)),tl1),tr1)),False)),h2)::hyp) const bound;
	    Printf.fprintf c ") (fun %s => " h2;
	    coq_spfterm c r1 ((coqnorm s1,h2)::hyp) const bound;
	    Printf.fprintf c ")";
	  end
      | _ -> failwith "decomposition failed to render as a coq spfterm"
    end

 (** Prints refutation r to out_channel c **)
let ref_coq_spfterm c r = 
  try
    match !conjecture with
      Some(_,con,_)->
	begin
	  let con = coqnorm con in
	  match con with
	  | False -> raise Not_found
	  | _ ->
	      let hyp = List.fold_left (fun l (s,pt) -> (coqnorm pt,s)::l) [] !coqsig_hyp_trm in
	      let h1 = get_hyp_name() in
	      Printf.fprintf c "exact (NNPP ";
	      coq_sterm c con (Variables.make ()) 5001 5000;
	      Printf.fprintf c " (fun %s => " h1;
	      coq_spfterm c r ((neg con,h1)::hyp) (!coqsig_const) (Variables.make ());
	      Printf.fprintf c ")).\nQed.\n";
	      flush c
	end
    | None -> raise Not_found
  with
  | Not_found ->
      let hyp = List.fold_left (fun l (s,pt) -> (coqnorm pt,s)::l) [] !coqsig_hyp_trm in
      Printf.fprintf c "exact (";
      coq_spfterm c r hyp (!coqsig_const) (Variables.make ());
      Printf.fprintf c ").\nQed.\n";
      flush c
