open Syntax

type refutation =
	(* Conflict(m1,m2), where [m1] = [~m2] *)
   Conflict of trm * trm
	(* Fal(m), where [m]=False *)
 | Fal of trm
	(* NegRefl(m), where [m]=~(s=s) for some term s*)
 | NegRefl of trm
	(* Implication(h,m1,m2,R1,R2), where [h]=s->t, [~m1]=s, [m2]=t *)
 | Implication of trm * trm * trm * refutation * refutation  
 | Disjunction of trm * trm * trm * refutation * refutation
 | NegConjunction of trm * trm * trm * refutation * refutation  
 | NegImplication of trm * trm * trm * refutation
 | Conjunction of trm * trm * trm * refutation 
 | NegDisjunction of trm * trm * trm * refutation 
	(* All(h,s,R,a,n,t), where [h] = forall_a.p , s = [pt]  *)
 | All of trm * trm * refutation * stp * trm *trm
	(* NegAll(h,s,R,a,n,x), where [~h] = forall_a.p , s = [px] *)
 | NegAll of trm * trm * refutation * stp * trm * string
 | Exist of trm * trm * refutation * stp * trm * string
 | NegExist of trm * trm * refutation * stp * trm *trm
	(* Mating(h1,h2,m_1..m_n,r_1..r_n), where [m_i]= ~(s_i = t_i), [h1 or h2]= p s_1 .. s_n, [h2 or h1]= ~p t_1 .. t_n*)
 | Mating of trm * trm * trm list * refutation list
	(* Decomposition(h,m_1..m_n,r_1..r_n), where [m_i]= ~(s_i = t_i), [h]= ~(p s_1 .. s_n=p t_1 .. t_n) *)
 | Decomposition of trm * trm list * refutation list 
 | Confront of trm * trm * trm * trm * trm * trm * refutation * refutation 
	(* Transitivity( of equality*)
 | Trans of trm * trm * trm * refutation
	(* Propositional Extensionality*)
 | NegEqualProp of trm * trm * trm * refutation * refutation
	(* Propositional Equality*)
 | EqualProp of trm * trm * trm * refutation * refutation
 | NegAequivalenz of trm * trm * trm * refutation * refutation
 | Aequivalenz of trm * trm * trm * refutation * refutation
	(* Functional Extensionality*)
 | NegEqualFunc of trm * trm * refutation
	(* Functional Equality*)
 | EqualFunc of trm * trm * refutation
 | ChoiceR of trm * trm * trm * trm * refutation * refutation 
 | Cut of trm * refutation * refutation     
 | DoubleNegation of trm * trm * refutation  
 | Rewrite of trm * trm * trm * refutation  
	(* Unfold definition*)
 | Delta of trm * trm * string * refutation
	(* Not_Yet_Implemented: used for debugging to indicate an error or uncaught cases*)
 | KnownResult of trm * string * stp list * refutation (* Chad: Aug 2011 *)
 | NYI of trm * trm * refutation 
	(* Used to close Branches after a timeout occurs*)
 | Timeout 

(** Debug function: turns a refutation into a string **)
let rec ref_str_level level r =
  (string_of_int level) ^ ": " ^
  match r with
 | Conflict(s,ns) -> (trm_str s) ^ " conflicts with\n" ^ (trm_str ns) ^ "\n"
 | Fal(_) ->"False is on the branch\n"
 | NegRefl(s) -> (trm_str s) ^ " is on the branch\n"
 | Implication(h,s,t,r1,r2) -> "use Implication rule on " ^ (trm_str h) ^"\nto get "^ (trm_str s) ^" or "^ (trm_str t)^"\n"
                               ^ ref_str_level (1+level) r1 ^ ref_str_level (1+level) r2
 | Disjunction(h,s,t,r1,r2) -> "use Or rule on " ^ (trm_str h) ^"\nto get "^ (trm_str s) ^" or "^ (trm_str t)^"\n"
                               ^ ref_str_level (1+level) r1 ^ ref_str_level (1+level) r2 
 | NegConjunction(h,s,t,r1,r2) -> "use NegAnd rule on " ^ (trm_str h) ^"\nto get "^ (trm_str s) ^" or "^ (trm_str t)^"\n"
                               ^ ref_str_level (1+level) r1 ^ ref_str_level (1+level) r2  
 | NegImplication(h,s,t,r1) ->"use NegImplication rule on " ^ (trm_str h) ^"\nto get "^ (trm_str s) ^" and "^ (trm_str t)^"\n"
                               ^ ref_str_level (1+level) r1
 | Conjunction(h,s,t,r1) ->"use And rule on " ^ (trm_str h) ^"\nto get "^ (trm_str s) ^" and "^ (trm_str t)^"\n"
                               ^ ref_str_level (1+level) r1 
 | NegDisjunction(h,s,t,r1) ->"use NegOr rule on " ^ (trm_str h) ^"\nto get "^ (trm_str s) ^" and "^ (trm_str t)^"\n"
                               ^ ref_str_level (1+level) r1   
 | All(h,s,r1,a,m,n) ->"use ForAll rule on " ^ (trm_str h) ^"\nwith inst " ^ (trm_str n) ^"\nto get "^ (trm_str s) ^"\n"
                               ^ ref_str_level (1+level) r1
 | NegAll(h,s,r1,a,m,x) ->"use NegForAll rule on " ^ (trm_str h) ^"\nwith eigenvar " ^ x ^"\nto get "^ (trm_str s) ^"\n"
                               ^ ref_str_level (1+level) r1
 | Exist(h,s,r1,a,m,x) ->"use Exist rule on " ^ (trm_str h) ^"\nto get "^ (trm_str s) ^"\n"
                               ^ ref_str_level (1+level) r1  
 | NegExist(h,s,r1,a,m,n) ->"use NegExist rule on " ^ (trm_str h) ^"\nto get "^ (trm_str s) ^"\n"
                               ^ ref_str_level (1+level) r1    
 | Mating(h1,h2, ss, rs) -> "use Mating rule on " ^ (trm_str h1) ^" and "^(trm_str h2)^"\nto get "^ (String.concat "," (List.map (fun a -> trm_str a) ss)) ^"\n"
                               ^ (String.concat "" (List.map (ref_str_level (1+level)) rs))
 | Decomposition(h1, ss, rs) -> "use Decomposition rule on " ^ (trm_str h1) ^"\nto get "^ (String.concat "," (List.map (fun a -> trm_str a) ss)) ^"\n"
                               ^ (String.concat "" (List.map (ref_str_level (1+level)) rs))
 
 | Confront(h1,h2,su,tu,sv,tv,r1,r2) ->"use Confrontation rule on " ^ (trm_str h1) ^" and "^(trm_str h2)^"\nto get "^ (trm_str su)^" and " ^ (trm_str tu) ^" or "^ (trm_str sv)^" and "^ (trm_str tv)^"\n"
                               ^ ref_str_level (1+level) r1 ^ ref_str_level (1+level) r2
 | Trans(h1,h2,s,r1) ->"use Transitivity rule on " ^ (trm_str h1) ^" and "^(trm_str h2)^"\nto get "^ (trm_str s) ^"\n"
                               ^ ref_str_level (1+level) r1
 | NegEqualProp(h,s,t,r1,r2) -> "use Boolean Extensionality rule on " ^ (trm_str h) ^"\nto get "^ (trm_str s)^" and " ^ (trm_str (neg t)) ^" or "^ (trm_str (neg s))^" and "^ (trm_str t)^"\n"
     ^ "BE1: " ^ ref_str_level (1+level) r1 ^ "BE2: " ^ ref_str_level (1+level) r2
 | EqualProp(h,s,t,r1,r2) -> "use Boolean Equality rule on " ^ (trm_str h) ^"\nto get "^ (trm_str s)^" and " ^ (trm_str t) ^" or "^ (trm_str (neg s))^" and "^ (trm_str (neg t))^"\n"
                               ^ ref_str_level (1+level) r1 ^ ref_str_level (1+level) r2
 | NegAequivalenz(h,s,t,r1,r2) -> "use NegAequivalenz rule on " ^ (trm_str h) ^"\nto get "^ (trm_str s)^" and " ^ (trm_str (neg t)) ^" or "^ (trm_str (neg s))^" and "^ (trm_str t)^"\n"
                               ^ ref_str_level (1+level) r1 ^ ref_str_level (1+level) r2
 | Aequivalenz(h,s,t,r1,r2) -> "use Aequivalenz rule on " ^ (trm_str h) ^"\nto get "^ (trm_str s)^" and " ^ (trm_str t) ^" or "^ (trm_str (neg s))^" and "^ (trm_str (neg t))^"\n"
                               ^ ref_str_level (1+level) r1 ^ ref_str_level (1+level) r2
 | NegEqualFunc(h,s,r1) ->"use functional Extensionality rule on " ^ (trm_str h) ^"\nto get "^ (trm_str s) ^"\n"
                               ^ ref_str_level (1+level) r1
 | EqualFunc(h,s,r1) ->"use functional Equality rule on " ^ (trm_str h) ^"\nto get "^ (trm_str s) ^"\n"
                               ^ ref_str_level (1+level) r1
 | ChoiceR(eps,pred,s,t,r1,r2) -> "use Choice rule \n to get "^ (trm_str s) ^" or "^ (trm_str t)^"\n"
                               ^ ref_str_level (1+level) r1 ^ ref_str_level (1+level) r2
 | Cut(s,r1,r2) -> "use analytic Cut \n to get "^ (trm_str s) ^" or "^ (trm_str (neg s)) ^"\n"
                               ^ ref_str_level (1+level) r1 ^ ref_str_level (1+level) r2
 | DoubleNegation(h,s,r1) ->"use DoubleNegation rule on " ^ (trm_str h) ^"\nto get "^ (trm_str s) ^"\n"
                               ^ ref_str_level (1+level) r1 
 | Rewrite(prefix,h,s,r1) ->"use Rewrite rule on " ^ (trm_str (onlybetanorm (Ap(prefix,h)))) ^"\nto get "^ (trm_str (onlybetanorm (Ap(prefix,s)))) ^"\n"
                               ^ ref_str_level (1+level) r1   
 | Delta(h,s,x,r1) -> "unfold "^x ^" in " ^ (trm_str h) ^ "\n" ^ (ref_str_level (1+level) r1)
 | KnownResult(_,name,al,r1) -> "known " ^ name ^ "[" ^ (String.concat " " (List.map stp_str al)) ^ "] " ^ "\n" ^ (ref_str_level (1+level) r1)
 | NYI(h,s,r1) ->"use NYI-normalization on " ^ (trm_str h) ^"\nto get "^ (trm_str s) ^"\n"
                               ^ ref_str_level (1+level) r1  
 | Timeout -> "timeout"
 | _ -> failwith "unknown refutation case in ref_str"

let ref_str r = ref_str_level 0 r

         
(** Prepreprocess : turn Leibniz equations into primitive equations**) 

(** Input: term m, DeBrujin index n 
	Checks wether the term m can be directly rewritten as a primitive equation.
	Output: (p,s,t,a) - where s =_a t and (lambda a. p) s == m  **)
let is_an_eqn_p m n =
  match m with
  | Ap (Forall (Ar (a, Prop)),
	Lam (Ar (_, Prop),
	     Ap (Ap (Imp, Ap (DB (0, Ar (_, Prop)), s)),
		 Ap (DB (0, Ar (_, Prop)), t))))
      when ((termNotFreeIn s 0) && (termNotFreeIn t 0))
    ->	let aao= Ar(a,Ar(a,Prop)) in
	let ao = Ar (a, Prop) in
	let prefix= Ap(Ap(DB(n,aao),shift s 0 (-1)),shift t 0 (-1)) in
	let pt = Lam(a,Lam(a, forall ao (imp (Ap(DB(0,ao),DB(2,a))) (Ap(DB(0,ao),DB(1,a))) ) ))	in	
	 (prefix,pt,Eq(a),aao)
  | Ap (Forall (Ar (a, Prop)),
	Lam (Ar (_, Prop),
	     Ap
	       (Ap (Imp,
		    Ap (Ap (Imp, Ap (DB (0, Ar (_, Prop)), s)),
			False)),
		Ap (Ap (Imp, Ap (DB (0, Ar (_, Prop)), t)),
		    False))))
    when ((termNotFreeIn s 0) && (termNotFreeIn t 0))
    ->  let aao= Ar(a,Ar(a,Prop)) in
	let ao = Ar (a, Prop) in
	let prefix= Ap(Ap(DB(n,aao),shift s 0 (-1)),shift t 0 (-1)) in
	let pt = Lam(a,Lam(a, forall ao (imp (neg (Ap(DB(0,ao),DB(2,a)))) (neg (Ap(DB(0,ao),DB(1,a)))) ) ))	in		
	 (prefix,pt,Eq(a),aao)
  | Ap (Forall (Ar (a, Ar (_, Prop))),
	Lam (Ar (_, Ar (_, Prop)),
	     Ap
	       (Ap (Imp,
		    Ap (Forall (_),
			Lam (_,
			     Ap (Ap (DB (1, Ar (_, Ar (_, Prop))), DB (0, _)),
				 DB (0, _))))),
		Ap (Ap (DB (0, Ar (_, Ar (_, Prop))), s),
		    t))))
    when ((termNotFreeIn s 0) && (termNotFreeIn t 0))
    -> 	let aao= Ar(a,Ar(a,Prop)) in
	let prefix= Ap(Ap(DB(n,aao),shift s 0 (-1)),shift t 0 (-1))  in
	let pt = Lam(a,Lam(a, forall aao (imp (forall a (Ap(Ap(DB(1,aao),DB(0,a)),DB(0,a)))) (Ap(Ap(DB(0,aao),DB(2,a)),DB(1,a))) )  ))	in	
	 (prefix,pt,Eq(a),aao)
  | Ap (Forall (Ar (a, Ar (_, Prop))),
	Lam (Ar (_, Ar (_, Prop)),
	     Ap
	       (Ap (Imp,
		    Ap
		      (Ap (Imp,
			   Ap
			     (Ap (DB (0, Ar (_, Ar (_, Prop))),
				  s),
			      t)),
		       False)),
		Ap
		  (Ap (Imp,
		       Ap (Forall (_),
			   Lam (_,
				Ap
				  (Ap (DB (1, Ar (_, Ar (_, Prop))), DB (0, _)),
				   DB (0, _))))),
		   False))))
    when ((termNotFreeIn s 0) && (termNotFreeIn t 0))
    -> 	let aao= Ar(a,Ar(a,Prop)) in
	let prefix= Ap(Ap(DB(n,aao),shift s 0 (-1)),shift t 0 (-1))  in
	let pt = Lam(a,Lam(a, forall aao (imp (neg (Ap(Ap(DB(0,aao),DB(2,a)),DB(1,a)))) (neg (forall a (Ap(Ap(DB(1,aao),DB(0,a)),DB(0,a))))) ) ))		
	in	(prefix,pt,Eq(a),aao)
  | _ -> raise Not_found (* It's not an equation. *)


