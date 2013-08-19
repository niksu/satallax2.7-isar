open String
open State
open Syntax
open Refutation
open Flag
open Norm

exception Mating_Mismatch of string

exception TranslateFailure

(** Translation [mostly Andreas Teucke's code] **)

(** Check wether to terms are equal or symmetric**)
let trm_eq' s t = 
  match (s,t) with 
  | ( Ap(Ap(Eq(a),s1),s2) , Ap(Ap(Eq(a'),t1),t2) ) when a=a' -> ( (s1=t1) && (s2=t2) ) || ( (s1=t2) && (s2=t1) ) 
  | ( Ap(Ap(Imp,Ap(Ap(Eq(a),s1),s2)),False), Ap(Ap(Imp,Ap(Ap(Eq(a'),t1),t2)),False) ) when a=a' -> ( (s1=t1) && (s2=t2) ) || ( (s1=t2) && (s2=t1) ) 
  | _ -> s=t
  
(** Check wether to terms would be considered equal or symmetric by Coq**)
let trm_eq s t = 
  trm_eq' (coqnorm s) (coqnorm t)

(** Input: association list branch, normalized term trm
	Invariant: every entry in branch is of the form ([m],m) with some term m 
	Output: prenormalized term associated to trm by branch **)  
let get_prenorm branch trm = try snd (List.find (fun (a,p) -> trm_eq' a trm) branch)  
                             with Not_found -> raise TranslateFailure (*** Sep 2011 - Chad : start over with safe_translate ***)
 (**  failwith("get_prenorm can't find term " ^ (trm_str trm))  **)

let rec termNotFreeIn m i =
let m = coqnorm m in
  match m with
    DB(j,_) when i = j -> false
  | Ap(m1,m2) -> (termNotFreeIn m1 i) && (termNotFreeIn m2 i)
  | Lam(a,m1) -> termNotFreeIn m1 (i + 1)
  | _ -> true  

  (** returns the type of a given trm m. m can be prenormalized.**)
let rec tpof m =
  match m with
    Name(_,a) -> a
  | False -> Prop
  | Imp -> Ar(Prop,Ar(Prop,Prop))
  | Forall(a) -> Ar(Ar(a,Prop),Prop)
  | Eq(a) -> Ar(a,Ar(a,Prop))
  | Choice(a) -> Ar(Ar(a,Prop),a)
  | True -> Prop
  | And -> Ar(Prop,Ar(Prop,Prop))
  | Or -> Ar(Prop,Ar(Prop,Prop))
  | Iff -> Ar(Prop,Ar(Prop,Prop))
  | Neg -> Ar(Prop,Prop)
  | Exists(a) -> Ar(Ar(a,Prop),Prop)
  | DB(_,a) -> a
  | Lam(a,n) -> Ar(a,tpof n)
  | Ap(f,n) ->
      begin
	match (tpof f) with
	  Ar(a,b) -> b
	| _ -> raise (GenericSyntaxError("Non-function applied: " ^ (trm_str m)))
      end
(*  | _ -> raise (GenericSyntaxError("Unexpected type case - were logical constants normalized away? " ^ (trm_str m))) *)

exception Delta_reduction of string * trm

exception NoMoreRewrites

(** Input: Term ptrm, Debrujin-Index n 
	Invariant: ptrm <> [ptrm]  
	Output: (prefix,pt,pt',b,a), where (lambda_a. prefix) pt = ptrm , (lambda_a. prefix) pt' = ptrm' 
			and pt=pt' is a lemma ; if b=false then an explicit rewrite is not necessary
	Throws Delta_reduction(name,definitiontrm) if the next normalization step is a delta-reduction
               NoMoreRewrites
        **)
let rec rewrite_refutation1 ptrm n =  
  if debug_translation then Printf.printf "rewrite_refutation1 called with\nptrm %s\n" (trm_str ptrm);
   match ptrm with
  | Name(x,a) -> (* delta *)
      begin
	try
	let def = onlynegnorm (Hashtbl.find name_def_prenorm x) in
	raise (Delta_reduction (x,def)) 
	with
	| Not_found -> failwith("translate can't find definition of "^ x)
      end
  | Lam(a,Ap(p,DB(0,_))) when (termNotFreeIn p 0) -> (* eta *)
	let b= tpof p in
    	let prefix = Ap(DB(n,Ar(b,b)),shift p 0 (- 1)) in
    	let ptrm = Lam(b,Lam(a,Ap(DB(1,b),DB(0,a)))) in
    	let ptrm' = Lam(b,DB(0,b)) in 
      (prefix,ptrm,ptrm',true,Ar(b,b))
  | Ap(Ap(Imp,Ap(Ap(Imp,m1),False)),False) -> (* double negation reduce *)
    let prefix = Ap(DB(n,Ar(Prop,Prop)),m1) in
    let ptrm = Lam(Ar(Prop,Prop),Ap(Ap(Imp,Ap(Ap(Imp,DB(0,Prop)),False)),False)) in
    let ptrm' = Lam(Ar(Prop,Prop),DB(0,Prop)) in 
      (prefix,ptrm,ptrm',true,Ar(Prop,Prop))
  | True -> (DB(n,Prop),True,imp False False,true,Prop) (* True => False -> False *)
  | Neg -> (DB(n,Ar(Prop,Prop)),Neg,Lam(Prop,imp (DB(0,Prop)) False),false,Ar(Prop,Prop)) (* ~s => s -> False , b is false as this is only a notation for Coq*) 
  | Or ->  (DB(n,Ar(Prop,Ar(Prop,Prop))),Or,Lam(Prop,Lam(Prop,disj (DB(1,Prop)) (DB(0,Prop)))),true,Ar(Prop,Ar(Prop,Prop))) (* s \/ t => ~s -> t*)
  | And -> if  debug_rewrite then Printf.printf  "Rewrite And \n"; 
	(DB(n,Ar(Prop,Ar(Prop,Prop))),And,Lam(Prop,Lam(Prop,conj (DB(1,Prop)) (DB(0,Prop)))),true,Ar(Prop,Ar(Prop,Prop))) (* s /\ t => ~(s -> ~t)*)   
  | Iff -> (DB(n,Ar(Prop,Ar(Prop,Prop))),Iff,Lam(Prop,Lam(Prop,iff (DB(1,Prop)) (DB(0,Prop)))),true,Ar(Prop,Ar(Prop,Prop))) (* s <-> t => s = t*)
  | Exists(a) ->
	let ao = Ar(a,Prop) in
	let aoo = Ar(Ar(a,Prop),Prop) in
    (DB(n,aoo),Exists(a),Lam(ao,exists a (Ap(DB(1,ao),DB(0,a)))),true,aoo) (* exist s => ~ forall ~ s *)
  | Ap(m1,m2) -> if  debug_rewrite then Printf.printf  "Rewrite looks at %s \n" (trm_str ptrm);
      if normalize m1 <> m1 (* if m1 is normal, normalize m2*)
      then let (pre,pt,pt',bb,stp)= rewrite_refutation1 m1 n in 
        (Ap(pre,m2),pt,pt',bb,stp) 
      else let (pre,pt,pt',bb,stp)= rewrite_refutation1 m2 n in 
        (Ap(m1,pre),pt,pt',bb,stp)
  | Lam(a,m) ->if  debug_rewrite then Printf.printf  "Rewrite looks at %s \n" (trm_str ptrm);
    let (pre,pt,pt',bb,stp)= rewrite_refutation1 m (n+1) in 
    (Lam(a,pre),pt,pt',bb,stp) 
  | _ -> raise NoMoreRewrites

(** eager rewrite - Satallax refutation **)

let rec satallax_rewrite b nb r trm ptrm =  
  try 
    let (pre,pt,pt',bb,stp)= rewrite_refutation1 ptrm 0 in
    let prefix= Lam(stp,pre) in
    let ptrm' = onlybetanorm (Ap(prefix,pt')) in
    if bb then begin
      if debug_translation then Printf.printf  "Rewrite %s into %s \n" (trm_str ptrm) (trm_str ptrm');
      Rewrite(prefix,pt,pt',eager_translate1 ((trm,ptrm')::(List.tl b)) nb r)
    end
    else
      eager_translate1 ((trm,ptrm')::(List.tl b)) nb r 
  with Delta_reduction(x,def) ->
    let ptrm'= onlybetanorm (namesubst ptrm x def) in
    Delta(ptrm,ptrm',x,eager_translate1 ((trm,ptrm')::(List.tl b)) nb r)
  | NoMoreRewrites ->
      if debug_translation then Printf.printf "eager_translate failed! Will use safe_translate\ntrm %s\nptrm %s\n" (trm_str trm) (trm_str ptrm);
      raise TranslateFailure (*** Aug 2011 - Chad : start over with safe_translate ***)
  | Failure(_) ->
      if debug_translation then Printf.printf "eager_translate failed! Will use safe_translate\ntrm %s\nptrm %s\n" (trm_str trm) (trm_str ptrm);
      raise TranslateFailure (*** Aug 2011 - Chad : start over with safe_translate ***)

(***
 b  : alist of terms and prenormalized terms
 nb : alist of terms that are considered equal by Coq (or almost the same -- see trm_eq)
 r  : refutation of map car b append map car nb
 Output refutation of map cdr b append map cdr nb
 ***)
and eager_translate1 b nb r =
  match b with
    [] -> sat_translation (List.rev nb) r
  | ((trm,ptrm)::br)-> 
      if trm_eq trm ptrm 
      then eager_translate1 br ((trm,ptrm)::nb) r
      else satallax_rewrite b nb r trm ptrm

and sat_translation b r = 
 match r with
 | Conflict(s,ns) ->
     begin
       let p = get_prenorm b s in
       let np = get_prenorm b ns in
       if debug_translation then Printf.printf  "Conflict %s\n" (trm_str p);
       if trm_eq np (neg p) then Conflict(p,np)
       else if trm_eq p (neg np) then Conflict(np,p)
       else raise TranslateFailure (*** Sep 2011 - Chad : start over with safe_translate ***) (** failwith("Error with Conflict between " ^ (trm_str p) ^" and " ^(trm_str np)) **)
     end  
 | Fal(s) -> begin
   let p = get_prenorm b s in
     if p = False then Fal(p) else raise TranslateFailure (*** Sep 2011 - Chad : start over with safe_translate ***) (** failwith("Error with Fal " ^ (trm_str p)) **)
 end 
 | NegRefl(s) -> begin
   let p = get_prenorm b s in
   match p with
     | Ap(Ap(Imp,Ap(Ap(Eq(_),m1),m2)),False) when m1 = m2 -> NegRefl(p)
     | _ -> raise TranslateFailure (*** Sep 2011 - Chad : start over with safe_translate ***) (** failwith("Error with NegRefl " ^ (trm_str p)) **)
     end  
 | Implication(h,s,t,r1,r2) -> begin
   let p = get_prenorm b h in
   if debug_translation then Printf.printf  "Implication %s = %s\n" (trm_str h) (trm_str p);
   match p with  
    | (Ap(Ap(Imp,m1),m2)) -> 
          Implication(p,neg m1,m2,eager_translate1 ((s,neg m1)::[]) b r1,eager_translate1 ((t,m2)::[]) b r2)
    | _ -> raise TranslateFailure (*** Sep 2011 - Chad : start over with safe_translate ***) (** failwith("Error with Implication " ^ (trm_str p)) **)
    end   
 | NegImplication(h,s,t,r1)   -> begin 
   let p = get_prenorm b h in 
   if debug_translation then Printf.printf  "NegImplication %s\n" (trm_str p);
   match p with 
   | (Ap(Ap(Imp,(Ap(Ap(Imp,m1),m2))),False)) -> begin
      NegImplication(p,m1,neg m2,eager_translate1 ((s,m1)::(t,neg m2)::[]) b r1)
    end    	
   | _ -> raise TranslateFailure (*** Sep 2011 - Chad : start over with safe_translate ***) (** failwith("Error with NegImplication " ^ (trm_str p)) **)
    end
 | All(h,s,r1,a,m,n) -> begin
   let p = get_prenorm b h in
   if debug_translation then Printf.printf  "All %s\n" (trm_str p);
   match p with  
    | (Ap(Forall(a'),m1)) -> 
      let m' = onlybetanorm (Ap(m1,n)) in
	All(p,m',eager_translate1 ((s,m')::[]) b r1,a,m,n)   
    | _ -> raise TranslateFailure (*** Sep 2011 - Chad : start over with safe_translate ***) (** failwith("Error with All " ^ (trm_str p)) **)
    end  
 | NegAll(h,s,r1,a,m,x) ->
      begin
   let p = get_prenorm b h in
   if debug_translation then Printf.printf  "NegAll %s\n" (trm_str p);
   match p with  
    | (Ap(Ap(Imp,Ap(Forall(a'),m1)),False)) -> 
	let m' = neg (onlybetanorm (Ap(m1,Name(x,a)))) in
	NegAll(p,m',eager_translate1 ((s,m')::[]) b r1,a,m,x)    
    | _ -> raise TranslateFailure (*** Sep 2011 - Chad : start over with safe_translate ***) (** failwith("Error with NegAll " ^ (trm_str p)) **)
    end  
 | Mating(h1,h2, ss, rs) -> begin 
   	let p = get_prenorm b h1 in
   	let np = get_prenorm b h2 in
	let h = List.combine ss rs in
   	if debug_translation then Printf.printf  "Mating %s\n" (trm_str p);
   	try
    	let pss = match (p,np) with  
     		| (Ap(f1,m1), Ap(Ap(Imp,Ap(f2,m2)),False)) ->  
		let (g1,args1)= head_spine (Ap(f1,m1)) in 
		let (g2,args2)= head_spine (Ap(f2,m2)) in
        	if not (trm_eq g1  g2) then  raise (Mating_Mismatch("unequal heads")) else
 		List.fold_left2 (fun a b c ->if tpof b = tpof c then (neg (eq (tpof b) b c))::a 
						else raise (Mating_Mismatch("type missmatch in spine")) ) [] args1 args2
     		| (Ap(Ap(Imp,Ap(f1,m1)),False), Ap(f2,m2)) -> 
		let (g1,args1)= head_spine (Ap(f2,m2)) in 
		let (g2,args2)= head_spine (Ap(f1,m1)) in
		if g1 <> g2 then  raise (Mating_Mismatch("unequal heads")) else
 		List.fold_left2 (fun a b c ->if tpof b = tpof c then (neg (eq (tpof b) b c))::a 
						else raise (Mating_Mismatch("type missmatch in spine")) ) [] args1 args2
     		| _ -> raise (Mating_Mismatch("terms can't be mated"))
    	in
	let pss = List.rev pss in  
	begin
	List.iter2 (fun ps s -> if not (trm_eq s (normalize ps)) 
				then raise (Mating_Mismatch("unexpected result :" ^ (trm_str ps)^" <> "^ (trm_str s))) ) pss ss; 
    	Mating(p,np, pss, List.map2 (fun ps (s,r) -> eager_translate1 ((s,ps)::[]) b r) pss h)
	end
   	with Mating_Mismatch(mess) -> raise TranslateFailure (*** Sep 2011 - Chad : start over with safe_translate ***) (** failwith("Error with Mating between " ^ (trm_str p) ^" and " ^(trm_str np)^":"^ mess) **)
	end  
| Decomposition(h1,ss, rs) -> begin 
   let p = get_prenorm b h1 in
   let h = List.combine ss rs in
   if debug_translation then Printf.printf  "Decomposition %s\n" (trm_str p);
   try
    let pss = match p with  
     | (Ap(Ap(Imp,Ap(Ap(Eq(Base(_)),m1),m2)),False))-> 
	let (g1,args1)= head_spine m1 in 
	let (g2,args2)= head_spine m2 in
        if g1 <> g2 then  raise (Mating_Mismatch("unequal heads")) else
 	List.fold_left2 (fun a b c ->if tpof b = tpof c 
					then (neg (eq (tpof b) b c))::a else raise (Mating_Mismatch("type missmatch in spine")) ) [] args1 args2
     | _ -> raise (Mating_Mismatch("term can't be decomposed"))
    in    
	let pss = List.rev pss in 
	List.iter2 (fun ps s -> if not (trm_eq s (normalize ps)) 
				then raise (Mating_Mismatch("unexpected result :" ^ (trm_str ps)^" <> "^ (trm_str s))) ) pss ss;  
	Decomposition(p ,pss, List.map2 (fun ps (s,r) -> eager_translate1 ((s,ps)::[]) b r) pss h)
   	with Mating_Mismatch(mess) -> raise TranslateFailure (*** Sep 2011 - Chad : start over with safe_translate ***) (** failwith("Error with Decomposition " ^ (trm_str p)^":"^ mess) **)
 	end  
| Confront(h1,h2,su,tu,sv,tv,r1,r2) ->begin 
   let p = get_prenorm b h1 in
   let np = get_prenorm b h2 in
   if debug_translation then Printf.printf  "Confronting %s\n" (trm_str p);
   let (bb,r) = begin match (p,np) with
			| (  Ap(Ap(Eq(a),s),t)   ,  Ap(Ap(Imp, Ap(Ap(Eq(a'),u),v) ),False)  ) when a=a' -> begin
				let (psu,ptu,psv,ptv)=(neg (eq a s u),neg (eq a t u),neg (eq a s v),neg (eq a t v)) in
     if trm_eq psu su then 
	(true,Confront(p,np,psu,ptu,psv,ptv, eager_translate1 ((su,psu)::(tu,ptu)::[]) b r1, eager_translate1 ((sv,psv)::(tv,ptv)::[]) b r2 ) )
else if trm_eq psu tu then
	(true,Confront(p,np,psu,ptu,psv,ptv, eager_translate1 ((tu,psu)::(su,ptu)::[]) b r1, eager_translate1 ((tv,psv)::(sv,ptv)::[]) b r2 ) )
else if trm_eq psu sv then
	(true,Confront(p,np,psu,ptu,psv,ptv, eager_translate1 ((sv,psu)::(tv,ptu)::[]) b r2, eager_translate1 ((su,psv)::(tu,ptv)::[]) b r1 ) )
else if trm_eq psu tv then
	(true,Confront(p,np,psu,ptu,psv,ptv, eager_translate1 ((tv,psu)::(sv,ptu)::[]) b r2, eager_translate1 ((tu,psv)::(su,ptv)::[]) b r1 ) ) 
else  (false,Fal(False)) end
			| (  Ap(Ap(Imp, Ap(Ap(Eq(a'),u),v) ),False)  ,  Ap(Ap(Eq(a),s),t) )  when a=a' -> begin
				let (psu,ptu,psv,ptv)=(neg (eq a s u),neg (eq a t u),neg (eq a s v),neg (eq a t v)) in
     if trm_eq psu su then 
	(true,Confront(p,np,psu,ptu,psv,ptv, eager_translate1 ((su,psu)::(tu,ptu)::[]) b r1, eager_translate1 ((sv,psv)::(tv,ptv)::[]) b r2 ) )
else if trm_eq psu tu then
	(true,Confront(p,np,psu,ptu,psv,ptv, eager_translate1 ((tu,psu)::(su,ptu)::[]) b r1, eager_translate1 ((tv,psv)::(sv,ptv)::[]) b r2 ) )
else if trm_eq psu sv then
	(true,Confront(p,np,psu,ptu,psv,ptv, eager_translate1 ((sv,psu)::(tv,ptu)::[]) b r2, eager_translate1 ((su,psv)::(tu,ptv)::[]) b r1 ) )
else if trm_eq psu tv then
	(true,Confront(p,np,psu,ptu,psv,ptv, eager_translate1 ((tv,psu)::(sv,ptu)::[]) b r2, eager_translate1 ((tu,psv)::(su,ptv)::[]) b r1 ) ) 
else  (false,Fal(False)) end
			| _ -> (false,Fal(False)) end 
  in
   if bb then  
    r
   else raise TranslateFailure (*** Sep 2011 - Chad : start over with safe_translate ***) (** failwith("Error with Confront between " ^ (trm_str p) ^" and " ^(trm_str np)) **)
 end 
| Trans(h1,h2,su,r1) -> begin
	let st = get_prenorm b h1 in
   	let tu = get_prenorm b h2 in
	if debug_translation then Printf.printf  "Transitivity %s\n" (trm_str st);
	match (st,tu) with
	| (  Ap(Ap(Eq(a),s),t) , Ap(Ap(Eq(a'),u),v) ) when a=a' -> begin
		 if  trm_eq s u then
            	Trans(st,tu,Ap(Ap(Eq(a),t),v), eager_translate1 ((su,Ap(Ap(Eq(a),t),v))::[]) b r1)
 	    	else if  trm_eq t u then
            	Trans(st,tu,Ap(Ap(Eq(a),s),v), eager_translate1 ((su,Ap(Ap(Eq(a),s),v))::[]) b r1)
 	    	else if  trm_eq s v then
            	Trans(st,tu,Ap(Ap(Eq(a),t),u), eager_translate1 ((su,Ap(Ap(Eq(a),t),u))::[]) b r1)
 	    	else if  trm_eq t v then
            	Trans(st,tu,Ap(Ap(Eq(a),s),u), eager_translate1 ((su,Ap(Ap(Eq(a),s),u))::[]) b r1)
 	    	else raise TranslateFailure (*** Sep 2011 - Chad : start over with safe_translate ***) (** failwith("Error with Transitivity " ^ (trm_str st)) **)
		end
	| _ -> raise TranslateFailure (*** Sep 2011 - Chad : start over with safe_translate ***) (** failwith("Error with Transitivity " ^ (trm_str st)) **)
	end
| NegEqualProp(h,s,t,r1,r2) -> begin
   let p = get_prenorm b h in
   if debug_translation then Printf.printf  "boolean extensionality %s\n" (trm_str p);
   match p with  
     | (Ap(Ap(Imp,Ap(Ap(Eq(Prop),m1),m2)),False)) -> begin
            if  trm_eq (normalize m2)  t && trm_eq (normalize m1)  s then
            NegEqualProp(p,m1,m2, eager_translate1 ((s,m1)::(normneg t,neg m2)::[]) b r1,eager_translate1((normneg s,neg m1)::(t,m2)::[]) b r2)
 	    else 
	    if   trm_eq (normalize m1)  t && trm_eq (normalize m2)  s then
            NegEqualProp(p,m1,m2, eager_translate1 ((t,m1)::(normneg s,neg m2)::[]) b r2,eager_translate1((normneg t,neg m1)::(s,m2)::[]) b r1)
 	    else raise TranslateFailure (*** Sep 2011 - Chad : start over with safe_translate ***) (** failwith("Error with NegEqualProp " ^ (trm_str p)) **)
          end     	  
    | _ -> raise TranslateFailure (*** Sep 2011 - Chad : start over with safe_translate ***) (** failwith("Error with NegEqualProp " ^ (trm_str p)) **)
    end  
 | EqualProp(h,s,t,r1,r2) -> begin
   let p = get_prenorm b h in
   if debug_translation then Printf.printf  "boolean Equality %s\n" (trm_str p);
   match p with  
     | Ap(Ap(Eq(Prop),m1),m2) -> begin
            if  trm_eq (normalize m2)  t && trm_eq (normalize m1)  s then
            EqualProp(p,m1,m2, eager_translate1 ((s,m1)::(t,m2)::[]) b r1,eager_translate1 ((normneg s,neg m1)::(normneg t,neg m2)::[]) b r2)
 	    else
	    if  trm_eq (normalize m1)  t && trm_eq (normalize m2)  s then
            EqualProp(p,m1,m2, eager_translate1 ((s,m2)::(t,m1)::[]) b r1,eager_translate1 ((normneg s,neg m2)::(normneg t,neg m1)::[]) b r2)
 	    else raise TranslateFailure (*** Sep 2011 - Chad : start over with safe_translate ***) (** failwith("Error with EqualProp " ^ (trm_str p)) **)
          end     	  
    | _ -> raise TranslateFailure (*** Sep 2011 - Chad : start over with safe_translate ***) (** failwith("Error with EqualProp " ^ (trm_str p)) **)
    end  
 | NegEqualFunc(h,s,r) -> begin 
   let p = get_prenorm b h in
   if debug_translation then Printf.printf  "functional extensionality %s\n" (trm_str p);
   if not (trm_eq p h) then raise TranslateFailure (*** Sep 2011 - Chad : start over with safe_translate ***) (** failwith("Error with NegEqualFunc" ^ (trm_str p)) **) else
   match p with  
     | (Ap(Ap(Imp,Ap(Ap(Eq(Ar(a,a')),m1),m2)),False)) -> 
	begin
	let left = (Ap(shift m1 0 1,DB(0,a))) in
	let right =  (Ap(shift m2 0 1,DB(0,a))) in
	let aao= Ar(a',Ar(a',Prop)) in
	let prefix= Lam(aao, neg ( forall a (Ap(Ap(DB(1,aao),left),right)) )) in
	let ps =  onlybetanorm (Ap(prefix,Eq(a'))) in
	if (coqnorm ps = s) then NegEqualFunc(p,ps, eager_translate1 ((s,ps)::[]) b r)
	else 
	begin
	let ps' = onlybetanorm (Ap(prefix,Lam(a',Lam(a',Ap(Ap(Eq(a'),DB(0,a')),DB(1,a'))))  )) in 
	if (coqnorm ps' = s) 
	then NegEqualFunc(p,ps, Rewrite(prefix,Eq(a'), Lam(a',Lam(a',Ap(Ap(Eq(a'),DB(0,a')),DB(1,a')))) ,eager_translate1 ((s,ps')::[]) b r) )
	else raise TranslateFailure (*** Sep 2011 - Chad : start over with safe_translate ***) (** failwith("Error with NegEqualFunc: Unexpected result " ^ (trm_str ps)) **)
	end        
	end     	 
    | _ -> raise TranslateFailure (*** Sep 2011 - Chad : start over with safe_translate ***) (** failwith("Error with NegEqualFunc " ^ (trm_str p)) **)
    end   
 | EqualFunc(h,s,r) -> begin 
   let p = get_prenorm b h in
   if debug_translation then Printf.printf  "functional Equality %s\n" (trm_str h);
   if not (trm_eq p h) then raise TranslateFailure (*** Sep 2011 - Chad : start over with safe_translate ***) (** failwith("Error with EqualFunc" ^ (trm_str p)) **) else
   match p with  
     | Ap(Ap(Eq(Ar(a,a')),m1),m2) -> begin
	 let left = (Ap(shift m1 0 1,DB(0,a))) in
	let right =  (Ap(shift m2 0 1,DB(0,a))) in
	let aao= Ar(a',Ar(a',Prop)) in
	let prefix= Lam(aao,( forall a (Ap(Ap(DB(1,aao),left),right)) )) in
	let ps =  onlybetanorm (Ap(prefix,Eq(a'))) in
		if (coqnorm ps = s) then EqualFunc(p,ps, eager_translate1 ((s,ps)::[]) b r)
		else let ps' = onlybetanorm (Ap(prefix,Lam(a',Lam(a',Ap(Ap(Eq(a'),DB(0,a')),DB(1,a'))))  )) in 
		if (coqnorm ps' = s) 
		then EqualFunc(p,ps,Rewrite(prefix,Eq(a'), Lam(a',Lam(a',Ap(Ap(Eq(a'),DB(0,a')),DB(1,a'))))  ,eager_translate1 ((s,ps')::[]) b r) )
		else raise TranslateFailure (*** Sep 2011 - Chad : start over with safe_translate ***) (** failwith("Error with EqualFunc: Unexpected result " ^ (trm_str ps) ^ "  s: " ^ (trm_str s)) **)
          end         	 
    | _ -> raise TranslateFailure (*** Sep 2011 - Chad : start over with safe_translate ***) (** failwith("Error with EqualFunc : cant apply on " ^ (trm_str p)) **)
    end 
 | ChoiceR(eps,pred,s,t,r1,r2) -> 
	let a = match tpof pred  with Ar(a,Prop) -> a | _ -> raise TranslateFailure (*** Sep 2011 - Chad : start over with safe_translate ***) (** failwith  "Error pred is not of type a --> o" **) in	
	let ps = onlybetanorm (forall a (neg (ap (shift pred 0 1,DB(0,a)) ) ) ) in
	let pt = onlybetanorm ( ap (pred,ap (eps,pred)) ) in
   	if debug_translation then Printf.printf  "Choice %s\n" (trm_str pred); 
	ChoiceR(eps,pred,ps,pt,eager_translate1 [(s, ps)] b r1,eager_translate1 [(t,pt)] b r2)   
 | Cut(s,r1,r2) -> 
	if debug_translation then Printf.printf  "Cut %s\n" (trm_str s); 
	Cut(s,sat_translation ((s,s)::b) r1,eager_translate1 [(normneg s,neg s)] b r2)   
 | Timeout -> Timeout
 | Rewrite(pre,pt,pt',r1) -> 
			let trm = onlybetanorm (Ap(pre,pt)) in
			if debug_translation then Printf.printf  "Rewrite %s\n" (trm_str trm); 
			let ptrm' =  onlybetanorm (Ap(pre,pt')) in
			let ptrm =  norm name_def (Ap(pre,pt')) in
			 Rewrite(pre,pt,pt',eager_translate1 [(ptrm,ptrm')] b r1 ) 
 | KnownResult(s,name,al,r1) -> KnownResult(s,name,al,eager_translate1 [(s,s)] b r1)
 | _ -> raise TranslateFailure (*** Sep 2011 - Chad : start over with safe_translate ***) (** failwith "unexpected refutation case in Sat_translation" **)
   
let eager_translate b r = eager_translate1 b [] r

(** rewrite last - prenorm refutation **)

(** Input: Branch b, Refutation r, Term trm, Term ptrm, Boolean delta (true-> explicit Unfold, false -> implicit by Coq)
	Invariant: [ptrm]= trm, trm <> ptrm,   
	Output: Refutation r completed with explicit rewrites 
	*)
let rec rewrite_refutation b r trm ptrm delta =  
  if debug_translation then Printf.printf "rewrite_refutation called with\ntrm %s\nptrm %s\n" (trm_str trm) (trm_str ptrm);
    try
	(* find possible rewrite step*)
      let (pre,pt,pt',bb,stp)= rewrite_refutation1 ptrm 0 in
      let prefix= Lam(stp,pre) in
      let ptrm' = onlybetanorm (Ap(prefix,pt')) in
      if bb (* add Rewrite-step only if necessary*) 
      then
	Rewrite(prefix,pt,pt',lazy_translate ((trm,ptrm')::b) r)
      else
	lazy_translate ((trm,ptrm')::b) r 
    with
    | Delta_reduction(x,def) ->
	let ptrm'= onlybetanorm (namesubst ptrm x def) in
	if delta (* add Unfold-step only if necessary*)
	then Delta(ptrm,ptrm',x,lazy_translate ((trm,ptrm')::b) r)
	else lazy_translate ((trm,ptrm')::b) r
    | NoMoreRewrites ->
	if debug_translation then Printf.printf "lazy_translate failed! Will use safe_translate\ntrm %s\nptrm %s\n" (trm_str trm) (trm_str ptrm);
	raise TranslateFailure (*** Aug 2011 - Chad : start over with safe_translate ***)
    | Failure(_) ->
	if debug_translation then Printf.printf "lazy_translate failed! Will use safe_translate\ntrm %s\nptrm %s\n" (trm_str trm) (trm_str ptrm);
	raise TranslateFailure (*** Aug 2011 - Chad : start over with safe_translate ***)
 
 (* Input: Association List (normalized term -> prenormalized term) b as current Branch and incomplete refutation r
	Output: completed refutation which avoids rewrites and tries to use alternative refutation steps instead 
	General scheme: 
		1. Check if rule or an alternative is applicable
		2. Check wether the application has a result equivalent to the expected result
		3. Update Branch and call recursive on subrefutation
		4. Otherwise call normalization on a principal formula *)
and lazy_translate b r = 
 match r with
 | Conflict(s,ns) ->  begin
   let p = get_prenorm b s in
   let np = get_prenorm b ns in
   if debug_translation then Printf.printf  "Conflict %s\n" (trm_str p);
   if trm_eq np (neg p) then Conflict(p,np)
   else if trm_eq p  (neg np) then Conflict(np,p)
   else if normalize np <> np  then normalize_refutation b (Conflict(ns,s)) ns np false (* both prenorm terms are alternately normalized*)
   else  normalize_refutation b (Conflict(ns,s)) s p false 
 end  
 | Fal(s) -> begin
   let p = get_prenorm b s in
     if p = False then Fal(p) else normalize_refutation b r s p false
 end 
 | NegRefl(s) -> begin
   let p = get_prenorm b s in
   match p with
     | Ap(Ap(Imp,Ap(Ap(Eq(_),m1),m2)),False) when trm_eq m1 m2 -> NegRefl(p)
     | _ -> normalize_refutation b r s p false
     end  
 | Implication(h,s,t,r1,r2) -> begin
   let p = get_prenorm b h in
   if debug_translation then Printf.printf  "Implication %s = %s\n" (trm_str h) (trm_str p);
   match p with  
    | (Ap(Ap(Imp,(Ap(Ap(And,m1),m2))),False)) -> (* Not and *)
		begin
      if  trm_eq' (normalize (neg m2)) t && trm_eq' (normalize (neg m1)) s then
          NegConjunction(p,neg m1,neg m2,lazy_translate ((s,neg m1)::b) r1,lazy_translate ((t,neg m2)::b) r2)
      else normalize_refutation b r h p false
          end     
     | (Ap(Ap(Or,m1),m2)) -> (* or *)
		begin
      if  trm_eq' (normalize m2) t && trm_eq' (normalize m1) s then 
        Disjunction(p,m1,m2,lazy_translate ((s,m1)::b) r1,lazy_translate ((t,m2)::b) r2)
      else normalize_refutation b r h p false
          end    
    | (Ap(Ap(Imp,m1),m2)) -> (* Implication *)
	begin
      if  trm_eq' (normalize m2) t && trm_eq' (normalize (neg m1)) s then
          Implication(p,neg m1,m2,lazy_translate ((s,neg m1)::b) r1,lazy_translate ((t,m2)::b) r2)
      else normalize_refutation b r h p false
    end    
    | _ ->  normalize_refutation b r h p false
    end  
 | NegImplication(h,s,t,r1)   -> begin 
   let p = get_prenorm b h in 
   if debug_translation then Printf.printf  "NegImplication %s\n" (trm_str p);
   match p with  
   | (Ap(Ap(Imp,(Ap(Ap(Imp,m1),m2))),False)) -> (* not implication*)
	if  trm_eq' (normalize (neg m2)) t && trm_eq' (normalize m1) s then
	  NegImplication(p,m1,neg m2,lazy_translate ((s,m1)::(t,neg m2)::b) r1)
	else normalize_refutation b r h p false
   | (Ap(Ap(And,m1),m2)) -> (* and *)
	if  trm_eq' (normalize m2) t && trm_eq' (normalize m1) s then  
      Conjunction(p,m1,m2,lazy_translate ((s,m1)::(t,m2)::b) r1) 
	 else normalize_refutation b r h p false
   | (Ap(Ap(Imp,(Ap(Ap(Or,m1),m2))),False)) -> (* not or *)
	if  trm_eq' (normalize (neg m2)) t && trm_eq' (normalize (neg m1)) s then
      NegDisjunction(p,neg m1,neg m2,lazy_translate ((s,neg m1)::(t,neg m2)::b) r1)
	 else normalize_refutation b r h p false
   | _ ->  normalize_refutation b r h p false
    end
| All(h,s,r1,a,m,n) -> begin
   let p = get_prenorm b h in
   if debug_translation then Printf.printf  "All %s\n" (trm_str p);
   match p with  
    | (Ap(Forall(a'),m1)) -> (* forall *)
		begin
      let m' = onlybetanorm (Ap(m1,n)) in
      if  trm_eq' (normalize m') s  then
          All(p,m',lazy_translate ((s,m')::b) r1,a,m,n)
      else
	begin
	  if debug_translation then Printf.printf  "calling normalize_refutation because of difference between\nnorm(m1 n) = %s\ns = %s\n" (trm_str (onlybetanorm(Ap(m1,n)))) (trm_str s);
	  normalize_refutation b r h p false
	end
    end  
    | (Ap(Ap(Imp,Ap(Exists(a'),m1)),False)) -> (* not exists *)
		begin
      let m' = neg (onlybetanorm (Ap(m1,n))) in
      if  trm_eq' (normalize m') s  then  
        NegExist(p,m',lazy_translate ((s,m')::b) r1,a,m,n)
      else normalize_refutation b r h p false
          end        
    | _ ->  normalize_refutation b r h p false
    end  
| NegAll(h,s,r1,a,m,x) ->
      begin
   let p = get_prenorm b h in
   if debug_translation then Printf.printf  "NegAll %s\n" (trm_str p);
   match p with  
    | (Ap(Exists(a'),m1)) -> (* exists *)
		begin
      let m' = onlybetanorm (Ap(m1,Name(x,a))) in
      if  trm_eq' (normalize m') s  then

          Exist(p,m',lazy_translate ((s,m')::b) r1,a,m,x)
      else normalize_refutation b r h p false
    end  
    | (Ap(Ap(Imp,Ap(Forall(a'),m1)),False)) -> (* not forall *)
		begin
      let m' = neg (onlybetanorm (Ap(m1,Name(x,a)))) in
      if  trm_eq' (normalize m') s then  
        NegAll(p,m',lazy_translate ((s,m')::b) r1,a,m,x)
      else normalize_refutation b r h p false
          end        
    | _ ->  normalize_refutation b r h p false
    end  
| Mating(h1,h2, ss, rs) -> begin 
   	let p = get_prenorm b h1 in
   	let np = get_prenorm b h2 in
	let h = List.combine ss rs in
   	if debug_translation then Printf.printf  "Mating %s\n" (trm_str p);
   	try
    	let pss = match (p,np) with  
     		| (Ap(f1,m1), Ap(Ap(Imp,Ap(f2,m2)),False)) ->  
		let (g1,args1)= head_spine (Ap(f1,m1)) in 
		let (g2,args2)= head_spine (Ap(f2,m2)) in
        	if g1 <> g2 then  raise (Mating_Mismatch("unequal heads")) else
 		List.fold_left2 (fun a b c ->if tpof b = tpof c then (neg (eq (tpof b) b c))::a 
						else raise (Mating_Mismatch("type missmatch in spine")) ) [] args1 args2
     		| (Ap(Ap(Imp,Ap(f1,m1)),False), Ap(f2,m2)) -> 
		let (g1,args1)= head_spine (Ap(f2,m2)) in 
		let (g2,args2)= head_spine (Ap(f1,m1)) in
		if g1 <> g2 then  raise (Mating_Mismatch("unequal heads")) else
 		List.fold_left2 (fun a b c ->if tpof b = tpof c then (neg (eq (tpof b) b c))::a 
						else raise (Mating_Mismatch("type missmatch in spine")) ) [] args1 args2
     		| _ -> raise (Mating_Mismatch("terms can't be mated"))
    	in
	let pss = List.rev pss in  
	begin
	List.iter2 (fun ps s -> if not (trm_eq' s (normalize ps)) 
				then raise (Mating_Mismatch("unexpected result :" ^ (trm_str ps)^" <> "^ (trm_str s))) ) pss ss; 
    	Mating(p,np, pss, List.map2 (fun ps (s,r) -> lazy_translate ((s,ps)::b)  r) pss h)
	end
   	with Mating_Mismatch(mess) -> 
	if normalize p <> p 
	then normalize_refutation b (Mating(h2,h1, ss, rs)) h1 p  true (* both prenorm terms are alternatly normalized*)
    else normalize_refutation b (Mating(h2,h1, ss, rs)) h2 np true (* true forces explicit unfolds *)  
	end  
| Decomposition(h1,ss, rs) -> begin 
   let p = get_prenorm b h1 in
   let h = List.combine ss rs in
   if debug_translation then Printf.printf  "Decomposition %s\n" (trm_str p);
   try
    let pss = match p with  
     | (Ap(Ap(Imp,Ap(Ap(Eq(Base(_)),m1),m2)),False))-> 
	let (g1,args1)= head_spine m1 in 
	let (g2,args2)= head_spine m2 in
        if g1 <> g2 then  raise (Mating_Mismatch("unequal heads")) else
 	List.fold_left2 (fun a b c ->if tpof b = tpof c 
					then (neg (eq (tpof b) b c))::a else raise (Mating_Mismatch("type missmatch in spine")) ) [] args1 args2
     | _ -> raise (Mating_Mismatch("term can't be decomposed"))
    in    
	let pss = List.rev pss in 
	List.iter2 (fun ps s -> if not (trm_eq' s (normalize ps)) 
				then raise (Mating_Mismatch("unexpected result :" ^ (trm_str ps)^" <> "^ (trm_str s))) ) pss ss;  
	Decomposition(p ,pss, List.map2 (fun ps (s,r) -> lazy_translate ((s,ps)::b) r) pss h)
   	with Mating_Mismatch(mess) -> normalize_refutation b r h1 p true (* true forces explicit unfolds *) 
 	end  
| Confront(h1,h2,su,tu,sv,tv,r1,r2) ->begin 
   let p = get_prenorm b h1 in
   let np = get_prenorm b h2 in
   if debug_translation then Printf.printf  "Confronting %s\n" (trm_str p);
   let (bb,r) = begin match (p,np) with
			| (  Ap(Ap(Eq(a),s),t)   ,  Ap(Ap(Imp, Ap(Ap(Eq(a'),u),v) ),False)  ) when a=a' -> begin
				let (psu,ptu,psv,ptv)=(neg (eq a s u),neg (eq a t u),neg (eq a s v),neg (eq a t v)) in
     if trm_eq' (normalize psu) su then 
	(true,Confront(p,np,psu,ptu,psv,ptv, lazy_translate ((su,psu)::(tu,ptu)::b) r1, lazy_translate ((sv,psv)::(tv,ptv)::b) r2 ) )
else if trm_eq' (normalize psu) tu then
	(true,Confront(p,np,psu,ptu,psv,ptv, lazy_translate ((tu,psu)::(su,ptu)::b) r1, lazy_translate ((tv,psv)::(sv,ptv)::b) r2 ) )
else if trm_eq' (normalize psu) sv then
	(true,Confront(p,np,psu,ptu,psv,ptv, lazy_translate ((sv,psu)::(tv,ptu)::b) r2, lazy_translate ((su,psv)::(tu,ptv)::b) r1 ) )
else if trm_eq' (normalize psu) tv then
	(true,Confront(p,np,psu,ptu,psv,ptv, lazy_translate ((tv,psu)::(sv,ptu)::b) r2, lazy_translate ((tu,psv)::(su,ptv)::b) r1 ) ) 
else  (false,Fal(False)) end
			| (  Ap(Ap(Imp, Ap(Ap(Eq(a'),u),v) ),False)  ,  Ap(Ap(Eq(a),s),t) )  when a=a' -> begin
				let (psu,ptu,psv,ptv)=(neg (eq a s u),neg (eq a t u),neg (eq a s v),neg (eq a t v)) in
     if trm_eq' (normalize psu) su then 
	(true,Confront(p,np,psu,ptu,psv,ptv, lazy_translate ((su,psu)::(tu,ptu)::b) r1, lazy_translate ((sv,psv)::(tv,ptv)::b) r2 ) )
else if trm_eq' (normalize psu) tu then
	(true,Confront(p,np,psu,ptu,psv,ptv, lazy_translate ((tu,psu)::(su,ptu)::b) r1, lazy_translate ((tv,psv)::(sv,ptv)::b) r2 ) )
else if trm_eq' (normalize psu) sv then
	(true,Confront(p,np,psu,ptu,psv,ptv, lazy_translate ((sv,psu)::(tv,ptu)::b) r2, lazy_translate ((su,psv)::(tu,ptv)::b) r1 ) )
else if trm_eq' (normalize psu) tv then
	(true,Confront(p,np,psu,ptu,psv,ptv, lazy_translate ((tv,psu)::(sv,ptu)::b) r2, lazy_translate ((tu,psv)::(su,ptv)::b) r1 ) ) 
else  (false,Fal(False)) end
			| _ -> (false,Fal(False)) end 
  in
  if bb then  
    r
   else if normalize p <> p  then normalize_refutation b (Confront(h2,h1,su,tu,sv,tv,r1,r2)) h1 p false (* both prenorm terms are alternatly normalized*)
   else  normalize_refutation b (Confront(h2,h1,su,tu,sv,tv,r1,r2)) h2 np false
 end  
| Trans(h1,h2,su,r1) -> 
	begin
	let st = get_prenorm b h1 in
   	let tu = get_prenorm b h2 in
	if debug_translation then Printf.printf  "Transitivity %s\n" (trm_str st);
	match (st,tu) with
	| (  Ap(Ap(Eq(a),s),t) , Ap(Ap(Eq(a'),u),v) ) when a=a' -> begin
		 if  trm_eq s u then
            	Trans(st,tu,Ap(Ap(Eq(a),t),v), lazy_translate ((su,Ap(Ap(Eq(a),t),v))::b) r1)
 	    	else if  trm_eq t u then
            	Trans(st,tu,Ap(Ap(Eq(a),s),v), lazy_translate ((su,Ap(Ap(Eq(a),s),v))::b) r1)
 	    	else if  trm_eq s v then
            	Trans(st,tu,Ap(Ap(Eq(a),t),u), lazy_translate ((su,Ap(Ap(Eq(a),t),u))::b) r1)
 	    	else if  trm_eq t v then
            	Trans(st,tu,Ap(Ap(Eq(a),s),u), lazy_translate ((su,Ap(Ap(Eq(a),s),u))::b) r1)
 	    	else if normalize st <> st  then normalize_refutation b (Trans(h2,h1,su,r1)) h1 st false
		else normalize_refutation b (Trans(h2,h1,su,r1)) h2 tu false
		end
	| _ ->  if normalize st <> st  then normalize_refutation b (Trans(h2,h1,su,r1)) h1 st false
		else normalize_refutation b (Trans(h2,h1,su,r1)) h2 tu false
	end
 | NegEqualProp(h,s,t,r1,r2) -> begin
   let p = get_prenorm b h in
   if debug_translation then Printf.printf  "boolean extensionality %s\n" (trm_str p);
   match p with  
     | (Ap(Ap(Imp,Ap(Ap(Eq(Prop),m1),m2)),False)) -> (* not equal *)
		begin
            if  trm_eq (normalize m2)  t && trm_eq (normalize m1)  s then
            NegEqualProp(p,m1,m2, lazy_translate ((s,m1)::(normneg t,neg m2)::b) r1,lazy_translate((normneg s,neg m1)::(t,m2)::b) r2)
 	    else 
	    if   trm_eq (normalize m1)  t && trm_eq (normalize m2)  s then
            NegEqualProp(p,m1,m2, lazy_translate ((t,m1)::(normneg s,neg m2)::b) r2,lazy_translate((normneg t,neg m1)::(s,m2)::b) r1)
 	    else normalize_refutation b r h p false
          end     	 
     | (Ap(Ap(Imp,Ap(Ap(Iff,m1),m2)),False)) -> (* not equivalent *)
		begin
            if  trm_eq (normalize m2)  t && trm_eq (normalize m1)  s then
            NegAequivalenz(p,m1,m2, lazy_translate ((s,m1)::(normneg t,neg m2)::b) r1,lazy_translate((normneg s,neg m1)::(t,m2)::b) r2)
 	    else 
	    if   trm_eq (normalize m1)  t && trm_eq (normalize m2)  s then
            NegAequivalenz(p,m1,m2, lazy_translate ((t,m1)::(normneg s,neg m2)::b) r2,lazy_translate((normneg t,neg m1)::(s,m2)::b) r1)
 	    else normalize_refutation b r h p false
          end     	 
    | _ ->  normalize_refutation b r h p false
    end  
 | EqualProp(h,s,t,r1,r2) -> begin
   let p = get_prenorm b h in
   if debug_translation then Printf.printf  "boolean Equality %s\n" (trm_str p);
   match p with  
     | Ap(Ap(Eq(Prop),m1),m2) -> (* equal *)
		begin
            if  trm_eq (normalize m2)  t && trm_eq (normalize m1)  s then
            EqualProp(p,m1,m2, lazy_translate ((s,m1)::(t,m2)::b) r1,lazy_translate ((normneg s,neg m1)::(normneg t,neg m2)::b) r2)
 	    else
	    if  trm_eq (normalize m1)  t && trm_eq (normalize m2)  s then
            EqualProp(p,m1,m2, lazy_translate ((s,m2)::(t,m1)::b) r1,lazy_translate ((normneg s,neg m2)::(normneg t,neg m1)::b) r2)
 	    else normalize_refutation b r h p false
          end     	 
    | Ap(Ap(Iff,m1),m2) -> (* equivalenz *)
		begin
           if  trm_eq (normalize m2)  t && trm_eq (normalize m1)  s then
            Aequivalenz(p,m1,m2, lazy_translate ((s,m1)::(t,m2)::b) r1,lazy_translate ((normneg s,neg m1)::(normneg t,neg m2)::b) r2)
 	    else
	    if  trm_eq (normalize m1)  t && trm_eq (normalize m2)  s then
            Aequivalenz(p,m1,m2, lazy_translate ((s,m2)::(t,m1)::b) r1,lazy_translate ((normneg s,neg m2)::(normneg t,neg m1)::b) r2)
 	    else normalize_refutation b r h p false
          end   
    | _ ->  normalize_refutation b r h p false
    end  
 | NegEqualFunc(h,s,r1) -> begin 
   let p = get_prenorm b h in
   if debug_translation then Printf.printf  "functional extensionality %s\n" (trm_str p);
   match p with  
     | (Ap(Ap(Imp,Ap(Ap(Eq(Ar(a,a')),m1),m2)),False)) -> 
	begin
	let left = (Ap(shift m1 0 1,DB(0,a))) in
	let right =  (Ap(shift m2 0 1,DB(0,a))) in
	let aao= Ar(a',Ar(a',Prop)) in
	let prefix= Lam(aao, neg ( forall a (Ap(Ap(DB(1,aao),left),right)) )) in
	let ps =  onlybetanorm (Ap(prefix,Eq(a'))) in
	if trm_eq' (normalize ps) s then NegEqualFunc(p,ps, lazy_translate ((s,ps)::b) r1)
	else 
	begin
	let ps' = onlybetanorm (Ap(prefix,Lam(a',Lam(a',Ap(Ap(Eq(a'),DB(0,a')),DB(1,a'))))  )) in 

	if trm_eq' (normalize ps') s
	then NegEqualFunc(p,ps, Rewrite(prefix,Eq(a'), Lam(a',Lam(a',Ap(Ap(Eq(a'),DB(0,a')),DB(1,a')))) ,lazy_translate ((s,ps')::b) r1) )
	else raise TranslateFailure (*** Sep 2011 - Chad : start over with safe_translate ***) (** failwith("Error with NegEqualFunc: Unexpected result " ^ (trm_str ps)) **)
	end        
	end     	 
    | _ -> normalize_refutation b r h p false
    end  
 | EqualFunc(h,s,r1) -> begin 
   let p = get_prenorm b h in
   if debug_translation then Printf.printf  "functional Equality %s\n" (trm_str p);
   match p with  
     | Ap(Ap(Eq(Ar(a,a')),m1),m2) -> begin
	 let left = (Ap(shift m1 0 1,DB(0,a))) in
	let right =  (Ap(shift m2 0 1,DB(0,a))) in
	let aao= Ar(a',Ar(a',Prop)) in
	let prefix= Lam(aao,( forall a (Ap(Ap(DB(1,aao),left),right)) )) in
	let ps =  onlybetanorm (Ap(prefix,Eq(a'))) in
		if trm_eq' (normalize ps) s 
		then EqualFunc(p,ps, lazy_translate ((s,ps)::b) r1)
		else let ps' = onlybetanorm (Ap(prefix,Lam(a',Lam(a',Ap(Ap(Eq(a'),DB(0,a')),DB(1,a'))))  )) in 
		if trm_eq' (normalize ps') s 
		then EqualFunc(p,ps,Rewrite(prefix,Eq(a'), Lam(a',Lam(a',Ap(Ap(Eq(a'),DB(0,a')),DB(1,a'))))  ,lazy_translate ((s,ps')::b) r1) )
		else raise TranslateFailure (*** Sep 2011 - Chad : start over with safe_translate ***) (** failwith("Error with EqualFunc: Unexpected result " ^ (trm_str (normalize ps)) ^ " s: " ^ (trm_str s)) **)
          end         	 
    | _ -> normalize_refutation b r h p false
    end  
 | ChoiceR(eps,pred,s,t,r1,r2) -> begin
	match eps with  
	| Name(x,Ar (Ar (a, Prop), _)) -> (* Case 1: The choice is a name defined by an axiom *)
		let (h,p,bb) = check_Choicop_axiom x a b in
		if not bb 
		then  normalize_refutation b r h p false
		else
		let ps = onlybetanorm (forall a (neg (ap (shift pred 0 1,DB(0,a)) ) ) ) in
		let pt = onlybetanorm ( ap (pred,ap (eps,pred)) ) in
   		if debug_translation then Printf.printf  "Choice %s\n" (trm_str pred); 
		ChoiceR(eps,pred,ps,pt,lazy_translate ((s, ps)::b) r1,lazy_translate ((t,pt)::b) r2)  
	| Choice(a) -> (* Case 2: The choice is a regular ochoice operator *)
		let ps = onlybetanorm (forall a (neg (ap (shift pred 0 1,DB(0,a)) ) ) ) in
		let pt = onlybetanorm ( ap (pred,ap (eps,pred)) ) in
   		if debug_translation then Printf.printf  "Choice %s\n" (trm_str pred); 
		ChoiceR(eps,pred,ps,pt,lazy_translate ((s, ps)::b) r1,lazy_translate ((t,pt)::b) r2)  
	| _ -> raise TranslateFailure (*** Sep 2011 - Chad : start over with safe_translate ***) (** failwith("Error with ChoiceR: eps = " ^ (trm_str eps)) **)
	end
 | Cut(s,r1,r2) -> 
	if debug_translation then Printf.printf  "Cut %s\n" (trm_str s); 
	Cut(s,lazy_translate ((s,s)::b) r1,lazy_translate ((normneg s,neg s)::b) r2)   
 | Rewrite(pre,pt,pt',r1) -> (* possibly produced by search, when leibniz equality is rewritten *)
			let trm = onlybetanorm (Ap(pre,pt)) in
			let p = get_prenorm b trm in
			if trm_eq p trm 
			then begin
			if debug_translation then Printf.printf  "Rewrite %s\n" (trm_str trm); 
			let ptrm' =  onlybetanorm (Ap(pre,pt')) in
			let ptrm =  norm name_def (Ap(pre,pt')) in
			 Rewrite(pre,pt,pt',lazy_translate ((ptrm,ptrm')::b) r1 ) end
			else normalize_refutation b r trm p false
 | KnownResult(s,name,al,r1) ->
     if debug_translation then Printf.printf "lazy translate known %s %s\n" name (trm_str s);
     KnownResult(s,name,al,lazy_translate ((s,s)::b) r1)
 | Timeout -> Timeout 
 | _ -> raise TranslateFailure (*** Sep 2011 - Chad : start over with safe_translate ***) (** failwith "unexpected refutation case in translation" **)

 (** Input: Branch b, Refutation r, Term trm, Term ptrm, Boolean delta (true-> explicit Unfold, false -> implicit by Coq)
	Invariant: [ptrm]= trm, trm <> ptrm, ptrm has  m -> False instead of Neg(m)
	Catches some special cases, where a top-level rewrite can be avoided by applying some rule instead.
	*)
and normalize_refutation b r trm ptrm delta = 
  if debug_translation then Printf.printf "normalize_refutation called with\ntrm %s\nptrm %s\n" (trm_str trm) (trm_str ptrm);
  match ptrm with
  | (Ap(Ap(Imp,m),False)) ->
      begin 
	match m with
        | (Ap(Ap(Imp,m'),False)) -> (* top-level double negation*)
	    if debug_translation then Printf.printf  "DoubleNegation %s\n" (trm_str ptrm);
	    DoubleNegation(ptrm,m',lazy_translate ((trm,m')::b) r)
        | (Ap(Ap(Imp,m'),f)) when normalize f = False ->  (* normalizing the inner False is avoided by applying NegImplication, as the second result is equivalent to true*)
	    NegImplication(ptrm,m',(Ap(Ap(Imp,False),False)),lazy_translate ((trm,m')::b) r)       
        | _ -> rewrite_refutation b r trm ptrm delta
      end
  | (Ap(Ap(Imp,m),f)) when normalize f = False ->  (* normalizing f is pushed down to the second branch of the implication rule*)
      Implication(ptrm,neg m,f,lazy_translate ((trm,neg m)::b) r,lazy_translate ((False,f)::b) (Fal(False)))       
  | _ ->  
      rewrite_refutation b r trm ptrm delta           

(** Input: Variable x, Type a, Branch b
	Invariant: a is the type of the choice.
	Output: Searches for the axiom in b that defines x as a choice operator. 
			Returns search result and wether the prenormalized form can be used in a Coq Lemma. **)
and check_Choicop_axiom x a b = 
let m1 = Ap (Forall (Ar (a, Prop)),Lam (Ar (a, Prop),Ap (Forall a,Lam (a,Ap (Ap (Imp, Ap (DB (1, Ar (a, Prop)), DB (0, a))),
	 Ap (DB (1, Ar (a, Prop)),Ap (Name (x, Ar (Ar (a, Prop), a)), DB (1, Ar (a, Prop))))))))) in
let m2 = Ap (Forall (Ar (a, Prop)),Lam (Ar (a, Prop),Ap(Ap (Imp,Ap(Ap (Imp,Ap (Forall a,Lam (a,
	Ap (Ap (Imp, Ap (DB (1, Ar (a, Prop)), DB (0, a))),False)))),False)),Ap (DB (0, Ar (a, Prop)),
	Ap (Name (x, Ar (Ar (a, Prop), a)),DB (0, Ar (a, Prop))))))) in
let m3 = Ap (Forall (Ar (a, Prop)),Lam (Ar (a, Prop),Ap(Ap (Imp,Ap (Exists a,Lam (a,
	Ap (DB (1, Ar (a, Prop)), DB (0, a))))),Ap (DB (0, Ar (a, Prop)),
	Ap (Name (x, Ar (Ar (a, Prop), a)),DB (0, Ar (a, Prop))))))) in
try
let (m,h)= List.find (fun (m,h) -> m = m1 || m = m2 || m = m3 ) b in 
(m,h,h = m1 || h = m2 || h = m3)
with Not_found -> raise TranslateFailure (*** Sep 2011 - Chad : start over with safe_translate ***) (** failwith("Error with ChoiceR: no choice axiom found for " ^ x ^ " " ^ (stp_str a)) **)

(* Chad, Aug 2011: leib_rewrite_refutation
   Inputs : m - term, p - term (subterm of porig) of same type as m, porig - term, n - int, r - refutation
   Invariant : m was preprocessed to be p
               At the moment this can only mean some instances of Leibniz equality/least reflexive relation in m became primitive equality in p.
               Most instances of these are caught in suche, but not all.
   Output : refutation with m instead of p
 *)
let rec leib_rewrite_refutation m p porig n r c =
  if debug_translation then Printf.printf "leib_rewrite_refutationa\nm %s\np %s\nporig %s\n" (trm_str m) (trm_str p) (trm_str porig);
  if (m = p) then
    r
  else
    begin
      if debug_translation then Printf.printf "leib_rewrite_refutationb\nm %s\np %s\n" (trm_str m) (trm_str p);
      try
	let (pred,e1,e2,aao) = is_an_eqn_p m n in
	let q = Lam(aao,c pred) in
	if debug_translation then Printf.printf "is_an_eqn_p returned with \nq %s\n" (trm_str q);
	Rewrite(q,e1,e2,leib_rewrite_refutation_2 (onlybetanorm (Ap(q,e2))) porig 0 r)
      with Not_found ->
(***  July 2012: Need to add case for exists rewritten to choice. Currently modes with EXISTSTOCHOICE true will often not produce proofs.
	try
	  let (pred,e1,e2,aoa) = exists_to_choice_p m p n in
	  let q = Lam(aoa,c pred) in
	  if debug_translation then Printf.printf "exists_to_choice_p returned with \nq %s\n" (trm_str q);
	  Rewrite(q,e1,e2,leib_rewrite_refutation_2 (onlybetanorm (Ap(q,e2))) porig 0 r)
	with Not_found ->
***)
	  match (m,p) with
	  | (Ap(m1,m2),Ap(p1,p2)) ->
	      leib_rewrite_refutation m1 p1 porig n (leib_rewrite_refutation m2 p2 porig n r (fun z -> c (Ap(p1,z)))) (fun z -> c (Ap(z,m2)))
	  | (Lam(a,m1),Lam(b,p1)) when a = b ->
	      leib_rewrite_refutation m1 p1 porig (n + 1) r (fun z -> c (Lam(a,z)))
	  | (Lam(a,m1),Ap(Eq(b),DB(0,_))) when a = b ->
	      leib_rewrite_refutation m1 (Ap(Ap(Eq(a),DB(1,a)),DB(0,a))) porig (n + 1) r (fun z -> c (Lam(a,z)))
	  | (Lam(a,m1),Eq(b)) when a = b ->
	      leib_rewrite_refutation m1 (Ap(Eq(b),DB(0,a))) porig (n + 1) r (fun z -> c (Lam(a,z)))
	  | _ ->
	      raise (GenericError ("Cannot show " ^ (trm_str m) ^ " and " ^ (trm_str p) ^ " are equal in leib_rewriting refutation."))
    end
and leib_rewrite_refutation_2 m p n r =
  if (m = p) then
    r
  else
    begin
      try
	let (pre,pt,pt',bb,stp)= rewrite_refutation1 m 0 in
	let prefix= Lam(stp,pre) in
	let m' = onlybetanorm (Ap(prefix,pt')) in
	if bb (* add Rewrite-step only if necessary*) 
	then
	  Rewrite(prefix,pt,pt',leib_rewrite_refutation_2 m' p n r) (*** m' is closer to being normal than m was. ***)
	else
	  raise NoMoreRewrites
      with
      |	Delta_reduction(x,def) -> (* should not happen, but just in case *)
	  let m'= onlybetanorm (namesubst m x def) in
	  Delta(m,m',x,leib_rewrite_refutation_2 m' p n r) (*** m' is closer to being normal than m was. ***)
      |	NoMoreRewrites ->
	  leib_rewrite_refutation m p p n r (fun z -> z)
    end

(*** Simply add rewrites. The Coq proof will do all these rewrites first. ***)
let rec safe_rew_translate b r =
  match b with
  | ((trm1,trm2)::br) ->
      if debug_translation then Printf.printf "safe_rew_translate \ntrm1 %s\ntrm2 %s\n" (trm_str trm1) (trm_str trm2);
      if ((onlynegnorm trm1) = (onlynegnorm trm2)) then (*** In this 'safe' version, I use onlynegnorm instead of coqnorm to demand all defns be explicitly unfolded. Mating and Decomposition require this to work properly. ***)
	safe_rew_translate br r
      else
	begin
	  if debug_translation then Printf.printf "* working on it\n";
	  try
	    let (pre,pt,pt',bb,stp)= rewrite_refutation1 trm2 0 in
	    let prefix= Lam(stp,pre) in
	    let trm2' = onlybetanorm (Ap(prefix,pt')) in
	    if bb (* add Rewrite-step only if necessary*) 
	    then
	      Rewrite(prefix,pt,pt',safe_rew_translate ((trm1,trm2')::br) r) (*** trm2' is closer to being normal than trm2 was. ***)
	    else
	      raise NoMoreRewrites (*** But coqnorm's were not equal - so work on the normalized form ***)
	  with
	  | Delta_reduction(x,def) ->
	      let trm2'= onlybetanorm (namesubst trm2 x def) in
	      Delta(trm2,trm2',x,safe_rew_translate ((trm1,trm2')::br) r)
	  | NoMoreRewrites ->
	      if debug_translation then Printf.printf "* final attempt to show same\n";
	      leib_rewrite_refutation trm2 trm1 trm1 0 r (fun z -> z)
	end
  | [] -> r

(*** Fill in any intermediate double negation and rewrite steps. ***)
let rec safe_fill_translate r =
  match r with
  | Implication(Ap(Ap(Imp,m1),m2) as m0,n,p,r1,r2) ->
      begin
	match m1 with
	| Ap(Ap(Imp,m1n),False) ->
	    Implication(m0,neg m1,m2,DoubleNegation(neg m1,m1n,safe_fill_translate r1),safe_fill_translate r2)
	| _ ->
	    Implication(m0,neg m1,m2,safe_fill_translate r1,safe_fill_translate r2)
      end
  | NegImplication(Ap(Ap(Imp,Ap(Ap(Imp,m1),m2)),False) as m0,n,p,r1) ->
      begin
	match m2 with
	| Ap(Ap(Imp,m2n),False) ->
	    NegImplication(m0,m1,neg m2,DoubleNegation(neg m2,m2n,safe_fill_translate r1))
	| _ ->
	    NegImplication(m0,m1,neg m2,safe_fill_translate r1)
      end
  | All(Ap(Forall(a),m1) as m0,m2,r1,b,m3,t) ->
      let m1t = onlybetanorm (Ap(m1,t)) in
      All(m0,m1t,safe_rew_translate [(m2,m1t)] (safe_fill_translate r1),b,m3,t)
  | NegAll(Ap(Ap(Imp,Ap(Forall(a),m1)),False) as m0,m2,r1,b,m3,x) ->
      let m1x = onlybetanorm (Ap(m1,Name(x,a))) in
      begin
	match m1x with
	| Ap(Ap(Imp,m1xn),False) ->
	    NegAll(m0,neg m1x,DoubleNegation(neg m1x,m1xn,safe_fill_translate r1),b,m3,x)
	| _ ->
	    NegAll(m0,m2,safe_fill_translate r1,b,m3,x)
      end
  | Mating(m,n,pl,rl) ->
      Mating(m,n,pl,List.map safe_fill_translate rl)
  | Decomposition(m,pl,rl) ->
      Decomposition(m,pl,List.map safe_fill_translate rl)
  | Confront(m1,m2,m3,m4,m5,m6,r1,r2) ->
      Confront(m1,m2,m3,m4,m5,m6,safe_fill_translate r1,safe_fill_translate r2)
  | Trans(m1,m2,m3,r1) ->
      Trans(m1,m2,m3,safe_fill_translate r1)
  | NegEqualProp(Ap(Ap(Imp,Ap(Ap(Eq(_),m1a),m1b)),False) as m0,m2,m3,r1,r2) ->
      begin
	match m2 with
	| Ap(Ap(Imp,m2n),False) ->
	    begin
	      match m3 with
	      | Ap(Ap(Imp,m3n),False) ->
		  NegEqualProp(m0,m2,m3,DoubleNegation(neg m3,m3n,safe_fill_translate r1),DoubleNegation(neg m2,m2n,safe_fill_translate r2))
	      | _ ->
		  NegEqualProp(m0,m2,m3,safe_fill_translate r1,DoubleNegation(neg m2,m2n,safe_fill_translate r2))
	    end
	| _ ->
	    begin
	      match m3 with
	      | Ap(Ap(Imp,m3n),False) ->
		  NegEqualProp(m0,m2,m3,DoubleNegation(neg m3,m3n,safe_fill_translate r1),safe_fill_translate r2)
	      | _ ->
		  NegEqualProp(m0,m2,m3,safe_fill_translate r1,safe_fill_translate r2)
	    end
      end
  | EqualProp(Ap(Ap(Eq(_),m1a),m1b) as m0,m2,m3,r1,r2) ->
      begin
	match m2 with
	| Ap(Ap(Imp,m2n),False) ->
	    begin
	      match m3 with
	      | Ap(Ap(Imp,m3n),False) ->
		  EqualProp(m0,m2,m3,safe_fill_translate r1,DoubleNegation(neg m2,m2n,DoubleNegation(neg m3,m3n,safe_fill_translate r2)))
	      | _ ->
		  EqualProp(m0,m2,m3,safe_fill_translate r1,DoubleNegation(neg m2,m2n,safe_fill_translate r2))
	    end
	| _ ->
	    begin
	      match m3 with
	      | Ap(Ap(Imp,m3n),False) ->
		  EqualProp(m0,m2,m3,safe_fill_translate r1,DoubleNegation(neg m3,m3n,safe_fill_translate r2))
	      | _ ->
		  EqualProp(m0,m2,m3,safe_fill_translate r1,safe_fill_translate r2)
	    end
      end
  | NegEqualFunc(Ap(Ap(Imp,Ap(Ap(Eq(Ar(a,b)),m1a),m1b)),False) as m0,m2,r1) ->
      NegEqualFunc(m0,m2,safe_fill_translate r1)
  | EqualFunc(Ap(Ap(Eq(Ar(a,b)),m1a),m1b) as m0,m2,r1) ->
      EqualFunc(m0,m2,safe_fill_translate r1)
  | ChoiceR(eps,pred,empty,choice,r1,r2) -> (*** Assume pred is normal ***)
      begin
	match (tpof pred) with
	| Ar(a,Prop) ->
	    let m1 = onlybetanorm (Ap(pred,Ap(eps,pred))) in
	    let m2 = onlybetanorm (Ap(shift pred 1 0,DB(0,a))) in
	    let m2n = neg m2 in
	    let m3 = forall a m2n in
	    let m4 = normalize (forall a m2n) in
	    let r1a = safe_fill_translate r1 in
	    let r2a = safe_fill_translate r2 in
	    ChoiceR(eps,pred,m3,choice,safe_rew_translate [(m4,m3)] r1a,r2a)
	| _ -> failwith "ChoiceR with non predicate."
      end
  | Cut(m,r1,r2) -> (*** Assume m is normal. For some reason it can be a negation (mode195, SYO357^2). ***)
      begin
	match m with
	| Ap(Ap(Imp,m1),False) ->
	    Cut(m,safe_fill_translate r1,DoubleNegation(neg m,m1,safe_fill_translate r2))
	| _ ->
	    Cut(m,safe_fill_translate r1,safe_fill_translate r2)
      end
  | Rewrite(m1,m2,m3,r1) -> (*** Assume m1 is normal ***)
      Rewrite(m1,m2,m3,safe_fill_translate r1)
  | KnownResult(m,s,al,r1) -> (*** Assume m is normal ***)
      KnownResult (m,s,al,safe_fill_translate r1)
  | Conflict(m1,m2) ->
      begin
	match m1 with
	| Ap(Ap(Imp,m1n),False) when coqnorm m1n = coqnorm m2 -> Conflict(m2,m1)
	| _ -> Conflict(m1,m2)
      end
  | _ -> r (*** This should be Timeout, Fal or NegRefl; no other refutation case is created in suche.ml ***)

(* safe_translate : Chad - Aug 2011 - Intended to work in every case, but generally gives the worst proof. It's a safety net. *)
let rec safe_translate b r = safe_rew_translate b (safe_fill_translate r)
