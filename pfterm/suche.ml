open Flags
open State
open String
open Syntax
open Refutation
open Flag
open Branch
open Step
open Litcount

exception No_More_Clauses
exception Independent_Refutation of refutation * Dependency.t 

exception Initialbranch_Hypothesis_Error 

let beforeSearch = ref 0.0
let isTimeout = ref false 

let myConflict n (a,b) = if debug_search then Printf.printf "myConflict %d %s %s\n" n (trm_str a) (trm_str b); Conflict(a,b)

(** HEURISTIK  **)  

(** Preprocess **)

(** Sort the list of steps in ascending order by the number of alternatives and in descending order Step.heuristic.
	Exist steps are an exception. They are sorted to the beginning of the list and their order is kept.  **)
let sort_steps sl litc = List.stable_sort 
	(fun a b ->
		let c = Pervasives.compare (Step.number_of_branches a ) (Step.number_of_branches b ) in
		if c = 0 then Pervasives.compare (Step.heuristic b litc ) (Step.heuristic a litc) else c ) sl 
(* stable_sort keeps the order of the exists*)

(** Input: List of clasues cl,cw and clause to rule info cr 
	Iterates over the list of clauses and adds symmetric clauses in certain cases, while avoiding duplication.
	**)
let rec add_sym_clauses cl cw cr =
	match cl with 
	| (c::clr) -> 
	begin
		match (cr c) with
		| MatingRule(plit,nlit) -> begin
			if  debug_add_clauses then (Printf.printf  "because of %s " (ruleinfo_str (cr c)));
			let c2=(nlit)::((plit)::(List.tl (List.tl c)) )  in 
			if List.mem c2 cw then ( if  debug_add_clauses then Printf.printf  "no add - already exists \n";(add_sym_clauses clr cw cr) )
			else
			try (ignore (cr c2); 
			 if  debug_add_clauses then (Printf.printf  "add  %s  \n" (ruleinfo_str (cr c2)) ); (add_sym_clauses clr (c2::cw) cr) )
			with Not_found ->  if  debug_add_clauses then Printf.printf  "no add \n" ; (add_sym_clauses clr cw cr)
			end 
		| ConfrontationRule(plit,nlit) ->
 			begin 
			if  debug_add_clauses then (Printf.printf  "because of %s " (ruleinfo_str (cr c)));
			let (n,m)= (literal_to_trm plit,literal_to_trm (-nlit) ) in
			let c2 = match (n,m) with
				| (  Ap(Ap(Eq(a),s),t)  ,  Ap(Ap(Eq(a'),u),v)  ) when a=a' -> begin
					let (su,tu)=(neg (eq a s u),neg (eq a t u)) in
					let (lsu,ltu) = (get_literal su,get_literal tu) in 
					[-nlit;-plit;lsu;ltu]					 
					end
				| _ -> failwith ("can't handle with Confrontation Rule: "^ (trm_str n) ^" and "^ (trm_str m) ) 
			in
			if List.mem c2 cw then ( if  debug_add_clauses then Printf.printf  "no add - already exists \n";add_sym_clauses clr cw cr )
			else
			try (ignore (cr c2); 
			 if  debug_add_clauses then (Printf.printf  "add  %s  \n" (ruleinfo_str (cr c2)) ); (add_sym_clauses clr (c2::cw) cr) )
			with Not_found ->  if  debug_add_clauses then Printf.printf  "no add \n" ; (add_sym_clauses clr cw cr)
			end 
		| _ -> (add_sym_clauses clr cw cr)
	end
	| [] -> cw


(** Input: List of clauses
	Output: Literal Count of the literals occuring in the clauses **)	
let initialise_literal_array cl = 
	if pftrm_litcount then begin
	let litc = LitCount.make (max_atom () +1) in 
	List.iter (fun c -> List.iter (fun l -> LitCount.incr litc l ) c ) cl;
	litc
	end else LitCount.make (max_atom () +1)

(** Input : List of clauses
	Output: List of steps **)
let preprocess_clauses cl cr =
	(** 1. Remove unit clauses such as assumption clauses, True and s=s **)
	let cl1 = List.fold_right (fun c cl' -> 
		if List.length c > 1
		then
		  c::cl'
		else
		  begin (*** Chad, Aug 2011: Keep 'Known' Unit Clauses ***)
		    try
		      match cr c with
		      | Known(_,_,_) -> (c::cl')
		      | _ -> cl'
		    with
		    | Not_found -> cl'
		  end) cl [] in 
	if result_statistic then (Printf.printf "Filtered to %d clauses\n" (List.length cl1); flush stdout); 
	
	(** 2. Add symmetric clauses - optional **)
	let cl2= if (get_bool_flag "PFTRM_ADD_SYM_CLAUSES") && pftrm_add_clauses then add_sym_clauses cl1 cl1 cr else cl1 in 
	if result_statistic then (Printf.printf "Added sym clauses and now %d clauses\n" (List.length cl2); flush stdout); 

	(** 3. Extract all existential witnesses **)
	let witnesses = List.fold_left (fun w c -> match cr c with FreshRule(_,_,x) -> x::w | _ -> w ) [] cl2 in
	if debug_free_names then (Printf.printf "found witnesses %d \n" (List.length witnesses); flush stdout); 
	if debug_free_names then Printf.printf  "found global witnesses %s \n" (String.concat "," witnesses) ;

	(** 4. Turn clauses into steps and avoid duplications **)
	let steps = List.fold_right (fun c sl -> List.fold_left (fun sl' s -> if List.mem s sl' then sl' else s::sl') sl (Step.make c cr witnesses) ) cl2 [] in
	if result_statistic then (Printf.printf "turned clauses into steps %d \n" (List.length steps); flush stdout); 

	(** 5. Extract literal count **)
	let litc = initialise_literal_array cl1  in
	if debug_litcount then (LitCount.print litc;Printf.printf "\nnumber of literals %d \n" (LitCount.count litc); flush stdout);

	(** 6. Sort the list of steps **)
	if (get_bool_flag "PFTRM_PRESORT_CLAUSES") then sort_steps steps litc  else steps


(** Choose next rule**)

(** Chooses the next step to be applied (directly or by a preceding cut) 
Input: Current Branch b and the list of steps sl
Invariant: There are no satisfied steps in sl and sl is not empty.
Output: The first suitable step in the list. If there is none, then the first step in the list. **)
let get_next_step b sl  = 
	let rec gnc blocked b sl = 
		match sl with 
		| (s::slr)-> 
			if Step.suitable blocked b s 
			then s
			else begin 
				let (exist,witness)= Step.get_witness s in 
				if exist (* Is the step an exists step?*)
				then gnc (witness::blocked) b slr 
 				else gnc blocked b slr  
			end
		| [] -> raise No_More_Clauses in
	try gnc [] b sl with No_More_Clauses -> (try List.hd sl with Failure("hd")-> failwith "No clauses left to choose from"  )

	
let remove_satisfied_steps b sl =
	List.filter (fun s -> not (Step.satisfied s b)) sl

	
(** syntactic branching + Tracking Dependencies **)


let rec apply_rule1 b  sl alts pf level = begin 
match alts with
	| (alt::altsr) -> 
		(* call to or_search for one alternative + reset branch to current level*)
		let (r,c) = try or_search alt (Branch.reset b level) sl 
			with Independent_Refutation(r,cond)-> (r,cond) in
		(* Timeout check*)
		if pftrm_Timeout && (!isTimeout) then (r::(List.map (fun t -> Timeout) altsr),c)
		else 
		(* Dependency check*)
		if ((get_bool_flag "PFTRM_REMOVE_INDEPENDENT") && pftrm_Independent_refutation  && (List.for_all (fun t ->not (Dependency.mem t c) ) alt)) 			
		then
		( if debug_Independent_refutation then Printf.printf  "found Independent refutation\n"; raise (Independent_Refutation(r,c)) )
		else 
		(* recursive call to refute the remaining alternatives*)
		let (rs,c') =  apply_rule1 b sl altsr pf level in
		if (!isTimeout) then (r::rs,c') 
		else
		(* merge dependencies*)
		let dep = Dependency.diffunion [] [c;c'] [alt;[]] in
		if debug_Independent_refutation then Printf.printf "condition = %s\n" (String.concat "," (List.map string_of_int (Dependency.elements dep))); 
		(r::rs,dep) 
		(* base case: empty refutation List*)
	| [] -> ([],Dependency.make pf)
end 

(** Input: Branch b, step list sl, alternatives alts, principal formulae pf
	Output: subrefutation list for each alternative and the diffunion of their dependencies.
	Throws Independent_Refutation, if a subrefutation does not depend on the applied step**)
and apply_rule b sl alts pf =
(* set new level to allow resetting the branch to the current state *)
let level = Branch.next_level b in
let (r,c) = apply_rule1 b sl alts pf level in
(ignore (Branch.reset b level);(r,c))

(** semantic branching + Tracking Dependencies **)

(** Semantic branching for Implication
	Input: Branch b, principal formula h (s->t), step list sl
	Output: refutation for the branch and the corresponding dependency.
	Throws Independent_Refutation, if a subrefutation does not depend on the implication step**)
and apply_Imp  b h s t cl = begin 
		
		if Branch.mem (-s) b || Branch.mem (-t) b then
		(* with -s or -t on the branch semantic branching is redundant*)
		let (r1::r2::rs,con)= apply_rule b cl [[s];[t]] [h]  in 
		(Implication(literal_to_trm h,literal_to_trm s,literal_to_trm t, r1, r2),con) 
		else 
		let level = Branch.next_level b in
		let (r,c) = try or_search [t;-s] b cl  
			with Independent_Refutation(r,con)-> (r,con) in
		if pftrm_Timeout && (!isTimeout) then (Implication(literal_to_trm h,literal_to_trm s,literal_to_trm t,Timeout,r),Dependency.empty)
		else
		if (Dependency.mem (-s) c) &&  (Dependency.mem t c)
		then
			let (r',c') =   try or_search [s] (Branch.reset b level) cl 
			with Independent_Refutation(r,con)-> (r,con) in
			if pftrm_Timeout && (!isTimeout) 
			then (Implication(literal_to_trm h,literal_to_trm s,literal_to_trm t,r',r),Dependency.empty)
			else
			if (Dependency.mem s c') 
			then 	(* semantic branching with cut on s *)
				let con = Dependency.diffunion [h] [c';c] [[s];[-s;t]] in 
				if debug_Independent_refutation then Printf.printf "condition(1) = %s\n" (String.concat "," (List.map string_of_int (Dependency.elements con)));
				(Cut(literal_to_trm s,r',Implication(literal_to_trm h,literal_to_trm s,literal_to_trm t,
								myConflict 1 (literal_to_trm s,literal_to_trm (-s)),r)),con) 
			else  (* Second subrefutation is independent *)
				(if debug_Independent_refutation then Printf.printf  "apply_Imp Independent_Refutation left(1)\n";
				raise (Independent_Refutation(r',c')))
		else
		if not (Dependency.mem (-s) c) &&  not (Dependency.mem t c)
		then (* First subrefutation is independent *)
			(if debug_Independent_refutation then Printf.printf  "apply_Imp Independent_Refutation right(1)\n" ;
			raise (Independent_Refutation(r,c) ) )
		else
		if (Dependency.mem (-s) c) &&  not (Dependency.mem t c)
		then 
			let (r',c') =   try or_search [s] (Branch.reset b level) cl 
			with Independent_Refutation(r,con)-> (r,con) in
			if pftrm_Timeout && (!isTimeout) 
			then (Implication(literal_to_trm h,literal_to_trm s,literal_to_trm t,r',r),Dependency.empty)
			else
			if (Dependency.mem s c') 
			then 	(* only cut on s*)
				let con = Dependency.diffunion [] [c';c] [[s];[-s]] in
				if debug_Independent_refutation then Printf.printf "condition(2) = %s\n" (String.concat "," (List.map string_of_int (Dependency.elements con)));
				(Cut(literal_to_trm s,r',r),con)
			else   (* Second subrefutation is independent *)
				(if debug_Independent_refutation then Printf.printf  "apply_Imp Independent_Refutation left(2)\n" ;
				raise (Independent_Refutation(r',c')) )
		else 
		if not (Dependency.mem (-s) c) &&  (Dependency.mem t c)
		then 
			let (r',c') =   try or_search [s;-t] (Branch.reset b level) cl
			with Independent_Refutation(r,con)-> (r,con) in
			if pftrm_Timeout && (!isTimeout) 
			then (Implication(literal_to_trm h,literal_to_trm s,literal_to_trm t,r',r),Dependency.empty)
			else
			if (Dependency.mem (-t) c') &&  (Dependency.mem s c') 
			then (* semantic branching with cut on t *)
				let con = Dependency.diffunion [h] [c';c] [[-t;s];[t]] in
				if debug_Independent_refutation then Printf.printf "condition(3) = %s\n" (String.concat "," (List.map string_of_int (Dependency.elements con)));
				(Cut(literal_to_trm t,r,Implication(literal_to_trm h,literal_to_trm s,literal_to_trm t,r',
						myConflict 2 (literal_to_trm t,literal_to_trm (-t)))),con) 					
			else 
			if not (Dependency.mem (-t) c') &&  (Dependency.mem s c') 	
			then  (* syntactic branching *)
				let con =  Dependency.diffunion [h] [c';c] [[s];[t]] in
				if debug_Independent_refutation then Printf.printf "condition(4) = %s\n" (String.concat "," (List.map string_of_int (Dependency.elements con)));
				(Implication(literal_to_trm h,literal_to_trm s,literal_to_trm t,r',r),con)
			else 
			if (Dependency.mem (-t) c') && not (Dependency.mem s c') 
			then (* only cut on t*)
				let con = Dependency.diffunion [] [c';c] [[-t];[t]] in
				if debug_Independent_refutation then Printf.printf "condition(5) = %s\n" (String.concat "," (List.map string_of_int (Dependency.elements con)));
					(Cut(literal_to_trm t,r,r'),con) 
			else
			if  not (Dependency.mem (-t) c') && not (Dependency.mem s c') 
			then  (* Second subrefutation is independent *)
				(if debug_Independent_refutation then Printf.printf  "apply_Imp Independent_Refutation left(3)\n" ;
				 raise (Independent_Refutation(r',c') ) )
			else  failwith "you found the fifth case out of four; I messed up" 
		else failwith "you found the fifth case out of four; I messed up" 
end

(** Semantic branching for Confrontation
	Input: Branch b, step list cl, alternatives br, principal formulae h
	Invariant: h= [s <> t; u <> v] , br = [[s <> u; t <> u]; [s <> v; t <> v]] up to symmetry
	Output: refutation for the branch and the corresponding dependency.
	Throws Independent_Refutation, if a subrefutation does not depend on the Confontation step**)
and apply_Con b cl br h =
  begin
    let  st = -List.hd h in
    let  uv = List.hd (List.tl h) in
    let (ss,tt) = match literal_to_trm (-st) with |  Ap(Ap(Eq(a),s),t) -> (Ap(Ap(Imp,Ap(Ap(Eq(a),s),s) ),False),Ap(Ap(Imp,Ap(Ap(Eq(a),t),t) ),False)) | _ -> failwith "error apply_con" in
    let [[su;tu];[sv;tv]] = br in
    if debug_search then (*** Chad, Aug 2011 - debugging ***)
      begin
	Printf.printf "apply_Con st = %d, uv = %d, su = %d, tu = %d, sv = %d, tv = %d\nbranch = %s\n" st uv su tu sv tv
	  (List.fold_right (fun l s -> (string_of_int l) ^ " " ^ s) (Branch.elements b) "");
      end;
    if Branch.mem (-su) b || Branch.mem (-tu) b || Branch.mem (-sv) b || Branch.mem (-tv) b then 
      let (r1::r2::rs,con)= apply_rule b cl br h  in 
      if debug_search then Printf.printf "dependencies after apply_rule call from apply_Con:\n%s\n" (List.fold_right (fun z r -> r ^ (string_of_int z) ^ "\n") (Dependency.elements con) "");
      if debug_Independent_refutation then Printf.printf  "apply_Con 1\n"; 
      (Confront(literal_to_trm (-st),literal_to_trm uv,literal_to_trm su,literal_to_trm tu,literal_to_trm sv,literal_to_trm tv,r1,r2),con)
    else if Branch.mem sv b || Branch.mem tv b then 
      let svb = Branch.mem sv b in
      let (r,d) = try or_search [tv;sv] b cl  with Independent_Refutation(r,dep)-> (r,dep) in
      if debug_search then Printf.printf "dependencies after recursive call from apply_Con:\n%s\n" (List.fold_right (fun z r -> r ^ (string_of_int z) ^ "\n") (Dependency.elements d) "");
      if pftrm_Timeout && (!isTimeout) 
      then (Confront(literal_to_trm (-st),literal_to_trm uv,literal_to_trm su,literal_to_trm tu,literal_to_trm sv,literal_to_trm tv, r, Timeout),Dependency.empty) 
      else 
	let [b1;b2] = Dependency.check d [tv;sv] in
	if b1 || b2 then 
	  let r1 = myConflict 3 (literal_to_trm (-st),literal_to_trm st) in
	  (*** Chad, Aug 2011: Testing Branch.mem sv b does not make sense unless we reset the branch -- tv and sv were added to b by the call to or_search in this case. I'm testing if sv is in b before calling or_search to avoid this problem. ***)
	  if svb then ( if debug_Independent_refutation then Printf.printf  "apply_Con 3\n";
				   (Confront(literal_to_trm (-st),literal_to_trm sv,ss,literal_to_trm st,literal_to_trm sv,literal_to_trm tv,r1,r),
				    Dependency.diffunion
				      [-st;sv] (*** Chad, Aug 2011: Changed "su" here to "sv" ***)
				      [d] [[tv;sv]]) )
	  else ( if debug_Independent_refutation then Printf.printf  "apply_Con 4\n";
		(Confront(literal_to_trm (-st),literal_to_trm tv,literal_to_trm st,tt,literal_to_trm sv,literal_to_trm tv,r1,r),
		 Dependency.diffunion
		   [-st;tv] (*** Chad, Aug 2011: Changed "tu" here to "tv" ***)
		   [d] [[tv;sv]]) )
	else (if debug_Independent_refutation then Printf.printf  "apply_con Independent_Refutation \n" ;
	      raise (Independent_Refutation(r,d) ) )	
    else if Branch.mem su b || Branch.mem tu b then
      let sub = Branch.mem su b in
      let (r,d) = try or_search [tu;su] b cl  with Independent_Refutation(r,dep)-> (r,dep) in
      if debug_search then Printf.printf "dependencies after recursive call from apply_Con:\n%s\n" (List.fold_right (fun z r -> r ^ (string_of_int z) ^ "\n") (Dependency.elements d) "");
      if pftrm_Timeout && (!isTimeout) 
      then (Confront(literal_to_trm (-st),literal_to_trm uv,literal_to_trm su,literal_to_trm tu,literal_to_trm sv,literal_to_trm tv, r, Timeout),Dependency.empty) 
      else 
	let [b1;b2] = Dependency.check d [tu;su] in
	if debug_search then (*** Chad, Aug 2011 - debugging ***)
	  begin
	    Printf.printf "apply_Con 5 or 6 branch = %s\n"
	      (List.fold_right (fun l s -> (string_of_int l) ^ " " ^ s) (Branch.elements b) "");
	  end;
	if b1 || b2 then 
	  let r1 = myConflict 4 (literal_to_trm (-st),literal_to_trm st) in
	  (*** Chad, Aug 2011: Testing Branch.mem su b does not make sense unless we reset the branch -- tu and su were added to b by the call to or_search in this case. I'm testing if su is in b before calling or_search to avoid this problem. ***)
	  if sub then ( if debug_Independent_refutation then Printf.printf  "apply_Con 5\n";
				   (Confront(literal_to_trm (-st),literal_to_trm su,ss,literal_to_trm st,literal_to_trm su,literal_to_trm tu,r1,r),
				    Dependency.diffunion [-st;su] [d] [[tu;su]]) )
	  else ( if debug_Independent_refutation then Printf.printf  "apply_Con 6\n";
		(Confront(literal_to_trm (-st),literal_to_trm tu,literal_to_trm st,tt,literal_to_trm su,literal_to_trm tu,r1,r),
		 Dependency.diffunion [-st;tu] [d] [[tu;su]]) )
	else (if debug_Independent_refutation then Printf.printf  "apply_Con Independent_Refutation \n" ;
	      raise (Independent_Refutation(r,d) ) )	
    else 
      let level = Branch.next_level b in
      let (r,d) = try or_search [-tv;-sv;su;tu] b cl  with Independent_Refutation(r,dep)-> (r,dep) in
      if pftrm_Timeout && (!isTimeout) 
      then (Confront(literal_to_trm (-st),literal_to_trm uv,literal_to_trm su,literal_to_trm tu,literal_to_trm sv,literal_to_trm tv, r, Timeout),Dependency.empty) 
      else
	let [b1;b2;b3;b4] = Dependency.check d [-tv;-sv;tu;su] in
	match (b1 || b2,b3 || b4) with
	| (true,true) -> begin 
	    let (r',d') =   try or_search [tv;sv] (Branch.reset b level) cl with Independent_Refutation(r,dep)-> (r,dep) in
	    if pftrm_Timeout && (!isTimeout) 
	    then (Confront(literal_to_trm (-st),literal_to_trm uv,literal_to_trm su,literal_to_trm tu,literal_to_trm sv,literal_to_trm tv, r, r'),Dependency.empty) 
	    else	
	      let [b5;b6] = Dependency.check d' [tv;sv] in
	      match (b5,b6) with
	      | (true,true) -> begin 
		  let r1 = myConflict 5 (literal_to_trm (-st),literal_to_trm st) in
		  if b1 then
		    let r2 = Confront(literal_to_trm (-st),literal_to_trm tv,literal_to_trm st,tt,literal_to_trm sv,literal_to_trm tv, r1, r') in
		    let r3 = myConflict 6 (literal_to_trm (-tv),literal_to_trm tv)  in
		    let r4 = Confront(literal_to_trm (-st),literal_to_trm uv,literal_to_trm su,literal_to_trm tu,literal_to_trm sv,literal_to_trm tv,r,r3) in
		    let r5 = if b2 then Trans(literal_to_trm (-st),literal_to_trm (-tv),literal_to_trm (-sv),r4) else r4 in
		    ( if debug_Independent_refutation then Printf.printf  "apply_Con 9\n";(Cut(literal_to_trm (-tv),r5,r2),Dependency.diffunion h [d;d'] [[-tv;-sv;su;tu];[tv;sv]])) 	
		  else 
		    let r2 = Confront(literal_to_trm (-st),literal_to_trm sv,ss,literal_to_trm st,literal_to_trm sv,literal_to_trm tv, r1, r') in
		    let r3 = myConflict 7 (literal_to_trm (-sv),literal_to_trm sv) in
		    let r4 = Confront(literal_to_trm (-st),literal_to_trm uv,literal_to_trm su,literal_to_trm tu,literal_to_trm sv,literal_to_trm tv,r,r3) in
		    (if debug_Independent_refutation then Printf.printf  "apply_Con 10\n";(Cut(literal_to_trm (-sv),r4,r2),Dependency.diffunion h [d;d'] [[-tv;-sv;su;tu];[tv;sv]])) 				
	      end
	      | (true,false) -> begin 
		  let r1 = myConflict 8 (literal_to_trm (-tv),literal_to_trm tv)  in
		  let r2 = Confront(literal_to_trm (-st),literal_to_trm uv,literal_to_trm su,literal_to_trm tu,literal_to_trm sv,literal_to_trm tv,r,r1) in
		  let r3 = if b2 then Trans(literal_to_trm (-st),literal_to_trm (-tv),literal_to_trm (-sv),r2) else r2 in
		  (if debug_Independent_refutation then Printf.printf  "apply_Con 11\n";(Cut(literal_to_trm (-tv),r3,r'),Dependency.diffunion h [d;d'] [[-tv;-sv;su;tu];[tv;sv]])) 				
	      end
	      | (false,true) -> begin 
		  let r1 = myConflict 9 (literal_to_trm (-sv),literal_to_trm sv) in
		  let r2 = Confront(literal_to_trm (-st),literal_to_trm uv,literal_to_trm su,literal_to_trm tu,literal_to_trm sv,literal_to_trm tv,r,r1) in
		  let r3 = if b1 then Trans(literal_to_trm (-st),literal_to_trm (-sv),literal_to_trm (-tv),r2) else r2 in
		  (if debug_Independent_refutation then Printf.printf  "apply_Con 12\n";(Cut(literal_to_trm (-sv),r3,r'),Dependency.diffunion h [d;d'] [[-tv;-sv;su;tu];[tv;sv]]) )	
	      end
	      | (false,false) -> begin
		  (if debug_Independent_refutation then Printf.printf  "apply_Con Independent_Refutation left(3)\n" ;
		   raise (Independent_Refutation(r',d') ) )				
	      end			
	end
	| (true,false) -> begin 
	    let (r',d') = try or_search [sv;tv] (Branch.reset b level) cl with Independent_Refutation(r,dep)-> (r,dep) in
	    if pftrm_Timeout && (!isTimeout) 
	    then (Confront(literal_to_trm (-st),literal_to_trm uv,literal_to_trm su,literal_to_trm tu,literal_to_trm sv,literal_to_trm tv, r, r'),Dependency.empty) 	
	    else
	      let [b5;b6] = Dependency.check d' [tv;sv] in
	      match (b5,b6) with
	      | (true,true) -> begin 
		  let r1 = myConflict 10 (literal_to_trm (-st),literal_to_trm st) in
		  if b1 then
		    let r2 = Confront(literal_to_trm (-st),literal_to_trm tv,literal_to_trm st,tt,literal_to_trm sv,literal_to_trm tv, r1, r') in
		    let r3 = if b2 then Trans(literal_to_trm (-st),literal_to_trm (-tv),literal_to_trm (-sv),r) else r in
		    (if debug_Independent_refutation then Printf.printf  "apply_Con 13\n";(Cut(literal_to_trm (-tv),r3,r2),Dependency.diffunion h [d;d'] [[-tv;-sv;su;tu];[tv;sv]]) 	)
		  else 
		    let r2 = Confront(literal_to_trm (-st),literal_to_trm sv,ss,literal_to_trm st,literal_to_trm sv,literal_to_trm tv, r1, r') in
		    (if debug_Independent_refutation then  Printf.printf  "apply_Con 14\n";(Cut(literal_to_trm (-sv),r,r2),Dependency.diffunion h [d;d'] [[-tv;-sv;su;tu];[tv;sv]]) ) 				
	      end
	      | (true,false) -> begin 
		  let r1 = if b2 then Trans(literal_to_trm (-st),literal_to_trm (-tv),literal_to_trm (-sv),r) else r in
		  (if debug_Independent_refutation then  Printf.printf  "apply_Con 15\n";(Cut(literal_to_trm (-tv),r1,r'),Dependency.diffunion h [d;d'] [[-tv;-sv;su;tu];[tv;sv]]) ) 				
	      end
	      | (false,true) -> begin 
		  let r1 = if b1 then Trans(literal_to_trm (-st),literal_to_trm (-sv),literal_to_trm (-tv),r) else r in
		  (if debug_Independent_refutation then  Printf.printf  "apply_Con 16\n";(Cut(literal_to_trm (-sv),r1,r'),Dependency.diffunion h [d;d'] [[-tv;-sv;su;tu];[tv;sv]]) )	
	      end
	      | (false,false) -> begin 
		  (if debug_Independent_refutation then Printf.printf  "apply_Con Independent_Refutation left(3)\n" ;
		   raise (Independent_Refutation(r',d') ) )				
	      end			
	end
	| (false,true) -> begin 
	    let (r',d') =   try or_search [-tu;-su;tv;sv] (Branch.reset b level) cl with Independent_Refutation(r,dep)-> (r,dep) in
	    if pftrm_Timeout && (!isTimeout) 
	    then (Confront(literal_to_trm (-st),literal_to_trm uv,literal_to_trm su,literal_to_trm tu,literal_to_trm sv,literal_to_trm tv, r, r'),Dependency.empty) 
	    else	
	      let [b1;b2;b5;b6] = Dependency.check d' [-tu;-su;tv;sv] in
	      match (b1 || b2,b5 || b6) with
	      | (true,true) -> begin 
		  let r1 = myConflict 11 (literal_to_trm (-st),literal_to_trm st) in
		  if b3 then
		    let r2 = if b4 then 
		      Confront(literal_to_trm (-st),literal_to_trm tu,literal_to_trm st,tt,literal_to_trm su,literal_to_trm tu, r1, r) 
		    else r in
		    let r3 = myConflict 12 (literal_to_trm (-tu),literal_to_trm tu)  in
		    let r4 = Confront(literal_to_trm (-st),literal_to_trm tu,literal_to_trm su,literal_to_trm tu,literal_to_trm sv,literal_to_trm tv,r3,r') in
		    let r5 = if b2 then Trans(literal_to_trm (-st),literal_to_trm (-tu),literal_to_trm (-su),r4) else r4 in
		    (if debug_Independent_refutation then  Printf.printf  "apply_Con 17\n";(Cut(literal_to_trm (-tu),r5,r2),Dependency.diffunion h [d;d'] [[-tv;-sv;su;tu];[tv;sv]]) )	
		  else 
		    let r2 = r in
		    let r3 = myConflict 13 (literal_to_trm (-su),literal_to_trm su) in
		    let r4 = Confront(literal_to_trm (-st),literal_to_trm uv,literal_to_trm su,literal_to_trm tu,literal_to_trm sv,literal_to_trm tv,r3,r') in
		    let r5 = if b1 then Trans(literal_to_trm (-st),literal_to_trm (-su),literal_to_trm (-tu),r4) else r4 in
		    ( if debug_Independent_refutation then Printf.printf  "apply_Con 18\n";(Cut(literal_to_trm (-su),r5,r2),Dependency.diffunion h [d;d'] [[-tv;-sv;su;tu];[tv;sv]])	)		
	      end
	      | (true,false) -> begin 
		  if b3 then
		    let r1 = myConflict 14 (literal_to_trm (-st),literal_to_trm st) in
		    let r2 = if b4 then Confront(literal_to_trm (-st),literal_to_trm tu,literal_to_trm st,tt,literal_to_trm su,literal_to_trm tu, r1, r) else r in
		    let r3 = if b2 then Trans(literal_to_trm (-st),literal_to_trm (-tu),literal_to_trm (-su),r') else r' in
		    if debug_Independent_refutation then Printf.printf  "apply_Con 19\n";(Cut(literal_to_trm (-tu),r3,r2),Dependency.diffunion h [d;d'] [[su;tu];[-tu;-su;tv;sv]])
		  else
		    let r1 = if b1 then Trans(literal_to_trm (-st),literal_to_trm (-su),literal_to_trm (-tu),r') else r' in
		    if debug_Independent_refutation then  Printf.printf  "apply_Con 20\n";(Cut(literal_to_trm (-su),r1,r),Dependency.diffunion h [d;d'] [[su;tu];[-tu;-su;tv;sv]])
	      end
	      | (false,true) -> begin 
		  (if debug_Independent_refutation then  Printf.printf  "apply_Con 21\n";(Confront(literal_to_trm(-st),literal_to_trm uv,literal_to_trm su,literal_to_trm tu,literal_to_trm sv,literal_to_trm tv,r,r'),Dependency.diffunion h [d;d'] [[su;tu];[tv;sv]]) )
	      end
	      | (false,false) -> begin 
		  (if debug_Independent_refutation then Printf.printf  "apply_Con Independent_Refutation \n" ;
		   raise (Independent_Refutation(r',d') ) )				
	      end
	end	
	| (false,false) -> begin 
	    (if debug_Independent_refutation then Printf.printf  "apply_Con Independent_Refutation \n" ;
	     raise (Independent_Refutation(r,d) ) )		
	end
  end

(** Semantic branching for Mating and Decomposition
	Input: Branch b, step list sl, alternatives alts, principal formulae pf, boolean mdf (true-> mating| false-> decomposition)
	Invariant: pf = [p s1 .. sn; ~ p t1 .. tn] or [p s1 .. sn <> p t1 .. tn] and alts = [[s1 <> t1]; ..; [sn <> tn]]
	Output: refutation for the branch and the corresponding dependency.
	Throws Independent_Refutation, if a subrefutation does not depend on the mating/decomposition step **)
and apply_mat b sl alts pf mdf = 
	let level = Branch.next_level b in
	
	(* helper function rec_apply:
		Input: (Literal * Refutation * Dependency) list lrdl, side formulae list sfs, DependencyGraph dg, (Refutation,Dependency) option rdo 
		Invariant: all literals are positive, sfs has no duplicates and
			for every entry (l,r,d) in lrdl, dg contains edges (l,l') for every l'  r depends on 
		Output: lrdl with an entry for every l in sfs and dg defines an partial ordering on sfs 
			rdo = some(r,d), where r depends only on Cuts, | None otherwise *)
	let rec rec_apply lrdl sfs dg rdo =
	match sfs with
	| [] -> (if debug_semantic then Printf.printf  "rec_apply: done\n");(lrdl,dg,rdo)
	| (l::sfr) -> begin
	(if debug_semantic then Printf.printf  "rec_apply: l = %d\n" l );
	(* Get the literals fls, whose refutations are either not computed yet or do not depend on l*)
	let fls = Dgraph.get_not_smaller dg l in (* return positive literals *)
	(if debug_semantic then Printf.printf  "rec_apply: fls = [%s]\n" (List.fold_left (fun a sf -> a ^ "," ^string_of_int sf ) "" fls ));
	(* call Or_Search to get refutation for one alternative with the added cut literals fls *)
	let (r,dep) = try or_search ((-l)::fls) (Branch.reset b level) sl  
		with Independent_Refutation(r,dep)-> (r,dep) in
	(* get the literals in fls that where used by the subrefutation*)	
	let dfl = List.filter (fun fl -> Dependency.mem fl dep) fls in
	(if debug_semantic then Printf.printf  "rec_apply: dfl = [%s]\n" (List.fold_left (fun a sf -> a ^ "," ^string_of_int sf ) "" dfl ));
	if Dependency.mem (-l) dep 
	then (* the side formula was used *)
		(* add new edges to the graph *)
		let dg = Dgraph.update dg l dfl in
		(if debug_semantic then Printf.printf  "rec_apply: %d is in dependency\n" l );
		(* recursively continue for the remaining alternatives*)
		rec_apply ((l,(r,dep))::lrdl) sfr  dg rdo
	else (* the alternative was not used *)
		match dfl with
		| [] ->	(* ...as where the cut literals -> Independent refutation*)
			(if debug_Independent_refutation then Printf.printf  "apply_mat Independent_Refutation\n" ;
			raise (Independent_Refutation(r,dep) ) )
		| _ ->	(* ...but some cut literals were used *)
			begin
			(* save the refutation in rdo*)
			let rdo = Some(r,dep) in
			(* we will only need refutations for the cut literals ->
				we reset the dgraph and throw away refutations that do not exclusivly depend on the cut literals*)
			let (ll,dg) = Dgraph.reset dg dfl in
			let sfs = List.filter (fun df -> not (List.mem df ll) ) dfl in
			let lrdl = List.filter (fun (l,_) -> List.mem l ll) lrdl in
			(* this is now a restart of rec_apply*)
			rec_apply lrdl sfs dg rdo
			end		
	end in	
	
	(* extract sideformulae and drop those that would already close the branch*)
	let sfs = List.filter (fun sf -> not (Branch.mem sf b || Branch.is_taut sf)) (List.map (fun alt -> -List.hd alt ) alts) in
	(if debug_semantic then Printf.printf  "sfs = [%s]\n" (List.fold_left (fun a sf -> a ^ "," ^string_of_int sf ) "" sfs ));
	(* also remove duplicates, but save them in another list - enforcing a cut on them will avoid duplicated subrefutations *)
	let (sfs,double) = List.fold_left (fun (sfr,doub) sf -> if List.mem sf sfr then if List.mem sf doub then (sfr,doub) else (sfr,sf::doub) else (sf::sfr,doub) ) ([],[]) sfs in
	(* initialize Dgraph*)
	let dg = Dgraph.make double sfs in
	(* call to rec_apply - returns necessary refutations and the order for the cuts*)
	let (lrdl,dg,rdo) = rec_apply [] sfs dg None in
	(* construct base refutation*)
	let (r,dep,dg) = 
		match rdo with
		| Some(r,d)-> (* rec_apply found a refutation that does not depend on a side formula -> use it as base *)
			(if debug_semantic then Printf.printf  "apply_mat: some partly indep. refutation\n" );(r,d,dg)
		| None -> (* normal case: construct the mating/decomposition step at the base of the semantic branching step *)
			begin
			let (ll,dg) = Dgraph.minimals dg in
			(if debug_semantic then Printf.printf  "apply_mat: minimals = [%s]\n" (List.fold_left (fun a sf -> a ^ "," ^string_of_int sf ) "" ll ));
			let rds = List.map (fun a-> 
				let l = -List.hd a in
				(if debug_semantic then Printf.printf  "apply_mat: l = %d\n" l );				
				if List.mem l ll 
				then (* sideformulae that do not need to be cut get their refutations inserted directly*)
				try  List.assoc l lrdl with Not_found -> failwith "no ref for l"
				else  (* all others are closed by conflict with their cut *)
				(myConflict 15 (literal_to_trm l,literal_to_trm (-l)),Dependency.make [l;-l]) ) alts in
			let (rs,ds) = List.split rds in
			let dep = Dependency.diffunion pf ds alts in
			(* mdf = true -> mating | false -> decomposition *)
			if mdf then (Mating(literal_to_trm  (List.nth pf 0),literal_to_trm  (List.nth pf 1),
					List.map (fun alt -> literal_to_trm (List.hd alt) ) alts,rs),dep,dg)
			else (Decomposition(literal_to_trm  (List.nth pf 0),
					List.map (fun alt -> literal_to_trm (List.hd alt) ) alts,rs),dep,dg)		
			end
		in
	(* build chain of cuts from bottom to top in the order given by the DependencyGraph *)
	List.fold_left 
		(fun (r1,d1) l -> 
			let (r2,d2) = try List.assoc l lrdl with Not_found -> failwith ("no ref for "^ (string_of_int l) ^" 2") in
			let r' = Cut(literal_to_trm l,r1,r2) in
			let dep' = Dependency.diffunion [] [d1;d2] [[l];[-l]] in
			(r',dep') ) 
		(r,dep) (Dgraph.minlist dg)	

	

(** SEARCH **)


(**	Input: Branch b, Step c, List of Steps sl 
	Invariant: c is a suitable step that was chosen by get_next_step
	Output: a refutation, dependency pair for the current branch b**)
and and_search b c sl  =
	let br = Step.get_branches c in
	let h = Step.get_head c in
	try 
	(* If the step cannot be applied one of the principal formulae is not on the branch *)
	let cutlit = List.find (fun l -> not (Branch.mem l b) ) h in
	if debug_search then Printf.printf  "apply CUT(2) %d\n" cutlit; 
	let (r1::r2::rs,con)= apply_rule b sl ([-(abs cutlit)]::[[abs cutlit]]) []  in 
	(* -> we cut on the missing formula*)
	(Cut( literal_to_trm (abs cutlit) , r2, r1),con)
	with Not_found -> (* otherwise we apply the step*)
	begin
	if debug_search then Printf.printf  "apply %s on %s\n" (Step.rule_to_str (Step.get_rule c)) (String.concat "," (List.map string_of_int h)) ;
	(* we first try semantic branching incase of implication, confrontation, mating or decomposition *)
	match Step.get_rule c with
	| Step.IMP -> 
		let head = List.hd h in
		let [[s];[t]] = br in
		if (get_bool_flag "PFTRM_REMOVE_INDEPENDENT") && pftrm_Independent_refutation && pftrm_semantic_imp	
			then	apply_Imp b head s t sl 
			else 	let (r1::r2::rs,con) = apply_rule b sl br h in
            		(Implication(literal_to_trm head,literal_to_trm s,literal_to_trm t, r1, r2),con)
	| Step.CON ->
		let  h1 =literal_to_trm (List.hd h) in
        	let  h2 =literal_to_trm (List.hd (List.tl h)) in
		let [[su;tu];[sv;tv]] = br in
		if (get_bool_flag "PFTRM_REMOVE_INDEPENDENT") && pftrm_Independent_refutation && pftrm_semantic_con	
		then
		  apply_Con b sl br h
		else
 		  let (r1::r2::rs,con) = apply_rule b sl br h  in
		  (Confront(h1,h2,literal_to_trm su,literal_to_trm tu,literal_to_trm sv,literal_to_trm tv, r1, r2),con)
	| Step.MAT ->
		if (get_bool_flag "PFTRM_REMOVE_INDEPENDENT") && pftrm_Independent_refutation && pftrm_semantic_mat_dec	
		then	apply_mat b sl br h true
		else   
		let (r,con) = apply_rule b sl br h  in
		let  [h1;h2] =h in
            	let  ss =  List.map (fun ls -> literal_to_trm (List.hd ls) ) br  in
	    	(Mating(literal_to_trm h1,literal_to_trm h2,ss , r),con)       
	| Step.DEC ->  
		if (get_bool_flag "PFTRM_REMOVE_INDEPENDENT") && pftrm_Independent_refutation && pftrm_semantic_mat_dec	
		then	apply_mat b sl br h false
		else
		let (r,con) = apply_rule b sl br h  in
		let h = literal_to_trm (List.hd h) in
		let ss = List.map (fun ls -> literal_to_trm (List.hd ls) ) br in	
		(Decomposition(h,ss,r),con) 
	| _ ->	begin 
	 (* otherwise we simply apply the syntactic rule  *)
	let (r,con) = apply_rule b sl br h   in

   	match Step.get_rule c with
	| Step.IMP -> 
		let head = List.hd h in
		let [[s];[t]] = br in
		let r1::r2::rs = r in
            	(Implication(literal_to_trm head,literal_to_trm s,literal_to_trm t, r1, r2),con) 
	| Step.NIMP -> 
		let h = literal_to_trm (List.hd h) in
		let [[s;t]] = br in
		let r1::rs = r in
		(NegImplication(h,literal_to_trm s,literal_to_trm t,r1),con)
	| Step.ALL(a,m,n) -> 
		let h = literal_to_trm (List.hd h) in
		let [[s]] = br in
		let r1::rs = r in
            	(All(h,literal_to_trm s,r1,a,m,n),con) 
	| Step.NALL(a,m,x) -> 
		if assert_freshness && List.exists (fun t -> List.mem x (Step.trm_free_variable (literal_to_trm t)))(Branch.elements b ) 
		then failwith "found freshness violation "  ; 
		let head = literal_to_trm (List.hd h) in
		let [[s]] = br in
		let r1::rs = r  in
            	(NegAll(head,literal_to_trm s,r1,a,m,x),con)  
	| Step.MAT ->  
		let  [h1;h2] =h in
            	let  ss =  List.map (fun ls -> literal_to_trm (List.hd ls) ) br  in
	    	(Mating(literal_to_trm h1,literal_to_trm h2,ss , r),con)       
	| Step.DEC ->  
		let h = literal_to_trm (List.hd h) in
		let ss = List.map (fun ls -> literal_to_trm (List.hd ls) ) br in	
		(Decomposition(h,ss,r),con) 
	| Step.CON ->
		let  h1 =literal_to_trm (List.hd h) in
        	let  h2 =literal_to_trm (List.hd (List.tl h)) in
		let [[su;tu];[sv;tv]] = br in
		let r1::r2::rs = r in
		(Confront(h1,h2,literal_to_trm su,literal_to_trm tu,literal_to_trm sv,literal_to_trm tv, r1, r2),con) 
	| Step.BE -> 
		let h =literal_to_trm (List.hd h) in	
		let [[s;_];[_;t]] = br in
		let r1::r2::rs = r in
		(NegEqualProp(h,literal_to_trm s,literal_to_trm t, r1, r2),con)  
	| Step.BQ ->  
		let h =literal_to_trm (List.hd h) in	
		let [[s;t];[_;_]] = br in
		let r1::r2::rs = r in
		(EqualProp(h,literal_to_trm s,literal_to_trm t, r1, r2),con)  
	| Step.FE -> 
		let h = literal_to_trm (List.hd h) in
		let s = literal_to_trm (List.hd (List.hd br)) in
		let r1::rs = r in
            	(NegEqualFunc(h, s, r1),con)
	| Step.FQ ->  
		let h = literal_to_trm (List.hd h) in
		let s = literal_to_trm (List.hd (List.hd br)) in
		let r1::rs = r in
            	(EqualFunc(h, s, r1),con)
	| Step.EPS(eps,pred) -> 
		let [[empty];[choice]] = br in
		let r1::r2::rs = r in
		(ChoiceR(eps,pred,literal_to_trm empty,literal_to_trm choice,r1, r2 ),con) 
	| Step.CUT ->
		let [_;[h]] = br in
		let r1::r2::rs = r in
		(Cut( literal_to_trm h , r2, r1),con)
	| Step.KNOWN(s,name,al) ->
	    let [[kn]] = br in
	    let r1::rs = r in
	    (KnownResult(s,name,al,r1),con)
	end
	end          
        
(** Input: a branch b and a list of steps cl 
	Output: a refutation, dependency pair for the current branch b**)
and or_search1 b cl  =
	(* Timeout check *)
	if pftrm_Timeout && !timeout < Sys.time() -. !beforeSearch then(isTimeout:=true; (Timeout,Dependency.empty)) 
	else
	(* remove satisfied steps from cl *)
	let cl = remove_satisfied_steps b cl  in  if debug_search then Printf.printf  "remove satisfied clauses done %d\n" (List.length cl); 
		(* choose he next step to be applied on b *)
		let c = get_next_step b cl  in
		if debug_search then Printf.printf  "apply next clause %f %d\n"  (Sys.time() -. !beforeSearch) (List.length cl) ; 
		and_search b c cl 

(** Input: List of literals ls, a branch b and a list of steps cl
	Adds the literals one by one to the branch. Continues with or_search1 if the branch is still open  
	Output: a refutation, dependency pair for the current branch b**)
and or_search ls b cl  = 
  match ls with
    | [] -> or_search1 b cl  
    | (l::lr) ->
	try Branch.add b l;or_search lr b cl  
	with Branch.Closed(r,c) ->(r,c)

 (* checks whether some subterm of m can be rewritten into a primitive equation 
 Output: (p,s,t,a) - where s =_a t and p s == m  *) 
let rec leibeq_to_primeq2 m n =
try
   is_an_eqn_p m n
with Not_found ->
    begin
	match m with
		| Ap(m1,m2) ->begin  if debug_leibeq then Printf.printf  "LEIBEQ Rewrite looks at %s \n" (trm_str m); 
     			try let (pre,pt,pt',stp)= leibeq_to_primeq2 m1 n in 
      				(Ap(pre,m2),pt,pt',stp) 
      			with Not_found -> let (pre,pt,pt',stp)= leibeq_to_primeq2 m2 n in 
        			(Ap(m1,pre),pt,pt',stp) end
  		| Lam(a1,m1) ->if debug_leibeq then Printf.printf  "LEIBEQ Rewrite looks at %s \n" (trm_str m);
    			let (pre,pt,pt',stp)= leibeq_to_primeq2 m1 (n+1) in 
    			(Lam(a1,pre),pt,pt',stp) 
		| _ -> raise Not_found
    end


(** Rewrites every occurence of leibniz equality or similar propeties in the branch b into primitive equality before starting the search
	Output: a refutation, dependency pair for the current branch b**)
and leibeq_to_primeq b sl =
	let rec leibeq_to_primeq1 b' b = match b' with
		| [] -> begin 
			try or_search [] b sl with Independent_Refutation(r,con)-> (r,con) end
		| (m::br) -> try
				(* look for possible rewrite in m*)
    			let (pre,pt,pt',stp)= leibeq_to_primeq2 (literal_to_trm m) 0 in
    			let prefix= Lam(stp,pre) in
    			let ptrm' =get_literal (norm name_def (Ap(prefix,pt'))) in
			begin
			try 
			(* add rewritten formula to the branch*)
			let b' = (Branch.add b ptrm';ptrm'::br) in
  			if debug_leibeq then Printf.printf  "LEIBEQ Rewrite %d into %d \n" m ptrm';
			(* try to rewrite the new formula further*)
			let (r,con) =try leibeq_to_primeq1  b' b 
							with Independent_Refutation(r,con)-> (r,con) in
			(* Dependency check*)
			if (get_bool_flag "PFTRM_REMOVE_INDEPENDENT") && pftrm_Independent_refutation  && not (Dependency.mem ptrm' con)
				then ( if debug_Independent_refutation then Printf.printf  "found Independent leibeq refutation\n";
				raise (Independent_Refutation(r,con)) )
			else 
  			(Rewrite(prefix,pt,pt',r),Dependency.diffunion [m] [con] [[ptrm']])
			with (* Branch closed by new formula? *)
			| Branch.Closed(r,c) -> (Rewrite(prefix,pt,pt',r),Dependency.diffunion [m] [c] [[ptrm']]) end
			with	(* no further rewrite possible -> continue with next formula*)
			| Not_found -> if debug_leibeq then Printf.printf  "LEIBEQ couldn't Rewrite %d \n" m;
					leibeq_to_primeq1  br b  
	in 
	leibeq_to_primeq1 (Branch.elements b) b

(** Process Refut **) 

(** Input: Branch b and refut r
	Output: a refutation, dependency pair for the current branch b
	Turns the refut steps into refutation steps**)
let rec process_refut1 b r =  
  match r with 
  | SearchR(cl,cr) ->  if debug_search then Printf.printf  "starting SearchR with branch %s\n" (List.fold_right (fun l s -> (string_of_int l) ^ " " ^ s) (Branch.elements b) "");
	(* Preprocess clauses*)
	let sl = preprocess_clauses cl cr in 
	(* depending on flag setting rewrite leibniz equations into primitive equations*)
	if (get_bool_flag "LEIBEQ_TO_PRIMEQ") then
    	  leibeq_to_primeq b sl 
  	else
	  or_search [] b sl 
        
  | NegImpR(m,n,r1) -> if debug_search then Printf.printf  "apply NegImpR\n";
    	let h = (normneg (imp m n)) in
    	let s = m in let t = (normneg n) in
	let s' = get_literal s in let t'= get_literal t in
	let (r,con)= try process_refut [s';t'] b r1 with Independent_Refutation(r,con)-> (r,con) in
(**	if debug_search then Printf.printf "con dependencies after recursive call from NegImpR:\n%s\n" (List.fold_right (fun z r -> r ^ (string_of_int z) ^ "\n") (Dependency.elements con) ""); **)
	if (get_bool_flag "PFTRM_REMOVE_INDEPENDENT") && pftrm_Independent_refutation  && not (Dependency.mem s' con || Dependency.mem t' con ) then
		( if debug_Independent_refutation then Printf.printf  "found Independent refutation\n";
		 raise (Independent_Refutation(r,con)) )
	else 
	let con = Dependency.diffunion [get_literal h] [con] [[s';t']] in
    	(NegImplication(h,s,t,r),con)

  | ImpR(m,n,r1,r2) -> if debug_search then Printf.printf  "apply ImpR\n";
	let l = Branch.next_level b in
    	let h =  (imp m n) in
    	let s =  (normneg m) in let t = n in
	let s' = get_literal s in let t'= get_literal t in
    	let (r,con)=try process_refut [s'] b r1 
					with Independent_Refutation(r,con)-> (r,con) in
(**	if debug_search then Printf.printf "con dependencies after first recursive call from ImpR:\n%s\n" (List.fold_right (fun z r -> r ^ (string_of_int z) ^ "\n") (Dependency.elements con) ""); **)
	if (get_bool_flag "PFTRM_REMOVE_INDEPENDENT") && pftrm_Independent_refutation  && not (Dependency.mem s' con) then
		( if debug_Independent_refutation then Printf.printf  "found Independent refutation\n";
			raise (Independent_Refutation(r,con)) )
	else 
   	let (r',con')= try process_refut [t'] (Branch.reset b l) r2 
						with Independent_Refutation(r,con)-> (r,con) in
(**	if debug_search then Printf.printf "con dependencies after second recursive call from ImpR:\n%s\n" (List.fold_right (fun z r -> r ^ (string_of_int z) ^ "\n") (Dependency.elements con') ""); **)
	if (get_bool_flag "PFTRM_REMOVE_INDEPENDENT") && pftrm_Independent_refutation  && not (Dependency.mem t' con') then
		( if debug_Independent_refutation then Printf.printf  "found Independent refutation\n";
			raise (Independent_Refutation(r',con')) )
	else 
	let con = Dependency.diffunion [get_literal h] [con;con'] [[s'];[t']]  in
   	(Implication(h,s,t,r ,r'),con)

  | FalseR ->  if debug_search then Printf.printf  "apply FalseR\n"; (Fal(False),Dependency.make [get_literal False])

  | NegReflR -> if debug_search then Printf.printf  "apply NegReflR \n";
	let h = List.find (fun t -> match (literal_to_trm t) with 
                                     		| Ap(Ap(Imp,Ap(Ap(Eq(_),s),t)),False)->  s = t
                                     		| _ -> false ) (Branch.elements b) in
	(NegRefl(literal_to_trm h),Dependency.make [h]) 

  | NegAllR(a,m,x,r1) -> if debug_search then Printf.printf  "apply NegAllR with branch %s\n" (List.fold_right (fun l s -> (string_of_int l) ^ " " ^ s) (Branch.elements b) "");
    	let h = (normneg (Ap(Forall(a),m))) in 
    	let s = (norm name_def (normneg (Ap(m,Name(x,a)))) ) in 
	let s' = get_literal s in
	let (r,con)=try process_refut [s'] b r1 with Independent_Refutation(r,con)-> (r,con) in
	if (get_bool_flag "PFTRM_REMOVE_INDEPENDENT") && pftrm_Independent_refutation  && not (Dependency.mem s' con) && (match (choiceop_axiom s) with Some _ -> false | None -> true)  then (*** Chad, Aug 2011, never throw away a proposition stating something is a choice operator. ***)
		( if debug_Independent_refutation then Printf.printf  "found Independent refutation\n";
			raise (Independent_Refutation(r,con)) )
	else 
	let con = Dependency.diffunion [get_literal h] [con] [[s']] in
    	(NegAll(h,s,r,a,m,x),con)

  | EqFR(a,a',s,t,r1) ->   if debug_search then Printf.printf  "apply EqFR\n";
    	let h =  (eq (Ar(a,a')) s t) in
    	let m = (norm name_def (forall a (eq a' (Ap(s,DB(0,a))) (Ap(t,DB(0,a))) ))) in
	let s' = get_literal m in
	let (r,con)=try process_refut [s'] b r1 with Independent_Refutation(r,con)-> (r,con) in
	if (get_bool_flag "PFTRM_REMOVE_INDEPENDENT") && pftrm_Independent_refutation  && not (Dependency.mem s' con) then
		( if debug_Independent_refutation then Printf.printf  "found Independent refutation\n";
			raise (Independent_Refutation(r,con)) )
	else 
	let con = Dependency.diffunion [get_literal h] [con] [[s']] in
    	(EqualFunc(h,m,r),con)

  | NegEqFR(a,a',s,t,r1) -> if debug_search then Printf.printf  "apply NegEqFR\n";
    	let h = neg (eq (Ar(a,a')) s t) in
    	let m = normneg (norm name_def (forall a (eq a' (Ap(s,DB(0,a))) (Ap(t,DB(0,a))) ))) in
	let s' = get_literal m in
	let (r,con)=try process_refut [s'] b r1 with Independent_Refutation(r,con)-> (r,con) in
	if (get_bool_flag "PFTRM_REMOVE_INDEPENDENT") && pftrm_Independent_refutation  && not (Dependency.mem s' con) then
		( if debug_Independent_refutation then Printf.printf  "found Independent refutation\n";
			raise (Independent_Refutation(r,con)) )
	else 
	let con = Dependency.diffunion [get_literal h] [con] [[s']] in
    	(NegEqualFunc(h,m,r),con)  

  | EqOR(s,t,r1,r2) -> if debug_search then Printf.printf  "apply EqOR\n";
	let l = Branch.next_level b in
    	let h =  (eq Prop s t) in
    	let ns =  (normneg s) in let nt =  (normneg t) in
	let s' = get_literal s in let t'= get_literal t in
	let ns' = get_literal ns in let nt'= get_literal nt in
	let (r,con)= try process_refut [s';t'] b r1 with Independent_Refutation(r,con)-> (r,con) in
	if (get_bool_flag "PFTRM_REMOVE_INDEPENDENT") && pftrm_Independent_refutation  && not (Dependency.mem s' con || Dependency.mem t' con) then
		( if debug_Independent_refutation then Printf.printf  "found Independent refutation\n";
			raise (Independent_Refutation(r,con)) )
	else 
	let (r',con')=try process_refut [ns';nt'] (Branch.reset b l) r2 
						with Independent_Refutation(r,con)-> (r,con)in
	if (get_bool_flag "PFTRM_REMOVE_INDEPENDENT") && pftrm_Independent_refutation  && not (Dependency.mem ns' con' || Dependency.mem nt' con') then
		( if debug_Independent_refutation then Printf.printf  "found Independent refutation\n";
			raise (Independent_Refutation(r',con')) )
	else 
	let con = Dependency.diffunion [get_literal h] [con;con'] [[s';t'];[ns';nt']] in
     	(EqualProp(h,s,t,r,r'),con)

  | NegEqOR(s,t,r1,r2) -> if debug_search then Printf.printf  "apply NegEqOR\n";
	let l = Branch.next_level b in
    	let h =  neg(eq Prop s t) in
    	let ns =  (normneg s) in let nt =  (normneg t) in
	let s' = get_literal s in let t'= get_literal t in
	let ns' = get_literal ns in let nt'= get_literal nt in
	let (r,con)=try process_refut [s';nt'] b r1 
					with Independent_Refutation(r,con)-> (r,con) in
	if (get_bool_flag "PFTRM_REMOVE_INDEPENDENT") && pftrm_Independent_refutation  && not (Dependency.mem s' con || Dependency.mem nt' con) then
		( if debug_Independent_refutation then Printf.printf  "found Independent refutation\n";
			raise (Independent_Refutation(r,con)) )
	else 
	let (r',con')=try  process_refut [ns';t'] (Branch.reset b l) r2 
						with Independent_Refutation(r,con)-> (r,con) in
	if (get_bool_flag "PFTRM_REMOVE_INDEPENDENT") && pftrm_Independent_refutation  && not (Dependency.mem ns' con' || Dependency.mem t' con') then
		( if debug_Independent_refutation then Printf.printf  "found Independent refutation\n";
			raise (Independent_Refutation(r',con')) )
	else 
	let con = Dependency.diffunion [get_literal h] [con;con'] [[s';nt'];[ns';t']] in
     	(NegEqualProp(h,s,t,r,r'),con) 

  | AssumptionConflictR -> 
		if (get_bool_flag "LEIBEQ_TO_PRIMEQ") then
	    	leibeq_to_primeq b []
  		else or_search (Branch.elements b) b [] 
			
  | _ ->   failwith "unknown refut case"
    

(** Input: List of literals ls, Branch b and refut r
	Invariant: 	intersection(ls,b)={}
	Output: a refutation, dependency pair for the current branch b
	 Adds new literals to the branch and checks wether the branch is still open **)
and process_refut ls b r = 
  match ls with
    | [] -> process_refut1 b r
    | (l::lr) ->try Branch.add b l;process_refut lr b r   
			with Branch.Closed(r,c) ->(r,c)

(** Input: List of assumptions ls and refut r
	Invariant: refut r is a pseudo refutation produced by Satallax
	Output: a refutation, dependency pair for the assumptions, search time and wether timeout was reached. **)
let search_refutation ls r = 
  beforeSearch := Sys.time() ;
  let (r,dep) = try process_refut ls (Branch.make ()) r with Independent_Refutation(r,con)-> (r,con) in
  let searchTime= int_of_float ((Sys.time() -. !beforeSearch) *. 1000.0) in
	(r,dep,searchTime,!isTimeout)
