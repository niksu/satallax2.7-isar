open Flags
open State
open Search
open String
open Syntax
open Refutation

let vold = 2
let vlat = 2
let beforeSearch = ref 0.0
let timeout = ref 60.0
let isTimeout = ref false 
let debug_heuristic = false
let debug_litcount = false
let debug_translation = false
let debug_rewrite = false
let debug_search = false
let debug_add_clauses = false
let debug_free_names = false
let debug_leibeq = false
let debug_Independent_refutation = false
let assert_freshness = false
let assert_condition = false
let result_print_search = false
let result_print_translation = false
let result_latex = false
let result_statistic = false
let result_coq = true
let result_print_coq_type = true
let pftrm_heuristic = false (* does nothing*)
let pftrm_add_Cuts = false
let pftrm_semantic = true
let pftrm_litcount = true
let pftrm_Timeout = true
let pftrm_add_clauses = true
let pftrm_Independent_refutation =  true
let pftrm_rewrite_first = false (* false => rewrite_last*)


type refutation =
   Conflict of trm * trm
 | Fal of trm
 | NegRefl of trm
 | Implication of trm * trm * trm * refutation * refutation  
 | Disjunction of trm * trm * trm * refutation * refutation
 | NegConjunction of trm * trm * trm * refutation * refutation  
 | NegImplication of trm * trm * trm * refutation
 | Conjunction of trm * trm * trm * refutation 
 | NegDisjunction of trm * trm * trm * refutation 
 | All of trm * trm * refutation * stp * trm *trm
 | NegAll of trm * trm * refutation * stp * trm * string
 | Exist of trm * trm * refutation * stp * trm * string
 | NegExist of trm * trm * refutation * stp * trm *trm
 | Mating of trm * trm * trm list * refutation list
 | Decomposition of trm * trm list * refutation list 
 | Confront of trm * trm * trm * trm * trm * trm * refutation * refutation 
 | NegEqualProp of trm * trm * trm * refutation * refutation
 | EqualProp of trm * trm * trm * refutation * refutation
 | NegAequivalenz of trm * trm * trm * refutation * refutation
 | Aequivalenz of trm * trm * trm * refutation * refutation
 | NegEqualFunc of trm * trm * refutation
 | EqualFunc of trm * trm * refutation
 | ChoiceR of trm * trm * trm * trm * refutation * refutation (* TODO use choiceop_axiom later *)
 | Cut of trm * refutation * refutation     
 | DoubleNegation of trm * trm * refutation  
 | Rewrite of trm * trm * trm * refutation  (* TODO: handle DB indices + Coq tactic Change*)
 | Delta of trm * trm * string * refutation
 | NYI of trm * trm * refutation   
 | Timeout 

module LitCount =
	struct
	type t = (int array) * (int array)
	let make n = (Array.make n 0,Array.make n 0)
	let copy (p,n) = (Array.copy p ,Array.copy n)
	let get (p,n) l =  if l > 0 then Array.get p l else Array.get n (-l)
	let put (p,n) l x = if l > 0 then Array.set p l x else Array.set n (-l) x
	let incr lc l = put lc l (get lc l + 1)
	let decr lc l = put lc l (if get lc l - 1 < 0 && debug_heuristic then Printf.printf "Literal %d removed too often" l;get lc l - 1  )
	let print (p,n) = Array.iteri (fun pos value ->if value+ Array.get p pos > 2 then Printf.printf "(%d:%d)" pos (value+ Array.get p pos) ) n
	let count (p,n) =  let c = ref 0 in (Array.iteri (fun pos value ->if value+ Array.get p pos > 0 then Pervasives.incr c ) n; !c )
	let get_lits (p,n) =  let lits = ref [] in (Array.iteri (fun pos value -> lits:= (pos,(value+ Array.get p pos))::!lits ) n; !lits)
	end;;

module OrderedInt =
   struct
     type t = int
     let compare = Pervasives.compare  
   end


module IntSet = Set.Make(OrderedInt)

module Branch =
	struct
	exception Closed of refutation * IntSet.t * int * int * int
	type history = Level of int | Add of int
	type t = (IntSet.t ref) * (history Stack.t) * (int ref)
	let make () = (ref IntSet.empty ,Stack.create (),ref 0) 
	let add (b,h,_) l = 
		let t = literal_to_trm l in  if debug_search then Printf.printf  "adding (%d) to the branch\n" l ;
		if t = False then (if debug_search then Printf.printf  "found False\n";raise (Closed (Fal(t),IntSet.singleton(l),1,1,1)))
                   else if begin  
                     		match t with 
                     		| Ap(Ap(Imp,Ap(Ap(Eq(_),s),t)),False) ->   s =  t 
                       		| _ -> false end 
                   		then (if debug_search then Printf.printf  "found NRefl\n";raise (Closed (NegRefl(t),IntSet.singleton(l),1,1,1)))
                   else 
		if IntSet.mem (-l) !b 
			then (if debug_search then Printf.printf  "found Conflict\n";
			raise (Closed (Conflict(literal_to_trm(abs l),literal_to_trm(-(abs l))),IntSet.add l (IntSet.singleton (-l)),1,1,1) ) )
		else if IntSet.mem l !b then ()
		else Stack.push (Add(l)) h; b:= IntSet.add l !b
	let is_taut l = let t = literal_to_trm (-l) in 
		if t = False then true
			else      match t with 
                     		| Ap(Ap(Imp,Ap(Ap(Eq(_),s),t)),False) ->   s =  t 
                       		| _ -> false 
	let mem  l (b,_,_) = IntSet.mem l !b
	let next_level (_,h,n) =  incr n ;Stack.push (Level(!n)) h; !n
	let reset (b,h,n') n = 
		let rec reset () = match Stack.pop h with
					| Level(m) -> if m = n then (n':=n; Stack.push (Level(n)) h;(b,h,n')) else reset ()
					| Add(l) ->  b:=IntSet.remove l !b; reset ()
		in reset ()
	let get_set (b,_,_) =  !b
	end 


exception Not_Implemented of string

module Step = struct
	type rule = IMP | NIMP | ALL of stp * trm * trm | NALL of stp * trm * string | MAT | DEC | CON | BE | BQ | FE | FQ | EPS of trm * trm | CUT
	type step = ((int list) * (int list list) * (string list) * rule) ref

	let rec trm_free_variable m = match m with
   	| Name(x,_) -> [x]
	| Lam(_,m1) -> trm_free_variable m1 
	| Ap(m1,m2) -> List.rev_append (trm_free_variable m1) (trm_free_variable m2) 
	| _ -> []    

	let rec free_variable c = match c with
	| (l::cr) -> let t = literal_to_trm (-l) in List.rev_append (trm_free_variable t) (free_variable cr)
	| [] -> []	
	
	let make_Cut l witnesses =
	let free = trm_free_variable (literal_to_trm l) in
	if debug_free_names then Printf.printf  "step has free %s \n" (String.concat "," free) ;
	let free = List.fold_left (fun f v -> if (not (List.mem v f)) && List.mem v witnesses then v::f else f) [] free in	
	ref ([],[[-l];[l]],free,CUT)  	
	
	let make c cr witnesses : step = 
	let free = free_variable c in
	if debug_free_names then Printf.printf  "step has free %s \n" (String.concat "," free) ;
	let free = List.fold_left (fun f v -> if (not (List.mem v f)) && List.mem v witnesses then v::f else f) [] free in	
	let (h,br,r) = match (cr c) with
  | NegPropRule(m) -> 
    begin 
  	let  head = [- List.hd c] in  
        match m with 
          | Ap(Ap(Imp,m1),m2) ->
		let (s,t) = (get_literal m1,get_literal m2) in 
		let  branches = [[s;-t]] in
		(head,branches,NIMP)
	  | Ap(Ap(Eq(Prop),x),y) ->
            	let  s = get_literal x in
            	let  t = get_literal y in 
		let branches = [[s;-t];[-s;t]] in
		(head,branches,BE)
	  | Ap(Ap(Eq(Base(_)),x),y) ->
            	let  ss = (List.tl c) in
		let branches = List.map (fun s -> [s]) ss in
		(head,branches,DEC)
          | Ap(Ap(Eq(Ar(_,_)),x),y) ->
            	let  s = List.hd (List.tl c) in
		let branches = [[s]] in
		(head,branches,FE)
          | _ ->  raise (Not_Implemented("can't handle yet term " ^ (trm_str m))) 
  	end
  | PosPropRule(m) -> 
    begin 
      let  head = [- List.hd c] in
        match m with 
          | Ap(Ap(Imp,_),_) ->
		let  s = List.hd (List.tl c) in
        	let  t = List.hd (List.tl (List.tl c)) in
		let branches = [[s];[t]] in
		(head,branches,IMP)
          | Ap(Ap(Eq(Prop),x),y) ->
            	let  s = get_literal x in
            	let  t = get_literal y in 
		let branches = [[s;t];[-s;-t]] in
		(head,branches,BQ)
          | Ap(Ap(Eq(Ar(_,_)),x),y) ->
            	let  s = List.hd (List.tl c) in
		let branches = [[s]] in
		(head,branches,FQ)
          | _ ->  raise (Not_Implemented("can't handle yet term " ^ (trm_str m)))  
    end
  | InstRule(a,m,n) -> 
    begin 
      	let  head = [- List.hd c] in    
	let  s = List.hd (List.tl c) in
	let branches = [[s]] in
	(head,branches,ALL(a,m,n))
    end
  | FreshRule(a,m,x) ->
    begin 
     	let  head = [- List.hd c] in
     	let  s = List.hd (List.tl c) in
	let branches = [[s]] in
	(head,branches,NALL(a,m,x))
    end
  | MatingRule(plit,nlit) ->  (* TODO use plti,nlit*)
    begin
	let head = [plit;nlit] in
      	let  ss = (List.tl (List.tl c)) in
	let branches = List.map (fun s -> [s]) ss in
	(head,branches,MAT)
    end
  | ConfrontationRule(plit,nlit) ->  (*  TODO Add all information at once*)
    begin 
	let (n,m)= (literal_to_trm plit,literal_to_trm (-nlit) ) in
	let head = [plit;nlit] in
		match (n,m) with
			| (  Ap(Ap(Eq(a),s),t)  ,  Ap(Ap(Eq(a'),u),v)  ) when a=a' -> begin
				let (su,tu,sv,tv)=(neg (eq a s u),neg (eq a t u),neg (eq a s v),neg (eq a t v)) in
				let (lsu,ltu,lsv,ltv) = (get_literal su,get_literal tu,get_literal sv,get_literal tv) in 
				let branches = [[lsu;ltu];[lsv;ltv]] in
				(head,branches,CON) end
			| _ -> raise (Not_Implemented("can't handle with Confrontation Rule: "^ (trm_str n) ^" and "^ (trm_str m) )) 
    end 
  | ChoiceRule(eps,pred) -> (*TODO consider eps = epsilon or name, choiceop_axiom*)
        let head = [] in
	let  s = List.hd c in
        let  t = List.hd (List.tl c) in
	let branches = [[t];[s]] in (* TODO switched the branches *)
	(head,branches,EPS(eps,pred))
  | ClauseRule(n, ns, ts) ->  raise (Not_Implemented("can't handle ClauseRule yet "))
	in
	if debug_free_names then Printf.printf  "step has witnesses %s \n" (String.concat "," free) ;
	let lits = (List.map (~-) h) @ (List.concat br ) in ref (h,br,free,r) 

	let get_head s = let (h,_,_,_) = !s in h
	let get_branches s = let  (_,b,_,_) = !s in b
	let get_free s = let (_,_,f,_) = !s in f 
	let get_rule s = let  (_,_,_,r) = !s in r 
	let rule_to_str r = match r with   IMP -> "IMP" | NIMP -> "NIMP"| ALL(_,_,_) -> "ALL" | NALL(_,_,_) -> "NALL" | MAT -> "MAT"| DEC -> "DEC" | CON -> "CON"| BE -> "BE" | BQ -> "BQ" | FE -> "FE" | FQ -> "FQ"| EPS(_,_) -> "EPS" | CUT -> "CUT"
	let number_of_branches s = let (_,b,_,r) = !s in match r with  NALL(_,_,_) -> 0  | _ ->  List.length b
	(* let eq s1 s2 = (get_rule s1 = get_rule s2) && (get_head s1 = get_head s2) *)
	let satisfied s b = let  (h,bl,f,r) = !s in List.exists (fun l -> IntSet.mem (-l) b) h || 
					List.exists (fun br -> List.for_all (fun l -> IntSet.mem l b ) br) bl 
	let heuristic s litc= let (head,bl,f,r) = !s in
		let heu = match r with
		| IMP -> List.fold_left (fun h ls -> List.fold_left (fun h' l -> h' + (LitCount.get litc l) + (LitCount.get litc (-l))) h ls ) 0 bl
		| _ -> List.fold_left (fun h ls -> List.fold_left (fun h' l -> h' + (LitCount.get litc l)) h ls ) 0 bl
		in
		if heu < 0 then Printf.printf  "bad : heuristc < 0\n" ; heu 
	end
 
exception No_More_Clauses
exception Independent_Refutation of refutation * IntSet.t * int * int * int

exception Initialbranch_Hypothesis_Error 
exception Mating_Missmatch of string

(** HEURISTIK  **)  



(** Preprocess **)

let sort_clauses sl litc = List.stable_sort 
	(fun a b ->
		let c = Pervasives.compare (Step.number_of_branches a ) (Step.number_of_branches b ) in
		if c = 0 then Pervasives.compare (Step.heuristic b litc ) (Step.heuristic a litc) else c ) sl 
(* stable_sort keeps the order of the exists*)

let rec add_sym_clauses cl cw cr =
match cl with 
| (c::clr) -> 
	begin
		match (cr c) with
		(*| PosPropRule(m) -> 
   			begin 
        		match m with 
          		| Ap(Ap(Imp,_),_) ->
				begin
				if  debug_add_clauses then (Printf.printf  "because of %s " (ruleinfo_str (cr c)));
				let c2=(-List.hd c)::[-List.hd (List.tl c)]  in 
				if List.mem c2 cw then ( if  debug_add_clauses then Printf.printf  "no add - already exists \n";(add_sym_clauses clr cw cr) )
				else (
			 	if  debug_add_clauses then (Printf.printf  "add   \n" ); 
				(add_sym_clauses clr (c2::cw) cr) ) 
				end  
			| _ ->  add_sym_clauses clr cw cr
			end*)
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
				| _ -> raise (Not_Implemented("can't handle with Confrontation Rule: "^ (trm_str n) ^" and "^ (trm_str m) )) 
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

let initialise_literal_array cl = 
if pftrm_litcount then begin
let litc = LitCount.make (max_atom () +1) in 
List.iter (fun c -> List.iter (fun l -> LitCount.incr litc l ) c ) cl;
litc
end else LitCount.make 1

let add_Cuts litc steps witnesses =
let lits = LitCount.get_lits litc in
let lits = List.sort (fun (n,a) (m,b) -> Pervasives.compare b a ) lits in
let (lits,_) = List.split lits in
let n = (List.length lits *10)/100 in
let rec add_Cuts1 lits n steps =
if n = 0 then steps
else add_Cuts1 (List.tl lits) (n-1) ((Step.make_Cut (List.hd lits) witnesses)::steps) in
add_Cuts1 lits n steps

let preprocess_clauses cl cr =
let (cl1,unitclauses)= List.fold_right (fun c (cl',b') -> 
		if List.length c > 1 then (c::cl',b') else (cl',(List.hd c)::b'))  cl ([],[]) in 
	(* removes initial assumptions and tautologies and add them to the branch *)
let assumptions = List.filter (fun l -> match literal_to_trm l with 
		True -> false | Ap(Ap(Imp,False),False) -> false | Ap(Ap(Eq(_),s),t) -> s=t | _ -> true) unitclauses in
if result_statistic then (Printf.printf "Filtered to %d clauses\n" (List.length cl1); flush stdout); 
let cl2= if (get_bool_flag "PFTRM_ADD_SYM_CLAUSES") && pftrm_add_clauses then add_sym_clauses cl1 cl1 cr else cl1 in 
if result_statistic then (Printf.printf "Added sym clauses and now %d clauses\n" (List.length cl2); flush stdout); 
let witnesses = List.fold_left (fun w c -> match cr c with FreshRule(_,_,x) -> x::w | _ -> w ) [] cl2 in
if debug_free_names then (Printf.printf "found witnesses %d \n" (List.length witnesses); flush stdout); 
if debug_free_names then Printf.printf  "found global witnesses %s \n" (String.concat "," witnesses) ;
let steps = List.fold_right (fun c sl -> let s = Step.make c cr witnesses in if List.mem s sl then sl else s::sl ) cl2 [] in
if result_statistic then (Printf.printf "turned clauses into steps %d \n" (List.length steps); flush stdout); 
let litc = initialise_literal_array cl1  in
let steps = if pftrm_add_Cuts then add_Cuts litc steps witnesses else steps in
if debug_litcount then (LitCount.print litc;Printf.printf "\nnumber of literals %d \n" (LitCount.count litc); flush stdout);
if (get_bool_flag "PFTRM_PRESORT_CLAUSES") then (sort_clauses steps litc ,assumptions) else (steps,assumptions)

(** Choose next rule**)

let apply_clause_check blocked b s = 
if debug_free_names then Printf.printf  "blocked witnesses %s and step has witnesses %s \n" (String.concat "," blocked) (String.concat "," (Step.get_free s)) ;
( List.for_all (fun n -> Branch.mem n b ) (Step.get_head s) ) && ( not ( List.exists (fun n -> List.mem n blocked) (Step.get_free s) ) )

let exists_clause_check s = match Step.get_rule s with Step.NALL(_,_,x) -> (true,x) | _ -> (false,"") 

let remove_satisfied_clauses b sl =
List.filter (fun s -> 
	if Step.satisfied s (Branch.get_set b)
	then ((*if pftrm_heuristic then List.iter (fun l -> LitCount.decr litc l ) (Step.get_literals s)*)();false) 
	else true) sl

let heuristic s litc =
	let lls = Step.get_branches s in
	let h = List.fold_left (fun h ls -> List.fold_left (fun h' l -> h' + (LitCount.get litc l) + (LitCount.get litc (-l)) ) h ls ) 0 lls in
	if h < 0 then Printf.printf  "bad : heuristc < 0\n" ; h

let get_next_clause blocked b cl  = 
	let rec gnc blocked b cl  c' h' l' = 
		match cl with  (***  TODO impl heuristic ***)
		| (c::clr)-> 
			if apply_clause_check blocked b c 
			then (* if pftrm_heuristic then begin 
				let l = Step.number_of_branches c in
				if  l < 2 
				then c
				else if l > l' 
					then c'
					else begin 
					let h = heuristic c litc in 
					if h > h'  
						then gnc blocked b clr litc c h l
						else gnc blocked b clr litc c' h' l'
					end
			end
			else *) c
			else begin 
				let (bb,x)= exists_clause_check c in 
				if bb
				then gnc (x::blocked) b clr  c' h' l'
 				else gnc blocked b clr   c' h' l'
			end
		| [] -> c' in
	gnc blocked b cl (try List.hd cl with Failure("hd")-> raise (Not_Implemented "No clauses left to choose from" ) ) (-1) 100

(** PostProcess **)


let rec apply_rule1 b cl tll hl level = begin (* TODO Use Fold_left instead*)
match tll with
	| (tl::tllr) -> 
		let (r,c,s,d,w) = try or_search tl (Branch.reset b level) (ref cl) 
			with Independent_Refutation(r,con,size,depth,width)-> (r,con,size,depth,width) in
		if pftrm_Timeout && (!isTimeout) then (r::(List.map (fun t -> Timeout) tllr),c,0,0,0)
		else 
		if ((get_bool_flag "PFTRM_REMOVE_INDEPENDENT") && pftrm_Independent_refutation  && (List.for_all (fun t ->not (IntSet.mem t c) ) tl)) then
		( if debug_Independent_refutation then Printf.printf  "found Independant refutation\n"; raise (Independent_Refutation(r,c,s,d,w)) )
		else 
		let (rs,c',s',d',w') =  apply_rule1 b cl tllr hl level in
		if (!isTimeout) then (r::rs,c',0,0,0) 
		else
		let con = IntSet.union (IntSet.filter (fun n -> not (List.mem n tl)) c) c' in
		if debug_Independent_refutation then Printf.printf "condition = %s\n" (String.concat "," (List.map string_of_int (IntSet.elements con))); 
		(r::rs,con,s+s',max d (d'-1) +1,w+w') 
		
	| [] -> ([],List.fold_left (fun s h -> IntSet.add h s) IntSet.empty hl,1,1,0)
end 

and apply_rule b cl tll hl =
let level = Branch.next_level b in
let (r,c,s,d,w) = apply_rule1 b !cl tll hl level in
(ignore (Branch.reset b level);(r,c,s,d,w))

and apply_Imp  b h s t cl = begin 
		if Branch.mem (-s) b || Branch.mem (-t) b then 
		let (r1::r2::rs,con,size,depth,width)= apply_rule b cl [[s];[t]] [h]  in 
		(Implication(literal_to_trm h,literal_to_trm s,literal_to_trm t, r1, r2),con,size,depth,width) 
		else 
		let level = Branch.next_level b in
		let (r,c,size,d,w) = try or_search [t;-s] b cl  
			with Independent_Refutation(r,con,size,depth,width)-> (r,con,size,depth,width) in
		if pftrm_Timeout && (!isTimeout) then (Implication(literal_to_trm h,literal_to_trm s,literal_to_trm t,Timeout,r),IntSet.empty,0,0,0)
		else
		if (IntSet.mem (-s) c) &&  (IntSet.mem t c)
		then
			let (r',c',size',d',w') =   try or_search [s] (Branch.reset b level) cl 
			with Independent_Refutation(r,con,size,depth,width)-> (r,con,size,depth,width) in
			if pftrm_Timeout && (!isTimeout) 
			then (Implication(literal_to_trm h,literal_to_trm s,literal_to_trm t,r',r),IntSet.empty,0,0,0)
			else
			if (IntSet.mem s c') 
			then 	
				let con = IntSet.union (IntSet.remove s c') (IntSet.remove (-s) (IntSet.add h (IntSet.remove t c))) in
				if debug_Independent_refutation then Printf.printf "condition(1) = %s\n" (String.concat "," (List.map string_of_int (IntSet.elements con)));
				let (size,depth,width)= (size+size'+3,max d' (d+1) +1,1+w+w') in
				(Cut(literal_to_trm s,r',Implication(literal_to_trm h,literal_to_trm s,literal_to_trm t,
								Conflict(literal_to_trm s,literal_to_trm (-s)),r)),con,size,depth,width) 
			else 
				(if debug_Independent_refutation then Printf.printf  "apply_Imp Independent_Refutation left(1)\n";
				raise (Independent_Refutation(r',c',size',d',w')))
		else
		if not (IntSet.mem (-s) c) &&  not (IntSet.mem t c)
		then
			(if debug_Independent_refutation then Printf.printf  "apply_Imp Independent_Refutation right(1)\n" ;
			raise (Independent_Refutation(r,c,size,d,w) ) )
		else
		if (IntSet.mem (-s) c) &&  not (IntSet.mem t c)
		then 
			let (r',c',size',d',w') =   try or_search [s] (Branch.reset b level) cl 
			with Independent_Refutation(r,con,size,depth,width)-> (r,con,size,depth,width) in
			if pftrm_Timeout && (!isTimeout) 
			then (Implication(literal_to_trm h,literal_to_trm s,literal_to_trm t,r',r),IntSet.empty,0,0,0)
			else
			if (IntSet.mem s c') 
			then 	
				let con = IntSet.union (IntSet.remove s c') (IntSet.remove (-s) c) in
				if debug_Independent_refutation then Printf.printf "condition(2) = %s\n" (String.concat "," (List.map string_of_int (IntSet.elements con)));
				let (size,depth,width)= (size+size'+1,max d' d +1,w+w') in
				(Cut(literal_to_trm s,r',r),con,size,depth,width)
			else 
				(if debug_Independent_refutation then Printf.printf  "apply_Imp Independent_Refutation left(2)\n" ;
				raise (Independent_Refutation(r',c',size',d',w')) )
		else 
		if not (IntSet.mem (-s) c) &&  (IntSet.mem t c)
		then
			let (r',c',size',d',w') =   try or_search [s;-t] (Branch.reset b level) cl
			with Independent_Refutation(r,con,size,depth,width)-> (r,con,size,depth,width) in
			if pftrm_Timeout && (!isTimeout) 
			then (Implication(literal_to_trm h,literal_to_trm s,literal_to_trm t,r',r),IntSet.empty,0,0,0)
			else
			if (IntSet.mem (-t) c') &&  (IntSet.mem s c') 
			then 
				let con = IntSet.union (IntSet.remove t c) (IntSet.remove (-t) (IntSet.add h (IntSet.remove s c'))) in
				if debug_Independent_refutation then Printf.printf "condition(3) = %s\n" (String.concat "," (List.map string_of_int (IntSet.elements con)));
				let (size,depth,width)= (size+size'+3,max d (d'+1) +1,1+w+w') in
				(Cut(literal_to_trm t,r,Implication(literal_to_trm h,literal_to_trm s,literal_to_trm t,r',
						Conflict(literal_to_trm t,literal_to_trm (-t)))),con,size,depth,width) 					
			else 
			if not (IntSet.mem (-t) c') &&  (IntSet.mem s c') 	
			then 
				let con = IntSet.add h (IntSet.union (IntSet.remove s c') (IntSet.remove t c)) in
				if debug_Independent_refutation then Printf.printf "condition(4) = %s\n" (String.concat "," (List.map string_of_int (IntSet.elements con)));
				let (size,depth,width)= (size+size'+1,max d d' +1,w+w') in
				(Implication(literal_to_trm h,literal_to_trm s,literal_to_trm t,r',r),con,size,depth,width)
			else 
			if (IntSet.mem (-t) c') && not (IntSet.mem s c') 
			then
				let con = IntSet.union (IntSet.remove t c) (IntSet.remove (-t) c') in
				if debug_Independent_refutation then Printf.printf "condition(5) = %s\n" (String.concat "," (List.map string_of_int (IntSet.elements con)));
				let (size,depth,width)= (size+size'+1,max d' d +1,w+w') in
					(Cut(literal_to_trm t,r,r'),con,size,depth,width) 
			else
			if  not (IntSet.mem (-t) c') && not (IntSet.mem s c') 
			then
				(if debug_Independent_refutation then Printf.printf  "apply_Imp Independent_Refutation left(3)\n" ;
				 raise (Independent_Refutation(r',c',size',d',w') ) )
			else  raise (Not_Implemented("you found the fifth case out of four; I messed up" )) 
		else raise (Not_Implemented("you found the fifth case out of four; I messed up" )) 
end

(** SEARCH **)

and and_search b c cl  =
	let br = Step.get_branches c in
	let h = Step.get_head c in
	try 
	let cutlit = List.find (fun l -> not (Branch.mem l b) ) h in
	if debug_search then Printf.printf  "apply CUT(2)\n" ; 
	let (r1::r2::rs,con,size,depth,width)= apply_rule b cl ([-(abs cutlit)]::[[abs cutlit]]) []  in 
	(Cut( literal_to_trm (abs cutlit) , r2, r1),con,size,depth,width)
	with Not_found -> 
	begin
	if debug_search then Printf.printf  "apply %s on %s\n" (Step.rule_to_str (Step.get_rule c)) (String.concat "," (List.map string_of_int h)) ;
	let (r,con,size,depth,width) =
		if Step.get_rule c = Step.IMP   
			then  ([],IntSet.empty,0,0,0) 
			else apply_rule b cl br h   in
   	match Step.get_rule c with
	| Step.IMP -> 
		let head = List.hd h in
		let [[s];[t]] = br in
		if (get_bool_flag "PFTRM_REMOVE_INDEPENDENT") && pftrm_Independent_refutation && pftrm_semantic
			then apply_Imp b head s t cl 
			else 
				let (r1::r2::rs,con,size,depth,width) = apply_rule b cl br h  in 
            			(Implication(literal_to_trm head,literal_to_trm s,literal_to_trm t, r1, r2),con,size,depth,width) 
	| Step.NIMP -> 
		let h = literal_to_trm (List.hd h) in
		let [[s;t]] = br in
		let r1::rs = r in
		(NegImplication(h,literal_to_trm s,literal_to_trm t,r1),con,size,depth,width)
	| Step.ALL(a,m,n) -> 
		let h = literal_to_trm (List.hd h) in
		let [[s]] = br in
		let r1::rs = r in
            	(All(h,literal_to_trm s,r1,a,m,n),con,size,depth,width) 
	| Step.NALL(a,m,x) -> 
		if assert_freshness && IntSet.exists (fun t -> List.mem x (Step.trm_free_variable (literal_to_trm t)))(Branch.get_set b ) 
		then raise (Not_Implemented("found freshness violation " )) ; 
		let head = literal_to_trm (List.hd h) in
		let [[s]] = br in
		let r1::rs = r  in
            	(NegAll(head,literal_to_trm s,r1,a,m,x),con,size,depth,width)  
	| Step.MAT ->  
		let  [h1;h2] =h in
            	let  ss =  List.map (fun ls -> literal_to_trm (List.hd ls) ) br  in
	    	(Mating(literal_to_trm h1,literal_to_trm h2,ss , r),con,size,depth,width)       
	| Step.DEC ->  
		let h = literal_to_trm (List.hd h) in
		let ss = List.map (fun ls -> literal_to_trm (List.hd ls) ) br in	
		(Decomposition(h,ss,r),con,size,depth,width) 
	| Step.CON ->
		let  h1 =literal_to_trm (List.hd h) in
        	let  h2 =literal_to_trm (List.hd (List.tl h)) in
		let [[su;tu];[sv;tv]] = br in
		let r1::r2::rs = r in
		(Confront(h1,h2,literal_to_trm su,literal_to_trm tu,literal_to_trm sv,literal_to_trm tv, r1, r2),con,size,depth,width) 
	| Step.BE -> 
		let h =literal_to_trm (List.hd h) in	
		let [[s;_];[_;t]] = br in
		let r1::r2::rs = r in
		(NegEqualProp(h,literal_to_trm s,literal_to_trm t, r1, r2),con,size,depth,width)  
	| Step.BQ ->  
		let h =literal_to_trm (List.hd h) in	
		let [[s;t];[_;_]] = br in
		let r1::r2::rs = r in
		(EqualProp(h,literal_to_trm s,literal_to_trm t, r1, r2),con,size,depth,width)  
	| Step.FE -> 
		let h = literal_to_trm (List.hd h) in
		let s = literal_to_trm (List.hd (List.hd br)) in
		let r1::rs = r in
            	(NegEqualFunc(h, s, r1),con,size,depth,width)
	| Step.FQ ->  
		let h = literal_to_trm (List.hd h) in
		let s = literal_to_trm (List.hd (List.hd br)) in
		let r1::rs = r in
            	(EqualFunc(h, s, r1),con,size,depth,width)
	| Step.EPS(eps,pred) -> 
		let [[empty];[choice]] = br in
		let r1::r2::rs = r in
		(ChoiceR(eps,pred,literal_to_trm empty,literal_to_trm choice,r1, r2 ),con,size,depth,width) 
	| Step.CUT ->(** TODO there are no Cuts yet **) 
		let [_;[h]] = br in
		let r1::r2::rs = r in
		(Cut( literal_to_trm h , r2, r1),con,size,depth,width)
	end
                  
and or_search1 b cl  =
	if pftrm_Timeout && !timeout < Sys.time() -. !beforeSearch then(isTimeout:=true; (Timeout,IntSet.empty,1,1,1)) 
	else
	try  let cl = remove_satisfied_clauses b cl  in  if debug_search then Printf.printf  "remove satisfied clauses done %d\n" (List.length cl); 
		let c = get_next_clause []  b cl  in
		if debug_search then Printf.printf  "apply next clause %f %d\n"  (Sys.time() -. !beforeSearch) (List.length cl) ; 
		and_search b c (ref cl) 
	with No_More_Clauses -> 
  match cl with
    (s :: clr) -> if Step.satisfied s (Branch.get_set b)
    then or_search1 b clr  (** TODO **)
    else (if debug_search then Printf.printf  "apply next clause(2) %f %d\n"  (Sys.time() -. !beforeSearch) (List.length cl) ; 
	and_search b s (ref cl) )
   | [] -> raise No_More_Clauses      

and or_search ls b cl  = 
  match ls with
    | [] -> or_search1 b !cl  
    | (l::lr) ->
	try Branch.add b l;or_search lr b cl  
	with Branch.Closed(r,c,s,d,w) ->(r,c,s,d,w)
			
 
(** Process Refut **) 

let is_an_eqn m n =
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
  | _ -> raise Not_found (*** It's not an equation. ***)

let rec leibeq_to_primeq2 m n =
try
   is_an_eqn m n
with Not_found ->
     		begin
		match m with
			| Ap(m1,m2) ->begin  if false then Printf.printf  "LEIBEQ Rewrite looks at %s \n" (trm_str m); 
     				try let (pre,pt,pt',stp)= leibeq_to_primeq2 m1 n in 
      					(Ap(pre,m2),pt,pt',stp) 
      				with Not_found -> let (pre,pt,pt',stp)= leibeq_to_primeq2 m2 n in 
        				(Ap(m1,pre),pt,pt',stp) end
  			| Lam(a1,m1) ->if false then Printf.printf  "LEIBEQ Rewrite looks at %s \n" (trm_str m);
    				let (pre,pt,pt',stp)= leibeq_to_primeq2 m1 (n+1) in 
    				(Lam(a1,pre),pt,pt',stp) 
			| _ -> raise Not_found
     			end


and leibeq_to_primeq unitc b sl =
	let b' = (* IntSet.filter (fun t ->not (List.mem t unitc)) *) (Branch.get_set b) in
	let rec leibeq_to_primeq1 b' b = match b' with
		| [] -> begin 
			List.iter (fun l -> if not (Branch.mem l b  || Branch.is_taut l)
					then Printf.printf  "Error - missing assumption : %s\n" (trm_str (literal_to_trm l))) unitc;
			try or_search [] b sl with Independent_Refutation(r,con,size,depth,width)-> (r,con,size,depth,width) end
		| (m::br) -> try
    			let (pre,pt,pt',stp)= leibeq_to_primeq2 (literal_to_trm m) 0 in
    			let prefix= Lam(stp,pre) in
    			let ptrm' =get_literal (norm name_def (Ap(prefix,pt'))) in
			begin
			try 
			let b' = (Branch.add b ptrm';ptrm'::br) in
  			if debug_leibeq then Printf.printf  "LEIBEQ Rewrite %d into %d \n" m ptrm';
			let (r,con,size,depth,width) =try leibeq_to_primeq1  b' b 
							with Independent_Refutation(r,con,size,depth,width)-> (r,con,size,depth,width) in
			if (get_bool_flag "PFTRM_REMOVE_INDEPENDENT") && pftrm_Independent_refutation  && not (IntSet.mem ptrm' con)
				then ( if debug_Independent_refutation then Printf.printf  "found Independant leibeq refutation\n";
				raise (Independent_Refutation(r,con,size,depth,width)) )
			else 
  			(Rewrite(prefix,pt,pt',r),IntSet.add m (IntSet.remove ptrm' con),size+1,depth+1,width)
			with 
			| Branch.Closed(r,c,s,d,w) -> (Rewrite(prefix,pt,pt',r),IntSet.add m (IntSet.remove ptrm' c),s+1,d+1,w) end
			with	
			| Not_found -> if debug_leibeq then Printf.printf  "LEIBEQ couldn't Rewrite %d \n" m;
					leibeq_to_primeq1  br b  
	in 
	leibeq_to_primeq1 (IntSet.elements b') b

let rec process_refut1 b r =  
  match r with 
  | SearchR(cl,cr) ->  if debug_search then Printf.printf  "starting SearchR\n";
	let (sl,unitc) = (preprocess_clauses cl cr) in 
	if (get_bool_flag "LEIBEQ_TO_PRIMEQ") then
    	leibeq_to_primeq unitc b (ref sl) 
  	else
	or_search [] b (ref sl) 
        
  | NegImpR(m,n,r1) -> if debug_search then Printf.printf  "apply NegImpR\n";
    	let h = (normneg (imp m n)) in
    	let s = m in let t = (normneg n) in
	let s' = get_literal s in let t'= get_literal t in
	let (r,con,size,depth,width)= try process_refut [s';t'] b r1 with Independent_Refutation(r,con,size,depth,width)-> (r,con,size,depth,width) in
	if (get_bool_flag "PFTRM_REMOVE_INDEPENDENT") && pftrm_Independent_refutation  && not (IntSet.mem s' con || IntSet.mem t' con ) then
		( if debug_Independent_refutation then Printf.printf  "found Independant refutation\n";
			raise (Independent_Refutation(r,con,size,depth,width)) )
	else 
	let con = IntSet.add (get_literal h) (IntSet.remove s' (IntSet.remove t' con)) in
    	(NegImplication(h,s,t,r),con,size+1,depth+1,width)
  | ImpR(m,n,r1,r2) -> if debug_search then Printf.printf  "apply ImpR\n";
	let l = Branch.next_level b in
    	let h =  (imp m n) in
    	let s =  (normneg m) in let t = n in
	let s' = get_literal s in let t'= get_literal t in
    	let (r,con,size,depth,width)=try process_refut [s'] b r1 
					with Independent_Refutation(r,con,size,depth,width)-> (r,con,size,depth,width) in
	if (get_bool_flag "PFTRM_REMOVE_INDEPENDENT") && pftrm_Independent_refutation  && not (IntSet.mem s' con) then
		( if debug_Independent_refutation then Printf.printf  "found Independant refutation\n";
			raise (Independent_Refutation(r,con,size,depth,width)) )
	else 
   	let (r',con',size',depth',width')= try process_refut [t'] (Branch.reset b l) r2 
						with Independent_Refutation(r,con,size,depth,width)-> (r,con,size,depth,width) in
	if (get_bool_flag "PFTRM_REMOVE_INDEPENDENT") && pftrm_Independent_refutation  && not (IntSet.mem t' con') then
		( if debug_Independent_refutation then Printf.printf  "found Independant refutation\n";
			raise (Independent_Refutation(r',con',size',depth',width')) )
	else 
	let con = IntSet.add (get_literal h) (IntSet.union (IntSet.remove s' con) (IntSet.remove t' con')) in
   	(Implication(h,s,t,r ,r'),con,size+size'+1,max depth depth' +1,width+width')
  | FalseR ->  if debug_search then Printf.printf  "apply FalseR\n"; (Fal(False),IntSet.singleton(get_literal False),1,1,1)
  | NegReflR -> if debug_search then Printf.printf  "apply NegReflR \n";
	let h = List.find (fun t -> match (literal_to_trm t) with 
                                     		| Ap(Ap(Imp,Ap(Ap(Eq(_),s),t)),False)->  s = t
                                     		| _ -> false ) (IntSet.elements (Branch.get_set b)) in
	(NegRefl(literal_to_trm h),IntSet.singleton(h),1,1,1) 
  | NegAllR(a,m,x,r1) -> if debug_search then Printf.printf  "apply NegAllR\n";
    	let h = (normneg (Ap(Forall(a),m))) in 
    	let s = (norm name_def (normneg (Ap(m,Name(x,a)))) ) in 
	let s' = get_literal s in
	let (r,con,size,depth,width)=try process_refut [s'] b r1 with Independent_Refutation(r,con,size,depth,width)-> (r,con,size,depth,width) in
	if (get_bool_flag "PFTRM_REMOVE_INDEPENDENT") && pftrm_Independent_refutation  && not (IntSet.mem s' con) then
		( if debug_Independent_refutation then Printf.printf  "found Independant refutation\n";
			raise (Independent_Refutation(r,con,size,depth,width)) )
	else 
	let con = IntSet.add (get_literal h) (IntSet.remove s' con) in
    	(NegAll(h,s,r,a,m,x),con,size+1,depth+1,width)
  | EqFR(a,a',s,t,r1) ->   if debug_search then Printf.printf  "apply EqFR\n";
    	let h =  (eq (Ar(a,a')) s t) in
    	let m = (norm name_def (forall a (eq a' (Ap(s,DB(0,a))) (Ap(t,DB(0,a))) ))) in
	let s' = get_literal m in
	let (r,con,size,depth,width)=try process_refut [s'] b r1 with Independent_Refutation(r,con,size,depth,width)-> (r,con,size,depth,width) in
	if (get_bool_flag "PFTRM_REMOVE_INDEPENDENT") && pftrm_Independent_refutation  && not (IntSet.mem s' con) then
		( if debug_Independent_refutation then Printf.printf  "found Independant refutation\n";
			raise (Independent_Refutation(r,con,size,depth,width)) )
	else 
	let con = IntSet.add (get_literal h) (IntSet.remove s' con) in
    	(EqualFunc(h,m,r),con,size+1,depth+1,width)
  | NegEqFR(a,a',s,t,r1) -> if debug_search then Printf.printf  "apply NegEqFR\n";
    	let h = neg (eq (Ar(a,a')) s t) in
    	let m = normneg (norm name_def (forall a (eq a' (Ap(s,DB(0,a))) (Ap(t,DB(0,a))) ))) in
	let s' = get_literal m in
	let (r,con,size,depth,width)=try process_refut [s'] b r1 with Independent_Refutation(r,con,size,depth,width)-> (r,con,size,depth,width) in
	if (get_bool_flag "PFTRM_REMOVE_INDEPENDENT") && pftrm_Independent_refutation  && not (IntSet.mem s' con) then
		( if debug_Independent_refutation then Printf.printf  "found Independant refutation\n";
			raise (Independent_Refutation(r,con,size,depth,width)) )
	else 
	let con = IntSet.add (get_literal h) (IntSet.remove s' con) in
    	(NegEqualFunc(h,m,r),con,size+1,depth+1,width)  
  | EqOR(s,t,r1,r2) -> if debug_search then Printf.printf  "apply EqOR\n";
	let l = Branch.next_level b in
    	let h =  (eq Prop s t) in
    	let ns =  (normneg s) in let nt =  (normneg t) in
	let s' = get_literal s in let t'= get_literal t in
	let ns' = get_literal ns in let nt'= get_literal nt in
	let (r,con,size,depth,width)= try process_refut [s';t'] b r1 with Independent_Refutation(r,con,size,depth,width)-> (r,con,size,depth,width) in
	if (get_bool_flag "PFTRM_REMOVE_INDEPENDENT") && pftrm_Independent_refutation  && not (IntSet.mem s' con || IntSet.mem t' con) then
		( if debug_Independent_refutation then Printf.printf  "found Independant refutation\n";
			raise (Independent_Refutation(r,con,size,depth,width)) )
	else 
	let (r',con',size',depth',width')=try process_refut [ns';nt'] (Branch.reset b l) r2 
						with Independent_Refutation(r,con,size,depth,width)-> (r,con,size,depth,width)in
	if (get_bool_flag "PFTRM_REMOVE_INDEPENDENT") && pftrm_Independent_refutation  && not (IntSet.mem ns' con' || IntSet.mem nt' con') then
		( if debug_Independent_refutation then Printf.printf  "found Independant refutation\n";
			raise (Independent_Refutation(r',con',size',depth',width')) )
	else 
	let con = IntSet.add (get_literal h) (IntSet.union (IntSet.remove s' (IntSet.remove t' con)) (IntSet.remove ns' (IntSet.remove nt' con'))) in
     	(EqualProp(h,s,t,r,r'),con,size+size'+1,max depth depth' +1,width+width')
  | NegEqOR(s,t,r1,r2) -> if debug_search then Printf.printf  "apply NegEqOR\n";
	let l = Branch.next_level b in
    	let h =  neg(eq Prop s t) in
    	let ns =  (normneg s) in let nt =  (normneg t) in
	let s' = get_literal s in let t'= get_literal t in
	let ns' = get_literal ns in let nt'= get_literal nt in
	let (r,con,size,depth,width)=try process_refut [s';nt'] b r1 
					with Independent_Refutation(r,con,size,depth,width)-> (r,con,size,depth,width) in
	if (get_bool_flag "PFTRM_REMOVE_INDEPENDENT") && pftrm_Independent_refutation  && not (IntSet.mem s' con || IntSet.mem nt' con) then
		( if debug_Independent_refutation then Printf.printf  "found Independant refutation\n";
			raise (Independent_Refutation(r,con,size,depth,width)) )
	else 
	let (r',con',size',depth',width')=try  process_refut [ns';t'] (Branch.reset b l) r2 
						with Independent_Refutation(r,con,size,depth,width)-> (r,con,size,depth,width) in
	if (get_bool_flag "PFTRM_REMOVE_INDEPENDENT") && pftrm_Independent_refutation  && not (IntSet.mem ns' con' || IntSet.mem t' con') then
		( if debug_Independent_refutation then Printf.printf  "found Independant refutation\n";
			raise (Independent_Refutation(r',con',size',depth',width')) )
	else 
	let con = IntSet.add (get_literal h) (IntSet.union (IntSet.remove s' (IntSet.remove nt' con)) (IntSet.remove ns' (IntSet.remove t' con'))) in
     	(NegEqualProp(h,s,t,r,r'),con,size+size'+1,max depth depth' +1,width+width') 
  | AssumptionConflictR -> 
		if (get_bool_flag "LEIBEQ_TO_PRIMEQ") then
	    	leibeq_to_primeq [] b (ref []) 
  		else or_search (IntSet.elements (Branch.get_set b)) b (ref []) 
			
  | _ ->   raise (Not_Implemented("unknown refut case")) 
    

and process_refut ls b r = 
  match ls with
    | [] -> process_refut1 b r
    | (l::lr) ->try Branch.add b l;process_refut lr b r   
			with Branch.Closed(r,c,s,d,w) ->(r,c,s,d,w)
    		
  
(** to String functions**)

 let rec trm_struct m =
  match m with
    Name(x,_) -> x
  | False -> "False"
  | Imp -> "Imp"
  | Forall(_) -> "Forall"
  | Eq(_) -> "Eq"
  | Choice(_) -> "Sepsilon"
  | True -> "True"
  | And -> "And"
  | Or -> "Or"
  | Iff -> "Iff"
  | Neg -> "Neg"
  | Exists(_) -> "Exists" 
  | DB(i,a) -> "DB(" ^ (string_of_int i) ^","^ (stp_str a)  ^")"
  | Lam(a,m) -> "Lam(" ^ (stp_str a) ^ "," ^ (trm_struct m)^")"
  | Ap(m1,m2) -> "Ap("^ (trm_struct m1) ^ "," ^ (trm_struct m2) ^")"                   
       
           
let rec ref_str r =
  match r with
 | Conflict(s,ns) -> (trm_str s) ^ " is conflicting\n"
 | Fal(_) ->"False is on the branch\n"
 | NegRefl(s) -> (trm_str s) ^ " is on the branch\n"
 | Implication(h,s,t,r1,r2) -> "use Implication rule on " ^ (trm_str h) ^"\nto get "^ (trm_str s) ^" or "^ (trm_str t)^"\n"
                               ^ ref_str r1 ^ ref_str r2
 | Disjunction(h,s,t,r1,r2) -> "use Or rule on " ^ (trm_str h) ^"\nto get "^ (trm_str s) ^" or "^ (trm_str t)^"\n"
                               ^ ref_str r1 ^ ref_str r2 
 | NegConjunction(h,s,t,r1,r2) -> "use NegAnd rule on " ^ (trm_str h) ^"\nto get "^ (trm_str s) ^" or "^ (trm_str t)^"\n"
                               ^ ref_str r1 ^ ref_str r2  
 | NegImplication(h,s,t,r1) ->"use NegImplication rule on " ^ (trm_str h) ^"\nto get "^ (trm_str s) ^" and "^ (trm_str t)^"\n"
                               ^ ref_str r1
 | Conjunction(h,s,t,r1) ->"use And rule on " ^ (trm_str h) ^"\nto get "^ (trm_str s) ^" and "^ (trm_str t)^"\n"
                               ^ ref_str r1 
 | NegDisjunction(h,s,t,r1) ->"use NegOr rule on " ^ (trm_str h) ^"\nto get "^ (trm_str s) ^" and "^ (trm_str t)^"\n"
                               ^ ref_str r1   
 | All(h,s,r1,a,m,n) ->"use ForAll rule on " ^ (trm_str h) ^"\nto get "^ (trm_str s) ^"\n"
                               ^ ref_str r1
 | NegAll(h,s,r1,a,m,x) ->"use NegForAll rule on " ^ (trm_str h) ^"\nto get "^ (trm_str s) ^"\n"
                               ^ ref_str r1
 | Exist(h,s,r1,a,m,x) ->"use Exist rule on " ^ (trm_str h) ^"\nto get "^ (trm_str s) ^"\n"
                               ^ ref_str r1  
 | NegExist(h,s,r1,a,m,n) ->"use NegExist rule on " ^ (trm_str h) ^"\nto get "^ (trm_str s) ^"\n"
                               ^ ref_str r1    
 | Mating(h1,h2, ss, rs) -> "use Mating rule on " ^ (trm_str h1) ^" and "^(trm_str h2)^"\nto get "^ (String.concat "," (List.map (fun a -> trm_str a) ss)) ^"\n"
                               ^ (String.concat "" (List.map ref_str rs))
 | Decomposition(h1, ss, rs) -> "use Decompostion rule on " ^ (trm_str h1) ^"\nto get "^ (String.concat "," (List.map (fun a -> trm_str a) ss)) ^"\n"
                               ^ (String.concat "" (List.map ref_str rs))
 
 | Confront(h1,h2,su,tu,sv,tv,r1,r2) ->"use Confrontation rule on " ^ (trm_str h1) ^" and "^(trm_str h2)^"\nto get "^ (trm_str su)^"and" ^ (trm_str tu) ^" or "^ (trm_str sv)^"and"^ (trm_str tv)^"\n"
                               ^ ref_str r1 ^ ref_str r2
 | NegEqualProp(h,s,t,r1,r2) -> "use Boolean Extensionality rule on " ^ (trm_str h) ^"\nto get "^ (trm_str s)^"and" ^ (trm_str (neg t)) ^" or "^ (trm_str (neg s))^"and"^ (trm_str t)^"\n"
                               ^ ref_str r1 ^ ref_str r2
 | EqualProp(h,s,t,r1,r2) -> "use Boolean Equality rule on " ^ (trm_str h) ^"\nto get "^ (trm_str s)^"and" ^ (trm_str t) ^" or "^ (trm_str (neg s))^"and"^ (trm_str (neg t))^"\n"
                               ^ ref_str r1 ^ ref_str r2
 | NegAequivalenz(h,s,t,r1,r2) -> "use NegAequivalenz rule on " ^ (trm_str h) ^"\nto get "^ (trm_str s)^"and" ^ (trm_str (neg t)) ^" or "^ (trm_str (neg s))^"and"^ (trm_str t)^"\n"
                               ^ ref_str r1 ^ ref_str r2
 | Aequivalenz(h,s,t,r1,r2) -> "use Aequivalenz rule on " ^ (trm_str h) ^"\nto get "^ (trm_str s)^"and" ^ (trm_str t) ^" or "^ (trm_str (neg s))^"and"^ (trm_str (neg t))^"\n"
                               ^ ref_str r1 ^ ref_str r2
 | NegEqualFunc(h,s,r1) ->"use functional Extensionality rule on " ^ (trm_str h) ^"\nto get "^ (trm_str s) ^"\n"
                               ^ ref_str r1
 | EqualFunc(h,s,r1) ->"use functional Equality rule on " ^ (trm_str h) ^"\nto get "^ (trm_str s) ^"\n"
                               ^ ref_str r1
 | ChoiceR(eps,pred,s,t,r1,r2) -> "use Choice rule \n to get "^ (trm_str s) ^" or "^ (trm_str t)^"\n"
                               ^ ref_str r1 ^ ref_str r2
 | Cut(s,r1,r2) -> "use analytic Cut \n to get "^ (trm_str s) ^" or "^ (trm_str (neg s)) ^"\n"
                               ^ ref_str r1 ^ ref_str r2
 | DoubleNegation(h,s,r1) ->"use DoubleNegation rule on " ^ (trm_str h) ^"\nto get "^ (trm_str s) ^"\n"
                               ^ ref_str r1 
 | Rewrite(prefix,h,s,r1) ->"use Rewrite rule on " ^ (trm_str (onlybetanorm (Ap(prefix,h)))) ^"\nto get "^ (trm_str (onlybetanorm (Ap(prefix,s)))) ^"\n"
                               ^ ref_str r1   
 | Delta(h,s,x,r1) -> "unfold "^x ^" in " ^ (trm_str h)
 | NYI(h,s,r1) ->"use NYI-normalization on " ^ (trm_str h) ^"\nto get "^ (trm_str s) ^"\n"
                               ^ ref_str r1  
 | Timeout -> "timeout"
 | _ -> raise (Not_Implemented("unknown refutation case in ref_str" ))
         
(** Statistc **)

let statcount = ref (Hashtbl.create 100) 
let update_statcount h s w b =
if b then 
let (zs,zw,n) = try Hashtbl.find !statcount h with Not_found -> (0,0,0) in
Hashtbl.replace !statcount h (zs+s,zw+w,n+1)


let statistic r  =
let _ = Hashtbl.clear !statcount in
let rec statistic1 r h b =
 match r with
 | Conflict(s,ns) -> (1,1,1,0,0,0,0)
 | Fal(_) -> (1,1,1,0,0,0,0)
 | NegRefl(s) -> (1,1,1,0,0,0,0)
 | Implication(_,_,_,r1,r2) -> 
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let (s2,d2,w2,c2,re2,nyi2,t2) = statistic1 r2 (h+1) b in
        let _ = update_statcount h (s1+s2+1) (w1+w2) b in 
	(1+s1+s2,max d1 d2 +1,w1+w2,c1+c2,re1+re2,nyi1+nyi2,t1+t2)
 | Disjunction(_,_,_,r1,r2) -> 
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let (s2,d2,w2,c2,re2,nyi2,t2) = statistic1 r2 (h+1) b in
	let _ = update_statcount h (s1+s2+1) (w1+w2) b in
	(1+s1+s2,max d1 d2 +1,w1+w2,c1+c2,re1+re2,nyi1+nyi2,t1+t2)
 | NegConjunction(_,_,_,r1,r2) -> 
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let (s2,d2,w2,c2,re2,nyi2,t2) = statistic1 r2 (h+1) b in
	let _ = update_statcount h (s1+s2+1) (w1+w2) b in
	(1+s1+s2,max d1 d2 +1,w1+w2,c1+c2,re1+re2,nyi1+nyi2,t1+t2)
 | NegImplication(_,_,_,r1) ->
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let _ = update_statcount h (s1+1) (w1) b in
	(1+s1,d1 +1,w1,c1,re1,nyi1,t1)
 | Conjunction(_,_,_,r1) ->
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let _ = update_statcount h (s1+1) (w1) b in
	(1+s1,d1 +1,w1,c1,re1,nyi1,t1)
 | NegDisjunction(_,_,_,r1) ->
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let _ = update_statcount h (s1+1) (w1) b in
	(1+s1,d1 +1,w1,c1,re1,nyi1,t1) 
 | All(_,_,r1,_,_,_) ->
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let _ = update_statcount h (s1+1) (w1) b in
	(1+s1,d1 +1,w1,c1,re1,nyi1,t1)
 | NegAll(_,_,r1,_,_,_) ->
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let _ = update_statcount h (s1+1) (w1) b in
	(1+s1,d1 +1,w1,c1,re1,nyi1,t1)
 | Exist(_,_,r1,_,_,_) ->
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let _ = update_statcount h (s1+1) (w1) b in
	(1+s1,d1 +1,w1,c1,re1,nyi1,t1) 
 | NegExist(_,_,r1,_,_,_) ->
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let _ = update_statcount h (s1+1) (w1) b in
	(1+s1,d1 +1,w1,c1,re1,nyi1,t1)   
 | Mating(_,_,_, rs) -> begin ( try ignore (List.hd rs) with Failure(_) -> raise (Not_Implemented("Mating ref list is empty" )) );
	let (s1,d1,w1,c1,re1,nyi1,t1) = List.fold_left (fun (s,d,w,c,re,nyi,t) r -> let (s',d',w',c',re',nyi',t') = statistic1 r (h+1) b in (s+s',max d' (d-1) +1,w+w',c+c',re+re',nyi+nyi',t+t')) (1,1,0,0,0,0,0) rs in
	let _ = update_statcount h s1 w1 b in	
	(s1,d1,w1,c1,re1,nyi1,t1)
	end
 | Decomposition(_,_,rs)-> begin ( try ignore (List.hd rs) with Failure(_) -> raise (Not_Implemented("Mating ref list is empty" )) );
	let (s1,d1,w1,c1,re1,nyi1,t1) = List.fold_left (fun (s,d,w,c,re,nyi,t) r -> let (s',d',w',c',re',nyi',t') = statistic1 r (h+1) b in (s+s',max d' (d-1) +1,w+w',c+c',re+re',nyi+nyi',t+t')) (1,1,0,0,0,0,0) rs in
	let _ = update_statcount h s1 w1 b in	
	(s1,d1,w1,c1,re1,nyi1,t1)
	end
 | Confront(_,_,_,_,_,_,r1,r2) ->
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let (s2,d2,w2,c2,re2,nyi2,t2) = statistic1 r2 (h+1) b in
	let _ = update_statcount h (s1+s2+1) (w1+w2) b in
	(1+s1+s2,max d1 d2 +1,w1+w2,c1+c2,re1+re2,nyi1+nyi2,t1+t2)
 | NegEqualProp(_,_,_,r1,r2) -> 
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let (s2,d2,w2,c2,re2,nyi2,t2) = statistic1 r2 (h+1) b in
	let _ = update_statcount h (s1+s2+1) (w1+w2) b in
	(1+s1+s2,max d1 d2 +1,w1+w2,c1+c2,re1+re2,nyi1+nyi2,t1+t2)
 | EqualProp(_,_,_,r1,r2) -> 
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let (s2,d2,w2,c2,re2,nyi2,t2) = statistic1 r2 (h+1) b in
	let _ = update_statcount h (s1+s2+1) (w1+w2) b in
	(1+s1+s2,max d1 d2 +1,w1+w2,c1+c2,re1+re2,nyi1+nyi2,t1+t2) 
 | NegAequivalenz(_,_,_,r1,r2) -> 
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let (s2,d2,w2,c2,re2,nyi2,t2) = statistic1 r2 (h+1) b in
	let _ = update_statcount h (s1+s2+1) (w1+w2) b in
	(1+s1+s2,max d1 d2 +1,w1+w2,c1+c2,re1+re2,nyi1+nyi2,t1+t2)
 | Aequivalenz(_,_,_,r1,r2) -> 
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let (s2,d2,w2,c2,re2,nyi2,t2) = statistic1 r2 (h+1) b in
	let _ = update_statcount h (s1+s2+1) (w1+w2) b in
	(1+s1+s2,max d1 d2 +1,w1+w2,c1+c2,re1+re2,nyi1+nyi2,t1+t2)
 | NegEqualFunc(_,_,r1) ->
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let _ = update_statcount h (s1+1) w1 b in	
	(1+s1,d1 +1,w1,c1,re1,nyi1,t1)   
 | EqualFunc(_,_,r1) ->
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let _ = update_statcount h (s1+1) w1 b in
	(1+s1,d1 +1,w1,c1,re1,nyi1,t1)   
 | ChoiceR(_,_,_,_,r1,r2) -> 
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let (s2,d2,w2,c2,re2,nyi2,t2) = statistic1 r2 (h+1) b in
	let _ = update_statcount h (s1+s2+1) (w1+w2) b in
	(1+s1+s2,max d1 d2 +1,w1+w2,c1+c2,re1+re2,nyi1+nyi2,t1+t2)
 | Cut(l,r1,r2) -> if debug_litcount then Printf.printf "cut on %d\n" (get_literal l);
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let (s2,d2,w2,c2,re2,nyi2,t2) = statistic1 r2 (h+1) b in
	let _ = update_statcount h (s1+s2+1) (w1+w2) b in
	(1+s1+s2,max d1 d2 +1,w1+w2,c1+c2+1,re1+re2,nyi1+nyi2,t1+t2)
 | DoubleNegation(_,_,r1) ->
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let _ = update_statcount h (s1+1) w1 b in
	(1+s1,d1 +1,w1,c1,re1,nyi1,t1)   
 | Rewrite(_,_,_,r1) ->
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let _ = update_statcount h (s1+1) w1 b in
	(1+s1,d1 +1,w1,c1,re1+1,nyi1,t1)    
 | Delta(_,_,_,r1) ->
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let _ = update_statcount h (s1+1) w1 b in
	(1+s1,d1 +1,w1,c1,re1+1,nyi1,t1)
 | NYI(_,_,r1) ->
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let _ = update_statcount h (s1+1) w1 b in
	(1+s1,d1 +1,w1,c1,re1,nyi1+1,t1) 
 | Timeout -> 
	let (zs,zw,n) =if b then (1,1,1) else try Hashtbl.find !statcount h with Not_found -> (1,1,1) in
	(zs/n,1,zw/n,0,0,0,1)   
 | _ -> raise (Not_Implemented("unknown refutation case in ref_str" ))
in 
let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r 0 true in
let (s2,_,w2,_,_,_,_) = statistic1 r 0 false in
(s1,s2,d1,w1,w2,c1,re1,nyi1,t1)

(** to Latex functions**)
   
  let lpar p = if p then "(" else ""

let rpar p = if p then ")" else ""      
      
let rec stp_lat_rec a p =
  match a with
    Base(x) -> escaped x 
  | Prop -> "o"
  | Ar(b,c) -> (lpar p) ^ (stp_lat_rec b true) ^ "" ^ (stp_lat_rec c false) ^ (rpar p)

let stp_str a = stp_lat_rec a false      
   
let escaped s = let r = ref "" in (* TODO *)
   String.iter (fun c ->  if c = '_' or c = '^' or c = '$' then r := !r^"\\"^(make 1 c) else r := !r^(make 1 c) ) s;
   !r
  
let rec trm_lat_rec m lp rp =
  match m with
  | Ap(Neg,y) ->  begin
    	match y with
            | Ap(Ap(Eq(a),x1),x2) ->
              if ((lp < 40) && (rp < 40)) 
              then	(trm_lat_rec x1 lp 40) ^" \\neq "^ (trm_lat_rec x2 40 rp)
              else  "("^(trm_lat_rec x1 (-1) 40) ^" \\neq "^ (trm_lat_rec x2 40 (-1))^")"
            | False -> "\\top "
            | _ ->
              if ((lp < 0) && (rp < 30)) 
              then   "\\neg " ^ trm_lat_rec y 30 rp
              else  "(\\neg " ^ trm_lat_rec y 30 (-1) ^ ")"
    end
  | Ap(Ap(Imp,y),False)  -> 
    begin
    	match y with
            | Ap(Ap(Eq(a),x1),x2) ->
              if ((lp < 40) && (rp < 40)) 
              then	(trm_lat_rec x1 lp 40) ^" \\neq "^ (trm_lat_rec x2 40 rp)
              else  "("^(trm_lat_rec x1 (-1) 40) ^" \\neq "^ (trm_lat_rec x2 40 (-1))^")"
            | False -> "\\top "
            | _ ->
              if ((lp < 0) && (rp < 30)) 
              then   "\\neg " ^ trm_lat_rec y 30 rp
              else  "(\\neg " ^ trm_lat_rec y 30 (-1) ^ ")"
    end
  | Ap(Forall(a),Lam(_,m)) ->
     if ((lp < 0) && (rp < 0)) 
     then "\\forall "^ trm_lat_rec m (-1) (-1)
     else "( \\forall "^ trm_lat_rec m (-1) (-1)^")"
  | Ap(Forall(a),m) ->   (* Notloesung *)
     if ((lp < 0) && (rp < 0)) 
     then "\\forall "^ trm_lat_rec (Ap (shift m 0 1, DB(0,a)))(-1) (-1)
     else "( \\forall "^ trm_lat_rec (Ap (shift m 0 1, DB(0,a))) (-1) (-1)^")"   
  | Ap(Exists(a),Lam(_,m)) ->
     if ((lp < 0) && (rp < 0)) 
     then "\\exists "^ trm_lat_rec m (-1) (-1)
     else "( \\exists "^ trm_lat_rec m (-1) (-1)^")"     
  | Ap(Exists(a),m) ->
      if ((lp < 0) && (rp < 0)) 
      then "\\exists "^trm_lat_rec (Ap (shift m 0 1, DB(0,a))) (-1) (-1)
      else "(\\exists "^ trm_lat_rec (Ap (shift m 0 1, DB(0,a))) (-1) (-1)^")";     
  | Ap(Ap(Imp,x),y) ->
     if ((lp < 17) && (rp < 16)) 
     then  trm_lat_rec x lp 17^" \\rightarrow "^ trm_lat_rec y 16 rp 
     else "("^ trm_lat_rec x (-1) 17^" \\rightarrow "^ trm_lat_rec y 16 (-1)^ ")"
  | Ap(Ap(And,m1),m2) ->
      if ((lp < 20) && (rp < 21)) 
      then trm_lat_rec m1  lp 20 ^ " \\wedge "^ trm_lat_rec m2  21 rp
	  else "("^ trm_lat_rec m1  (-1) 20^ " \\wedge "^ trm_lat_rec m2  21 (-1)^")"
  | Ap(Ap(Or,m1),m2) ->
      if ((lp < 18) && (rp < 19)) 
      then trm_lat_rec m1  lp 18^ " \\vee "^ trm_lat_rec m2  19 rp
	  else "("^ trm_lat_rec m1 (-1) 18^" \\vee "^trm_lat_rec m2  19 (-1)^ ")"
  | Ap(Ap(Iff,m1),m2) ->
      if ((lp < 14) && (rp < 14)) 
      then trm_lat_rec m1  lp 14^ " \\leftrightarrow "^ trm_lat_rec m2  14 rp
      else "("^trm_lat_rec m1 (-1) 14^" \\leftrightarrow "^ trm_lat_rec m2  14 (-1)^")"	       
  | Ap(Ap(Eq(a),x1),x2) ->
    if ((lp < 40) && (rp < 40)) 
    then	(trm_lat_rec x1 lp 40) ^" = "^ (trm_lat_rec x2 40 rp)
              else  "("^(trm_lat_rec x1 (-1) 40) ^" = "^ (trm_lat_rec x2 40 (-1))^")"
  | Name(x,_) -> escaped x 
  | False -> "\\bot"
  | True -> "\\top"  
  | Imp -> "\\rightarrow"

  | Iff -> "\\leftrightarrow"
  | And -> "\\wedge"
  | Or  -> "\\vee" 
  | Neg -> "\\neg "
  | Forall(_) -> "\\forall"
  | Exists(_) -> "\\exists"  
  | Eq(_) -> "="
  | Choice(_) -> "\\varepsilon"
  | DB(i,_) -> " \\hat{" ^ (string_of_int i) ^"}"
  | Lam(a,m) -> 
     if ((lp < 0) && (rp < 0)) 
     then "\\lambda:" ^ escaped (stp_str a) ^ "." ^ trm_lat_rec m (-1) (-1)
     else "( \\lambda:" ^ escaped (stp_str a) ^ "." ^ trm_lat_rec m  (-1) (-1)^")"
  | Ap(m1,m2) ->
    if ((lp < 5000) && (rp < 5001)) 
    then trm_lat_rec m1 lp 5000^ " ~ "^trm_lat_rec m2 5001 rp
    else "("^trm_lat_rec m1 (-1) 5000^ " ~ "^trm_lat_rec m2 5001 (-1)^")"

let trm_lat m = "$" ^trm_lat_rec m (-1) (-1) ^ "$"
  
let rec cformat n =  if n =0 then "" else "|c" ^ cformat (n-1) 
  
let rec ref_lat r =
  match r with
 | Conflict(s,ns) -> "$\\lightning$"
 | Fal(_) -> "$\\lightning$"
 | NegRefl(s) -> "$\\lightning$"
 | Implication(h,s,t,r1,r2) -> 					"\\begin{tabular}{@{}c|c@{}} \n " 
			^"\\multicolumn{2}{c}{\\textcolor[rgb]{0, 0, 1}{$\\mathcal T _{\\rightarrow}$}} \\\\ \n"							
								^ (trm_lat s) ^" & "^ (trm_lat t)^ " \\\\ \n"
   								^ ref_lat r1 ^" & \n"^ ref_lat r2 ^" \\\\ \n"
   								^ "\\end{tabular} \n " 

 | Disjunction(h,s,t,r1,r2) ->					 "\\begin{tabular}{@{}c|c@{}} \n " 
								^"\\multicolumn{2}{c}{\\textcolor[rgb]{0, 0, 1}{$\\mathcal T _{\\vee}$}} \\\\ \n"  
								^ (trm_lat s) ^" & "^ (trm_lat t)^ " \\\\ \n"
   								^ ref_lat r1 ^" & \n"^ ref_lat r2 ^" \\\\ \n"
   								^ "\\end{tabular} \n " 

 | NegConjunction(h,s,t,r1,r2) -> "\\begin{tabular}{c} \n "	^"\\textcolor[rgb]{0, 0, 1}{$\\mathcal T _{\\neg\\wedge}$} \\\\ \n"
								^"\\begin{tabular}{c|c} \n " 
								^ (trm_lat s) ^" & "^ (trm_lat t)^ " \\\\ \n"
   								^ ref_lat r1 ^" & \n"^ ref_lat r2 ^" \\\\ \n"
   								^ "\\end{tabular} \n " 
				^ "\\end{tabular} \n " 
   
 | NegImplication(h,s,t,r1) ->"\\begin{tabular}{c} \n " 
   								^"\\textcolor[rgb]{0, 0, 1}{$\\mathcal T _{\\neg \\rightarrow}$}  \\\\ \n"
								^ (trm_lat s) ^ " \\\\ \n"
								^ (trm_lat t) ^ " \\\\ \n"
   								^ ref_lat r1  ^" \\\\ \n"
   			^ "\\end{tabular} \n " 

 | Conjunction(h,s,t,r1) ->"\\begin{tabular}{c} \n " 
   								^"\\textcolor[rgb]{0, 0, 1}{$\\mathcal T _{\\wedge}$}   \\\\ \n"
								^ (trm_lat s) ^ " \\\\ \n"
								^ (trm_lat t) ^ " \\\\ \n"
   								^ ref_lat r1  ^" \\\\ \n"
			^ "\\end{tabular} \n "

 | NegDisjunction(h,s,t,r1) ->"\\begin{tabular}{c} \n " 
   								^"\\textcolor[rgb]{0, 0, 1}{$\\mathcal T _{\\neg\\vee}$}   \\\\ \n"
								^ (trm_lat s) ^ " \\\\ \n"
								^ (trm_lat t) ^ " \\\\ \n"
   								^ ref_lat r1  ^" \\\\ \n"  
   			^ "\\end{tabular} \n " 
  
 | All(h,s,r1,a,m,n) ->"\\begin{tabular}{c} \n " 
   								^"\\textcolor[rgb]{0, 0, 1}{$\\mathcal T _{\\forall}$}   \\\\ \n"
								 ^ (trm_lat s) ^ " \\\\ \n"
   								^ ref_lat r1  ^" \\\\ \n"
   			^ "\\end{tabular} \n " 

 | NegAll(h,s,r1,a,m,x) ->"\\begin{tabular}{c} \n " 
   								^"\\textcolor[rgb]{0, 0, 1}{$\\mathcal T _{\\neg \\forall}$}  \\\\ \n"
								^ (trm_lat s) ^ " \\\\ \n"
   								^ ref_lat r1  ^" \\\\ \n"
   			^ "\\end{tabular} \n " 
 
 | Exist(h,s,r1,a,m,x) ->"\\begin{tabular}{c} \n " 
   								^"\\textcolor[rgb]{0, 0, 1}{$\\mathcal T _{\\exists}$}    \\\\ \n"
								^ (trm_lat s) ^ " \\\\ \n"
   								^ ref_lat r1  ^" \\\\ \n"
   			^ "\\end{tabular} \n "   

 | NegExist(h,s,r1,a,m,n) ->"\\begin{tabular}{c} \n " 
   								^"\\textcolor[rgb]{0, 0, 1}{$\\mathcal T _{\\neg\\exists}$}   \\\\ \n"
								^ (trm_lat s) ^ " \\\\ \n"
   								^ ref_lat r1  ^" \\\\ \n"
   			^ "\\end{tabular} \n "     

 | Mating(h1,h2, ss, rs) ->					"\\begin{tabular}{@{}" ^(String.concat "|" (List.map (fun s->"c") ss))^ "@{}} \n " 
						^"\\multicolumn{"^ (string_of_int (List.length ss)) ^"}{c}{\\textcolor[rgb]{0, 0, 1}{$\\mathcal T _{MAT}$}} \\\\ \n" 
   								^ (String.concat " & " (List.map (fun s  -> trm_lat s ) ss)) ^" \\\\ \n"
   								^ (String.concat " & \n" (List.map (fun r  ->ref_lat r ) rs)) ^" \\\\ \n"
   								^ "\\end{tabular} \n " 

 | Decomposition(h1, ss, rs) -> "\\begin{tabular}{@{}" ^(String.concat "|" (List.map (fun s->"c") ss))^ "@{}} \n " 
				^"\\multicolumn{"^ (string_of_int (List.length ss)) ^"}{c}{\\textcolor[rgb]{0, 0, 1}{$\\mathcal T _{DEC}$}} \\\\ \n" 
   								^ (String.concat " & " (List.map (fun s  -> trm_lat s ) ss)) ^" \\\\ \n"
   								^ (String.concat " & \n" (List.map (fun r  ->ref_lat r ) rs)) ^" \\\\ \n"
   								^ "\\end{tabular} \n " 

 | Confront(h1,h2,su,tu,sv,tv,r1,r2) -> 			"\\begin{tabular}{@{}c|c@{}} \n " 
								^"\\multicolumn{2}{c}{\\textcolor[rgb]{0, 0, 1}{$\\mathcal T _{CON}$}} \\\\ \n"
   								^ (trm_lat su) ^" & "^ (trm_lat sv)^ " \\\\ \n"
								^ (trm_lat tu) ^" & "^ (trm_lat tv)^ " \\\\ \n"
   								^ ref_lat r1 ^" & \n"^ ref_lat r2 ^" \\\\ \n"
   								^ "\\end{tabular} \n" 

 | NegEqualProp(h,s,t,r1,r2) -> 				"\\begin{tabular}{@{}c|c@{}} \n " 
								^"\\multicolumn{2}{c}{\\textcolor[rgb]{0, 0, 1}{$\\mathcal T _{BE}$}} \\\\ \n"
								^ (trm_lat s)^" & "^ (trm_lat (neg s))^ " \\\\ \n"
								^(trm_lat (neg t))^" & "^ (trm_lat t)^ " \\\\ \n"
   								^ ref_lat r1 ^" & \n"^ ref_lat r2 ^" \\\\ \n"
   								^ "\\end{tabular} \n " 

 | NegAequivalenz(h,s,t,r1,r2) ->  "\\begin{tabular}{c} \n " ^"\\textcolor[rgb]{0, 0, 1}{$\\mathcal T _{\\neg \\leftrightarrow}$} \\\\ \n"
								^"\\begin{tabular}{c|c} \n " 
								^ (trm_lat s)^" & "^ (trm_lat (neg s))^ " \\\\ \n"
								^(trm_lat (neg t))^" & "^ (trm_lat t)^ " \\\\ \n"
   								^ ref_lat r1 ^" & \n"^ ref_lat r2 ^" \\\\ \n"
   								^ "\\end{tabular} \n " 
				^ "\\end{tabular} \n" 

 | EqualProp(h,s,t,r1,r2) ->  					"\\begin{tabular}{@{}c|c@{}} \n " 
								^"\\multicolumn{2}{c}{\\textcolor[rgb]{0, 0, 1}{$\\mathcal T _{BQ}$}} \\\\ \n" 	
								^ (trm_lat s)^" & "^ (trm_lat (neg s))^ " \\\\ \n"
								^(trm_lat t)^" & "^ (trm_lat (neg t))^ " \\\\ \n"
   								^ ref_lat r1 ^" & \n"^ ref_lat r2 ^" \\\\ \n"
   								^ "\\end{tabular} \n " 

 | Aequivalenz(h,s,t,r1,r2) -> "\\begin{tabular}{c} \n " ^"\\textcolor[rgb]{0, 0, 1}{$\\mathcal T _{\\leftrightarrow}$}  \\\\ \n"
								^ "\\begin{tabular}{c|c} \n " 
								^ (trm_lat s)^" & "^ (trm_lat (neg s))^ " \\\\ \n"
								^(trm_lat t)^" & "^ (trm_lat (neg t))^ " \\\\ \n"
   								^ ref_lat r1 ^" & \n"^ ref_lat r2 ^" \\\\ \n"
   								^ "\\end{tabular} \n " 
				^ "\\end{tabular} \n" 

 | NegEqualFunc(h,s,r1) ->"\\begin{tabular}{c} \n " 
   								^"\\textcolor[rgb]{0, 0, 1}{$\\mathcal T _{FE}$}  \\\\ \n"
								^ (trm_lat s) ^ " \\\\ \n"
   								^ ref_lat r1  ^" \\\\ \n"
   				^ "\\end{tabular} \n " 

 | EqualFunc(h,s,r1) ->"\\begin{tabular}{c} \n " 
   								^"\\textcolor[rgb]{0, 0, 1}{$\\mathcal T _{FQ}$}   \\\\ \n"
								^ (trm_lat s) ^ " \\\\ \n"
   								^ ref_lat r1  ^" \\\\ \n"
   			^ "\\end{tabular} \n " 

 | ChoiceR(eps,pred,s,t,r1,r2) -> 				"\\begin{tabular}{@{}c|c@{}} \n " 
								^"\\multicolumn{2}{c}{\\textcolor[rgb]{0, 0, 1}{$\\mathcal T _{\\varepsilon}$}} \\\\ \n"
								^ (trm_lat s) ^" & "^ (trm_lat t)^ " \\\\ \n"
   								^ ref_lat r1 ^" & \n"^ ref_lat r2 ^" \\\\ \n"
   								^ "\\end{tabular} \n "

 | Cut(s,r1,r2) ->  "\\begin{tabular}{c|c} \n \\textcolor[rgb]{1, 0, 0}{" 
   								^ (trm_lat (s)) ^"} & \\textcolor[rgb]{1, 0, 0}{"^ (trm_lat (preneg s))^ "} \\\\ \n"
   								^ ref_lat r1 ^" & \n"^ ref_lat r2 ^" \\\\ \n"
   			^ "\\end{tabular} \n "    

 | DoubleNegation(h,s,r1) ->"\\begin{tabular}{c} \n " 
   								^"\\textcolor[rgb]{0, 0, 1}{$\\mathcal T _{\\neg\\neg}$} " ^"   \\\\ \n"
								^ (trm_lat s) ^ " \\\\ \n"
   								^ ref_lat r1  ^" \\\\ \n"
   				^ "\\end{tabular} \n "

 | Rewrite(prefix,h,s,r1) ->"\\begin{tabular}{c} \n " 
   					^"\\textcolor[rgb]{1, 0,0}{ "^ (trm_lat (onlybetanorm (Ap(prefix,h)))) ^" $\\Downarrow$ }" ^"   \\\\ \n"
								^ (trm_lat (onlybetanorm (Ap(prefix,s)))) ^ " \\\\ \n"
   								^ ref_lat r1  ^" \\\\ \n"
   				^ "\\end{tabular} \n "  
 
 | Delta(h,s,x,r1) ->	ref_lat r1  

 | NYI(h,s,r1) ->"\\begin{tabular}{c} \n " 
   								^"\\textcolor[rgb]{1, 0,1}{"^ (trm_lat h) ^" $\\downarrow$} \\\\ \n"
								^ (trm_lat s) ^ " \\\\ \n"
   								^ ref_lat r1  ^" \\\\ \n"
   			^ "\\end{tabular} \n "  
 | Timeout -> "\\textcolor[rgb]{1, 0,0}{X}"
    
let rec ref_lat1 ts r = match ts with
  | [] -> ref_lat r
  | (t::tr) -> trm_lat t ^ " \\\\ \n" ^ ref_lat1 tr r     
 

(** Translation **)

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

let onlynegnorm m =  
  let (n,_) = negnorm1 m in onlybetanorm n 

let coqnorm m =
  let m = betanorm name_def_prenorm m in  
  let (n,_) = negnorm1 m in n 

  (* TODO: environment module  *)

let trm_eq s t = (* TODO this is a simple solution*)
let s = coqnorm s in
let t = coqnorm t in
match (s,t) with 
| ( Ap(Ap(Eq(a),s1),s2) , Ap(Ap(Eq(a'),t1),t2) ) when a=a' -> ( (s1=t1) && (s2=t2) ) || ( (s1=t2) && (s2=t1) ) 
| ( Ap(Ap(Imp,Ap(Ap(Eq(a),s1),s2)),False), Ap(Ap(Imp,Ap(Ap(Eq(a'),t1),t2)),False) ) when a=a' -> ( (s1=t1) && (s2=t2) ) || ( (s1=t2) && (s2=t1) ) 
| _ -> s=t

let trm_eq' s t = (* TODO this is a simple solution*)
match (s,t) with 
| ( Ap(Ap(Eq(a),s1),s2) , Ap(Ap(Eq(a'),t1),t2) ) when a=a' -> ( (s1=t1) && (s2=t2) ) || ( (s1=t2) && (s2=t1) ) 
| ( Ap(Ap(Imp,Ap(Ap(Eq(a),s1),s2)),False), Ap(Ap(Imp,Ap(Ap(Eq(a'),t1),t2)),False) ) when a=a' -> ( (s1=t1) && (s2=t2) ) || ( (s1=t2) && (s2=t1) ) 
| _ -> s=t
  
let get_prenorm branch trm = try snd (List.find (fun (a,p) -> trm_eq' a trm) branch)  
                             with Not_found ->  raise  (Not_Implemented("get_prenorm can't find term " ^ (trm_str trm)))
 
let normalize pt = norm name_def (logicnorm pt)  
  
let rec termNotFreeIn m i =
let m = coqnorm m in
  match m with
    DB(j,_) when i = j -> false
  | Ap(m1,m2) -> (termNotFreeIn m1 i) && (termNotFreeIn m2 i)
  | Lam(a,m1) -> termNotFreeIn m1 (i + 1)
  | _ -> true  

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
  | _ -> raise (GenericSyntaxError("Unexpected type case - were logical constants normalized away? " ^ (trm_str m)))

exception Delta_reduction of string * trm

let rec rewrite_refutation1 b r trm ptrm n =  
   match ptrm with
  | Name(x,a) -> (* delta *)
      begin
	try
	let def = onlynegnorm (Hashtbl.find name_def_prenorm x) in
	raise (Delta_reduction (x,def))
	with
	| Not_found -> raise (Not_Implemented("translate can't find definition of "^ x)) 
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
  | True -> (DB(n,Prop),True,imp False False,true,Prop) 
  | Neg -> (DB(n,Ar(Prop,Prop)),Neg,Lam(Prop,imp (DB(0,Prop)) False),false,Ar(Prop,Prop))  
  | Or ->  (DB(n,Ar(Prop,Ar(Prop,Prop))),Or,Lam(Prop,Lam(Prop,disj (DB(1,Prop)) (DB(0,Prop)))),true,Ar(Prop,Ar(Prop,Prop))) 
  | And -> if  debug_rewrite then Printf.printf  "Rewrite And \n";
	(DB(n,Ar(Prop,Ar(Prop,Prop))),And,Lam(Prop,Lam(Prop,conj (DB(1,Prop)) (DB(0,Prop)))),true,Ar(Prop,Ar(Prop,Prop)))   
  | Iff -> (DB(n,Ar(Prop,Ar(Prop,Prop))),Iff,Lam(Prop,Lam(Prop,iff (DB(1,Prop)) (DB(0,Prop)))),true,Ar(Prop,Ar(Prop,Prop))) 
  | Exists(a) ->
	let ao = Ar(a,Prop) in
	let aoo = Ar(Ar(a,Prop),Prop) in
    (DB(n,aoo),Exists(a),Lam(ao,exists a (Ap(DB(1,ao),DB(0,a)))),true,aoo) 
  | Ap(m1,m2) -> if  debug_rewrite then Printf.printf  "Rewrite looks at %s \n" (trm_str ptrm);
      if normalize m1 <> m1 
      then let (pre,pt,pt',bb,stp)= rewrite_refutation1 b r trm m1 n in 
        (Ap(pre,m2),pt,pt',bb,stp) 
      else let (pre,pt,pt',bb,stp)= rewrite_refutation1 b r trm m2 n in 
        (Ap(m1,pre),pt,pt',bb,stp)
  | Lam(a,m) ->if  debug_rewrite then Printf.printf  "Rewrite looks at %s \n" (trm_str ptrm);
    let (pre,pt,pt',bb,stp)= rewrite_refutation1 b r trm m (n+1) in 
    (Lam(a,pre),pt,pt',bb,stp) 
  | _ -> raise (Not_Implemented("translate can't normalize"))  

(** rewrite first - Satallax refutation **)

let rec satallax_rewrite b nb r trm ptrm =  
    try 
    let (pre,pt,pt',bb,stp)= rewrite_refutation1 b r trm ptrm 0 in
    let prefix= Lam(stp,pre) in
    let ptrm' = onlybetanorm (Ap(prefix,pt')) in
  if bb then begin
  if debug_translation then Printf.printf  "Rewrite %s into %s \n" (trm_str ptrm) (trm_str ptrm');
  Rewrite(prefix,pt,pt',satallax_translation ((trm,ptrm')::(List.tl b)) nb r)
  end
  else  satallax_translation ((trm,ptrm')::(List.tl b)) nb r 
    with Delta_reduction(x,def) ->  let ptrm'= onlybetanorm (namesubst ptrm x def) in
			Delta(ptrm,ptrm',x,satallax_translation ((trm,ptrm')::(List.tl b)) nb r)
	| Not_Implemented(_)->  if debug_translation then Printf.printf  "NYI %s \ninto %s \n" (trm_str ptrm) (trm_str trm);
		NYI(ptrm,trm,satallax_translation ((trm,trm)::(List.tl b)) nb r) (* This should never happen*)

and satallax_translation b nb r =
match b with
	 [] -> sat_translation (List.rev nb) r
	|((trm,ptrm)::br)-> 
		if trm_eq trm ptrm 
		then satallax_translation br ((trm,ptrm)::nb) r
		else satallax_rewrite b nb r trm ptrm

and sat_translation b r = 
 match r with
 | Conflict(s,ns) ->  begin
   let p = get_prenorm b s in
   let np = get_prenorm b ns in
   if debug_translation then Printf.printf  "Conflict %s\n" (trm_str p);
   if trm_eq np (neg p) then Conflict(p,np)
   else if trm_eq p (neg np) then Conflict(np,p)
   else raise (Not_Implemented("Error with Conflict between " ^ (trm_str p) ^" and " ^(trm_str np))) 
 end  
 | Fal(s) -> begin
   let p = get_prenorm b s in
     if p = False then Fal(p) else raise (Not_Implemented("Error with Fal " ^ (trm_str p)))
 end 
 | NegRefl(s) -> begin
   let p = get_prenorm b s in
   match p with
     | Ap(Ap(Imp,Ap(Ap(Eq(_),m1),m2)),False) when m1 = m2 -> NegRefl(p)
     | _ -> raise (Not_Implemented("Error with NegRefl " ^ (trm_str p)))
     end  
 | Implication(h,s,t,r1,r2) -> begin
   let p = get_prenorm b h in
   if debug_translation then Printf.printf  "Implication %s = %s\n" (trm_str h) (trm_str p);
   match p with  
    | (Ap(Ap(Imp,m1),m2)) -> 
          Implication(p,neg m1,m2,satallax_translation ((s,neg m1)::[]) b r1,satallax_translation ((t,m2)::[]) b r2)
    | _ -> raise (Not_Implemented("Error with Implication " ^ (trm_str p)))
    end   
 | NegImplication(h,s,t,r1)   -> begin 
   let p = get_prenorm b h in 
   if debug_translation then Printf.printf  "NegImplication %s\n" (trm_str p);
   match p with 
   | (Ap(Ap(Imp,(Ap(Ap(Imp,m1),m2))),False)) -> begin
      NegImplication(p,m1,neg m2,satallax_translation ((s,m1)::(t,neg m2)::[]) b r1)
    end    	
   | _ ->  raise (Not_Implemented("Error with NegImplication " ^ (trm_str p)))
    end
 | All(h,s,r1,a,m,n) -> begin
   let p = get_prenorm b h in
   if debug_translation then Printf.printf  "All %s\n" (trm_str p);
   match p with  
    | (Ap(Forall(a'),m1)) -> 
      let m' = onlybetanorm (Ap(m1,n)) in
	All(p,m',satallax_translation ((s,m')::[]) b r1,a,m,n)   
    | _ ->   raise (Not_Implemented("Error with All " ^ (trm_str p)))
    end  
 | NegAll(h,s,r1,a,m,x) ->
      begin
   let p = get_prenorm b h in
   if debug_translation then Printf.printf  "NegAll %s\n" (trm_str p);
   match p with  
    | (Ap(Ap(Imp,Ap(Forall(a'),m1)),False)) -> 
	let m' = neg (onlybetanorm (Ap(m1,Name(x,a)))) in
	NegAll(p,m',satallax_translation ((s,m')::[]) b r1,a,m,x)    
    | _ -> raise (Not_Implemented("Error with NegAll " ^ (trm_str p)))
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
        	if not (trm_eq g1  g2) then  raise (Mating_Missmatch("unequal heads")) else
 		List.fold_left2 (fun a b c ->if tpof b = tpof c then (neg (eq (tpof b) b c))::a 
						else raise (Mating_Missmatch("type missmatch in spine")) ) [] args1 args2
     		| (Ap(Ap(Imp,Ap(f1,m1)),False), Ap(f2,m2)) -> 
		let (g1,args1)= head_spine (Ap(f2,m2)) in 
		let (g2,args2)= head_spine (Ap(f1,m1)) in
		if g1 <> g2 then  raise (Mating_Missmatch("unequal heads")) else
 		List.fold_left2 (fun a b c ->if tpof b = tpof c then (neg (eq (tpof b) b c))::a 
						else raise (Mating_Missmatch("type missmatch in spine")) ) [] args1 args2
     		| _ -> raise (Mating_Missmatch("terms can't be mated"))
    	in
	let pss = List.rev pss in  
	begin
	List.iter2 (fun ps s -> if not (trm_eq s (normalize ps)) 
				then raise (Mating_Missmatch("unexpected result :" ^ (trm_str ps)^" <> "^ (trm_str s))) ) pss ss; 
    	Mating(p,np, pss, List.map2 (fun ps (s,r) -> satallax_translation ((s,ps)::[]) b r) pss h)
	end
   	with Mating_Missmatch(mess) -> raise (Not_Implemented("Error with Mating between " ^ (trm_str p) ^" and " ^(trm_str np)^":"^ mess)) 
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
        if g1 <> g2 then  raise (Mating_Missmatch("unequal heads")) else
 	List.fold_left2 (fun a b c ->if tpof b = tpof c 
					then (neg (eq (tpof b) b c))::a else raise (Mating_Missmatch("type missmatch in spine")) ) [] args1 args2
     | _ -> raise (Mating_Missmatch("term can't be decomposed"))
    in    
	let pss = List.rev pss in 
	List.iter2 (fun ps s -> if not (trm_eq s (normalize ps)) 
				then raise (Mating_Missmatch("unexpected result :" ^ (trm_str ps)^" <> "^ (trm_str s))) ) pss ss;  
	Decomposition(p ,pss, List.map2 (fun ps (s,r) -> satallax_translation ((s,ps)::[]) b r) pss h)
   	with Mating_Missmatch(mess) ->raise (Not_Implemented("Error with Decomposition " ^ (trm_str p)^":"^ mess))
 	end  
| Confront(h1,h2,su,tu,sv,tv,r1,r2) ->begin 
   let p = get_prenorm b h1 in
   let np = get_prenorm b h2 in
   if debug_translation then Printf.printf  "Confronting %s\n" (trm_str p);
   let (bb,r) = begin match (p,np) with
			| (  Ap(Ap(Eq(a),s),t)   ,  Ap(Ap(Imp, Ap(Ap(Eq(a'),u),v) ),False)  ) when a=a' -> begin
				let (psu,ptu,psv,ptv)=(neg (eq a s u),neg (eq a t u),neg (eq a s v),neg (eq a t v)) in
     if trm_eq psu su then 
	(true,Confront(p,np,psu,ptu,psv,ptv, satallax_translation ((su,psu)::(tu,ptu)::[]) b r1, satallax_translation ((sv,psv)::(tv,ptv)::[]) b r2 ) )
else if trm_eq psu tu then
	(true,Confront(p,np,psu,ptu,psv,ptv, satallax_translation ((tu,psu)::(su,ptu)::[]) b r1, satallax_translation ((tv,psv)::(sv,ptv)::[]) b r2 ) )
else if trm_eq psu sv then
	(true,Confront(p,np,psu,ptu,psv,ptv, satallax_translation ((sv,psu)::(tv,ptu)::[]) b r2, satallax_translation ((su,psv)::(tu,ptv)::[]) b r1 ) )
else if trm_eq psu tv then
	(true,Confront(p,np,psu,ptu,psv,ptv, satallax_translation ((tv,psu)::(sv,ptu)::[]) b r2, satallax_translation ((tu,psv)::(su,ptv)::[]) b r1 ) ) 
else  (false,Fal(False)) end
			| (  Ap(Ap(Imp, Ap(Ap(Eq(a'),u),v) ),False)  ,  Ap(Ap(Eq(a),s),t) )  when a=a' -> begin
				let (psu,ptu,psv,ptv)=(neg (eq a s u),neg (eq a t u),neg (eq a s v),neg (eq a t v)) in
     if trm_eq psu su then 
	(true,Confront(p,np,psu,ptu,psv,ptv, satallax_translation ((su,psu)::(tu,ptu)::[]) b r1, satallax_translation ((sv,psv)::(tv,ptv)::[]) b r2 ) )
else if trm_eq psu tu then
	(true,Confront(p,np,psu,ptu,psv,ptv, satallax_translation ((tu,psu)::(su,ptu)::[]) b r1, satallax_translation ((tv,psv)::(sv,ptv)::[]) b r2 ) )
else if trm_eq psu sv then
	(true,Confront(p,np,psu,ptu,psv,ptv, satallax_translation ((sv,psu)::(tv,ptu)::[]) b r2, satallax_translation ((su,psv)::(tu,ptv)::[]) b r1 ) )
else if trm_eq psu tv then
	(true,Confront(p,np,psu,ptu,psv,ptv, satallax_translation ((tv,psu)::(sv,ptu)::[]) b r2, satallax_translation ((tu,psv)::(su,ptv)::[]) b r1 ) ) 
else  (false,Fal(False)) end
			| _ -> (false,Fal(False)) end 
  in
   if bb then  
    r
   else raise (Not_Implemented("Error with Confront between " ^ (trm_str p) ^" and " ^(trm_str np))) 
 end 
| NegEqualProp(h,s,t,r1,r2) -> begin
   let p = get_prenorm b h in
   if debug_translation then Printf.printf  "boolean extensionality %s\n" (trm_str p);
   match p with  
     | (Ap(Ap(Imp,Ap(Ap(Eq(Prop),m1),m2)),False)) -> begin
            if  trm_eq (normalize m2)  t && trm_eq (normalize m1)  s then
            NegEqualProp(p,m1,m2, satallax_translation ((s,m1)::(normneg t,neg m2)::[]) b r1,satallax_translation((normneg s,neg m1)::(t,m2)::[]) b r2)
 	    else 
	    if   trm_eq (normalize m1)  t && trm_eq (normalize m2)  s then
            NegEqualProp(p,m1,m2, satallax_translation ((t,m1)::(normneg s,neg m2)::[]) b r2,satallax_translation((normneg t,neg m1)::(s,m2)::[]) b r1)
 	    else raise (Not_Implemented("Error with NegEqualProp " ^ (trm_str p)))
          end     	  
    | _ ->  raise (Not_Implemented("Error with NegEqualProp " ^ (trm_str p)))
    end  
 | EqualProp(h,s,t,r1,r2) -> begin
   let p = get_prenorm b h in
   if debug_translation then Printf.printf  "boolean Equality %s\n" (trm_str p);
   match p with  (* TODO : this might or might not work*)
     | Ap(Ap(Eq(Prop),m1),m2) -> begin
            if  trm_eq (normalize m2)  t && trm_eq (normalize m1)  s then
            EqualProp(p,m1,m2, satallax_translation ((s,m1)::(t,m2)::[]) b r1,satallax_translation ((normneg s,neg m1)::(normneg t,neg m2)::[]) b r2)
 	    else
	    if  trm_eq (normalize m1)  t && trm_eq (normalize m2)  s then
            EqualProp(p,m1,m2, satallax_translation ((s,m2)::(t,m1)::[]) b r1,satallax_translation ((normneg s,neg m2)::(normneg t,neg m1)::[]) b r2)
 	    else raise (Not_Implemented("Error with EqualProp " ^ (trm_str p)))
          end     	  
    | _ ->  raise (Not_Implemented("Error with EqualProp " ^ (trm_str p)))
    end  
 | NegEqualFunc(h,s,r) -> begin (* TODO solve symmetry*)
   let p = get_prenorm b h in
   if debug_translation then Printf.printf  "functional extensionality %s\n" (trm_str p);
   if not (trm_eq p h) then raise (Not_Implemented("Error with NegEqualFunc" ^ (trm_str p)) ) else
   match p with  (* TODO : this might or might not work*)
     | (Ap(Ap(Imp,Ap(Ap(Eq(Ar(a,a')),m1),m2)),False)) -> 
	begin
	let left = (Ap(shift m1 0 1,DB(0,a))) in
	let right =  (Ap(shift m2 0 1,DB(0,a))) in
	let aao= Ar(a',Ar(a',Prop)) in
	let prefix= Lam(aao, neg ( forall a (Ap(Ap(DB(1,aao),left),right)) )) in
	let ps =  onlybetanorm (Ap(prefix,Eq(a'))) in
	if (coqnorm ps = s) then NegEqualFunc(p,ps, satallax_translation ((s,ps)::[]) b r)
	else 
	begin
	let ps' = onlybetanorm (Ap(prefix,Lam(a',Lam(a',Ap(Ap(Eq(a'),DB(0,a')),DB(1,a'))))  )) in 
	if (coqnorm ps' = s) 
	then NegEqualFunc(p,ps, Rewrite(prefix,Eq(a'), Lam(a',Lam(a',Ap(Ap(Eq(a'),DB(0,a')),DB(1,a')))) ,satallax_translation ((s,ps')::[]) b r) )
	else raise (Not_Implemented("Error with NegEqualFunc: Unexpected result " ^ (trm_str ps)))
	end        
	end     	 
    | _ -> raise (Not_Implemented("Error with NegEqualFunc " ^ (trm_str p)))
    end   
 | EqualFunc(h,s,r) -> begin (* TODO solve symmetry*)
   let p = get_prenorm b h in
   if debug_translation then Printf.printf  "functional Equality %s\n" (trm_str h);
   if not (trm_eq p h) then raise (Not_Implemented("Error with EqualFunc" ^ (trm_str p)) ) else
   match p with  (* TODO : this might or might not work*)
     | Ap(Ap(Eq(Ar(a,a')),m1),m2) -> begin
	 let left = (Ap(shift m1 0 1,DB(0,a))) in
	let right =  (Ap(shift m2 0 1,DB(0,a))) in
	let aao= Ar(a',Ar(a',Prop)) in
	let prefix= Lam(aao,( forall a (Ap(Ap(DB(1,aao),left),right)) )) in
	let ps =  onlybetanorm (Ap(prefix,Eq(a'))) in
		if (coqnorm ps = s) then EqualFunc(p,ps, satallax_translation ((s,ps)::[]) b r)
		else let ps' = onlybetanorm (Ap(prefix,Lam(a',Lam(a',Ap(Ap(Eq(a'),DB(0,a')),DB(1,a'))))  )) in 
		if (coqnorm ps' = s) 
		then EqualFunc(p,ps,Rewrite(prefix,Eq(a'), Lam(a',Lam(a',Ap(Ap(Eq(a'),DB(0,a')),DB(1,a'))))  ,satallax_translation ((s,ps')::[]) b r) )
		else raise (Not_Implemented("Error with EqualFunc: Unexpected result " ^ (trm_str ps) ^ "  s: " ^ (trm_str s)))
          end         	 
    | _ -> raise (Not_Implemented("Error with EqualFunc : cant apply on " ^ (trm_str p)))
    end 
 | ChoiceR(eps,pred,s,t,r1,r2) -> (* check for prenorm s in b? - NO! *)
	let a = match tpof pred  with Ar(a,Prop) -> a | _ -> raise (Not_Implemented  "Error pred is not of type a --> o") in	
	let ps = onlybetanorm (forall a (neg (ap (shift pred 0 1,DB(0,a)) ) ) ) in
	let pt = onlybetanorm ( ap (pred,ap (eps,pred)) ) in
   	if debug_translation then Printf.printf  "Choice %s\n" (trm_str pred); 
	ChoiceR(eps,pred,ps,pt,satallax_translation [(s, ps)] b r1,satallax_translation [(t,pt)] b r2)   
 | Cut(s,r1,r2) -> 
	if debug_translation then Printf.printf  "Cut %s\n" (trm_str s); 
	Cut(s,sat_translation ((s,s)::b) r1,satallax_translation [(normneg s,neg s)] b r2)   
   (* Other cases shouldn't occur, they only appear on prenorm_refutations *)
 | Timeout -> Timeout
 | Rewrite(pre,pt,pt',r1) -> 
			let trm = onlybetanorm (Ap(pre,pt)) in
			if debug_translation then Printf.printf  "Rewrite %s\n" (trm_str trm); 
			let ptrm' =  onlybetanorm (Ap(pre,pt')) in
			let ptrm =  norm name_def (Ap(pre,pt')) in
			 Rewrite(pre,pt,pt',satallax_translation [(ptrm,ptrm')] b r1 ) 
 | _ -> raise (Not_Implemented("unexpected refutation case in Sat_translation"))
   

(** rewrite last - prenorm refutation **)

let rec rewrite_refutation b r trm ptrm delta =  (* TODO: turn ptrm into a specific trm*)
    try
    let (pre,pt,pt',bb,stp)= rewrite_refutation1 b r trm ptrm 0 in
    let prefix= Lam(stp,pre) in
    let ptrm' = onlybetanorm (Ap(prefix,pt')) in
  if bb then
  Rewrite(prefix,pt,pt',translate_refutation ((trm,ptrm')::b) r)
  else  translate_refutation ((trm,ptrm')::b) r 
    with Delta_reduction(x,def) ->  let ptrm'= onlybetanorm (namesubst ptrm x def) in
			if delta then Delta(ptrm,ptrm',x,translate_refutation ((trm,ptrm')::b) r)
			else translate_refutation ((trm,ptrm')::b) r
	|Not_Implemented(_)->  NYI(ptrm,trm,translate_refutation ((trm,trm)::b) r) (* This should never happen*)
 
and translate_refutation b r = 
 match r with
 | Conflict(s,ns) ->  begin
   let p = get_prenorm b s in
   let np = get_prenorm b ns in
   if debug_translation then Printf.printf  "Conflict %s\n" (trm_str p);
   if trm_eq np (neg p) then Conflict(p,np)
   else if trm_eq p  (neg np) then Conflict(np,p)
   else if normalize np <> np  then normalize_refutation b (Conflict(ns,s)) ns np false (* both prenorm terms are alternatly normalized*)
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
   match p with  (* TODO : this might or might not work*)
    | (Ap(Ap(Imp,(Ap(Ap(And,m1),m2))),False)) -> begin
      if  trm_eq' (normalize (neg m2)) t && trm_eq' (normalize (neg m1)) s then
          NegConjunction(p,neg m1,neg m2,translate_refutation ((s,neg m1)::b) r1,translate_refutation ((t,neg m2)::b) r2)
      else normalize_refutation b r h p false
          end     
     | (Ap(Ap(Or,m1),m2)) -> begin
      if  trm_eq' (normalize m2) t && trm_eq' (normalize m1) s then 
        Disjunction(p,m1,m2,translate_refutation ((s,m1)::b) r1,translate_refutation ((t,m2)::b) r2)
      else normalize_refutation b r h p false
          end    
    | (Ap(Ap(Imp,m1),m2)) -> begin
      if  trm_eq' (normalize m2) t && trm_eq' (normalize (neg m1)) s then
          Implication(p,neg m1,m2,translate_refutation ((s,neg m1)::b) r1,translate_refutation ((t,m2)::b) r2)
      else normalize_refutation b r h p false
    end    
    | _ ->  normalize_refutation b r h p false
    end  
 | NegImplication(h,s,t,r1)   -> begin 
   let p = get_prenorm b h in 
   if debug_translation then Printf.printf  "NegImplication %s\n" (trm_str p);
   match p with  (* TODO : this might or might not work*)
   | (Ap(Ap(Imp,(Ap(Ap(Imp,m1),m2))),False)) -> 
	if  trm_eq' (normalize (neg m2)) t && trm_eq' (normalize m1) s then
      NegImplication(p,m1,neg m2,translate_refutation ((s,m1)::(t,neg m2)::b) r1)
	 else normalize_refutation b r h p false
   | (Ap(Ap(And,m1),m2)) ->
	if  trm_eq' (normalize m2) t && trm_eq' (normalize m1) s then  
      Conjunction(p,m1,m2,translate_refutation ((s,m1)::(t,m2)::b) r1) 
	 else normalize_refutation b r h p false
   | (Ap(Ap(Imp,(Ap(Ap(Or,m1),m2))),False)) ->
	if  trm_eq' (normalize (neg m2)) t && trm_eq' (normalize (neg m1)) s then
      NegDisjunction(p,neg m1,neg m2,translate_refutation ((s,neg m1)::(t,neg m2)::b) r1)
	 else normalize_refutation b r h p false
   | _ ->  normalize_refutation b r h p false
    end
| All(h,s,r1,a,m,n) -> begin
   let p = get_prenorm b h in
   if debug_translation then Printf.printf  "All %s\n" (trm_str p);
   match p with  (* TODO : this might or might not work*)
    | (Ap(Forall(a'),m1)) -> begin
      let m' = onlybetanorm (Ap(m1,n)) in
      if  trm_eq' (normalize m') s  then
          All(p,m',translate_refutation ((s,m')::b) r1,a,m,n)
      else normalize_refutation b r h p false
    end  
    | (Ap(Ap(Imp,Ap(Exists(a'),m1)),False)) -> begin
      let m' = neg (onlybetanorm (Ap(m1,n))) in
      if  trm_eq' (normalize m') s  then  
        NegExist(p,m',translate_refutation ((s,m')::b) r1,a,m,n)
      else normalize_refutation b r h p false
          end        
    | _ ->  normalize_refutation b r h p false
    end  
| NegAll(h,s,r1,a,m,x) ->
      begin
   let p = get_prenorm b h in
   if debug_translation then Printf.printf  "NegAll %s\n" (trm_str p);
   match p with  (* TODO : this might or might not work*)
    | (Ap(Exists(a'),m1)) -> begin
      let m' = onlybetanorm (Ap(m1,Name(x,a))) in
      if  trm_eq' (normalize m') s  then

          Exist(p,m',translate_refutation ((s,m')::b) r1,a,m,x)
      else normalize_refutation b r h p false
    end  
    | (Ap(Ap(Imp,Ap(Forall(a'),m1)),False)) -> begin
      let m' = neg (onlybetanorm (Ap(m1,Name(x,a)))) in
      if  trm_eq' (normalize m') s then  
        NegAll(p,m',translate_refutation ((s,m')::b) r1,a,m,x)
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
        	if g1 <> g2 then  raise (Mating_Missmatch("unequal heads")) else
 		List.fold_left2 (fun a b c ->if tpof b = tpof c then (neg (eq (tpof b) b c))::a 
						else raise (Mating_Missmatch("type missmatch in spine")) ) [] args1 args2
     		| (Ap(Ap(Imp,Ap(f1,m1)),False), Ap(f2,m2)) -> 
		let (g1,args1)= head_spine (Ap(f2,m2)) in 
		let (g2,args2)= head_spine (Ap(f1,m1)) in
		if g1 <> g2 then  raise (Mating_Missmatch("unequal heads")) else
 		List.fold_left2 (fun a b c ->if tpof b = tpof c then (neg (eq (tpof b) b c))::a 
						else raise (Mating_Missmatch("type missmatch in spine")) ) [] args1 args2
     		| _ -> raise (Mating_Missmatch("terms can't be mated"))
    	in
	let pss = List.rev pss in  
	begin
	List.iter2 (fun ps s -> if not (trm_eq' s (normalize ps)) 
				then raise (Mating_Missmatch("unexpected result :" ^ (trm_str ps)^" <> "^ (trm_str s))) ) pss ss; 
    	Mating(p,np, pss, List.map2 (fun ps (s,r) -> translate_refutation ((s,ps)::b)  r) pss h)
	end
   	with Mating_Missmatch(mess) -> if normalize p <> p  then normalize_refutation b (Mating(h2,h1, ss, rs)) h1 p  true (* both prenorm terms are alternatly normalized*)
   else  normalize_refutation b (Mating(h2,h1, ss, rs)) h2 np true
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
        if g1 <> g2 then  raise (Mating_Missmatch("unequal heads")) else
 	List.fold_left2 (fun a b c ->if tpof b = tpof c 
					then (neg (eq (tpof b) b c))::a else raise (Mating_Missmatch("type missmatch in spine")) ) [] args1 args2
     | _ -> raise (Mating_Missmatch("term can't be decomposed"))
    in    
	let pss = List.rev pss in 
	List.iter2 (fun ps s -> if not (trm_eq' s (normalize ps)) 
				then raise (Mating_Missmatch("unexpected result :" ^ (trm_str ps)^" <> "^ (trm_str s))) ) pss ss;  
	Decomposition(p ,pss, List.map2 (fun ps (s,r) -> translate_refutation ((s,ps)::b) r) pss h)
   	with Mating_Missmatch(mess) -> normalize_refutation b r h1 p true
 	end  
| Confront(h1,h2,su,tu,sv,tv,r1,r2) ->begin 
   let p = get_prenorm b h1 in
   let np = get_prenorm b h2 in
   if debug_translation then Printf.printf  "Confronting %s\n" (trm_str p);
   let (bb,r) = begin match (p,np) with
			| (  Ap(Ap(Eq(a),s),t)   ,  Ap(Ap(Imp, Ap(Ap(Eq(a'),u),v) ),False)  ) when a=a' -> begin
				let (psu,ptu,psv,ptv)=(neg (eq a s u),neg (eq a t u),neg (eq a s v),neg (eq a t v)) in
     if trm_eq' (normalize psu) su then 
	(true,Confront(p,np,psu,ptu,psv,ptv, translate_refutation ((su,psu)::(tu,ptu)::b) r1, translate_refutation ((sv,psv)::(tv,ptv)::b) r2 ) )
else if trm_eq' (normalize psu) tu then
	(true,Confront(p,np,psu,ptu,psv,ptv, translate_refutation ((tu,psu)::(su,ptu)::b) r1, translate_refutation ((tv,psv)::(sv,ptv)::b) r2 ) )
else if trm_eq' (normalize psu) sv then
	(true,Confront(p,np,psu,ptu,psv,ptv, translate_refutation ((sv,psu)::(tv,ptu)::b) r2, translate_refutation ((su,psv)::(tu,ptv)::b) r1 ) )
else if trm_eq' (normalize psu) tv then
	(true,Confront(p,np,psu,ptu,psv,ptv, translate_refutation ((tv,psu)::(sv,ptu)::b) r2, translate_refutation ((tu,psv)::(su,ptv)::b) r1 ) ) 
else  (false,Fal(False)) end
			| (  Ap(Ap(Imp, Ap(Ap(Eq(a'),u),v) ),False)  ,  Ap(Ap(Eq(a),s),t) )  when a=a' -> begin
				let (psu,ptu,psv,ptv)=(neg (eq a s u),neg (eq a t u),neg (eq a s v),neg (eq a t v)) in
     if trm_eq' (normalize psu) su then 
	(true,Confront(p,np,psu,ptu,psv,ptv, translate_refutation ((su,psu)::(tu,ptu)::b) r1, translate_refutation ((sv,psv)::(tv,ptv)::b) r2 ) )
else if trm_eq' (normalize psu) tu then
	(true,Confront(p,np,psu,ptu,psv,ptv, translate_refutation ((tu,psu)::(su,ptu)::b) r1, translate_refutation ((tv,psv)::(sv,ptv)::b) r2 ) )
else if trm_eq' (normalize psu) sv then
	(true,Confront(p,np,psu,ptu,psv,ptv, translate_refutation ((sv,psu)::(tv,ptu)::b) r2, translate_refutation ((su,psv)::(tu,ptv)::b) r1 ) )
else if trm_eq' (normalize psu) tv then
	(true,Confront(p,np,psu,ptu,psv,ptv, translate_refutation ((tv,psu)::(sv,ptu)::b) r2, translate_refutation ((tu,psv)::(su,ptv)::b) r1 ) ) 
else  (false,Fal(False)) end
			| _ -> (false,Fal(False)) end 
  in
  if bb then  
    r
   else if normalize p <> p  then normalize_refutation b (Confront(h2,h1,su,tu,sv,tv,r1,r2)) h1 p false (* both prenorm terms are alternatly normalized*)
   else  normalize_refutation b (Confront(h2,h1,su,tu,sv,tv,r1,r2)) h2 np false
 end  
 | NegEqualProp(h,s,t,r1,r2) -> begin
   let p = get_prenorm b h in
   if debug_translation then Printf.printf  "boolean extensionality %s\n" (trm_str p);
   match p with  (* TODO : this might or might not work*)
     | (Ap(Ap(Imp,Ap(Ap(Eq(Prop),m1),m2)),False)) -> begin
            if  trm_eq (normalize m2)  t && trm_eq (normalize m1)  s then
            NegEqualProp(p,m1,m2, translate_refutation ((s,m1)::(normneg t,neg m2)::b) r1,translate_refutation((normneg s,neg m1)::(t,m2)::b) r2)
 	    else 
	    if   trm_eq (normalize m1)  t && trm_eq (normalize m2)  s then
            NegEqualProp(p,m1,m2, translate_refutation ((t,m1)::(normneg s,neg m2)::b) r2,translate_refutation((normneg t,neg m1)::(s,m2)::b) r1)
 	    else normalize_refutation b r h p false
          end     	 
     | (Ap(Ap(Imp,Ap(Ap(Iff,m1),m2)),False)) -> begin
            if  trm_eq (normalize m2)  t && trm_eq (normalize m1)  s then
            NegAequivalenz(p,m1,m2, translate_refutation ((s,m1)::(normneg t,neg m2)::b) r1,translate_refutation((normneg s,neg m1)::(t,m2)::b) r2)
 	    else 
	    if   trm_eq (normalize m1)  t && trm_eq (normalize m2)  s then
            NegAequivalenz(p,m1,m2, translate_refutation ((t,m1)::(normneg s,neg m2)::b) r2,translate_refutation((normneg t,neg m1)::(s,m2)::b) r1)
 	    else normalize_refutation b r h p false
          end     	 
    | _ ->  normalize_refutation b r h p false
    end  
 | EqualProp(h,s,t,r1,r2) -> begin
   let p = get_prenorm b h in
   if debug_translation then Printf.printf  "boolean Equality %s\n" (trm_str p);
   match p with  (* TODO : this might or might not work*)
     | Ap(Ap(Eq(Prop),m1),m2) -> begin
            if  trm_eq (normalize m2)  t && trm_eq (normalize m1)  s then
            EqualProp(p,m1,m2, translate_refutation ((s,m1)::(t,m2)::b) r1,translate_refutation ((normneg s,neg m1)::(normneg t,neg m2)::b) r2)
 	    else
	    if  trm_eq (normalize m1)  t && trm_eq (normalize m2)  s then
            EqualProp(p,m1,m2, translate_refutation ((s,m2)::(t,m1)::b) r1,translate_refutation ((normneg s,neg m2)::(normneg t,neg m1)::b) r2)
 	    else normalize_refutation b r h p false
          end     	 
    | Ap(Ap(Iff,m1),m2) -> begin
           if  trm_eq (normalize m2)  t && trm_eq (normalize m1)  s then
            Aequivalenz(p,m1,m2, translate_refutation ((s,m1)::(t,m2)::b) r1,translate_refutation ((normneg s,neg m1)::(normneg t,neg m2)::b) r2)
 	    else
	    if  trm_eq (normalize m1)  t && trm_eq (normalize m2)  s then
            Aequivalenz(p,m1,m2, translate_refutation ((s,m2)::(t,m1)::b) r1,translate_refutation ((normneg s,neg m2)::(normneg t,neg m1)::b) r2)
 	    else normalize_refutation b r h p false
          end   
    | _ ->  normalize_refutation b r h p false
    end  
 | NegEqualFunc(h,s,r1) -> begin (* TODO solve symmetry*)
   let p = get_prenorm b h in
   if debug_translation then Printf.printf  "functional extensionality %s\n" (trm_str p);
   match p with  (* TODO : this might or might not work*)
     | (Ap(Ap(Imp,Ap(Ap(Eq(Ar(a,a')),m1),m2)),False)) -> 
	begin
	let left = (Ap(shift m1 0 1,DB(0,a))) in
	let right =  (Ap(shift m2 0 1,DB(0,a))) in
	let aao= Ar(a',Ar(a',Prop)) in
	let prefix= Lam(aao, neg ( forall a (Ap(Ap(DB(1,aao),left),right)) )) in
	let ps =  onlybetanorm (Ap(prefix,Eq(a'))) in
	if trm_eq' (normalize ps) s then NegEqualFunc(p,ps, translate_refutation ((s,ps)::b) r1)
	else 
	begin
	let ps' = onlybetanorm (Ap(prefix,Lam(a',Lam(a',Ap(Ap(Eq(a'),DB(0,a')),DB(1,a'))))  )) in 

	if trm_eq' (normalize ps') s
	then NegEqualFunc(p,ps, Rewrite(prefix,Eq(a'), Lam(a',Lam(a',Ap(Ap(Eq(a'),DB(0,a')),DB(1,a')))) ,translate_refutation ((s,ps')::b) r1) )
	else raise (Not_Implemented("Error with NegEqualFunc: Unexpected result " ^ (trm_str ps)))
	end        
	end     	 
    | _ -> normalize_refutation b r h p false
    end  
 | EqualFunc(h,s,r1) -> begin (* TODO solve symmetry*)
   let p = get_prenorm b h in
   if debug_translation then Printf.printf  "functional Equality %s\n" (trm_str p);
   match p with  (* TODO : this might or might not work*)
     | Ap(Ap(Eq(Ar(a,a')),m1),m2) -> begin
	 let left = (Ap(shift m1 0 1,DB(0,a))) in
	let right =  (Ap(shift m2 0 1,DB(0,a))) in
	let aao= Ar(a',Ar(a',Prop)) in
	let prefix= Lam(aao,( forall a (Ap(Ap(DB(1,aao),left),right)) )) in
	let ps =  onlybetanorm (Ap(prefix,Eq(a'))) in
		if trm_eq' (normalize ps) s 
		then EqualFunc(p,ps, translate_refutation ((s,ps)::b) r1)
		else let ps' = onlybetanorm (Ap(prefix,Lam(a',Lam(a',Ap(Ap(Eq(a'),DB(0,a')),DB(1,a'))))  )) in 
		if trm_eq' (normalize ps') s 
		then EqualFunc(p,ps,Rewrite(prefix,Eq(a'), Lam(a',Lam(a',Ap(Ap(Eq(a'),DB(0,a')),DB(1,a'))))  ,translate_refutation ((s,ps')::b) r1) )
		else raise (Not_Implemented("Error with EqualFunc: Unexpected result " ^ (trm_str (normalize ps)) ^ " s: " ^ (trm_str s)))
          end         	 
    | _ -> normalize_refutation b r h p false
    end  
 | ChoiceR(eps,pred,s,t,r1,r2) -> begin
	match eps with  
	| Name(x,Ar (Ar (a, Prop), _)) -> let (h,p,bb) = check_Choicop_axiom x a b in
		if not bb then  normalize_refutation b r h p false
		else
		let ps = onlybetanorm (forall a (neg (ap (shift pred 0 1,DB(0,a)) ) ) ) in
		let pt = onlybetanorm ( ap (pred,ap (eps,pred)) ) in
   		if debug_translation then Printf.printf  "Choice %s\n" (trm_str pred); 
		ChoiceR(eps,pred,ps,pt,translate_refutation ((s, ps)::b) r1,translate_refutation ((t,pt)::b) r2)  
	| Choice(a) -> 
		(* let a = match tpof pred  with Ar(a,Prop) -> a | _ -> raise (Not_Implemented  "Error pred is not of type a --> o") in	*)
		let ps = onlybetanorm (forall a (neg (ap (shift pred 0 1,DB(0,a)) ) ) ) in
		let pt = onlybetanorm ( ap (pred,ap (eps,pred)) ) in
   		if debug_translation then Printf.printf  "Choice %s\n" (trm_str pred); 
		ChoiceR(eps,pred,ps,pt,translate_refutation ((s, ps)::b) r1,translate_refutation ((t,pt)::b) r2)  
	| _ ->   raise (Not_Implemented("Error with ChoiceR: eps = " ^ (trm_str eps)))
	end
 | Cut(s,r1,r2) -> 
	if debug_translation then Printf.printf  "Cut %s\n" (trm_str s); 
	Cut(s,translate_refutation ((s,s)::b) r1,translate_refutation ((normneg s,neg s)::b) r2)   
 | Rewrite(pre,pt,pt',r1) -> 
			let trm = onlybetanorm (Ap(pre,pt)) in
			let p = get_prenorm b trm in
			if trm_eq p trm 
			then begin
			if debug_translation then Printf.printf  "Rewrite %s\n" (trm_str trm); 
			let ptrm' =  onlybetanorm (Ap(pre,pt')) in
			let ptrm =  norm name_def (Ap(pre,pt')) in
			 Rewrite(pre,pt,pt',translate_refutation ((ptrm,ptrm')::b) r1 ) end
			else normalize_refutation b r trm p false
 | Timeout -> Timeout 
   (* These cases shouldn't occur, they only appear on prenorm_refutations *)
 | DoubleNegation(h,s,r1) -> DoubleNegation(h,s,translate_refutation ((h,s)::b) r1)
 | Disjunction(h,s,t,r1,r2) -> Disjunction(h,s,t,translate_refutation ((s,s)::b) r1,translate_refutation ((t,t)::b) r2)   
 | NegConjunction(h,s,t,r1,r2) -> NegConjunction(h,s,t,translate_refutation ((s,s)::b) r1,translate_refutation ((t,t)::b) r2)   
 | Conjunction(h,s,t,r1) -> Conjunction(h,s,t,translate_refutation ((s,s)::(t,t)::b) r1) 
 | NegDisjunction(h,s,t,r1) -> NegDisjunction(h,s,t,translate_refutation ((s,s)::(t,t)::b) r1) 
 | Exist(h,s,r1,a,m,x) ->Exist(h,s,translate_refutation ((s,s)::b) r1,a,m,x)
 | NegExist(h,s,r1,a,m,n) ->NegExist(h,s,translate_refutation ((s,s)::b) r1,a,m,n)
 | NYI(h,s,r1) -> NYI(h,s,translate_refutation ((h,s)::b) r1) 
 | _ -> raise (Not_Implemented("unknown refutation case in translation"))

 
and normalize_refutation b r trm ptrm delta= (* TODO : special rewrites for and,or.. without prefix*)
      match ptrm with
        | (Ap(Ap(Imp,m),False)) -> begin 
          match m with
            | (Ap(Ap(Imp,m'),False)) -> 
		if debug_translation then Printf.printf  "DoubleNegation %s\n" (trm_str ptrm);
		DoubleNegation(ptrm,m',translate_refutation ((trm,m')::b) r)
            | (Ap(Ap(Imp,m'),f)) when normalize f = False ->  NegImplication(ptrm,m',True,translate_refutation ((trm,m')::b) r)       
            | _ -> rewrite_refutation b r trm ptrm delta
        end
        | (Ap(Ap(Imp,m),f)) when normalize f = False ->  Implication(ptrm,neg m,f,translate_refutation ((trm,neg m)::b) r,translate_refutation ((False,f)::b) (Fal(False)))       
        | _ ->  rewrite_refutation b r trm ptrm delta           

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
with Not_found -> raise (Not_Implemented("Error with ChoiceR: no choice axiom found for" ^ x ^ (stp_str a)))

(** to Coq functions **)

module Variables = struct
	type t = int * (string list)
	let make () = (1,[])
	let rec push (n,v) = 
		let x = "x" ^ (string_of_int n) in
		let n = n+1 in
		if (Hashtbl.mem coq_used_names x) 
			then push (n,v)	    
  			else (n,x::v)  
	let top (_,v) = List.hd v
	let get i (_,v) = List.nth v i	
end

let rec print_stp_coq c m h p =
  match m with
  | Base x ->
	let x = try (Hashtbl.find h x) with Not_found -> raise (Not_Implemented("print_stp_coq can't find coqname of "^x)) in
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


let rec trm_to_coq c m bound lp rp =
  match m with
    Name(x,_) ->
	let x = try (Hashtbl.find coq_names x) with Not_found -> x in
      Printf.fprintf c "%s" x
  | False -> Printf.fprintf c "False"
  | Ap(Ap(Imp,m1),False) ->  
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
   | Ap(Ap(Imp,m1),m2) ->
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
  | Ap(Forall(a),m1) -> 
	begin
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c "(";
	begin
	  Printf.fprintf c "forall";
	  print_all_coq c a m1 bound
	end;
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c ")";
	end
  | Forall(_) -> Printf.fprintf c "(fun p => forall x, p x)"
  | Ap(Ap(Eq(a),m1),m2) ->
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
  | Ap(Eq(a),m) ->     
	if ((lp < 5000) && (rp < 5001)) then
	begin
	  Printf.fprintf c "eq ";
	  trm_to_coq c m bound 5001 rp;
	end
      else
	begin
	  Printf.fprintf c "(eq ";
	  trm_to_coq c m bound 5001 (-1);
	  Printf.fprintf c ")";
	end  
  | Eq(a) ->     
	if ((lp < 5000) && (rp < 5001)) then
	begin
	  Printf.fprintf c "@eq ";
	  print_stp_coq c a coq_names true;
	end
      else
	begin
	  Printf.fprintf c "(@eq ";
	  print_stp_coq c a coq_names true;
	  Printf.fprintf c ")";
	end      
(*
  | Ap(Eq(a),m1) -> trm_to_coq c (Lam(a,Ap(Ap(Eq(a),shift m1 0 1),DB(0,a)))) bound lp rp;
  | Eq(a) -> trm_to_coq c (Lam(a,Lam(a,Ap(Ap(Eq(a),DB(1,a)),DB(0,a))))) bound lp rp; 
*)
  | Ap(Choice(a),m) ->     
	if ((lp < 5000) && (rp < 5001)) then
	begin
	  Printf.fprintf c "Sepsilon ";
	  trm_to_coq c m bound 5001 rp;
	end
      else
	begin
	  Printf.fprintf c "(Sepsilon ";
	  trm_to_coq c m bound 5001 (-1);
	  Printf.fprintf c ")";
	end      
  | Choice(a) -> Printf.fprintf c "@Sepsilon "; print_stp_coq c a coq_names true;
  | True ->Printf.fprintf c "True"
  | Ap(Ap(And,m1),m2) ->
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
  | Ap(Ap(Or,m1),m2) ->
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
  | Ap(Ap(Iff,m1),m2) ->
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
  | Ap(Exists(a),m1) ->
      begin
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c "(";
	begin
	  print_ex_coq c a m1 bound
	end;
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c ")";
      end
  | Exists(_) ->  Printf.fprintf c "(fun p => exists x, p x)" 
  | DB(i,a) -> Printf.fprintf c "%s" (Variables.get i bound)
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

and print_lam_coq c a m bound =
	let bound = Variables.push bound in
	Printf.fprintf c " ("; Printf.fprintf c "%s" (Variables.top bound); Printf.fprintf c ":"; print_stp_coq c a coq_names false; Printf.fprintf c ")";
	match m with
		| Lam(b,m') -> print_lam_coq c b m' bound
		| _ -> Printf.fprintf c " => "; trm_to_coq c m bound (-1) (-1)
	
and print_all_coq c a m bound =
	let bound = Variables.push bound in
	Printf.fprintf c " ("; Printf.fprintf c "%s" (Variables.top bound); Printf.fprintf c ":"; print_stp_coq c a coq_names false; Printf.fprintf c ")";
	match m with
		| Lam(_,Ap(Forall(a'),m'))-> print_all_coq c a' m' bound
		| Lam(_,m') -> Printf.fprintf c ", "; trm_to_coq c m' bound (-1) (-1)
		| _ -> Printf.fprintf c ", "; trm_to_coq c (Ap(shift m 0 1,DB(0,a))) bound (-1) (-1)

and print_ex_coq c a m bound =
 	let bound = Variables.push bound in
	Printf.fprintf c "exists"; Printf.fprintf c " %s" (Variables.top bound); 
	Printf.fprintf c ":"; print_stp_coq c a coq_names false; 
        Printf.fprintf c ", ";
	match m with
		| Lam(_,m') -> trm_to_coq c m' bound (-1) (-1)
		| _ -> trm_to_coq c (Ap(shift m 0 1,DB(0,a))) bound (-1) (-1)



let get_Choicop_axiom x a hyp = 
let ao = Ar(a,Prop) in
let m1 = Ap (Forall (Ar (a, Prop)),Lam (Ar (a, Prop),Ap (Forall a,Lam (a,Ap (Ap (Imp, Ap (DB (1, Ar (a, Prop)), DB (0, a))),
	 Ap (DB (1, Ar (a, Prop)),Ap (Name (x, Ar (Ar (a, Prop), a)), DB (1, Ar (a, Prop))))))))) in
let m2 = Ap (Forall (Ar (a, Prop)),Lam (Ar (a, Prop),Ap(Ap (Imp,Ap(Ap (Imp,Ap (Forall a,Lam (a,
	Ap (Ap (Imp, Ap (DB (1, Ar (a, Prop)), DB (0, a))),False)))),False)),Ap (DB (0, Ar (a, Prop)),
	Ap (Name (x, Ar (Ar (a, Prop), a)),DB (0, Ar (a, Prop)))))))in
let m3 = Ap (Forall (Ar (a, Prop)),Lam (Ar (a, Prop),Ap(Ap (Imp,Ap (Exists a,Lam (a,
	Ap (DB (1, Ar (a, Prop)), DB (0, a))))),Ap (DB (0, Ar (a, Prop)),
	Ap (Name (x, Ar (Ar (a, Prop), a)),DB (0, Ar (a, Prop)))))))in
try
let (m,h)= List.find (fun (m,h) -> m = m1 || m = m2 || m = m3 ) hyp in h
with Not_found -> "missing_choice_axiom_for"^x

let next_fresh_hyp : int ref = ref 0

let rec get_hyp_name hyp =
	let x = "H" ^ (string_of_int (!next_fresh_hyp)) in
	incr next_fresh_hyp;
	if (Hashtbl.mem coq_used_names x)  (* do i have to check somwhere else too?*)
	then get_hyp_name hyp
  	else x 

let add_fresh_const c const n sp =
	let rec find_fresh_const n =
	match n with 
	| Name(x,a) ->
		let x = Hashtbl.find coq_names x in
		if List.mem_assoc x const then [] else [(x,a)] 
	| Ap(m1,m2) -> find_fresh_const m1 @ find_fresh_const m2
	| Lam(_,m) -> find_fresh_const m
	| _ -> [] in
List.fold_left (fun cons (x,a) -> 
	if List.mem (x,a) cons then cons 
	else (Printf.fprintf c "%stab_inh (" sp; print_stp_coq c a coq_names false;Printf.fprintf c ") %s.\n" x ;(x,a)::cons) ) 
	const (find_fresh_const (coqnorm n))
 
let rec ref_coq1 c r hyp const sp=
	match r with
 | Conflict(s,ns) -> 			
	Printf.fprintf c "%stab_conflict %s %s.\n" sp (List.assoc (coqnorm s) hyp) (List.assoc (coqnorm ns) hyp)
 | Fal(_) -> 				
	Printf.fprintf c "%stab_false %s.\n" sp (List.assoc False hyp) 
 | NegRefl(s) -> 			
	Printf.fprintf c "%stab_refl %s.\n" sp (List.assoc (coqnorm s) hyp)
 | Implication(h,s,t,r1,r2) -> 	
	let h1 = get_hyp_name() in	
	Printf.fprintf c "%stab_imp %s %s.\n" sp (List.assoc (coqnorm h) hyp) h1;
	ref_coq1 c r1 ((coqnorm s,h1)::hyp) const (sp^" ");
	ref_coq1 c r2 ((coqnorm t,h1)::hyp) const (sp^" ");
 | Disjunction(h,s,t,r1,r2) ->
	let h1 = get_hyp_name() in	
	Printf.fprintf c "%stab_or %s %s.\n" sp (List.assoc (coqnorm h) hyp) h1;
	ref_coq1 c r1 ((coqnorm s,h1)::hyp) const (sp^" ");
	ref_coq1 c r2 ((coqnorm t,h1)::hyp) const (sp^" "); 	
 | NegConjunction(h,s,t,r1,r2) ->
	let h1 = get_hyp_name() in	
	Printf.fprintf c "%stab_nand %s %s.\n" sp (List.assoc (coqnorm h) hyp) h1;
	ref_coq1 c r1 ((coqnorm s,h1)::hyp) const (sp^" ");
	ref_coq1 c r2 ((coqnorm t,h1)::hyp) const (sp^" ");  
 | NegImplication(h,s,t,r1) ->
	let h1 = get_hyp_name() in
	let h2 = get_hyp_name() in	
	Printf.fprintf c "%stab_negimp %s %s %s.\n" sp (List.assoc (coqnorm h) hyp) h1 h2;
	ref_coq1 c r1 ((coqnorm s,h1)::(coqnorm t,h2)::hyp) const sp
 | Conjunction(h,s,t,r1) ->
	let h1 = get_hyp_name() in
	let h2 = get_hyp_name() in	
	Printf.fprintf c "%stab_and %s %s %s.\n" sp (List.assoc (coqnorm h) hyp) h1 h2;
	ref_coq1 c r1 ((coqnorm s,h1)::(coqnorm t,h2)::hyp) const sp
 | NegDisjunction(h,s,t,r1) ->
	let h1 = get_hyp_name() in
	let h2 = get_hyp_name() in	
	Printf.fprintf c "%stab_nor %s %s %s.\n" sp (List.assoc (coqnorm h) hyp) h1 h2;
	ref_coq1 c r1 ((coqnorm s,h1)::(coqnorm t,h2)::hyp) const sp
 | All(h,s,r1,a,m,n) ->
	let const = add_fresh_const c const n sp in
	let h1 = get_hyp_name() in	
	Printf.fprintf c "%stab_all %s (" sp (List.assoc (coqnorm h) hyp); 
	(trm_to_coq c n (Variables.make ()) (-1) (-1));
	Printf.fprintf c ") %s.\n" h1;
	ref_coq1 c r1 ((coqnorm s,h1)::hyp) const sp
 | NegAll(h,s,r1,a,m,x) ->
	let h1 = get_hyp_name() in
	let x = ( Hashtbl.find coq_names x ) in
	Printf.fprintf c "%stab_negall %s %s %s.\n" sp (List.assoc (coqnorm h) hyp) x h1;
	ref_coq1 c r1 ((coqnorm s,h1)::hyp) ((x,a)::const) sp
 | Exist(h,s,r1,a,m,x) ->
	let h1 = get_hyp_name() in
	let x = ( Hashtbl.find coq_names x ) in
	Printf.fprintf c "%stab_ex %s %s %s.\n" sp (List.assoc (coqnorm h) hyp) x h1;
	ref_coq1 c r1 ((coqnorm s,h1)::hyp) ((x,a)::const) sp
 | NegExist(h,s,r1,a,m,n) ->
	let const = add_fresh_const c const n sp in
	let h1 = get_hyp_name() in	
	Printf.fprintf c "%stab_negex %s (" sp (List.assoc (coqnorm h) hyp); 
	(trm_to_coq c n (Variables.make ()) (-1) (-1));
	Printf.fprintf c ") %s.\n" h1;
	ref_coq1 c r1 ((coqnorm s,h1)::hyp) const sp	
 | Mating(h1,h2, ss, rs) ->
	let h3 = get_hyp_name() in	
	Printf.fprintf c "%stab_mat %s %s %s.\n" sp (List.assoc (coqnorm h1) hyp) (List.assoc (coqnorm h2) hyp) h3;
	List.iter (fun (s,r) -> ref_coq1 c r ((coqnorm s,h3)::hyp) const (sp^" ")) (List.combine ss rs)
 | Decomposition(h1, ss, rs) ->
	let h3 = get_hyp_name() in	
	Printf.fprintf c "%stab_dec %s %s.\n" sp (List.assoc (coqnorm h1) hyp) h3;
	List.iter (fun (s,r) -> ref_coq1 c r ((coqnorm s,h3)::hyp) const (sp^" ")) (List.combine ss rs) 	
 | Confront(h1,h2,su,tu,sv,tv,r1,r2) ->
	let h3 = get_hyp_name() in
	let h4 = get_hyp_name() in	
	Printf.fprintf c "%stab_con %s %s %s %s.\n" sp (List.assoc (coqnorm h1) hyp) (List.assoc (coqnorm h2) hyp) h3 h4;
	ref_coq1 c r1 ((coqnorm su,h3)::(coqnorm tu,h4)::hyp) const (sp^" ");
	ref_coq1 c r2 ((coqnorm sv,h3)::(coqnorm tv,h4)::hyp) const (sp^" ");	
 | NegEqualProp(h,s,t,r1,r2) -> 
	let h1 = get_hyp_name() in
	let h2 = get_hyp_name() in	
	Printf.fprintf c "%stab_be %s %s %s.\n" sp (List.assoc (coqnorm h) hyp) h1 h2;
	ref_coq1 c r1 ((coqnorm s,h1)::(coqnorm (neg t),h2)::hyp) const (sp^" ");
	ref_coq1 c r2 ((coqnorm (neg s),h1)::(coqnorm t,h2)::hyp) const (sp^" ");
 | EqualProp(h,s,t,r1,r2) -> 
	let h1 = get_hyp_name() in
	let h2 = get_hyp_name() in	
	Printf.fprintf c "%stab_bq %s %s %s.\n" sp (List.assoc (coqnorm h) hyp) h1 h2;
	ref_coq1 c r1 ((coqnorm s,h1)::(coqnorm t,h2)::hyp) const (sp^" ");
	ref_coq1 c r2 ((coqnorm (neg s),h1)::(coqnorm (neg t),h2)::hyp) const (sp^" ");
 | NegAequivalenz(h,s,t,r1,r2) -> 
	let h1 = get_hyp_name() in
	let h2 = get_hyp_name() in	
	Printf.fprintf c "%stab_negiff %s %s %s.\n" sp (List.assoc (coqnorm h) hyp) h1 h2;
	ref_coq1 c r1 ((coqnorm s,h1)::(coqnorm (neg t),h2)::hyp) const (sp^" ");
	ref_coq1 c r2 ((coqnorm (neg s),h1)::(coqnorm t,h2)::hyp) const (sp^" ");
 | Aequivalenz(h,s,t,r1,r2) -> 
	let h1 = get_hyp_name() in
	let h2 = get_hyp_name() in	
	Printf.fprintf c "%stab_iff %s %s %s.\n" sp (List.assoc (coqnorm h) hyp) h1 h2;
	ref_coq1 c r1 ((coqnorm s,h1)::(coqnorm t,h2)::hyp) const (sp^" ");
	ref_coq1 c r2 ((coqnorm (neg s),h1)::(coqnorm (neg t),h2)::hyp) const (sp^" ");
 | NegEqualFunc(h,s,r1) ->
	let h1 = get_hyp_name() in	
	Printf.fprintf c "%stab_fe %s %s.\n" sp (List.assoc (coqnorm h) hyp) h1;
	ref_coq1 c r1 ((coqnorm s,h1)::hyp) const sp
 | EqualFunc(h,s,r1) ->
	let h1 = get_hyp_name() in	
	Printf.fprintf c "%stab_fq %s %s.\n" sp (List.assoc (coqnorm h) hyp) h1;
	ref_coq1 c r1 ((coqnorm s,h1)::hyp) const  sp
 | ChoiceR(eps,pred,s,t,r1,r2) -> (* TODO Choiceop_axiom *)
	let const = add_fresh_const c const pred sp in
	let h1 = get_hyp_name() in	begin
	match eps with
	| Choice(a) -> 
	Printf.fprintf c "%stab_choice (" sp;
	(trm_to_coq c pred (Variables.make ()) (-1) (-1));
	Printf.fprintf c ") %s.\n" h1;
	ref_coq1 c r1 ((coqnorm s,h1)::hyp) const (sp^" ");
	ref_coq1 c r2 ((coqnorm t,h1)::hyp) const (sp^" ");
	| Name(x,Ar(Ar(a,Prop),_)) ->
	Printf.fprintf c "%stab_choice' (" sp;
	(trm_to_coq c pred (Variables.make ()) (-1) (-1));
	Printf.fprintf c ") %s %s.\n" (get_Choicop_axiom x a hyp) h1;
	ref_coq1 c r1 ((coqnorm s,h1)::hyp) const (sp^" ");
	ref_coq1 c r2 ((coqnorm t,h1)::hyp) const (sp^" ");
	| _ -> raise (Not_Implemented "eps is not a valid epsilon")
	end
 | Cut(s,r1,r2) -> 
	let const = add_fresh_const c const s sp in
	let h1 = get_hyp_name() in	
	Printf.fprintf c "%stab_cut (" sp;
	(trm_to_coq c s (Variables.make ()) (-1) (-1));
	Printf.fprintf c ") %s.\n" h1;
	ref_coq1 c r2 ((coqnorm (neg s),h1)::hyp) const (sp^" ");
	ref_coq1 c r1 ((coqnorm s,h1)::hyp) const (sp^" ");
 | DoubleNegation(h,s,r1) ->
	let h1 = get_hyp_name() in	
	Printf.fprintf c "%stab_dn %s %s.\n" sp (List.assoc (coqnorm h) hyp) h1;
	ref_coq1 c r1 ((coqnorm s,h1)::hyp) const sp;
 | Rewrite(prefix,pt,pt',r1) ->
	let h =  coqnorm (Ap(prefix,pt)) in
	let h1 = List.assoc h hyp in	
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
		| _ -> raise (Not_Implemented("unknown rewrite step found in ref_coq" ^ (trm_str pt)))
	end;
	ref_coq1 c r1 ((s,h2)::hyp) const sp
 | Delta(h,s,x,r1) ->
	let h1 = (List.assoc (coqnorm h) hyp) in	
	Printf.fprintf c "%sunfold %s in %s.\n" sp ( Hashtbl.find coq_names x ) h1;
	ref_coq1 c r1 ((coqnorm s,h1)::hyp) const sp;
 | NYI(h,s,r1) -> raise (Not_Implemented("NYI step found in ref_coq" ))
 | Timeout -> raise (Not_Implemented("Timeout step found in ref_coq" ))
 | _ -> raise (Not_Implemented("unknown refutation case in ref_coq" ))    

let ref_coq c r = (* TODO *)
	let con =match !conjecture with Some(_,con)->coqnorm con | None-> False in
	let hyp = List.fold_left (fun l (s,pt) -> (coqnorm pt,s)::l ) [] !coqsig_hyp_trm in
	let h1 = get_hyp_name() in
  Printf.fprintf c "\ntab_start %s.\n" h1;
  ref_coq1 c r ((neg con,h1)::hyp) (!coqsig_const) ""; 
  Printf.fprintf c "Qed.\n" 
  

(** MAIN **)    


let print_proofterm_old c r =
  
  if (!verbosity > vold) then Printf.printf  "starting print_proofterm.\n";
  if (!verbosity > vold) then print_refut r;

	(*** Search ***)

  let initbranch = (List.rev !initial_branch) in
  let b =List.map get_literal initbranch in
  let (refutation,con,size,depth,width) = ( beforeSearch :=Sys.time() ;
	try process_refut b (Branch.make ()) r with Independent_Refutation(r,con,size,depth,width)-> (r,con,size,depth,width))  in
  let con = List.fold_left (fun c a -> IntSet.remove a c) con b in
  if assert_condition && not (IntSet.is_empty con ) then 
	 Printf.printf  "Error with refutation: Still open conditions  \n" ;	 
  let searchTime= int_of_float ((Sys.time() -. !beforeSearch) *. 1000.0) in
	if !isTimeout then let (size,tsize,depth,width,twidth,cut,rewrite,notyetImpl,timeouts) = statistic refutation  in 
  	Printf.printf  "Timeout!  time %d ms size %d depth %d width %d cuts %d rewrite %d NYI %d timeouts %d \n" searchTime size depth width cut rewrite notyetImpl timeouts
  	else 	
  begin
   if result_print_search then Printf.printf  "%s\n" (ref_str refutation);
  Printf.printf "Search time %d ms size %d depth %d width %d \n" searchTime size depth width ;

	(*** Translation  ***)

  let initbranch_prenorm =List.map 
	(fun pn ->let p= onlynegnorm pn in  if debug_translation then Printf.printf  "%s = %s \n" (trm_str pn) (trm_str p) ;p ) 
	(List.rev !initial_branch_prenorm) in
(* TODO Add Flag to Choose between satallax_translation and translate_refutation *)
  let beforeTrans= Sys.time() in
  let branch = (List.combine initbranch  initbranch_prenorm) in
  try
  let prenorm_refutation =if pftrm_rewrite_first then satallax_translation branch [] refutation else translate_refutation branch refutation in
  let transTime= int_of_float ((Sys.time() -. beforeTrans) *. 1000.0) in
  begin
  let (size,_,depth,width,_,cut,rewrite,notyetImpl,timeout) = statistic prenorm_refutation  in
  if result_print_translation then Printf.printf  "%s\n" (ref_str prenorm_refutation);
  Printf.printf  "Translation NYI %d time %d ms size %d depth %d width %d cuts %d rewrite %d  \n" notyetImpl transTime size depth width cut rewrite  ;

	(*** Output Coq ***)

  let beforeCoq= Sys.time() in
  if (result_coq && size < 800 ) then ref_coq c prenorm_refutation else raise (GenericError ("Coq Proof Too Big: " ^ (string_of_int size) ^ " steps"));
  let coqTime= int_of_float ((Sys.time() -. beforeCoq) *. 1000.0) in
  if (result_coq ) then Printf.printf  "Coq output done: time %d  \n" coqTime ;
	(*** Output Latex Search ***)

  if (result_latex && width < 50 && depth < 30) then
  Printf.fprintf c "(*** \n %%beginLatex \n size %d depth %d width %d \n \n \\begin{tabular}{c} \n %s \\end{tabular} \n\n %%endLatex \n ***)\n" 
  size depth width (ref_lat1 initbranch refutation)
  else if (result_latex) then Printf.fprintf c "(*** \n %%beginLatex \n size %d depth %d width %d \n \n  %%endLatex \n ***)\n" size depth width;
 
	(*** Output Latex Translation ***)

  if (result_latex &&  width < 50 && depth < 30) then
  Printf.fprintf c "(*** \n %%beginLatex \n size %d depth %d width %d cuts %d rewrite  %d NYI %d \n \n \\begin{tabular}{c} \n %s \\end{tabular} \n\n %%endLatex \n***)" 
  size depth width cut rewrite notyetImpl  (ref_lat1 initbranch_prenorm prenorm_refutation)
  else if (result_latex) then Printf.fprintf c "(*** \n %%beginLatex \n \n \n Translation successful, probably \n \n size %d depth %d width %d cuts %d rewrite %d  NYI %d \n %%endLatex \n***)" size depth width cut rewrite notyetImpl 
  ; flush stdout
  end
  with Not_Implemented(s) -> Printf.printf "Error %s \n" s 
  end		
  
