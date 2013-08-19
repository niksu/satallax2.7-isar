open State
open Syntax
open Flag
open Branch
open Litcount
  
  
(** The module step encodes a set of tableau steps, where principal and side formulae are fixed, but the actual branch is left open**)
module Step = struct
  
  type rule = IMP | NIMP | ALL of stp * trm * trm | NALL of stp * trm * string | MAT | DEC | CON | BE | BQ | FE | FQ | EPS of trm * trm | CUT | KNOWN of trm * string * stp list
	(**  The type of step is principal formulae * alternatives * free existential witnesses * rule **)
  type step = ((int list) * (int list list) * (string list) * rule) 
	
	
  let rec trm_free_variable m = match m with
  | Name(x,_) -> [x]
  | Lam(_,m1) -> trm_free_variable m1 
  | Ap(m1,m2) -> List.rev_append (trm_free_variable m1) (trm_free_variable m2) 
  | _ -> []    
	
  let rec free_variable c = match c with
  | (l::cr) -> let t = literal_to_trm (-l) in List.rev_append (trm_free_variable t) (free_variable cr)
  | [] -> []	
	
	
	(** unused - 
	   given a literal l and a list of witnesses it creates a Cut-step on the term of l **)
  let make_Cut l witnesses =
    let free = trm_free_variable (literal_to_trm l) in
    if debug_free_names then Printf.printf  "step has free %s \n" (String.concat "," free) ;
    let free = List.fold_left (fun f v -> if (not (List.mem v f)) && List.mem v witnesses then v::f else f) [] free in	
    ([],[[-l];[l]],free,CUT)  	
      
	(** Input: a rule clause c, the clause to ruleinfo function cr and a list of witnesses
	   Invariant: 
	   cr c succeeds,
	   witnesses contains all variable names which are selected by a not-forall clause.
	   Output: the list of steps that are (possibly partially) encoded by c, 
	   with the list of free variables that are in witnesses
	   Note: For all clauses except pattern clauses the list contains only one step
	   **)
  let make c cr witnesses : step list = 
    let free = List.append (free_variable c)
 (*** Chad: Aug 2011: Added any free variables in an instantiation. There's a problem if the quantifier is vacuous and the instantiation (though it disappears upon reduction) contains witness variables. This bug showed up in LCL732^5.p ***)
	(try match (cr c) with InstRule(_,_,n) -> trm_free_variable n | _ -> [] with Not_found -> [])
    in
    if debug_free_names then Printf.printf  "step has free %s \n" (String.concat "," free) ;
    let free = List.fold_left (fun f v -> if (not (List.mem v f)) && List.mem v witnesses then v::f else f) [] free in
    begin	
      match cr c with
      | NegPropRule(m) -> 
	  begin 
  	    let  head = [- List.hd c] in  
            match m with 
            | Ap(Ap(Imp,m1),m2) ->
		let (s,t) = (get_literal m1,get_literal m2) in 
		let  branches = [[s;-t]] in
		[(head,branches,free,NIMP)]
	    | Ap(Ap(Eq(Prop),x),y) ->
		let  s = get_literal x in
		let  t = get_literal y in 
		let branches = [[s;-t];[-s;t]] in
		[(head,branches,free,BE)]
	    | Ap(Ap(Eq(Base(_)),x),y) ->
		let  ss = (List.tl c) in
		let branches = List.map (fun s -> [s]) ss in
		[(head,branches,free,DEC)]
            | Ap(Ap(Eq(Ar(_,_)),x),y) ->
		let  s = List.hd (List.tl c) in
		let branches = [[s]] in
		[(head,branches,free,FE)]
            | _ ->  failwith("can't handle yet term " ^ (trm_str m))
  	  end
      | PosPropRule(m) -> 
	  begin 
	    let  head = [- List.hd c] in
            match m with 
            | Ap(Ap(Imp,_),_) ->
		let  s = List.hd (List.tl c) in
		let  t = List.hd (List.tl (List.tl c)) in
		let branches = [[s];[t]] in
		[(head,branches,free,IMP)]
            | Ap(Ap(Eq(Prop),x),y) ->
		let  s = get_literal x in
		let  t = get_literal y in 
		let branches = [[s;t];[-s;-t]] in
		[(head,branches,free,BQ)]
            | Ap(Ap(Eq(Ar(_,_)),x),y) ->
		let  s = List.hd (List.tl c) in
		let branches = [[s]] in
		[(head,branches,free,FQ)]
            | _ ->  failwith("can't handle yet term " ^ (trm_str m)) 
	  end
      | InstRule(a,m,n) -> 
	  begin 
      	    let  head = [- List.hd c] in    
	    let  s = List.hd (List.tl c) in
	    let branches = [[s]] in
	    [(head,branches,free,ALL(a,m,n))]
	  end
      | FreshRule(a,m,x) ->
	  begin 
     	    let  head = [- List.hd c] in
     	    let  s = List.hd (List.tl c) in
	    let branches = [[s]] in
	    [(head,branches,free,NALL(a,m,x))]
	  end
      | MatingRule(plit,nlit) ->  
	  begin
	    let head = [plit;nlit] in
      	    let  ss = (List.tl (List.tl c)) in
	    let branches = List.map (fun s -> [s]) ss in
	    [(head,branches,free,MAT)]
	  end
      | ConfrontationRule(plit,nlit) ->  
	  begin 
	    let (n,m)= (literal_to_trm plit,literal_to_trm (-nlit) ) in
	    let head = [plit;nlit] in
	    match (n,m) with
	    | (  Ap(Ap(Eq(a),s),t)  ,  Ap(Ap(Eq(a'),u),v)  ) when a=a' -> begin
		let (su,tu,sv,tv)=(neg (eq a s u),neg (eq a t u),neg (eq a s v),neg (eq a t v)) in
		let (lsu,ltu,lsv,ltv) = (get_literal su,get_literal tu,get_literal sv,get_literal tv) in 
		let branches = [[lsu;ltu];[lsv;ltv]] in
		[(head,branches,free,CON)] end
	    | _ -> failwith("can't handle with Confrontation Rule: "^ (trm_str n) ^" and "^ (trm_str m) )
	  end 
      | ChoiceRule(eps,pred) -> 
	  begin
            let head = [] in
	    let  s = List.hd c in
            let  t = List.hd (List.tl c) in
	    let branches = [[t];[s]] in 
	    [(head,branches,free,EPS(eps,pred))]
	  end
      | Known(n,s,al) ->
	  [([],[[n]],free,KNOWN(literal_to_trm n,s,al))]
    end
      
      
  let get_head (h,_,_,_) =  h
      
  let get_branches (_,b,_,_) = b
      
  let get_free (_,_,f,_) = f 
      
  let get_rule  (_,_,_,r) =  r 
      
  let rule_to_str r = match r with   IMP -> "IMP" | NIMP -> "NIMP"| ALL(_,_,_) -> "ALL" | NALL(_,_,_) -> "NALL" | MAT -> "MAT"| DEC -> "DEC" | CON -> "CON"| BE -> "BE" | BQ -> "BQ" | FE -> "FE" | FQ -> "FQ"| EPS(_,_) -> "EPS" | CUT -> "CUT" | KNOWN(_,_,_) -> "KNOWN"
      
      
  let number_of_branches (_,b,_,r) =  match r with  NALL(_,_,_) -> 0  | _ ->  List.length b	
      
(** Input: A step and a branch
   Output: returns true if the negation of a principal formula is on the branch 
   or if an alternative is a subset of the branch **)
  let satisfied (h,bl,f,r) b =  
    List.exists (fun l -> Branch.mem (-l) b) h || 
    List.exists (fun br -> List.for_all (fun l -> Branch.mem l b ) br) bl 
      
(** Input: A list of blocked witnesses, a branch b and a step s 
   Invariant: satisfied s b = false
   Output: returns true if the step can be applied to the branch
   and if no blocked variable is free in the step**)
  let suitable blocked b (h,_,f,_) = 
    if debug_free_names then Printf.printf  "blocked witnesses %s and step has witnesses %s \n" 
	(String.concat "," blocked) (String.concat "," f) ;
    ( List.for_all (fun n -> Branch.mem n b ) h ) && ( not ( List.exists (fun n -> List.mem n blocked) f ) )
      
      
  let get_witness (_,_,_,r) = match r with NALL(_,_,x) -> (true,x) | _ -> (false,"") 
      
(** Input: Step s and a literal count array litc
   Invariant: litc maps literals to the number of their occurences in the set of steps
   Output: The sum of the occurences of all side formulae, for implication positive and negative occurences are added
   Note: This was an arbitrary implementation and can be changed or left out**)
  let heuristic (head,bl,f,r) litc= 
    let heu = match r with
    | NALL(_,_,_) -> 0
    | IMP -> List.fold_left (fun h ls -> List.fold_left (fun h' l -> h' + (LitCount.get litc l) + (LitCount.get litc (-l))) h ls ) 0 bl
    | _ -> List.fold_left (fun h ls -> List.fold_left (fun h' l -> h' + (LitCount.get litc l)) h ls ) 0 bl
    in
    heu 
end
