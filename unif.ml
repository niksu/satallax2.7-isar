(* File: unif.ml *)
(* Author: Chad E Brown *)
(* Created: December 2010 *)

open Syntax

(*** For Terms with Meta Vars and Meta Type Vars ***)
exception NotGround

type metatrm =
   | MGround of trm (*** Assume this is DB, Name, or a logical constant ***)
   | MVar of metatrm option ref * metatrm list
   | MLam of stp * metatrm
   | MAp of metatrm * metatrm

let rec to_meta m =
  match m with
  | Ap(m1,m2) -> MAp(to_meta m1,to_meta m2)
  | Lam(a,m1) -> MLam(a,to_meta m1)
  | _ -> MGround(m)

let rec meta_to_ground_rec m tau =
   match m with
   | MGround(m1) -> simulsubst m1 tau
   | MVar(x,sigma) ->
       begin
	 match (!x) with
	 | None -> raise NotGround
	 | Some n -> meta_to_ground_rec n (List.map (fun p -> meta_to_ground_rec p tau) sigma)
       end
   | MLam(a,m1) -> Lam(a,meta_to_ground_rec m1 ((DB(0,a))::(List.map (fun n -> shift n 0 1) tau)))
   | MAp(m1,m2) -> Ap(meta_to_ground_rec m1 tau,meta_to_ground_rec m2 tau)

let meta_to_ground d m =
   norm d (meta_to_ground_rec m [])

let rec metashift m i j =
  match m with
    MGround(DB(k,_)) when k < i -> m
  | MGround(DB(k,a)) -> MGround(DB(k + j,a))
  | MLam(a1,m2) -> MLam(a1,metashift m2 (i + 1) j)
  | MAp(m1,m2) -> MAp(metashift m1 i j,metashift m2 i j)
  | _ -> m

let rec metasubst m i n =
  match m with
    MGround(DB(k,_)) when k < i -> m
  | MGround(DB(k,_)) when k = i -> n
  | MGround(DB(k,a)) -> MGround(DB(k - 1,a))
  | MLam(a1,m2) -> MLam(a1,metasubst m2 (i + 1) (metashift n 0 1))
  | MAp(m1,m2) -> MAp(metasubst m1 i n,metasubst m2 i n)
  | _ -> m

let rec metatermNotFreeIn m i =
  match m with
    MGround(DB(j,_)) when i = j -> false
  | MAp(m1,m2) -> (metatermNotFreeIn m1 i) && (metatermNotFreeIn m2 i)
  | MLam(a,m1) -> metatermNotFreeIn m1 (i + 1)
  | _ -> true

let rec metanorm1 d m =
  match m with
  | MGround(m1) ->
      let (n1,b) = norm1 d m1 in
      (MGround(n1),b)
  | MAp(MLam(a,m1),m2) -> (* beta *)
      let (n1,_) = metanorm1 d m1 in
      let (n2,_) = metanorm1 d m2 in
      (metasubst n1 0 n2,true)
  | MLam(_,MAp(m1,MGround(DB(0,_)))) when (metatermNotFreeIn m1 0) -> (* eta *)
      (metashift m1 0 (- 1),true)
	(*** dneg ***)
  | MAp(MAp(MGround(Imp),MAp(MAp(MGround(Imp),m1),MGround(False))),MGround(False)) -> (* double negation reduce *)
      let (n1,_) = metanorm1 d m1 in
      (n1,true)
  | MAp(m1,m2) ->
      let (n1,b1) = metanorm1 d m1 in
      let (n2,b2) = metanorm1 d m2 in
      if (b1 || b2) then
	(MAp(n1,n2),true)
      else
	(m,false)
  | MLam(a1,m1) ->
      let (n1,b1) = metanorm1 d m1 in
      if b1 then
	(MLam(a1,n1),true)
      else
	(m,false)
  | _ -> (m,false)

(* beta-eta-delta-dneg *)
let rec metanorm d m =
  let (m1,reduced) = metanorm1 d m in
  if reduced then (metanorm d m1) else m

let rec meta_simulsubst_meta m tau =
   match m with
   | MGround(DB(k,_)) -> List.nth tau k
   | MGround(m1) -> m
   | MVar(x,sigma) ->
   begin
   match (!x) with
   | None ->
   MVar(x,List.map (fun p -> meta_simulsubst_meta p tau) sigma)
   | Some n ->
   meta_simulsubst_meta n (List.map (fun p -> meta_simulsubst_meta p tau) sigma)
   end
   | MLam(a,m1) -> MLam(a,meta_simulsubst_meta m1 ((MGround(DB(0,a)))::(List.map (fun n -> metashift n 0 1) tau)))
   | MAp(m1,m2) -> MAp(meta_simulsubst_meta m1 tau,meta_simulsubst_meta m2 tau)
	
type ctx = stp list
type dpair = ctx * metatrm * metatrm * stp

let rec distinct_bvar_list_p_rec ml dl =
  match ml with
  | [] -> true
  | ((MGround(DB(i,_)))::mr) when (not (List.mem i dl)) -> distinct_bvar_list_p_rec mr (i::dl)
  | _ -> false

let distinct_bvar_list_p ml =
  distinct_bvar_list_p_rec ml []

let rec pattern_p m =
  match m with
  | MGround(m1) -> true
  | MVar(x,ml) ->
      begin
	match (!x) with
	| None -> distinct_bvar_list_p ml
	| Some n -> raise NotGround (*** Actually, this is not yet written ***)
      end
  | MLam(a,m1) -> pattern_p m1
  | MAp(m1,m2) -> pattern_p m1 && pattern_p m2

let rec meta_head_spine_rec m args =
  match m with
  | MAp(m1,m2) -> meta_head_spine_rec m1 (m2::args)
  | MGround(m1) -> (m1,tpof m1,args)
  | _ -> raise (Failure "Unexpected case in meta_head_spine_rec")

let meta_head_spine m =
  meta_head_spine_rec m []

let rec occurs_check_p x m =
  match m with
  | MGround(_) -> false
  | MVar(y,_) when (x = y) -> true
  | MVar(y,ml) -> occurs_check_list_p x ml
  | MLam(a,m1) -> occurs_check_p x m1
  | MAp(m1,m2) -> occurs_check_p x m1 || occurs_check_p x m2
and occurs_check_list_p x ml =
  match ml with
  | (m::mr) -> occurs_check_p x m || occurs_check_list_p x mr
  | [] -> false

let rec pattern_invert x ml n j =
  match n with
  | MGround(DB(i,_)) ->
      raise (Failure "unwritten") (*** to do - compare with j, if i>=j, find it in ml and use position, OW fail ***)
  | MGround(_) -> n
  | MVar(y,_) when (x = y) -> raise (Failure "Pattern Unify Failure") (*** occurs check ***)
  | MVar(y,nl) -> MVar(y,pattern_list_invert x ml nl j)
  | MLam(a,n1) -> MLam(a,pattern_invert x ml n1 (j + 1))
  | MAp(n1,n2) -> MAp(pattern_invert x ml n1 j,pattern_invert x ml n2 j)
and pattern_list_invert x ml nl j =
  match nl with
  | (n::nr) -> (pattern_invert x ml n j::pattern_list_invert x ml nr j)
  | [] -> []

let rec pattern_unify_rec dl cl =
  match dl with
  | [] -> cl
  | (d::dr) -> pattern_unify_rec_1 d dr cl
and pattern_unify_rec_1 d dl cl =
  match d with
  | (gamma,MLam(a1,m1),MLam(a2,n1),Ar(a,b)) when (a = a1) && (a = a2) ->
      pattern_unify_rec_1 (a::gamma,m1,n1,b) dl cl
  | (gamma,(MVar(x,ml) as m),n,b) ->
      begin
	match (!x) with
	| None ->
	    begin
	      if (distinct_bvar_list_p ml) then
		begin
		  match n with
		  | MVar(y,nl) ->
		      begin
			match (!y) with
			| None ->
			    begin
			      if (distinct_bvar_list_p nl) then
				begin
				  if (x == y) then
				    begin  (*** Flex Flex Same.  ml and nl must have the same length. ***)
				      raise (Failure "unwritten")
				    end
				  else
				    begin  (*** Flex Flex Diff. ***)
				      raise (Failure "unwritten")
				    end
				end
			      else
				begin
				  let xsub = pattern_invert x ml n 0 in
				  x := Some xsub;
				  pattern_unify_rec (List.append dl cl) []
				end
			    end
			| Some(ny) ->
			    pattern_unify_rec_1 (gamma,m,meta_simulsubst_meta ny nl,b) dl cl
		      end
		  | MGround(n1) ->
		      raise (Failure "unwritten")
		  | _ ->
		      raise (Failure "Pattern Unify Failure")
		end
	      else
		begin
		  match n with
		  | MVar(y,nl) ->
		      if (distinct_bvar_list_p nl) then
			begin
			  if (x == y) then
			    begin  (*** Flex Flex Same.  ml and nl must have the same length. ***)
			      raise (Failure "unwritten")
			    end
			  else
			    begin  (*** Flex Flex Diff. ***)
			      raise (Failure "unwritten")
			    end
			end
		      else
			begin
			  raise (Failure "unwritten")
			end
		  | MGround(n1) ->
		      raise (Failure "unwritten")
		  | _ ->
		      raise (Failure "Pattern Unify Failure")
		end
	    end
	| Some(mx) -> pattern_unify_rec_1 (gamma,n,meta_simulsubst_meta mx ml,b) dl cl
      end
  | (gamma,m,(MVar(y,nl) as n),b) ->
      pattern_unify_rec_1 (gamma,n,m,b) dl cl
  | (gamma,m,n,b) ->
      let (mh,mhtp,ml) = meta_head_spine m in
      let (nh,_,nl) = meta_head_spine n in
      if (mh = nh) then
	pattern_unify_rec_spine gamma mhtp ml nl dl cl
      else
	raise (Failure "Pattern Unify Failure")
  | _ -> raise (Failure "Pattern Unify Failure")
and pattern_unify_rec_spine gamma tp ml nl dl cl =
  match (tp,ml,nl) with
  | (_,[],[]) -> pattern_unify_rec dl cl
  | (Ar(a,b),(m::ml),(n::nl)) -> pattern_unify_rec_spine gamma b ml nl ((gamma,m,n,a)::dl) cl
  | _ -> raise (Failure "Pattern Unify Failure")
      
let pattern_unify dl = pattern_unify_rec dl []
