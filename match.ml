(* File: match.ml *)
(* Author: Chad E Brown *)
(* Created: December 2010 *)

open Syntax
open Flags

(*** For Terms with Meta Vars and Meta Type Vars ***)
exception NotGround
exception PatternMatchFailed

let emptyd : (string,trm) Hashtbl.t = Hashtbl.create 1

type metatrm =
   | MGround of trm (*** Assume this is DB, Name, or a logical constant ***)
   | MVar of (int * metatrm option ref) * metatrm list
   | MLam of stp * metatrm
   | MAp of metatrm * metatrm

type ctx = stp list
type dpair = ctx * metatrm * trm * stp
type evar = int * metatrm option ref

let rec id_subst i gamma =
  match gamma with
  | (a::gammar) -> ((MGround(DB(i,a)))::(id_subst (i + 1) gammar))
  | [] -> []

let evarcount = ref 0

let string_of_evar (e,_) =
  "?" ^ (string_of_int e)

let rec new_evar v gamma a : evar * metatrm =
  match a with
  | Ar(a1,a2) ->
      let (x,xs) = new_evar v (a1::gamma) a2 in
      (x,MLam(a1,xs))
  | _ ->
      let x = (!evarcount,ref None) in
      incr evarcount;
      let s = id_subst 0 gamma in
      (x,MVar(x,s))

let rec copy_evar v x : evar =
  let y = (!evarcount,ref None) in
  incr evarcount;
  y

let lpar p = if p then "(" else ""

let rpar p = if p then ")" else ""

let rec metatrm_str_rec m p =
  match m with
  | MGround(m0) -> "<" ^ (trm_str m0) ^ ">"
  | MVar(x,s) -> (lpar p) ^ (string_of_evar x) ^ "[" ^ (String.concat "," (List.map (fun m -> metatrm_str_rec m false) s)) ^ "]" ^ (rpar p)
  | MLam(a,m1) -> (lpar p) ^ "\\_:" ^ (stp_str a) ^ "." ^ (metatrm_str_rec m1 false) ^ (rpar p)
  | MAp(m1,m2) ->
      begin
	match m1 with
	| MLam _ -> (lpar p) ^ (metatrm_str_rec m1 true) ^ " " ^ (metatrm_str_rec m2 true) ^ (rpar p)
	| _ -> (lpar p) ^ (metatrm_str_rec m1 false) ^ " " ^ (metatrm_str_rec m2 true) ^ (rpar p)
      end

let metatrm_str m = metatrm_str_rec m false
  
let rec to_meta m =
  match m with
  | Ap(m1,m2) -> MAp(to_meta m1,to_meta m2)
  | Lam(a,m1) -> MLam(a,to_meta m1)
  | _ -> MGround(m)

let rec meta_to_ground_rec m tau =
  match m with
  | MGround(m1) -> simulsubst m1 tau
  | MVar((e,x),sigma) ->
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
  | MGround(_) -> m
  | MLam(a1,m2) -> MLam(a1,metasubst m2 (i + 1) (metashift n 0 1))
  | MAp(m1,m2) -> MAp(metasubst m1 i n,metasubst m2 i n)
  | MVar(x,sigma) -> MVar(x,List.map (fun m0 -> metasubst m0 i n) sigma)

let gen_mlam_body a m =
  match m with
  | MLam(_,m1) -> m1
  | MVar(x,sigma) -> raise (Failure ("Metavar of function type? " ^ (string_of_evar x)))
  | _ -> MAp(metashift m 0 1,MGround(DB(0,a)))

let rec metatermNotFreeIn m i =
  match m with
  | MGround(DB(j,_)) when i = j -> false
  | MVar(x,ml) -> metatermNotFreeInL ml i
  | MAp(m1,m2) -> (metatermNotFreeIn m1 i) && (metatermNotFreeIn m2 i)
  | MLam(a,m1) -> metatermNotFreeIn m1 (i + 1)
  | _ -> true
and metatermNotFreeInL ml i =
  match ml with
  | (m::mr) -> (metatermNotFreeIn m i) && (metatermNotFreeInL mr i)
  | [] -> true

let rec meta_simulsubst_meta m tau =
   match m with
   | MGround(DB(k,_)) -> List.nth tau k
   | MGround(m1) -> m
   | MVar((e,x),sigma) ->
       begin
	 match (!x) with
	 | None ->
	     MVar((e,x),List.map (fun p -> meta_simulsubst_meta p tau) sigma)
	 | Some n ->
	     meta_simulsubst_meta n (List.map (fun p -> meta_simulsubst_meta p tau) sigma)
       end
   | MLam(a,m1) -> MLam(a,meta_simulsubst_meta m1 ((MGround(DB(0,a)))::(List.map (fun n -> metashift n 0 1) tau)))
   | MAp(m1,m2) -> MAp(meta_simulsubst_meta m1 tau,meta_simulsubst_meta m2 tau)

let rec metanorm1 m =
  match m with
  | MGround(m1) ->
      let (n1,b) = onlybetanorm1 m1 in
      (MGround(n1),b)
  | MAp(MLam(a,m1),m2) -> (* beta *)
      let (n1,_) = metanorm1 m1 in
      let (n2,_) = metanorm1 m2 in
      (metasubst n1 0 n2,true)
(***  | MLam(_,MAp(m1,MGround(DB(0,_)))) when (metatermNotFreeIn m1 0) -> (* eta *) (*** Removed eta here.  The way dpairs at functional type are handled, they will be more or less eta expanded on the fly anyway.  Hence there is no point in wasting time doing this. - Chad, Jan 10, 2011 ***)
      (metashift m1 0 (- 1),true) ***)
	(*** dneg ***)
  | MAp(MAp(MGround(Imp),MAp(MAp(MGround(Imp),m1),MGround(False))),MGround(False)) -> (* double negation reduce *)
      let (n1,_) = metanorm1 m1 in
      (n1,true)
  | MAp(m1,m2) ->
      let (n1,b1) = metanorm1 m1 in
      let (n2,b2) = metanorm1 m2 in
      if (b1 || b2) then
	(MAp(n1,n2),true)
      else
	(m,false)
  | MLam(a1,m1) ->
      let (n1,b1) = metanorm1 m1 in
      if b1 then
	(MLam(a1,n1),true)
      else
	(m,false)
  | MVar((e,x),sigma) ->
      begin
	match (!x) with
	| None ->
	    let (sigmar,sigmab) = metasubstnorm1 sigma in
	    if sigmab then
	      (MVar((e,x),sigmar),true)
	    else
	      (m,false)
	| Some m1 ->
	    (meta_simulsubst_meta m1 sigma,true)
      end
and metasubstnorm1 sigma =
  match sigma with
  | (m1::sigmar) ->
      let (n1,b1) = metanorm1 m1 in
      let (sigma2,b2) = metasubstnorm1 sigmar in
      if (b1 || b2) then
	(n1::sigma2,true)
      else
	(sigma,false)
  | [] -> ([],false)

(* beta-dneg *)
let rec metanorm m =
  let (m1,reduced) = metanorm1 m in
  if reduced then (metanorm m1) else m

let metanormneg m =
  match m with
  | MAp(MAp(MGround(Imp),m1),MGround(False)) -> m1
  | _ -> MAp(MAp(MGround(Imp),m),MGround(False))

let rec meta_copy m evarassoc =
  begin
    match m with
    | MGround(m1) -> m
    | MVar((e,x),sigma) ->
	let sigma1 = List.map (fun m -> meta_copy m evarassoc) sigma in
	begin
	  match (!x) with
	  | None ->
	      begin
		try
		  let (_,y) = List.find (fun (e1,_) -> (e == e1)) evarassoc in
		  MVar(y,sigma1)
		with
		| Not_found ->
		    MVar((e,x),sigma1)
	      end
	  | Some m1 ->
	      let m1c = meta_copy m1 evarassoc in
	      metanorm (meta_simulsubst_meta m1c sigma1)
	end
    | MLam(a1,m1) ->
	let m1c = meta_copy m1 evarassoc in
	MLam(a1,m1c)
    | MAp(m1,m2) ->
	let m1c = meta_copy m1 evarassoc in
	let m2c = meta_copy m2 evarassoc in
	MAp(m1c,m2c)
  end

let rec distinct_bvar_list_p_rec ml dl =
  match ml with
  | [] -> true
  | ((MGround(DB(i,_)))::mr) when (not (List.mem i dl)) -> distinct_bvar_list_p_rec mr (i::dl)
  | _ -> false

let distinct_bvar_list_p ml =
  distinct_bvar_list_p_rec ml []

let mvar_p m =
  match m with
  | MVar _ -> true
  | _ -> false

let rec pattern_p m =
  match m with
  | MGround(m1) -> true
  | MVar((e,x),ml) ->
      begin
	match (!x) with
	| None -> distinct_bvar_list_p ml
	| Some n ->
	    pattern_p (meta_simulsubst_meta n ml) (*** Mar 2012 - finally wrote this case ***)
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

let rec occurs_check_p (e,x) m =
  match m with
  | MGround(_) -> false
  | MVar((e',y),_) when (e = e') -> true
  | MVar((e',y),ml) -> occurs_check_list_p (e,x) ml
  | MLam(a,m1) -> occurs_check_p (e,x) m1
  | MAp(m1,m2) -> occurs_check_p (e,x) m1 || occurs_check_p (e,x) m2
and occurs_check_list_p x ml =
  match ml with
  | (m::mr) -> occurs_check_p x m || occurs_check_list_p x mr
  | [] -> false

let rec pattern_invert_db ml n j i k =
  match ml with
  | ((MGround(DB(i2,a)))::mr) when i = i2 -> MGround(DB(j+k,a))
  | (_::mr) -> pattern_invert_db mr n j i (k + 1)
  | [] -> raise PatternMatchFailed

let rec pattern_invert x ml n j =
  match n with
  | DB(i,_) ->
      if (i < j) then
	MGround(n)
      else
	pattern_invert_db ml n j (i - j) 0
  | Lam(a,n1) -> MLam(a,pattern_invert x ml n1 (j + 1))
  | Ap(n1,n2) -> MAp(pattern_invert x ml n1 j,pattern_invert x ml n2 j)
  | _ -> MGround(n)
and pattern_list_invert x ml nl j =
  match nl with
  | (n::nr) -> (pattern_invert x ml n j::pattern_list_invert x ml nr j)
  | [] -> []

let rec pattern_match_rec dl cl =
  match dl with
  | [] -> cl
  | (d::dr) -> pattern_match_rec_1 d dr cl
and pattern_match_rec_1 d dl cl =
  match d with
  | (gamma,m1,n1,Ar(a,b)) ->
      pattern_match_rec_1 (a::gamma,gen_mlam_body a m1,gen_lam_body a n1,b) dl cl
  | (gamma,MVar((e,x),ml),n,b) ->
      begin
	match (!x) with
	| None ->
	    begin
	      if (distinct_bvar_list_p ml) then
		let ni = pattern_invert (e,x) ml n 0 in
		begin
		  x := Some ni;
		  let clr = ref [] in
		  let dlr = ref dl in
		  List.iter
		    (fun ((gammac,mc,nc,b) as c) ->
		      let (mc1,mb) = metanorm1 mc in
		      if mb then
			let mcn = metanorm mc1 in
			dlr := ((gammac,mcn,nc,b)::!dlr)
		      else
			clr := (c::(!clr))
		    )
		    cl;
		  pattern_match_rec (!dlr) (!clr)
		end
	      else
		begin
		  pattern_match_rec dl (d::cl)
		end
	    end
	| Some(mx) -> pattern_match_rec_1 (gamma,metanorm (meta_simulsubst_meta mx ml),n,b) dl cl
      end
  | (gamma,m,n,b) ->
      let (mh,mhtp,ml) = meta_head_spine m in
      let (nh,nl) = head_spine n in
      if (mh = nh) then
	pattern_match_rec_spine gamma mhtp ml nl dl cl
      else
	raise PatternMatchFailed
and pattern_match_rec_spine gamma tp ml nl dl cl =
  match (tp,ml,nl) with
  | (_,[],[]) -> pattern_match_rec dl cl
  | (Ar(a,b),(m::ml),(n::nl)) -> pattern_match_rec_spine gamma b ml nl ((gamma,m,n,a)::dl) cl
  | _ -> raise PatternMatchFailed
      
let pattern_match dl = pattern_match_rec dl []

let mem_evar (d,a) l =
  try
    ignore(List.find (fun (e,x) -> e = d) l);
    true
  with Not_found -> false

let rec update_strict xl m =
  match m with
  | MGround(_) -> xl
  | MVar(x,sigma) ->
      if (mem_evar x xl) then
	xl
      else if (distinct_bvar_list_p sigma) then
	(x::xl)
      else
	xl
  | MAp(m1,m2) -> update_strict (update_strict xl m1) m2
  | MLam(a1,m1) -> update_strict xl m1

(** HOUNIF1 - Mar 2012 - Chad **)
type udpair = ctx * metatrm * metatrm * stp
type cdpairs = int * evar list * metatrm list * (ctx * metatrm * metatrm * stp) list
type frpairstp = (ctx * (metatrm * (int * metatrm option ref) * metatrm list) *
         (metatrm * Syntax.trm * Syntax.stp * metatrm list) * stp) list
type ffpairstp = (ctx * (metatrm * (int * metatrm option ref) * metatrm list) *
		    (metatrm * (int * metatrm option ref) * metatrm list) * stp) list

exception SimplFailed
exception SimplElim of evar * metatrm * udpair list * frpairstp * ffpairstp

let verbosity : int ref = ref 0;;

let rec id_subst_2 i gamma =
  match gamma with
  | (a::gammar) -> ((DB(i,a))::(id_subst_2 (i + 1) gammar))
  | [] -> []

let meta_to_ground_2 m tau =
   norm emptyd (meta_to_ground_rec m tau)

let rec spine_dpairs gam a args1 args2 dpairs =
  match (a,args1,args2) with
  | (Ar(a,b),(m1::args1),(m2::args2)) -> spine_dpairs gam b args1 args2 ((gam,m1,m2,a)::dpairs)
  | (_,[],[]) -> dpairs
  | _ -> raise (Failure "Unexpected case in spine_dpairs")

let rec metapattern_invert_db ml n j i k =
  match ml with
  | ((MGround(DB(i2,a)))::mr) when i = i2 -> MGround(DB(j+k,a))
  | (_::mr) -> pattern_invert_db mr n j i (k + 1)
  | [] -> raise PatternMatchFailed

let rec metapattern_invert (e,x) ml n j =
  match n with
  | MGround(DB(i,_)) ->
      if (i < j) then
	n
      else
	metapattern_invert_db ml n j (i - j) 0
  | MGround(_) -> n
  | MLam(a,n1) -> MLam(a,metapattern_invert (e,x) ml n1 (j + 1))
  | MAp(n1,n2) -> MAp(metapattern_invert (e,x) ml n1 j,metapattern_invert (e,x) ml n2 j)
  | MVar((d,y),sl) when e = d -> raise PatternMatchFailed (*** occurs check ***)
  | MVar((d,y),sl) -> MVar((d,y),metapattern_list_invert (e,x) ml sl j)
and metapattern_list_invert x ml nl j =
  match nl with
  | (n::nr) -> (metapattern_invert x ml n j::metapattern_list_invert x ml nr j)
  | [] -> []

let pack_into_dpairs dpairs frpairs ffpairs =
  (List.append (List.map (fun (gam,m1,m2,a) -> (gam,metanorm m1,metanorm m2,a)) dpairs)
     (List.append
	(List.map (fun (gam,(m1,_,_),(m2,_,_,_),a) -> (gam,metanorm m1,metanorm m2,a)) frpairs)
	(List.map (fun (gam,(m1,_,_),(m2,_,_),a) -> (gam,metanorm m1,metanorm m2,a)) ffpairs)))

let rec simpl_dpairs (dpairs:udpair list) xl frpairs ffpairs =
  if (!verbosity > 5) then
    begin
      Printf.printf "simpl_dpairs\n";
      List.iter (fun (gam,m1,m2,b) -> Printf.printf ". %s\nm1 = %s\nm2 = %s\n" (stp_str b) (metatrm_str m1) (metatrm_str m2)) dpairs;
    end;
  match dpairs with
  | (gam,m1,m2,Ar(a,b))::dpairs ->
      if (!verbosity > 5) then begin Printf.printf "simpl_dpairs 0\n" end;
      simpl_dpairs ((a::gam,gen_mlam_body a m1,gen_mlam_body a m2,b)::dpairs) xl frpairs ffpairs
  | (gam,((MVar(x,sl1)) as m1),m2,b)::dpairs when distinct_bvar_list_p sl1 -> (*** pattern ***)
      begin
	try
	  let m2' = metapattern_invert x sl1 m2 0 in
	  raise (SimplElim(x,m2',dpairs,frpairs,ffpairs))
	with PatternMatchFailed ->
	  simpl_dpairs_2 dpairs xl frpairs ffpairs gam m1 m2 b
      end
  | (gam,m1,((MVar(x,sl2)) as m2),b)::dpairs when distinct_bvar_list_p sl2 -> (*** pattern ***)
      begin
	try
	  let m1' = metapattern_invert x sl2 m1 0 in
	  raise (SimplElim(x,m1',dpairs,frpairs,ffpairs))
	with PatternMatchFailed ->
	  simpl_dpairs_2 dpairs xl frpairs ffpairs gam m1 m2 b
      end
  | (gam,m1,m2,b)::dpairs ->
      simpl_dpairs_2 dpairs xl frpairs ffpairs gam m1 m2 b
  | [] -> (frpairs,ffpairs)
and simpl_dpairs_2 dpairs xl frpairs ffpairs gam m1 m2 b =
  if (!verbosity > 5) then begin Printf.printf "simpl_dpairs_2\n" end;
  begin
    match (m1,m2) with
    | (MVar(x1,sigma1),MVar(x2,sigma2)) ->
	simpl_dpairs dpairs xl frpairs ((gam,(m1,x1,sigma1),(m2,x2,sigma2),b)::ffpairs)
    | (_,MVar(x2,sigma2)) ->
	begin
	  match (meta_head_spine m1) with
	  | (h1,h1tp,args1) ->
	      simpl_dpairs dpairs xl ((gam,(m2,x2,sigma2),(m1,h1,h1tp,args1),b)::frpairs) ffpairs
	end
    | (MVar(x1,sigma1),_) ->
	begin
	  match (meta_head_spine m2) with
	  | (h2,h2tp,args2) ->
	      simpl_dpairs dpairs xl ((gam,(m1,x1,sigma1),(m2,h2,h2tp,args2),b)::frpairs) ffpairs
	end
    |	_ ->
	begin
	  match (meta_head_spine m1,meta_head_spine m2) with
	  | ((h1,h1tp,args1),(h2,h2tp,args2)) ->
	      if (h1 = h2) then
		simpl_dpairs
		  (spine_dpairs gam h1tp args1 args2 dpairs)
		  xl
		  frpairs ffpairs
	      else
		raise SimplFailed
	end
  end

let defaultinsts : (int,metatrm) Hashtbl.t = Hashtbl.create 100
let evargamma : (int,ctx) Hashtbl.t = Hashtbl.create 100
let evarprojs : (int,(int * stp * stp list * stp) list) Hashtbl.t = Hashtbl.create 100

let defaultmeta a =
  match a with
  | Prop -> MGround(False)
  | _ -> MAp(MGround(Choice(a)),MLam(a,MGround(False)))

let rec new_evar_w_default gamma a g =
  match a with
  | Ar(a1,a2) ->
      let (x,xs) = new_evar_w_default (a1::gamma) a2 (fun n -> MLam(a1,g n)) in
      (x,MLam(a1,xs))
  | _ ->
      let x = (!evarcount,ref None) in
      let s = id_subst 0 gamma in
      Hashtbl.add defaultinsts !evarcount (g (defaultmeta a));
      Hashtbl.add evargamma !evarcount gamma;
      let i = ref 0 in
      let projl = ref [] in
      List.iter (fun b ->
	let (argtps,rtp) = argtps_rtp b in
	if (rtp = a) then
	  begin
	    if (!verbosity > 20) then Printf.printf "%d is a possible projection for %s\n" !i (string_of_evar x);
	    projl := (!i,b,argtps,a)::!projl;
	  end;
	incr i;
	)
	gamma;
      Hashtbl.add evarprojs !evarcount !projl;
      incr evarcount;
      (x,MVar(x,s))

let rec force_meta_to_ground_rec m tau =
  if (!verbosity > 5) then begin Printf.printf "force_meta_to_ground_rec m %s\n" (metatrm_str m) end;
   match m with
   | MGround(m1) -> simulsubst m1 tau
   | MVar((e,x),sigma) ->
       begin
	 match (!x) with
	 | None ->
	     let n = Hashtbl.find defaultinsts e in
	     x := Some n;
	     force_meta_to_ground_rec n (List.map (fun p -> force_meta_to_ground_rec p tau) sigma)
	 | Some n ->
	     force_meta_to_ground_rec n (List.map (fun p -> force_meta_to_ground_rec p tau) sigma)
       end
   | MLam(a,m1) -> Lam(a,force_meta_to_ground_rec m1 ((DB(0,a))::(List.map (fun n -> shift n 0 1) tau)))
   | MAp(m1,m2) -> Ap(force_meta_to_ground_rec m1 tau,force_meta_to_ground_rec m2 tau)

let rec imitate gam gam' sigma h a args =
  match (a,args) with
  | (Ar(a1,a2),(arg1::argr)) ->
      let (z,zsub) = new_evar_w_default gam a1 (fun x -> x) in
      let (g,zl,dpairs2) = imitate gam gam' sigma (MAp(h,zsub)) a2 argr in
      (g,(z::zl),((gam',(meta_simulsubst_meta zsub sigma),arg1,a1)::dpairs2))
  | (_,[]) -> (h,[],[])
  | _ -> raise (Failure "Unexpected case in imitate")

let rec project gam h a =
  match a with
  | Ar(a1,a2) ->
      let (z,zsub) = new_evar_w_default gam a1 (fun x -> x) in
      let (g,zl) = project gam (MAp(h,zsub)) a2 in
      (g,(z::zl))
  | _ -> (h,[])

(*** yl are the 'local' meta-variables (may not be needed), xsl is the original metavars with a subst that will give potential instantiations in the end ***)
let rec hounif1da (yl:evar list) (xsl:metatrm list) (dpairs:udpair list) (b:int) (f:stp -> trm -> unit) =
  if (!verbosity > 5) then begin Printf.printf "hounif1d\n" end;
  if (!verbosity > 5) then begin List.iter (fun (_,m1,m2,a) -> Printf.printf "> %s\n%s\n%s\n" (stp_str a) (metatrm_str m1) (metatrm_str m2)) dpairs end;
  try
    let (frpairs,ffpairs) = simpl_dpairs dpairs yl [] [] in
    begin
      if (!verbosity > 5) then
	begin
	  Printf.printf "simpl_dpairs returned frpairs\n";
	  List.iter (fun (_,(m1,x,sigma),(m2,h,htp,args2),a) -> Printf.printf "> %s\n%s\n%s\n" (stp_str a) (metatrm_str m1) (metatrm_str m2)) frpairs;
	  Printf.printf "simpl_dpairs returned ffpairs\n";
	  List.iter (fun (_,(m1,x,sigma),(m2,y,sigma2),a) -> Printf.printf "> %s\n%s\n%s\n" (stp_str a) (metatrm_str m1) (metatrm_str m2)) ffpairs;
	  flush stdout;
	end;
      match frpairs with
      | ((gam,(m1,(e,x),sigma),(m2,h,htp,args2),a)::frpairs') ->
	  begin
	    if (b > 0) then
	      begin
		let b2 = b - (get_int_flag "HOUNIF1PROJECT") in
		if (!verbosity > 5) then begin Printf.printf "Looking up projs for %s\n" (string_of_evar (e,x)) end;
		List.iter
		  (fun (i,a2,argtps,basetp) ->
		    if (!verbosity > 5) then begin Printf.printf "About to project %d for %s\n" i (string_of_evar (e,x)) end;
		    let (g,zl) = project (Hashtbl.find evargamma e) (MGround(DB(i,a2))) a2 in
		    begin (*** Project i ***)
		      x := Some g;
		      hounif1da (List.append
				   zl
				   (List.filter (fun (d,y) -> not (d = e)) yl))
			xsl
			(pack_into_dpairs [(gam,m1,m2,a)] frpairs ffpairs) b2 f;
		      if (!verbosity > 5) then begin Printf.printf "Resetting %s from project %d\n" (string_of_evar (e,x)) i end;
		      x := None; (*** Reset x ***)
		    end
		      )
		  (Hashtbl.find evarprojs e);
		if (!verbosity > 5) then begin Printf.printf "Finished Projections for %s\n" (string_of_evar (e,x)) end;
		begin
		  match h with
		  | DB _ -> ()
		  | _ ->
		      let (g,zl,dpairs2) = imitate (Hashtbl.find evargamma e) gam sigma (MGround(h)) htp args2 in
		      begin (*** Imitate h ***)
			if (!verbosity > 5) then begin Printf.printf "About to imitate ?%d\n" e end;
			x := Some g;
			hounif1da (List.append
				     zl
				     (List.filter (fun (d,y) -> not (d = e)) yl))
			  xsl
			  (pack_into_dpairs dpairs2 frpairs' ffpairs)
			  (b - (get_int_flag "HOUNIF1IMITATE")) f;
			if (!verbosity > 5) then begin Printf.printf "Resetting %s from imitate\n" (string_of_evar (e,x)) end;
			x := None (*** Reset x ***)
		      end
		end;
	      end
	  end
      | [] ->
		(*** Only flex-flex remain ***)
	  if (!verbosity > 5) then begin Printf.printf "only flex-flex remain b = %d\n" b end;
	  List.iter 
	    (fun n ->
	      let n' = norm emptyd (force_meta_to_ground_rec n []) in
	      if (!verbosity > 5) then begin Printf.printf "new inst %s\n" (trm_str n') end;
	      f (tpof n') n'
		)
	    xsl;
	  List.iter (fun (d,y) ->
	    if (!verbosity > 5) then begin Printf.printf "Resetting %s from final force\n" (string_of_evar (d,y)) end;
	    y := None) yl;
	  ()
    end
  with
  | SimplElim((e,x),m,dpairs,frpairs,ffpairs) ->
      if (!verbosity > 5) then begin Printf.printf "Eliminating %s := %s\n" (string_of_evar (e,x)) (metatrm_str m) end;
      x := Some m;
      hounif1da (List.filter (fun (d,y) -> not (d = e)) yl) xsl (pack_into_dpairs dpairs frpairs ffpairs) b f;
      if (!verbosity > 5) then begin Printf.printf "Resetting %s from elim\n" (string_of_evar (e,x)) end;
      x := None; (*** Reset x ***)
  | SimplFailed -> ()

(*** yl are the 'local' meta-variables (may not be needed), xsl is the original metavars with a subst that will give potential instantiations in the end ***)
let rec hounif1db (yl:evar list) (xsl:metatrm list) (dpairs:udpair list) (b:int) (r:cdpairs list) (f:stp -> trm -> unit) : cdpairs list =
  if (!verbosity > 5) then begin Printf.printf "hounif1db\n" end;
  if (!verbosity > 5) then begin List.iter (fun (_,m1,m2,a) -> Printf.printf "> %s\n%s\n%s\n" (stp_str a) (metatrm_str m1) (metatrm_str m2)) dpairs end;
  try
    let (frpairs,ffpairs) = simpl_dpairs dpairs yl [] [] in
    begin
      if (!verbosity > 5) then
	begin
	  Printf.printf "simpl_dpairs returned frpairs\n";
	  List.iter (fun (_,(m1,x,sigma),(m2,h,htp,args2),a) -> Printf.printf "> %s\n%s\n%s\n" (stp_str a) (metatrm_str m1) (metatrm_str m2)) frpairs;
	  Printf.printf "simpl_dpairs returned ffpairs\n";
	  List.iter (fun (_,(m1,x,sigma),(m2,y,sigma2),a) -> Printf.printf "> %s\n%s\n%s\n" (stp_str a) (metatrm_str m1) (metatrm_str m2)) ffpairs;
	  flush stdout;
	end;
      match frpairs with
      | ((gam,(m1,(e,x),sigma),(m2,h,htp,args2),a)::frpairs') ->
	  let r2 = ref r in
	  begin
	    if (b > 0) then
	      begin
		let b2 = b - (get_int_flag "HOUNIF1PROJECT") in
		if (!verbosity > 5) then begin Printf.printf "Looking up projs for %s\n" (string_of_evar (e,x)) end;
		List.iter
		  (fun (i,a2,argtps,basetp) ->
		    if (!verbosity > 5) then begin Printf.printf "About to project %d for %s\n" i (string_of_evar (e,x)) end;
		    let (g,zl) = project (Hashtbl.find evargamma e) (MGround(DB(i,a2))) a2 in
		    begin (*** Project i ***)
		      x := Some g;
		      r2 := hounif1db (List.append
					 zl
					 (List.filter (fun (d,y) -> not (d = e)) yl))
			  xsl
			  (pack_into_dpairs [(gam,m1,m2,a)] frpairs ffpairs) b2 (!r2) f;
		      if (!verbosity > 5) then begin Printf.printf "Resetting %s from project %d\n" (string_of_evar (e,x)) i end;
		      x := None (*** Reset x ***)
		    end
		      )
		  (Hashtbl.find evarprojs e);
		if (!verbosity > 5) then begin Printf.printf "Finished Projections for %s\n" (string_of_evar (e,x)) end;
		begin
		  match h with
		  | DB _ -> ()
		  | _ ->
		      let (g,zl,dpairs2) = imitate (Hashtbl.find evargamma e) gam sigma (MGround(h)) htp args2 in
		      begin (*** Imitate h ***)
			if (!verbosity > 5) then begin Printf.printf "About to imitate ?%d\n" e end;
			x := Some g;
			r2 := hounif1db (List.append
					   zl
					   (List.filter (fun (d,y) -> not (d = e)) yl))
			    xsl
			    (pack_into_dpairs dpairs2 frpairs' ffpairs)
			    (b - (get_int_flag "HOUNIF1IMITATE")) (!r2) f;
			if (!verbosity > 5) then begin Printf.printf "Resetting %s from imitate\n" (string_of_evar (e,x)) end;
			x := None (*** Reset x ***)
		      end
		end
	      end;
	    !r2
	  end
      | [] ->
	  begin
	    match ffpairs with
	    | (_::_) ->
		      (*** Only flex-flex remain ***)
		if (!verbosity > 5) then begin Printf.printf "only flex-flex remain b = %d\n" b end;
		      (*** Copy evars and flex-flex ***)
		let evarassoc = ref [] in
		let yl' = ref [] in
		List.iter
		  (fun (d,y) ->
		    match (!y) with
		    | Some _ -> ()
		    | None ->
			begin
			  let y' = copy_evar (!verbosity) y in
			  evarassoc := ((d,y')::(!evarassoc));
			  yl' := (y'::(!yl'))
			end)
		  yl;
		let xsl' = List.map (fun xs -> meta_copy xs (!evarassoc)) xsl in
		let ffpairs' = List.map (fun (gam,(m1,_,_),(m2,_,_),a) -> (gam,meta_copy (metanorm m1) (!evarassoc),meta_copy (metanorm m2) (!evarassoc),a)) ffpairs in
		(b,!yl',xsl',ffpairs')::r
	    | [] ->
		      (*** Completely solved - make the instantiations ***)
		if (!verbosity > 5) then begin Printf.printf "completely solved b = %d\n" b end;
		List.iter 
		  (fun n ->
		    try
		      let n' = norm emptyd (meta_to_ground_rec n []) in
		      if (!verbosity > 5) then begin Printf.printf "new inst %s\n" (trm_str n') end;
		      f (tpof n') n'
		    with NotGround -> ()
			)
		  xsl;
		List.iter (fun (d,y) ->
		  if (!verbosity > 5) then begin Printf.printf "Resetting %s from final force\n" (string_of_evar (d,y)) end;
		  y := None) yl;
		r
	  end
    end
  with
  | SimplElim((e,x),m,dpairs,frpairs,ffpairs) ->
      if (!verbosity > 5) then begin Printf.printf "Eliminating %s := %s\n" (string_of_evar (e,x)) (metatrm_str m) end;
      x := Some m;
      let r = hounif1db (List.filter (fun (d,y) -> not (d = e)) yl) xsl (pack_into_dpairs dpairs frpairs ffpairs) b r f in
      if (!verbosity > 5) then begin Printf.printf "Resetting %s from elim\n" (string_of_evar (e,x)) end;
      x := None;
      r (*** Reset x ***)
  | SimplFailed -> r

let rec union_evars xl yl =
  match xl with
  | (x::xr) ->
      begin
	try
	  ignore (List.find (fun x' -> x' == x) yl);
	  union_evars xr yl
	with
	  Not_found -> union_evars xr (x::yl)
      end
  | [] -> yl

let rec union_metatrms ml nl =
  match ml with
  | (m::mr) ->
      begin
	if (List.mem m nl) then
	  union_metatrms mr nl
	else
	  union_metatrms mr (m::nl)
      end
  | [] -> nl

let mate_dpairs : (int * cdpairs) list ref = ref [];;
let metaflexposatoms : (evar list * metatrm list * metatrm) list ref = ref [];;
let metaflexnegatoms : (evar list * metatrm list * metatrm) list ref = ref [];;
let metaposatoms : (evar list * metatrm list * metatrm) list ref = ref [];;
let metanegatoms : (evar list * metatrm list * metatrm) list ref = ref [];;

let rec process_cdpairs mm r f =
  List.iter
    (fun ((b,yl,xsl,dpairs) as cdpairs) ->
      List.iter
	(fun (mm',(b',yl',xsl',dpairs')) ->
	  if ((mm' > 0) && ((b - b') > 0)) then
	    begin
	      if (!verbosity > 5) then Printf.printf "process_cdpairs\n";
	      let r' = hounif1db (union_evars yl yl') (union_metatrms xsl xsl') (List.append dpairs dpairs') (b - b') [] f in
	      process_cdpairs (mm' - mm) r' f
	    end)
	!mate_dpairs;
      mate_dpairs := (mm,cdpairs)::!mate_dpairs)
    r

let mateatom yl xsl m p f =
  if (!verbosity > 2) then Printf.printf "mateatom %s m = %s\n" (if p then "+" else "-") (metatrm_str m);
  let mm = (get_int_flag "HOUNIF1MAXMATES") - 1 in
  let b = (get_int_flag "HOUNIF1BOUND") in
  List.iter
    (fun (yl2,xsl2,m2) -> 
     if (!verbosity > 2) then Printf.printf "mateatom against m2 = %s\n" (metatrm_str m2);
      let r = hounif1db (union_evars yl yl2) (union_metatrms xsl xsl2) [([],m,m2,Prop)] b [] f in
      process_cdpairs mm r f)
    (if p then (!metanegatoms) else (!metaposatoms));
  List.iter
    (fun (yl2,xsl2,m2) ->
      if (!verbosity > 2) then Printf.printf "mateatom against m2 = %s\n" (metatrm_str m2);
      let r = hounif1db (union_evars yl yl2) (union_metatrms xsl xsl2) [([],m2,m,Prop)] b [] f in
      process_cdpairs mm r f)
    (if p then (!metaflexnegatoms) else (!metaflexposatoms));
  let m' = metanormneg m in
  List.iter
    (fun (yl2,xsl2,m2) ->
      if (!verbosity > 2) then Printf.printf "mateatom against m2 = %s\n" (metatrm_str m2);
      let r = hounif1db (union_evars yl yl2) (union_metatrms xsl xsl2) [([],m2,m',Prop)] b [] f in
      process_cdpairs mm r f)
    (if p then (!metaflexposatoms) else (!metaflexnegatoms));
  if p then
    metaposatoms := (yl,xsl,m)::!metaposatoms
  else
    metanegatoms := (yl,xsl,m)::!metanegatoms

let mateflexatom yl xsl m p f =
  if (!verbosity > 2) then Printf.printf "mateflexatom %s m = %s\n" (if p then "+" else "-") (metatrm_str m);
  let mm = (get_int_flag "HOUNIF1MAXMATES") - 1 in
  let b = (get_int_flag "HOUNIF1BOUND") in
  List.iter
    (fun (yl2,xsl2,m2) ->
      if (!verbosity > 2) then Printf.printf "mateatom against m2 = %s\n" (metatrm_str m2);
      let r = hounif1db (union_evars yl yl2) (union_metatrms xsl xsl2) [([],m,m2,Prop)] b [] f in
      process_cdpairs mm r f)
    (if p then (!metanegatoms) else (!metaposatoms));
  List.iter
    (fun (yl2,xsl2,m2) ->
      if (!verbosity > 2) then Printf.printf "mateatom against m2 = %s\n" (metatrm_str m2);
      let r = hounif1db (union_evars yl yl2) (union_metatrms xsl xsl2) [([],m,m2,Prop)] b [] f in
      process_cdpairs mm r f)
    (if p then (!metaflexnegatoms) else (!metaflexposatoms));
  List.iter
    (fun (yl2,xsl2,m2) ->
      if (!verbosity > 2) then Printf.printf "mateatom against m2 = %s\n" (metatrm_str m2);
      let r = hounif1db (union_evars yl yl2) (union_metatrms xsl xsl2) [([],m,metanormneg m2,Prop)] b [] f in
      process_cdpairs mm r f)
    (if p then (!metaposatoms) else (!metanegatoms));
  List.iter
    (fun (yl2,xsl2,m2) ->
      if (!verbosity > 2) then Printf.printf "mateatom against m2 = %s\n" (metatrm_str m2);
      let r = hounif1db (union_evars yl yl2) (union_metatrms xsl xsl2) [([],m,metanormneg m2,Prop)] b [] f in
      process_cdpairs mm r f)
    (if p then (!metaflexposatoms) else (!metaflexnegatoms));
  if p then
    metaflexposatoms := (yl,xsl,m)::!metaflexposatoms
  else
    metaflexnegatoms := (yl,xsl,m)::!metaflexnegatoms

let hounif1d (v:int) (yl:evar list) (xsl:metatrm list) (dpairs:udpair list) (b:int) (f:stp -> trm -> unit) =
  verbosity := v;
  hounif1da yl xsl dpairs b f
	  
let rec hounif1a m xl xsl gam b p f =
  if (!verbosity > 5) then begin Printf.printf "hounif1 %s gam = %s m = %s\n" (if p then "+" else "-") (match gam with [] -> "[]" | _ -> "...") (metatrm_str m); flush stdout end;
  begin
    match m with
    | MAp(MAp(MGround(Imp),m1),MGround(False)) -> hounif1a m1 xl xsl gam b (not p) f
    | MAp(MAp(MGround(Imp),m1),m2) -> hounif1a m1 xl xsl gam b (not p) f; hounif1a m2 xl xsl gam b p f
    | MAp(MGround(Forall(a)),(MLam(_,m1))) when p && (match gam with [] -> true | _ -> false) ->
      begin
        let (x,xsub) = new_evar_w_default gam a (fun x -> x) in
        hounif1a (metanorm (metasubst m1 0 xsub)) (x::xl) (xsub::xsl) gam b p f
      end
    | MAp(MGround(Forall(a)),(MLam(_,m1))) -> hounif1a m1 xl xsl (a::gam) b p f
    | MAp(MAp(MGround(Eq(Ar(a1,a2))),m1),m2) when p && (match gam with [] -> true | _ -> false) -> (** rigid if negative or gam is nonempty **)
	begin
          let (x,xsub) = new_evar_w_default gam a1 (fun x -> x) in
	  hounif1a (metanorm (MAp(MAp(MGround(Eq(a2)),MAp(m1,xsub)),MAp(m2,xsub)))) (x::xl) (xsub::xsl) gam b p f
	end
    | MAp(MAp(MGround(Eq(Ar(a1,a2))),m1),m2) -> (** rigid if negative or gam is nonempty **)
	hounif1a (metanorm (MAp(MAp(MGround(Eq(a2)),MAp(metashift m1 0 1,MGround(DB(0,a1)))),MAp(metashift m2 0 1,MGround(DB(0,a1)))))) xl xsl (a1::gam) b p f
    | MAp(MAp(MGround(Eq(Prop)),m1),m2) when get_bool_flag "HOUNIF1MATEBELOWEQUIV" ->
	hounif1a m1 xl xsl gam b false f;
	hounif1a m2 xl xsl gam b false f;
	hounif1a m1 xl xsl gam b true f;
	hounif1a m2 xl xsl gam b true f;
    | MAp(MAp(MGround(Eq(a)),m1),m2) when not p ->
	begin
	  hounif1da xl xsl [(gam,m1,m2,a)] b f;
	  if (get_bool_flag "HOUNIF1MATE") then
	    begin
	    match gam with
	    | [] ->
		begin
		  mateatom xl xsl m p f;
		  mateatom xl xsl (MAp(MAp(MGround(Eq(a)),m2),m1)) p f (*** Symmetric Eqn ***)
		end
	    | _ -> ()
	    end
	end
    | MVar(x,sl) ->
	if (get_bool_flag "HOUNIF1MATE") then
	begin
	  match gam with
	  | [] -> mateflexatom xl xsl m p f
	  | _ -> ()
	end
    | _ ->
	begin
	  if (get_bool_flag "HOUNIF1MATE") then
	    match gam with
	    | [] -> mateatom xl xsl m p f
	    | _ -> ()
	end
  end;
  ()

let hounif1 v m xl xsl gam b p f =
  if (!verbosity > 2) then Printf.printf "hounif1 init with %s %s\n" (if p then "+" else "-") (metatrm_str m);
  verbosity := v;
  hounif1a m xl xsl gam b p f
