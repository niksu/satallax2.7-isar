open Flags
open State
open String
open Syntax
open Search
open Refutation
open Flag
open Suche
open Translation
open Latex
open Coq
open Branch

(** to String functions for debugging**)

(** Debug function: Alternative way to print terms **)
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
       
(** Statistic **)

(* statcount is an attempt to guess the size of the final refutation after timeout stopped the search *)
let statcount = ref (Hashtbl.create 100) 
let update_statcount h s w b =
if b then 
let (zs,zw,n) = try Hashtbl.find !statcount h with Not_found -> (0,0,0) in
Hashtbl.replace !statcount h (zs+s,zw+w,n+1)

(* statistic extract simple information from a refutation: size, depth, width, No. cuts, No. rewrites, No. NYIs, No. timeouts *)
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
 | Mating(_,_,_, rs) -> begin ( try ignore (List.hd rs) with Failure(_) -> failwith "Mating refutation list is empty" );
	let (s1,d1,w1,c1,re1,nyi1,t1) = List.fold_left (fun (s,d,w,c,re,nyi,t) r -> let (s',d',w',c',re',nyi',t') = statistic1 r (h+1) b in (s+s',max d' (d-1) +1,w+w',c+c',re+re',nyi+nyi',t+t')) (1,1,0,0,0,0,0) rs in
	let _ = update_statcount h s1 w1 b in	
	(s1,d1,w1,c1,re1,nyi1,t1)
	end
 | Decomposition(_,_,rs)-> begin ( try ignore (List.hd rs) with Failure(_) -> failwith"Decomposition refutation list is empty"  );
	let (s1,d1,w1,c1,re1,nyi1,t1) = List.fold_left (fun (s,d,w,c,re,nyi,t) r -> let (s',d',w',c',re',nyi',t') = statistic1 r (h+1) b in (s+s',max d' (d-1) +1,w+w',c+c',re+re',nyi+nyi',t+t')) (1,1,0,0,0,0,0) rs in
	let _ = update_statcount h s1 w1 b in	
	(s1,d1,w1,c1,re1,nyi1,t1)
	end
 | Confront(_,_,_,_,_,_,r1,r2) ->
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let (s2,d2,w2,c2,re2,nyi2,t2) = statistic1 r2 (h+1) b in
	let _ = update_statcount h (s1+s2+1) (w1+w2) b in
	(1+s1+s2,max d1 d2 +1,w1+w2,c1+c2,re1+re2,nyi1+nyi2,t1+t2)
 | Trans(_,_,_,r1) ->
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let _ = update_statcount h (s1+1) (w1) b in
	(1+s1,d1 +1,w1,c1,re1,nyi1,t1)
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
 | KnownResult(_,name,al,r1) ->
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
(* | _ -> failwith "unknown refutation case in statistic" *)
in 
let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r 0 true in
let (s2,_,w2,_,_,_,_) = statistic1 r 0 false in
(s1,s2,d1,w1,w2,c1,re1,nyi1,t1)

(** MAIN **)
let tstp : bool ref = ref false;;

let print_coq_proofscript c r =
  
  if (!verbosity > vold) then Printf.printf  "starting print_coq_proofscript.\n";
  if (!verbosity > vold) then print_refut r;

	(*** Search ***)

  (* get assumptions *)
  let initbranch1 = (List.rev !initial_branch) in
  let initbranch = (List.map preprocess initbranch1) in (*** Chad, Aug 2011: Preprocess to handle LEIBEQ_TO_PRIMEQ here as well as in suche.ml. Example: SYO348^5.p ***)
  let b =List.map get_literal initbranch in
  (* call search *)
  let (refutation,con,searchTime,isTimeout) = search_refutation b r in
  (* check wether the dependency of the returned refutation is a subset of the assumptions - fail indicates some bug*)
  if assert_condition && not (Dependency.is_empty (Dependency.diffunion [] [con] [b]) ) then 
    (if (!verbosity > 0) then Printf.printf  "Error with refutation: Still open conditions  \n") ;	 
  let (size,_,depth,width,_,cut,rewrite,notyetImpl,timeouts) = statistic refutation in
  (* if timeout was reached the refutation is unfinished - at least output some information about the completed part*)
	if isTimeout  || timeouts > 0 then  
  	  (if (!verbosity > 0) then Printf.printf  "Timeout!  time %d ms size %d depth %d width %d cuts %d rewrite %d NYI %d timeouts %d \n" searchTime size depth width cut rewrite notyetImpl timeouts)
  	else 	
  begin
    if result_print_search then Printf.printf  "%s\n" (ref_str refutation);
    if (!verbosity > 3) then Printf.printf "Search time %d ms size %d depth %d width %d \n" searchTime size depth width ;

	(*** Translation  ***)

(* get prenormalized assumptions *)
  let initbranch_prenorm = List.map 
	(fun pn ->let p= onlynegnorm pn in  if debug_translation then Printf.printf  "%s = %s \n" (trm_str pn) (trm_str p) ;p ) 
	(List.rev !initial_branch_prenorm) in
  let beforeTrans= Sys.time() in
(* Branch is an association list from normalized terms to their prenormalized counterparts *)
  let branch = (List.combine initbranch  initbranch_prenorm) in
  if debug_translation then (Printf.printf "About to translate. Branch assoc with prenorm:\n"; List.iter (fun (m,p) -> Printf.printf "trm: %s\npre: %s\n" (trm_str m) (trm_str p)) branch);
(* The flag pftrm_eager_rewrite decides wether rewrites are eagerly or lazily handled *) 
  let prenorm_refutation =
    begin
      try
	if pftrm_eager_rewrite then
	  eager_translate branch refutation
	else
	  lazy_translate branch refutation
      with TranslateFailure -> safe_translate branch refutation (*** Chad Aug 2011 : Fall back on safe_translate ***)
    end
  in
  if debug_translation then (Printf.printf "Translated prenorm_refutation\n%s\n" (ref_str prenorm_refutation));
  let transTime= int_of_float ((Sys.time() -. beforeTrans) *. 1000.0) in
  begin
  let (size,_,depth,width,_,cut,rewrite,notyetImpl,_) = statistic prenorm_refutation  in
  if result_print_translation then Printf.printf  "%s\n" (ref_str prenorm_refutation);
  if (!verbosity > 3) then Printf.printf  "Translation NYI %d time %d ms size %d depth %d width %d cuts %d rewrite %d  \n" notyetImpl transTime size depth width cut rewrite  ;

	(*** Output Coq ***)

  let beforeCoq= Sys.time() in
  if (!tstp) then (*** output in tstp format ***)
    begin
      ref_tstp c prenorm_refutation
    end
  else
    begin
      if result_coq then
        if size < maxcoqproofsize then
          ref_coq c prenorm_refutation
        else raise (CoqProofTooBig size)
      else if result_isabellehol then
        if size < max_isabellehol_proofsize then
          ref_isabellehol c prenorm_refutation
        else raise (CoqProofTooBig size) (*FIXME replace with IsabelleHOLProofTooBig*)
    end;
  let coqTime= int_of_float ((Sys.time() -. beforeCoq) *. 1000.0) in
  if (result_coq ) then if (!verbosity > 3) then Printf.printf  "Coq output done: time %d  \n" coqTime ;
	(*** Output Latex Search ***)

  if (result_latex && width < 50 && depth < 30) then
  Printf.fprintf c "(*** \n %%beginLatex \n size %d depth %d width %d \n \n \\begin{tabular}{c} \n %s \\end{tabular} \n\n %%endLatex \n ***)\n" 
  size depth width (ref_to_lat initbranch refutation)
  else if (result_latex) then Printf.fprintf c "(*** \n %%beginLatex \n size %d depth %d width %d \n \n  %%endLatex \n ***)\n" size depth width;
 
	(*** Output Latex Translation ***)

  if (result_latex &&  width < 50 && depth < 30) then
  Printf.fprintf c "(*** \n %%beginLatex \n size %d depth %d width %d cuts %d rewrite  %d NYI %d \n \n \\begin{tabular}{c} \n %s \\end{tabular} \n\n %%endLatex \n***)" 
  size depth width cut rewrite notyetImpl  (ref_to_lat initbranch_prenorm prenorm_refutation)
  else if (result_latex) then Printf.fprintf c "(*** \n %%beginLatex \n \n \n Translation successful, probably \n \n size %d depth %d width %d cuts %d rewrite %d  NYI %d \n %%endLatex \n***)" size depth width cut rewrite notyetImpl 
  ; flush stdout
  end
  end		

let print_coq_sproofterm c r =
  
  if (!verbosity > vold) then Printf.printf "starting print_coq_proofspfterm.\n";
  if (!verbosity > vold) then print_refut r;

	(*** Search ***)

  (* get assumptions *)
  let initbranch1 = (List.rev !initial_branch) in
  let initbranch = (List.map preprocess initbranch1) in (*** Chad, Aug 2011: Preprocess to handle LEIBEQ_TO_PRIMEQ here as well as in suche.ml. Example: SYO348^5.p ***)
  let b =List.map get_literal initbranch in
  (* call search *)
  let (refutation,con,searchTime,isTimeout) = search_refutation b r in
  (* check wether the dependency of the returned refutation is a subset of the assumptions - fail indicates some bug*)
  if assert_condition && not (Dependency.is_empty (Dependency.diffunion [] [con] [b]) ) then 
    (if (!verbosity > 0) then Printf.printf  "Error with refutation: Still open conditions  \n") ;	 
  let (size,_,depth,width,_,cut,rewrite,notyetImpl,timeouts) = statistic refutation in
  (* if timeout was reached the refutation is unfinished - at least output some information about the completed part*)
	if isTimeout  || timeouts > 0 then  
  	  (if (!verbosity > 0) then Printf.printf  "Timeout!  time %d ms size %d depth %d width %d cuts %d rewrite %d NYI %d timeouts %d \n" searchTime size depth width cut rewrite notyetImpl timeouts)
  	else 	
  begin
    if result_print_search then Printf.printf  "%s\n" (ref_str refutation);
    if (!verbosity > 3) then Printf.printf "Search time %d ms size %d depth %d width %d \n" searchTime size depth width ;

	(*** Translation  ***)

(* get prenormalized assumptions *)
  let initbranch_prenorm = List.map 
	(fun pn ->let p= onlynegnorm pn in  if debug_translation then Printf.printf  "%s = %s \n" (trm_str pn) (trm_str p) ;p ) 
	(List.rev !initial_branch_prenorm) in
  let beforeTrans= Sys.time() in
(* Branch is an association list from normalized terms to their prenormalized counterparts *)
  let branch = (List.combine initbranch  initbranch_prenorm) in
  if debug_translation then (Printf.printf "About to translate. Branch assoc with prenorm:\n"; List.iter (fun (m,p) -> Printf.printf "trm: %s\npre: %s\n" (trm_str m) (trm_str p)) branch);
(* The flag pftrm_eager_rewrite decides wether rewrites are eagerly or lazily handled *) 
  let prenorm_refutation =
    begin
      try
	if pftrm_eager_rewrite then
	  eager_translate branch refutation
	else
	  lazy_translate branch refutation
      with TranslateFailure -> safe_translate branch refutation (*** Chad Aug 2011 : Fall back on safe_translate ***)
    end
  in
  if debug_translation then (Printf.printf "Translated prenorm_refutation\n%s\n" (ref_str prenorm_refutation));
  let transTime= int_of_float ((Sys.time() -. beforeTrans) *. 1000.0) in
  begin
  let (size,_,depth,width,_,cut,rewrite,notyetImpl,_) = statistic prenorm_refutation  in
  if result_print_translation then Printf.printf  "%s\n" (ref_str prenorm_refutation);
  if (!verbosity > 3) then Printf.printf  "Translation NYI %d time %d ms size %d depth %d width %d cuts %d rewrite %d  \n" notyetImpl transTime size depth width cut rewrite  ;

	(*** Output Coq ***)

  let beforeCoq= Sys.time() in
  if (result_coq && size < maxcoqproofsize ) then ref_coq_spfterm c prenorm_refutation else raise (CoqProofTooBig size);
  let coqTime= int_of_float ((Sys.time() -. beforeCoq) *. 1000.0) in
  if (result_coq ) then if (!verbosity > 3) then Printf.printf  "Coq output done: time %d  \n" coqTime ;
	(*** Output Latex Search ***)

  if (result_latex && width < 50 && depth < 30) then
  Printf.fprintf c "(*** \n %%beginLatex \n size %d depth %d width %d \n \n \\begin{tabular}{c} \n %s \\end{tabular} \n\n %%endLatex \n ***)\n" 
  size depth width (ref_to_lat initbranch refutation)
  else if (result_latex) then Printf.fprintf c "(*** \n %%beginLatex \n size %d depth %d width %d \n \n  %%endLatex \n ***)\n" size depth width;
 
	(*** Output Latex Translation ***)

  if (result_latex &&  width < 50 && depth < 30) then
  Printf.fprintf c "(*** \n %%beginLatex \n size %d depth %d width %d cuts %d rewrite  %d NYI %d \n \n \\begin{tabular}{c} \n %s \\end{tabular} \n\n %%endLatex \n***)" 
  size depth width cut rewrite notyetImpl  (ref_to_lat initbranch_prenorm prenorm_refutation)
  else if (result_latex) then Printf.fprintf c "(*** \n %%beginLatex \n \n \n Translation successful, probably \n \n size %d depth %d width %d cuts %d rewrite %d  NYI %d \n %%endLatex \n***)" size depth width cut rewrite notyetImpl 
  ; flush stdout
  end
  end		
  
(*** Chad, August 2011: Added this way of printing proof information at the request of Jasmin Blanchette. ***)
let print_hocore c r =
  let don : (string,unit) Hashtbl.t = Hashtbl.create 1000 in
  let report_name name =
    if (not (Hashtbl.mem don name)) then
      begin
	Printf.fprintf c "%s\n" name;
	Hashtbl.add don name ()
      end
  in
  let rec hocore_1 c r a =
    if (!verbosity > 50) then
      begin
	Printf.printf "hocore_1 r\n";
	print_refut r;
	Printf.printf "hocore_1 a BEGIN\n";
	List.iter (fun (m,n) -> Printf.printf "%s : %s\n" n (trm_str m)) a;
	Printf.printf "hocore_1 a END\n";
      end;
    match r with
    | SearchR(cl,cr) ->
	List.iter
	  (fun c0 ->
	    try
	      if (!verbosity > 50) then
		begin
		  Printf.printf "Calling cr on clause ";
		  List.iter (fun i -> Printf.printf "%d\n" i) c0;
		  Printf.printf "\n";
		end;
	      match (cr c0) with
	      |	ChoiceRule(Name(eps,_),p) ->
		  begin
		    if (!verbosity > 50) then Printf.printf "cr found it's a choice rule\n";
		    try
		      let (_,choiceax) = Hashtbl.find choiceopnames eps in
		      let name = List.assoc choiceax a in
		      report_name name
		    with
		      Not_found -> ()
		  end
	      |	ri ->
		  begin
		    if (!verbosity > 50) then Printf.printf "cr found it has rule info %s\n" (ruleinfo_str ri);
		  end
	    with (** Assumptions have no associated rule info **)
	      Not_found ->
		begin
		  if (!verbosity > 50) then Printf.printf "cr found no rule info\n";
		  match c0 with
		  | [l] ->
		      begin
			let tm = literal_to_trm l in
			try
			  report_name (List.assoc tm a)
			with Not_found -> ()
		      end
		  | _ -> raise (GenericError "Non-Unit Assumption") (*** Unexpected case: Non-unit Assumption ***)
		end)
	  cl
    | AssumptionConflictR -> (*** There must be a formula (m,name) on a such that (~m,name2) is on a. Otherwise, there's a bug. ***)
	let rec find_conflict a =
	  match a with
	  | (((Ap(Ap(Imp,m),False)),name)::ar) ->
	      begin
		try
		  report_name (List.assoc m ar);
		  report_name name
		with
		| Not_found -> find_conflict ar
	      end
	  | ((m,name)::ar) ->
	      let nm = Ap(Ap(Imp,m),False) in
	      begin
		try
		  report_name (List.assoc nm ar);
		  report_name name
		with
		| Not_found -> find_conflict ar
	      end
	  | [] -> raise (GenericError "Assumption Conflict Not Found")
	in
	find_conflict a
    | FalseR ->
	begin
	  try
	    report_name (List.assoc False a)
	  with Not_found -> raise (GenericError "Assumption 'False' Not Found")
	end
    | NegReflR ->
	let rec find_conflict a =
	  match a with
	  | (((Ap(Ap(Imp,Ap(Ap(Eq(_),m),n)),False)),name)::_) when (m = n) -> report_name name
	  | (_::ar) -> find_conflict ar
	  | [] -> raise (GenericError "Assumption of Negated Reflexive Equation Not Found")
	in
	find_conflict a
	  (*** Otherwise, follow the refutation, adding things to the assoc list a as we break down the formulas. ***)
    | NegImpR(m,n,r) ->
	begin
	  try
	    let name = List.assoc (neg (imp m n)) a in
	    hocore_1 c r ((m,name)::(normneg n,name)::a)
	  with Not_found -> raise (GenericError ("Unknown Assumption " ^ (trm_str (neg (imp m n)))))
	end
    | ImpR(m,n,r1,r2) ->
	begin
	  try
	    let name = List.assoc (imp m n) a in
	    hocore_1 c r1 ((normneg m,name)::a);
	    hocore_1 c r2 ((n,name)::a)
	  with Not_found -> raise (GenericError ("Unknown Assumption " ^ (trm_str (imp m n))))
	end
    | NegAllR(b,m,x,r) -> 
	begin
	  try
	    let name = List.assoc (neg (Ap(Forall(b),m))) a in
	    hocore_1 c r (((norm name_def (neg (Ap(m,Name(x,b))))),name)::a)
	  with Not_found -> raise (GenericError ("Unknown Assumption " ^ (trm_str (neg (Ap(Forall(b),m))))))
	end
    | EqFR(a1,a2,m,n,r) ->  (*** This doesn't appear to be used at the moment. - Chad, Aug 2011 ***)
	begin
	  try
	    let name = List.assoc (Ap(Ap(Eq(Ar(a1,a2)),m),n)) a in
	    hocore_1 c r (((norm name_def (forall a1 (eq a2 (Ap(m,DB(0,a1))) (Ap(n,DB(0,a1)))))),name)::a)
	  with Not_found -> raise (GenericError ("Unknown Assumption " ^ (trm_str (Ap(Ap(Eq(Ar(a1,a2)),m),n)))))
	end
    | NegEqFR(a1,a2,m,n,r) -> 
	begin
	  try
	    let name = List.assoc (neg (Ap(Ap(Eq(Ar(a1,a2)),m),n))) a in
	    hocore_1 c r (((norm name_def (normneg (forall a1 (eq a2 (Ap(m,DB(0,a1))) (Ap(n,DB(0,a1))))))),name)::a)
	  with Not_found -> raise (GenericError ("Unknown Assumption " ^ (trm_str (neg (Ap(Ap(Eq(Ar(a1,a2)),m),n))))))
	end
    | EqOR(m,n,r1,r2) -> 
	begin
	  try
	    let name = List.assoc (eq Prop m n) a in
	    hocore_1 c r1 ((m,name)::(normneg n,name)::a);
	    hocore_1 c r2 ((normneg m,name)::(n,name)::a)
	  with Not_found -> raise (GenericError ("Unknown Assumption " ^ (trm_str (eq Prop m n))))
	end
    | NegEqOR(m,n,r1,r2) -> 
	begin
	  try
	    let name = List.assoc (neg (eq Prop m n)) a in
	    hocore_1 c r1 ((m,name)::(normneg n,name)::a);
	    hocore_1 c r2 ((normneg m,name)::(n,name)::a)
	  with Not_found -> raise (GenericError ("Unknown Assumption " ^ (trm_str (neg (eq Prop m n)))))
	end
  in
  let a = Hashtbl.fold (fun k v l -> (v,k)::l) name_hyp []
  in
  hocore_1 c r
    begin
      match !conjecture with
      | Some (_,_,ntmn) ->
	  if (!verbosity > 20) then Printf.printf "neg conj name %s %s\n" !conjecturename (trm_str ntmn);
	  ((ntmn,!conjecturename)::a)
      | _ -> a
    end

(*** Chad - July 2012 - output proof script in tstp format. ***)
let print_tstp c r =
  tstp := true;
  print_coq_proofscript c r

