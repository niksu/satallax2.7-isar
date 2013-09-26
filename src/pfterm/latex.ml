open State
open String
open Syntax
open Refutation

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
  | Ap(Forall(a),m) ->  
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
 | Trans(h1,h2,s,r1) ->"\\begin{tabular}{c} \n " 
   								^"\\textcolor[rgb]{0, 0, 1}{$\\mathcal T _{Trans}$}   \\\\ \n"
								 ^ (trm_lat s) ^ " \\\\ \n"
   								^ ref_lat r1  ^" \\\\ \n"
   			^ "\\end{tabular} \n " 

 
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
 | KnownResult(s,name,al,r1) -> ref_lat r1 (*** Not mentioning Known results in the latex version. - Chad, August 2011 ***)

 | NYI(h,s,r1) ->"\\begin{tabular}{c} \n " 
   								^"\\textcolor[rgb]{1, 0,1}{"^ (trm_lat h) ^" $\\downarrow$} \\\\ \n"
								^ (trm_lat s) ^ " \\\\ \n"
   								^ ref_lat r1  ^" \\\\ \n"
   			^ "\\end{tabular} \n "  
 | Timeout -> "\\textcolor[rgb]{1, 0,0}{X}"
    
let rec ref_to_lat ts r = match ts with
  | [] -> ref_lat r
  | (t::tr) -> trm_lat t ^ " \\\\ \n" ^ ref_to_lat tr r     
 
