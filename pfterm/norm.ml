open Syntax
open State

(** Replaces all occurences of 'Neg' by 'implies False' **)
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

(** applies neg- and betanormalization**) 
let onlynegnorm m =  
  let (n,_) = negnorm1 m in onlybetanorm n 

(** applies neg-, beta- and delta-normalization**) 
let coqnorm m =
  let m = betanorm name_def_prenorm m in  
  let (n,_) = negnorm1 m in n 

(** applies full satallax normalization**)  
let normalize pt = norm name_def (logicnorm pt)  

