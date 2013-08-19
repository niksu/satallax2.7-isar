(*** File: priorityqueue.ml ***)
(*** Author: Chad E Brown, Oct 2010 ***)
(*** Priority Queue Implementation ***)

(*** Multiple Implementations, Jan 2011 ***)
(*** Version 0: Balanced binary tree with same priorities treated as stacks (implemented as lists on the node of the priority). Fairness ensured with an offset incremented every 1024 inserts. ***)
module PriorityQueue0 = functor (T : sig type t end) ->
  struct
    type a = T.t
    let pqueue_offset = ref 0

	(*** Binary Tree: Node(p,xl,m,lft,rght)
	     -- p is priority (tree is ordered wrt p)
	     -- xl is list of data with priority p
	     -- m is size of tree (sum of length of xl and sizes of children)
	     -- lft and rght are the two children
	 ***)
    type tree = Node of (int * T.t list * int * tree * tree) | Leaf

    let size n =
      match n with
      | Node(_,_,m,_,_) -> m
      | Leaf -> 0

    let rec lbalance (p,xl,m,l,n7) =
      match l with
      | Node(p4,xl4,m4,((Node(p2,xl2,m2,n1,n3)) as n2),n5) when m4 > (size n7) ->
	  let m6' = m + (size n5) - m4 in
	  Node(p4,xl4,m,n2,Node(p,xl,m6',n5,n7))
      | Node(p2,xl2,m2,n1,Node(p4,xl4,m4,n3,n5)) when m2 > (size n7) ->
	  let m2' = m2 + (size n3) - m4 in
	  let m6' = m + (size n5) - m2 in
	  Node(p4,xl4,m,Node(p2,xl2,m2',n1,n3),Node(p,xl,m6',n5,n7))
      | _ -> Node(p,xl,m,l,n7)

    let rec rbalance (p,xl,m,n1,r) =
      match r with
      | Node(p6,xl6,m6,Node(p4,xl4,m4,n3,n5),n7) when (size n1) < m6 ->
	  let m3 = size n3 in
	  let m5 = size n5 in
	  let m2' = m + m3 - m6 in
	  let m6' = m6 + m5 - m4 in
	  Node(p4,xl4,m,Node(p,xl,m2',n1,n3),Node(p6,xl6,m6',n5,n7))
      | Node(p4,xl4,m4,n3,((Node(p6,xl6,m6,n5,n7)) as n6)) when (size n1) < m4 ->
	  let m3 = size n3 in
	  let m2' = m + m3 - m4 in
	  Node(p4,xl4,m,Node(p,xl,m2',n1,n3),n6)
      | _ -> Node(p,xl,m,n1,r)

    let rec insertNode px x n =
      match n with
      | Node(p,xl,m,l,r) ->
	  if (p = px) then
	    Node(p,(x::xl),m+1,l,r)
	  else if (px < p) then
	    lbalance(p,xl,m+1,insertNode px x l,r)
	  else
	    rbalance(p,xl,m+1,l,insertNode px x r)
      | Leaf -> Node(px,[x],1,Leaf,Leaf)

    let rec popFirst n =
      match n with
      | Node(_,(x::[]),_,Leaf,r) ->
	  (x,r)
      | Node(p,(x::xl),m,Leaf,r) ->
	  (x,Node(p,xl,m-1,Leaf,r))
      | Node(p,xl,m,l,r) ->
	  let (x,l') = popFirst l in
	  (x,rbalance(p,xl,m-1,l',r))
      | Leaf -> raise Not_found

    let rec peekFirst n =
      match n with
      | Node(p,(x::_),_,Leaf,_) -> (p,x)
      | Node(_,_,_,l,_) -> peekFirst l
      | Leaf -> raise Not_found

    let pqueue : tree ref = ref Leaf
    let reset () = pqueue := Leaf
    let insertWithPriority p o =
      let p' = p + ((!pqueue_offset) asr 9) in (*** The offset is just for fairness, and should have minimal effect otherwise.  asr 10 is bitshift by 10, i.e., division by 1024 ***)
      begin
	incr pqueue_offset;
	pqueue := insertNode p' o (!pqueue)
      end
    let getNext () = let (x,n) = popFirst (!pqueue) in pqueue := n; x
    let peekAtNext () = peekFirst (!pqueue)

	(*** Just for debugging ***)
    let rec debug_print_rec f n =
      match n with
      | Node(p,xl,m,lft,rght) ->
	  begin
	    Printf.printf "Node with priority %d, size %d.\n" p m;
	    List.iter (fun x -> Printf.printf "> %s\n" (f x)) xl;
	    Printf.printf "Left of %d.\n" p;
	    debug_print_rec f lft;
	    Printf.printf "Right of %d.\n" p;
	    debug_print_rec f rght
	  end
      | Leaf -> Printf.printf "Leaf.\n"

    let debug_print f = Printf.printf "-----BEGIN-----\n"; debug_print_rec f (!pqueue); Printf.printf "-----END-----\n"
  end

(*** Version 1: Balanced binary tree with same priorities treated as queues (implemented by only having a single option in each node). Fairness ensured with an offset incremented every 1024 inserts. ***)
module PriorityQueue1 = functor (T : sig type t end) ->
  struct
    type a = T.t
    let pqueue_offset = ref 0

	(*** Binary Tree: Node(p,x,m,lft,rght)
	     -- p is priority (tree is ordered wrt p)
	     -- x is an entry with priority p
	     -- m is size of tree (sum of length of xl and sizes of children)
	     -- lft and rght are the two children
	 ***)
    type tree = Node of (int * T.t * int * tree * tree) | Leaf

    let size n =
      match n with
      | Node(_,_,m,_,_) -> m
      | Leaf -> 0

    let rec lbalance (p,x,m,l,n7) =
      match l with
      | Node(p4,x4,m4,((Node(p2,x2,m2,n1,n3)) as n2),n5) when m4 > (size n7) ->
	  let m6' = m + (size n5) - m4 in
	  Node(p4,x4,m,n2,Node(p,x,m6',n5,n7))
      | Node(p2,x2,m2,n1,Node(p4,x4,m4,n3,n5)) when m2 > (size n7) ->
	  let m2' = m2 + (size n3) - m4 in
	  let m6' = m + (size n5) - m2 in
	  Node(p4,x4,m,Node(p2,x2,m2',n1,n3),Node(p,x,m6',n5,n7))
      | _ -> Node(p,x,m,l,n7)

    let rec rbalance (p,x,m,n1,r) =
      match r with
      | Node(p6,x6,m6,Node(p4,x4,m4,n3,n5),n7) when (size n1) < m6 ->
	  let m3 = size n3 in
	  let m5 = size n5 in
	  let m2' = m + m3 - m6 in
	  let m6' = m6 + m5 - m4 in
	  Node(p4,x4,m,Node(p,x,m2',n1,n3),Node(p6,x6,m6',n5,n7))
      | Node(p4,x4,m4,n3,((Node(p6,x6,m6,n5,n7)) as n6)) when (size n1) < m4 ->
	  let m3 = size n3 in
	  let m2' = m + m3 - m4 in
	  Node(p4,x4,m,Node(p,x,m2',n1,n3),n6)
      | _ -> Node(p,x,m,n1,r)

    let rec insertNode px x n =
      match n with
      | Node(p,y,m,l,r) ->
	  if (px < p) then
	    lbalance(p,y,m+1,insertNode px x l,r)
	  else (*** insert on the right if >= ***)
	    rbalance(p,y,m+1,l,insertNode px x r)
      | Leaf -> Node(px,x,1,Leaf,Leaf)

    let rec popFirst n =
      match n with
      | Node(_,x,_,Leaf,r) ->
	  (x,r)
      | Node(p,y,m,l,r) ->
	  let (x,l') = popFirst l in
	  (x,rbalance(p,y,m-1,l',r))
      | Leaf -> raise Not_found

    let rec peekFirst n =
      match n with
      | Node(p,x,_,Leaf,_) -> (p,x)
      | Node(_,_,_,l,_) -> peekFirst l
      | Leaf -> raise Not_found

    let pqueue : tree ref = ref Leaf
    let reset () = pqueue := Leaf
    let insertWithPriority p o =
      let p' = p + ((!pqueue_offset) asr 10) in (*** The offset is just for fairness, and should have minimal effect otherwise.  asr 10 is bitshift by 10, i.e., division by 1024 ***)
      begin
	incr pqueue_offset;
	pqueue := insertNode p' o (!pqueue)
      end
    let getNext () = let (x,n) = popFirst (!pqueue) in pqueue := n; x
    let peekAtNext () = peekFirst (!pqueue)

	(*** Just for debugging ***)
    let rec debug_print_rec f n =
      match n with
      | Node(p,x,m,lft,rght) ->
	  begin
	    Printf.printf "Node with priority %d, size %d.\n" p m;
	    Printf.printf "> %s\n" (f x);
	    Printf.printf "Left of %d.\n" p;
	    debug_print_rec f lft;
	    Printf.printf "Right of %d.\n" p;
	    debug_print_rec f rght
	  end
      | Leaf -> Printf.printf "Leaf.\n"

    let debug_print f = Printf.printf "-----BEGIN-----\n"; debug_print_rec f (!pqueue); Printf.printf "-----END-----\n"
  end

(*** Version 2: Balanced binary tree with same priorities treated as stacks (implemented as lists on the node of the priority). Fairness ensured with counters modulo 4 at each priority. ***)
module PriorityQueue2 = functor (T : sig type t end) ->
  struct
    type a = T.t
    let modulus = 4
    let h : (int,int) Hashtbl.t = Hashtbl.create 10

    let check_priority_ctr p =
      begin
	let c =
	  try
	    Hashtbl.find h p
	  with
	  | Not_found -> 0
	in
	if (c = modulus) then raise Not_found
      end

    let incr_priority_ctr p =
      begin
	try
	  let c = ((Hashtbl.find h p) + 1) mod modulus in
	  Hashtbl.replace h p c;
	  if (c = 0) then raise Not_found
	with
	| Not_found -> Hashtbl.add h p 1
      end

	(*** Binary Tree: Node(p,xl,m,lft,rght)
	     -- p is priority (tree is ordered wrt p)
	     -- xl is list of data with priority p
	     -- m is size of tree (sum of length of xl and sizes of children)
	     -- lft and rght are the two children
	 ***)
    type tree = Node of (int * T.t list * int * tree * tree) | Leaf

    let size n =
      match n with
      | Node(_,_,m,_,_) -> m
      | Leaf -> 0

    let rec lbalance (p,xl,m,l,n7) =
      match l with
      | Node(p4,xl4,m4,((Node(p2,xl2,m2,n1,n3)) as n2),n5) when m4 > (size n7) ->
	  let m6' = m + (size n5) - m4 in
	  Node(p4,xl4,m,n2,Node(p,xl,m6',n5,n7))
      | Node(p2,xl2,m2,n1,Node(p4,xl4,m4,n3,n5)) when m2 > (size n7) ->
	  let m2' = m2 + (size n3) - m4 in
	  let m6' = m + (size n5) - m2 in
	  Node(p4,xl4,m,Node(p2,xl2,m2',n1,n3),Node(p,xl,m6',n5,n7))
      | _ -> Node(p,xl,m,l,n7)

    let rec rbalance (p,xl,m,n1,r) =
      match r with
      | Node(p6,xl6,m6,Node(p4,xl4,m4,n3,n5),n7) when (size n1) < m6 ->
	  let m3 = size n3 in
	  let m5 = size n5 in
	  let m2' = m + m3 - m6 in
	  let m6' = m6 + m5 - m4 in
	  Node(p4,xl4,m,Node(p,xl,m2',n1,n3),Node(p6,xl6,m6',n5,n7))
      | Node(p4,xl4,m4,n3,((Node(p6,xl6,m6,n5,n7)) as n6)) when (size n1) < m4 ->
	  let m3 = size n3 in
	  let m2' = m + m3 - m4 in
	  Node(p4,xl4,m,Node(p,xl,m2',n1,n3),n6)
      | _ -> Node(p,xl,m,n1,r)

    let rec insertNode px x n =
      match n with
      | Node(p,xl,m,l,r) ->
	  if (p = px) then
	    Node(p,(x::xl),m+1,l,r)
	  else if (px < p) then
	    lbalance(p,xl,m+1,insertNode px x l,r)
	  else
	    rbalance(p,xl,m+1,l,insertNode px x r)
      | Leaf -> Node(px,[x],1,Leaf,Leaf)

    let rec popFirst n =
      match n with
      | Node(p,xl,m,l,r) ->
	  begin
	    try
	      let (x,l') = popFirst l in
	      (x,rbalance(p,xl,m-1,l',r))
	    with
	    | Not_found ->
		begin
		  match xl with
		  | (y::yl) ->
		      begin
			incr_priority_ctr p;
			match yl with
			| (_::_) -> (y,Node(p,yl,m-1,l,r))
			| [] -> (y,Leaf)
		      end
		  | [] -> raise Not_found
		end
	  end
      | Leaf -> raise Not_found

    let rec peekFirst n =
      match n with
      | Node(p,xl,m,l,r) ->
	  begin
	    try
	      peekFirst l
	    with
	    | Not_found ->
		begin
		  match xl with
		  | (y::yl) ->
		      begin
			check_priority_ctr p;
			(p,y)
		      end
		  | [] -> raise Not_found
		end
	  end
      | Leaf -> raise Not_found		

    let pqueue : tree ref = ref Leaf
    let reset () = pqueue := Leaf
    let insertWithPriority p o =
      begin
	pqueue := insertNode p o (!pqueue)
      end
    let getNext () = let (x,n) = popFirst (!pqueue) in pqueue := n; x (*** Hmm. What if every counter is 0? - could raise Not_found ***)
    let peekAtNext () = peekFirst (!pqueue) (*** Hmm. What if every counter is 0? - could raise Not_found ***)

	(*** Just for debugging ***)
    let rec debug_print_rec f n =
      match n with
      | Node(p,xl,m,lft,rght) ->
	  begin
	    Printf.printf "Node with priority %d [%d], size %d.\n" p (try Hashtbl.find h p with | Not_found -> 0) m;
	    List.iter (fun x -> Printf.printf "> %s\n" (f x)) xl;
	    Printf.printf "Left of %d.\n" p;
	    debug_print_rec f lft;
	    Printf.printf "Right of %d.\n" p;
	    debug_print_rec f rght
	  end
      | Leaf -> Printf.printf "Leaf.\n"

    let debug_print f = Printf.printf "-----BEGIN-----\n"; debug_print_rec f (!pqueue); Printf.printf "-----END-----\n"
  end

(*** Version 3: Balanced binary tree with same priorities 
alternating between being treated as stacks and queues (implemented as lists on the node of the priority).
Fairness ensured with an offset incremented every 1024 inserts. ***)
module PriorityQueue3 = functor (T : sig type t end) ->
  struct
    type a = T.t
    let pqueue_offset = ref 0

	(*** Binary Tree: Node(p,xl,m,lft,rght)
	     -- p is priority (tree is ordered wrt p)
	     -- xl is list of data with priority p
	     -- m is size of tree (sum of length of xl and sizes of children)
	     -- lft and rght are the two children
	 ***)
    type tree = Node of (int * T.t list * int * tree * tree) | Leaf

    let size n =
      match n with
      | Node(_,_,m,_,_) -> m
      | Leaf -> 0

    let rec lbalance (p,xl,m,l,n7) =
      match l with
      | Node(p4,xl4,m4,((Node(p2,xl2,m2,n1,n3)) as n2),n5) when m4 > (size n7) ->
	  let m6' = m + (size n5) - m4 in
	  Node(p4,xl4,m,n2,Node(p,xl,m6',n5,n7))
      | Node(p2,xl2,m2,n1,Node(p4,xl4,m4,n3,n5)) when m2 > (size n7) ->
	  let m2' = m2 + (size n3) - m4 in
	  let m6' = m + (size n5) - m2 in
	  Node(p4,xl4,m,Node(p2,xl2,m2',n1,n3),Node(p,xl,m6',n5,n7))
      | _ -> Node(p,xl,m,l,n7)

    let rec rbalance (p,xl,m,n1,r) =
      match r with
      | Node(p6,xl6,m6,Node(p4,xl4,m4,n3,n5),n7) when (size n1) < m6 ->
	  let m3 = size n3 in
	  let m5 = size n5 in
	  let m2' = m + m3 - m6 in
	  let m6' = m6 + m5 - m4 in
	  Node(p4,xl4,m,Node(p,xl,m2',n1,n3),Node(p6,xl6,m6',n5,n7))
      | Node(p4,xl4,m4,n3,((Node(p6,xl6,m6,n5,n7)) as n6)) when (size n1) < m4 ->
	  let m3 = size n3 in
	  let m2' = m + m3 - m4 in
	  Node(p4,xl4,m,Node(p,xl,m2',n1,n3),n6)
      | _ -> Node(p,xl,m,n1,r)

    let rec insertNode px x n =
      match n with
      | Node(p,xl,m,l,r) ->
	  if (p = px) then
	    begin
	      if (List.length xl mod 2 = 0) then
		Node(p,(x::xl),m+1,l,r)
	      else
		Node(p,(xl @ [x]),m+1,l,r)
	    end
	  else if (px < p) then
	    lbalance(p,xl,m+1,insertNode px x l,r)
	  else
	    rbalance(p,xl,m+1,l,insertNode px x r)
      | Leaf -> Node(px,[x],1,Leaf,Leaf)

    let rec popFirst n =
      match n with
      | Node(_,(x::[]),_,Leaf,r) ->
	  (x,r)
      | Node(p,(x::xl),m,Leaf,r) ->
	  (x,Node(p,xl,m-1,Leaf,r))
      | Node(p,xl,m,l,r) ->
	  let (x,l') = popFirst l in
	  (x,rbalance(p,xl,m-1,l',r))
      | Leaf -> raise Not_found

    let rec peekFirst n =
      match n with
      | Node(p,(x::_),_,Leaf,_) -> (p,x)
      | Node(_,_,_,l,_) -> peekFirst l
      | Leaf -> raise Not_found

    let pqueue : tree ref = ref Leaf
    let reset () = pqueue := Leaf
    let insertWithPriority p o =
      let p' = p + ((!pqueue_offset) asr 9) in (*** The offset is just for fairness, and should have minimal effect otherwise.  asr 9 is bitshift by 9, i.e., division by 512 ***)
      begin
	incr pqueue_offset;
	pqueue := insertNode p' o (!pqueue)
      end
    let getNext () = let (x,n) = popFirst (!pqueue) in pqueue := n; x
    let peekAtNext () = peekFirst (!pqueue)

	(*** Just for debugging ***)
    let rec debug_print_rec f n =
      match n with
      | Node(p,xl,m,lft,rght) ->
	  begin
	    Printf.printf "Node with priority %d, size %d.\n" p m;
	    List.iter (fun x -> Printf.printf "> %s\n" (f x)) xl;
	    Printf.printf "Left of %d.\n" p;
	    debug_print_rec f lft;
	    Printf.printf "Right of %d.\n" p;
	    debug_print_rec f rght
	  end
      | Leaf -> Printf.printf "Leaf.\n"

    let debug_print f = Printf.printf "-----BEGIN-----\n"; debug_print_rec f (!pqueue); Printf.printf "-----END-----\n"
  end

(*** Version 4: Balanced binary tree with same priorities treated as stacks (implemented as lists on the node of the priority). Fairness ensured with an offset incremented every 512 inserts. ***)
module PriorityQueue4 = functor (T : sig type t end) ->
  struct
    type a = T.t
    let logmodulus = 9
    let pqueue_offset = ref 0

	(*** Binary Tree: Node(p,xl,m,lft,rght)
	     -- p is priority (tree is ordered wrt p)
	     -- xl is list of data with priority p
	     -- m is size of tree (sum of length of xl and sizes of children)
	     -- lft and rght are the two children
	 ***)
    type tree = Node of (int * T.t list * int * tree * tree) | Leaf

    let size n =
      match n with
      | Node(_,_,m,_,_) -> m
      | Leaf -> 0

    let rec lbalance (p,xl,m,l,n7) =
      match l with
      | Node(p4,xl4,m4,((Node(p2,xl2,m2,n1,n3)) as n2),n5) when m4 > (size n7) ->
	  let m6' = m + (size n5) - m4 in
	  Node(p4,xl4,m,n2,Node(p,xl,m6',n5,n7))
      | Node(p2,xl2,m2,n1,Node(p4,xl4,m4,n3,n5)) when m2 > (size n7) ->
	  let m2' = m2 + (size n3) - m4 in
	  let m6' = m + (size n5) - m2 in
	  Node(p4,xl4,m,Node(p2,xl2,m2',n1,n3),Node(p,xl,m6',n5,n7))
      | _ -> Node(p,xl,m,l,n7)

    let rec rbalance (p,xl,m,n1,r) =
      match r with
      | Node(p6,xl6,m6,Node(p4,xl4,m4,n3,n5),n7) when (size n1) < m6 ->
	  let m3 = size n3 in
	  let m5 = size n5 in
	  let m2' = m + m3 - m6 in
	  let m6' = m6 + m5 - m4 in
	  Node(p4,xl4,m,Node(p,xl,m2',n1,n3),Node(p6,xl6,m6',n5,n7))
      | Node(p4,xl4,m4,n3,((Node(p6,xl6,m6,n5,n7)) as n6)) when (size n1) < m4 ->
	  let m3 = size n3 in
	  let m2' = m + m3 - m4 in
	  Node(p4,xl4,m,Node(p,xl,m2',n1,n3),n6)
      | _ -> Node(p,xl,m,n1,r)

    let rec insertNode px x n =
      match n with
      | Node(p,xl,m,l,r) ->
	  if (p = px) then
	    Node(p,(x::xl),m+1,l,r)
	  else if (px < p) then
	    lbalance(p,xl,m+1,insertNode px x l,r)
	  else
	    rbalance(p,xl,m+1,l,insertNode px x r)
      | Leaf -> Node(px,[x],1,Leaf,Leaf)

    let rec popFirst n =
      match n with
      | Node(_,(x::[]),_,Leaf,r) ->
	  (x,r)
      | Node(p,(x::xl),m,Leaf,r) ->
	  (x,Node(p,xl,m-1,Leaf,r))
      | Node(p,xl,m,l,r) ->
	  let (x,l') = popFirst l in
	  (x,rbalance(p,xl,m-1,l',r))
      | Leaf -> raise Not_found

    let rec peekFirst n =
      match n with
      | Node(p,(x::_),_,Leaf,_) -> (p,x)
      | Node(_,_,_,l,_) -> peekFirst l
      | Leaf -> raise Not_found

    let pqueue : tree ref = ref Leaf
    let reset () = pqueue := Leaf
    let insertWithPriority p o =
      let p' = p + ((!pqueue_offset) asr logmodulus) in (*** The offset is just for fairness, and should have minimal effect otherwise. ***)
      begin
	incr pqueue_offset;
	pqueue := insertNode p' o (!pqueue)
      end
    let getNext () = let (x,n) = popFirst (!pqueue) in pqueue := n; x
    let peekAtNext () = peekFirst (!pqueue)

	(*** Just for debugging ***)
    let rec debug_print_rec f n =
      match n with
      | Node(p,xl,m,lft,rght) ->
	  begin
	    Printf.printf "Node with priority %d, size %d.\n" p m;
	    List.iter (fun x -> Printf.printf "> %s\n" (f x)) xl;
	    Printf.printf "Left of %d.\n" p;
	    debug_print_rec f lft;
	    Printf.printf "Right of %d.\n" p;
	    debug_print_rec f rght
	  end
      | Leaf -> Printf.printf "Leaf.\n"

    let debug_print f = Printf.printf "-----BEGIN-----\n"; debug_print_rec f (!pqueue); Printf.printf "-----END-----\n"
  end

(*** Version 5: Balanced binary tree with same priorities treated as stacks (implemented as lists on the node of the priority). Fairness ensured with an offset incremented every 256 inserts. ***)
module PriorityQueue5 = functor (T : sig type t end) ->
  struct
    type a = T.t
    let logmodulus = 8
    let pqueue_offset = ref 0

	(*** Binary Tree: Node(p,xl,m,lft,rght)
	     -- p is priority (tree is ordered wrt p)
	     -- xl is list of data with priority p
	     -- m is size of tree (sum of length of xl and sizes of children)
	     -- lft and rght are the two children
	 ***)
    type tree = Node of (int * T.t list * int * tree * tree) | Leaf

    let size n =
      match n with
      | Node(_,_,m,_,_) -> m
      | Leaf -> 0

    let rec lbalance (p,xl,m,l,n7) =
      match l with
      | Node(p4,xl4,m4,((Node(p2,xl2,m2,n1,n3)) as n2),n5) when m4 > (size n7) ->
	  let m6' = m + (size n5) - m4 in
	  Node(p4,xl4,m,n2,Node(p,xl,m6',n5,n7))
      | Node(p2,xl2,m2,n1,Node(p4,xl4,m4,n3,n5)) when m2 > (size n7) ->
	  let m2' = m2 + (size n3) - m4 in
	  let m6' = m + (size n5) - m2 in
	  Node(p4,xl4,m,Node(p2,xl2,m2',n1,n3),Node(p,xl,m6',n5,n7))
      | _ -> Node(p,xl,m,l,n7)

    let rec rbalance (p,xl,m,n1,r) =
      match r with
      | Node(p6,xl6,m6,Node(p4,xl4,m4,n3,n5),n7) when (size n1) < m6 ->
	  let m3 = size n3 in
	  let m5 = size n5 in
	  let m2' = m + m3 - m6 in
	  let m6' = m6 + m5 - m4 in
	  Node(p4,xl4,m,Node(p,xl,m2',n1,n3),Node(p6,xl6,m6',n5,n7))
      | Node(p4,xl4,m4,n3,((Node(p6,xl6,m6,n5,n7)) as n6)) when (size n1) < m4 ->
	  let m3 = size n3 in
	  let m2' = m + m3 - m4 in
	  Node(p4,xl4,m,Node(p,xl,m2',n1,n3),n6)
      | _ -> Node(p,xl,m,n1,r)

    let rec insertNode px x n =
      match n with
      | Node(p,xl,m,l,r) ->
	  if (p = px) then
	    Node(p,(x::xl),m+1,l,r)
	  else if (px < p) then
	    lbalance(p,xl,m+1,insertNode px x l,r)
	  else
	    rbalance(p,xl,m+1,l,insertNode px x r)
      | Leaf -> Node(px,[x],1,Leaf,Leaf)

    let rec popFirst n =
      match n with
      | Node(_,(x::[]),_,Leaf,r) ->
	  (x,r)
      | Node(p,(x::xl),m,Leaf,r) ->
	  (x,Node(p,xl,m-1,Leaf,r))
      | Node(p,xl,m,l,r) ->
	  let (x,l') = popFirst l in
	  (x,rbalance(p,xl,m-1,l',r))
      | Leaf -> raise Not_found

    let rec peekFirst n =
      match n with
      | Node(p,(x::_),_,Leaf,_) -> (p,x)
      | Node(_,_,_,l,_) -> peekFirst l
      | Leaf -> raise Not_found

    let pqueue : tree ref = ref Leaf
    let reset () = pqueue := Leaf
    let insertWithPriority p o =
      let p' = p + ((!pqueue_offset) asr logmodulus) in (*** The offset is just for fairness, and should have minimal effect otherwise. ***)
      begin
	incr pqueue_offset;
	pqueue := insertNode p' o (!pqueue)
      end
    let getNext () = let (x,n) = popFirst (!pqueue) in pqueue := n; x
    let peekAtNext () = peekFirst (!pqueue)

	(*** Just for debugging ***)
    let rec debug_print_rec f n =
      match n with
      | Node(p,xl,m,lft,rght) ->
	  begin
	    Printf.printf "Node with priority %d, size %d.\n" p m;
	    List.iter (fun x -> Printf.printf "> %s\n" (f x)) xl;
	    Printf.printf "Left of %d.\n" p;
	    debug_print_rec f lft;
	    Printf.printf "Right of %d.\n" p;
	    debug_print_rec f rght
	  end
      | Leaf -> Printf.printf "Leaf.\n"

    let debug_print f = Printf.printf "-----BEGIN-----\n"; debug_print_rec f (!pqueue); Printf.printf "-----END-----\n"
  end

(*** Version 6: Balanced binary tree with same priorities treated as stacks (implemented as lists on the node of the priority). Fairness ensured with an offset incremented every 128 inserts. ***)
module PriorityQueue6 = functor (T : sig type t end) ->
  struct
    type a = T.t
    let logmodulus = 7
    let pqueue_offset = ref 0

	(*** Binary Tree: Node(p,xl,m,lft,rght)
	     -- p is priority (tree is ordered wrt p)
	     -- xl is list of data with priority p
	     -- m is size of tree (sum of length of xl and sizes of children)
	     -- lft and rght are the two children
	 ***)
    type tree = Node of (int * T.t list * int * tree * tree) | Leaf

    let size n =
      match n with
      | Node(_,_,m,_,_) -> m
      | Leaf -> 0

    let rec lbalance (p,xl,m,l,n7) =
      match l with
      | Node(p4,xl4,m4,((Node(p2,xl2,m2,n1,n3)) as n2),n5) when m4 > (size n7) ->
	  let m6' = m + (size n5) - m4 in
	  Node(p4,xl4,m,n2,Node(p,xl,m6',n5,n7))
      | Node(p2,xl2,m2,n1,Node(p4,xl4,m4,n3,n5)) when m2 > (size n7) ->
	  let m2' = m2 + (size n3) - m4 in
	  let m6' = m + (size n5) - m2 in
	  Node(p4,xl4,m,Node(p2,xl2,m2',n1,n3),Node(p,xl,m6',n5,n7))
      | _ -> Node(p,xl,m,l,n7)

    let rec rbalance (p,xl,m,n1,r) =
      match r with
      | Node(p6,xl6,m6,Node(p4,xl4,m4,n3,n5),n7) when (size n1) < m6 ->
	  let m3 = size n3 in
	  let m5 = size n5 in
	  let m2' = m + m3 - m6 in
	  let m6' = m6 + m5 - m4 in
	  Node(p4,xl4,m,Node(p,xl,m2',n1,n3),Node(p6,xl6,m6',n5,n7))
      | Node(p4,xl4,m4,n3,((Node(p6,xl6,m6,n5,n7)) as n6)) when (size n1) < m4 ->
	  let m3 = size n3 in
	  let m2' = m + m3 - m4 in
	  Node(p4,xl4,m,Node(p,xl,m2',n1,n3),n6)
      | _ -> Node(p,xl,m,n1,r)

    let rec insertNode px x n =
      match n with
      | Node(p,xl,m,l,r) ->
	  if (p = px) then
	    Node(p,(x::xl),m+1,l,r)
	  else if (px < p) then
	    lbalance(p,xl,m+1,insertNode px x l,r)
	  else
	    rbalance(p,xl,m+1,l,insertNode px x r)
      | Leaf -> Node(px,[x],1,Leaf,Leaf)

    let rec popFirst n =
      match n with
      | Node(_,(x::[]),_,Leaf,r) ->
	  (x,r)
      | Node(p,(x::xl),m,Leaf,r) ->
	  (x,Node(p,xl,m-1,Leaf,r))
      | Node(p,xl,m,l,r) ->
	  let (x,l') = popFirst l in
	  (x,rbalance(p,xl,m-1,l',r))
      | Leaf -> raise Not_found

    let rec peekFirst n =
      match n with
      | Node(p,(x::_),_,Leaf,_) -> (p,x)
      | Node(_,_,_,l,_) -> peekFirst l
      | Leaf -> raise Not_found

    let pqueue : tree ref = ref Leaf
    let reset () = pqueue := Leaf
    let insertWithPriority p o =
      let p' = p + ((!pqueue_offset) asr logmodulus) in (*** The offset is just for fairness, and should have minimal effect otherwise. ***)
      begin
	incr pqueue_offset;
	pqueue := insertNode p' o (!pqueue)
      end
    let getNext () = let (x,n) = popFirst (!pqueue) in pqueue := n; x
    let peekAtNext () = peekFirst (!pqueue)

	(*** Just for debugging ***)
    let rec debug_print_rec f n =
      match n with
      | Node(p,xl,m,lft,rght) ->
	  begin
	    Printf.printf "Node with priority %d, size %d.\n" p m;
	    List.iter (fun x -> Printf.printf "> %s\n" (f x)) xl;
	    Printf.printf "Left of %d.\n" p;
	    debug_print_rec f lft;
	    Printf.printf "Right of %d.\n" p;
	    debug_print_rec f rght
	  end
      | Leaf -> Printf.printf "Leaf.\n"

    let debug_print f = Printf.printf "-----BEGIN-----\n"; debug_print_rec f (!pqueue); Printf.printf "-----END-----\n"
  end

(*** Version 7: Balanced binary tree with same priorities treated as stacks (implemented as lists on the node of the priority). Fairness ensured with an offset incremented every 64 inserts. ***)
module PriorityQueue7 = functor (T : sig type t end) ->
  struct
    type a = T.t
    let logmodulus = 6
    let pqueue_offset = ref 0

	(*** Binary Tree: Node(p,xl,m,lft,rght)
	     -- p is priority (tree is ordered wrt p)
	     -- xl is list of data with priority p
	     -- m is size of tree (sum of length of xl and sizes of children)
	     -- lft and rght are the two children
	 ***)
    type tree = Node of (int * T.t list * int * tree * tree) | Leaf

    let size n =
      match n with
      | Node(_,_,m,_,_) -> m
      | Leaf -> 0

    let rec lbalance (p,xl,m,l,n7) =
      match l with
      | Node(p4,xl4,m4,((Node(p2,xl2,m2,n1,n3)) as n2),n5) when m4 > (size n7) ->
	  let m6' = m + (size n5) - m4 in
	  Node(p4,xl4,m,n2,Node(p,xl,m6',n5,n7))
      | Node(p2,xl2,m2,n1,Node(p4,xl4,m4,n3,n5)) when m2 > (size n7) ->
	  let m2' = m2 + (size n3) - m4 in
	  let m6' = m + (size n5) - m2 in
	  Node(p4,xl4,m,Node(p2,xl2,m2',n1,n3),Node(p,xl,m6',n5,n7))
      | _ -> Node(p,xl,m,l,n7)

    let rec rbalance (p,xl,m,n1,r) =
      match r with
      | Node(p6,xl6,m6,Node(p4,xl4,m4,n3,n5),n7) when (size n1) < m6 ->
	  let m3 = size n3 in
	  let m5 = size n5 in
	  let m2' = m + m3 - m6 in
	  let m6' = m6 + m5 - m4 in
	  Node(p4,xl4,m,Node(p,xl,m2',n1,n3),Node(p6,xl6,m6',n5,n7))
      | Node(p4,xl4,m4,n3,((Node(p6,xl6,m6,n5,n7)) as n6)) when (size n1) < m4 ->
	  let m3 = size n3 in
	  let m2' = m + m3 - m4 in
	  Node(p4,xl4,m,Node(p,xl,m2',n1,n3),n6)
      | _ -> Node(p,xl,m,n1,r)

    let rec insertNode px x n =
      match n with
      | Node(p,xl,m,l,r) ->
	  if (p = px) then
	    Node(p,(x::xl),m+1,l,r)
	  else if (px < p) then
	    lbalance(p,xl,m+1,insertNode px x l,r)
	  else
	    rbalance(p,xl,m+1,l,insertNode px x r)
      | Leaf -> Node(px,[x],1,Leaf,Leaf)

    let rec popFirst n =
      match n with
      | Node(_,(x::[]),_,Leaf,r) ->
	  (x,r)
      | Node(p,(x::xl),m,Leaf,r) ->
	  (x,Node(p,xl,m-1,Leaf,r))
      | Node(p,xl,m,l,r) ->
	  let (x,l') = popFirst l in
	  (x,rbalance(p,xl,m-1,l',r))
      | Leaf -> raise Not_found

    let rec peekFirst n =
      match n with
      | Node(p,(x::_),_,Leaf,_) -> (p,x)
      | Node(_,_,_,l,_) -> peekFirst l
      | Leaf -> raise Not_found

    let pqueue : tree ref = ref Leaf
    let reset () = pqueue := Leaf
    let insertWithPriority p o =
      let p' = p + ((!pqueue_offset) asr logmodulus) in (*** The offset is just for fairness, and should have minimal effect otherwise. ***)
      begin
	incr pqueue_offset;
	pqueue := insertNode p' o (!pqueue)
      end
    let getNext () = let (x,n) = popFirst (!pqueue) in pqueue := n; x
    let peekAtNext () = peekFirst (!pqueue)

	(*** Just for debugging ***)
    let rec debug_print_rec f n =
      match n with
      | Node(p,xl,m,lft,rght) ->
	  begin
	    Printf.printf "Node with priority %d, size %d.\n" p m;
	    List.iter (fun x -> Printf.printf "> %s\n" (f x)) xl;
	    Printf.printf "Left of %d.\n" p;
	    debug_print_rec f lft;
	    Printf.printf "Right of %d.\n" p;
	    debug_print_rec f rght
	  end
      | Leaf -> Printf.printf "Leaf.\n"

    let debug_print f = Printf.printf "-----BEGIN-----\n"; debug_print_rec f (!pqueue); Printf.printf "-----END-----\n"
  end

(*** Version 8: Balanced binary tree with same priorities treated as stacks (implemented as lists on the node of the priority). Fairness ensured with an offset incremented every 32 inserts. ***)
module PriorityQueue8 = functor (T : sig type t end) ->
  struct
    type a = T.t
    let logmodulus = 5
    let pqueue_offset = ref 0

	(*** Binary Tree: Node(p,xl,m,lft,rght)
	     -- p is priority (tree is ordered wrt p)
	     -- xl is list of data with priority p
	     -- m is size of tree (sum of length of xl and sizes of children)
	     -- lft and rght are the two children
	 ***)
    type tree = Node of (int * T.t list * int * tree * tree) | Leaf

    let size n =
      match n with
      | Node(_,_,m,_,_) -> m
      | Leaf -> 0

    let rec lbalance (p,xl,m,l,n7) =
      match l with
      | Node(p4,xl4,m4,((Node(p2,xl2,m2,n1,n3)) as n2),n5) when m4 > (size n7) ->
	  let m6' = m + (size n5) - m4 in
	  Node(p4,xl4,m,n2,Node(p,xl,m6',n5,n7))
      | Node(p2,xl2,m2,n1,Node(p4,xl4,m4,n3,n5)) when m2 > (size n7) ->
	  let m2' = m2 + (size n3) - m4 in
	  let m6' = m + (size n5) - m2 in
	  Node(p4,xl4,m,Node(p2,xl2,m2',n1,n3),Node(p,xl,m6',n5,n7))
      | _ -> Node(p,xl,m,l,n7)

    let rec rbalance (p,xl,m,n1,r) =
      match r with
      | Node(p6,xl6,m6,Node(p4,xl4,m4,n3,n5),n7) when (size n1) < m6 ->
	  let m3 = size n3 in
	  let m5 = size n5 in
	  let m2' = m + m3 - m6 in
	  let m6' = m6 + m5 - m4 in
	  Node(p4,xl4,m,Node(p,xl,m2',n1,n3),Node(p6,xl6,m6',n5,n7))
      | Node(p4,xl4,m4,n3,((Node(p6,xl6,m6,n5,n7)) as n6)) when (size n1) < m4 ->
	  let m3 = size n3 in
	  let m2' = m + m3 - m4 in
	  Node(p4,xl4,m,Node(p,xl,m2',n1,n3),n6)
      | _ -> Node(p,xl,m,n1,r)

    let rec insertNode px x n =
      match n with
      | Node(p,xl,m,l,r) ->
	  if (p = px) then
	    Node(p,(x::xl),m+1,l,r)
	  else if (px < p) then
	    lbalance(p,xl,m+1,insertNode px x l,r)
	  else
	    rbalance(p,xl,m+1,l,insertNode px x r)
      | Leaf -> Node(px,[x],1,Leaf,Leaf)

    let rec popFirst n =
      match n with
      | Node(_,(x::[]),_,Leaf,r) ->
	  (x,r)
      | Node(p,(x::xl),m,Leaf,r) ->
	  (x,Node(p,xl,m-1,Leaf,r))
      | Node(p,xl,m,l,r) ->
	  let (x,l') = popFirst l in
	  (x,rbalance(p,xl,m-1,l',r))
      | Leaf -> raise Not_found

    let rec peekFirst n =
      match n with
      | Node(p,(x::_),_,Leaf,_) -> (p,x)
      | Node(_,_,_,l,_) -> peekFirst l
      | Leaf -> raise Not_found

    let pqueue : tree ref = ref Leaf
    let reset () = pqueue := Leaf
    let insertWithPriority p o =
      let p' = p + ((!pqueue_offset) asr logmodulus) in (*** The offset is just for fairness, and should have minimal effect otherwise. ***)
      begin
	incr pqueue_offset;
	pqueue := insertNode p' o (!pqueue)
      end
    let getNext () = let (x,n) = popFirst (!pqueue) in pqueue := n; x
    let peekAtNext () = peekFirst (!pqueue)

	(*** Just for debugging ***)
    let rec debug_print_rec f n =
      match n with
      | Node(p,xl,m,lft,rght) ->
	  begin
	    Printf.printf "Node with priority %d, size %d.\n" p m;
	    List.iter (fun x -> Printf.printf "> %s\n" (f x)) xl;
	    Printf.printf "Left of %d.\n" p;
	    debug_print_rec f lft;
	    Printf.printf "Right of %d.\n" p;
	    debug_print_rec f rght
	  end
      | Leaf -> Printf.printf "Leaf.\n"

    let debug_print f = Printf.printf "-----BEGIN-----\n"; debug_print_rec f (!pqueue); Printf.printf "-----END-----\n"
  end
