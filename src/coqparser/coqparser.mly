/* File: parser.mly */
/* Author: Chad E Brown */

%token DEQ COLON SEMICOLON COMMA DARR LPAREN RPAREN EQ NEQ PROP OPENCOM CLOSECOM
%token REQUIRE EXPORT SECTION END
%token ALL EX EXU IMP LAM CONJ DISJ IFF NEG FALSE TRUE BLANK LLET IN
%token SAR INDTYPE PROPTYPE MEM NMEM SUBQ NSUBQ
%token VAR HYP BLET PARAM AXIOM DEF THEOREM EXACT QED
%token <int> CONJECTURE
%token <int> DOT
%token <string> POLY1
%token <string> POLY2
%token <string> NARY1
%token <string> NARY2
%token <int> INT
%token <string> ID
%nonassoc IFF
%right IMP
%left DISJ
%left CONJ
%nonassoc NEG
%nonassoc EQ NEQ MEM NMEM SUBQ NSUBQ
%start documentitem
%type <unit> documentitem
%%
documentitem:
  | REQUIRE ID DOT { (State.require $2) }
  | REQUIRE EXPORT ID DOT { (State.require $3) }
  | SECTION ID DOT {
    if (!State.coqglobalfile) then
      begin
	State.coqglobalsectionstack := (($2,!State.coqoutfn1,!State.coqctx)::!State.coqglobalsectionstack);
	State.coqctx := []
      end
    else raise (State.GenericError "Sections are only allowed in global Coq files.") }
  | END ID DOT {
    if (!State.coqglobalfile) then
      begin
	match (!State.coqglobalsectionstack) with
	| ((x,fn,ctx)::sr) when x = $2 -> (State.coqoutfn1 := fn; State.coqctx := ctx; State.coqglobalsectionstack := sr)
	| ((x,_,_)::_) -> raise (State.GenericError ("Attempt to End Section " ^ $2 ^ ", but Sections " ^ x ^ " is open."))
	| _ -> raise (State.GenericError "Attempt to End a Section, but no sections are open.")
      end
    else raise (State.GenericError "Sections are only allowed in global Coq files.") }
  | HYP ID COLON preterm DOT {
    if (!State.coqglobalfile) then
      begin
	let co1 = !State.coqoutfn1 in
	let cod : (out_channel -> unit) -> out_channel -> unit = (fun g -> fun c -> g c; Printf.fprintf c "Axiom %s:" $2; Syntax.print_pretrm_coq2 c $4 (9999) (9999); Printf.fprintf c ".\n") in
	State.coqoutfn1 := cod co1;
	State.coqctx := (None,Some $4,None)::!State.coqctx
      end
    else raise (State.GenericError "Hypotheses are only allowed in global Coq files.") }
  | AXIOM ID COLON preterm DOT {
    if (!State.coqglobalfile) then
      begin
	let co1 = !State.coqoutfn1 in
	let cod : Syntax.prectx -> (out_channel -> unit) -> out_channel -> unit =
	  (fun cx g -> fun c -> g c; Printf.fprintf c "Axiom %s:" $2; Syntax.print_pretrm_coq2 c (Syntax.prectx_all cx $4) (9999) (9999); Printf.fprintf c ".\n")
	in
	State.coqoutfn1 := cod [] co1;
	State.coqglobalsectionstack := State.updatecoqglobalsectionstack (!State.coqctx) (!State.coqglobalsectionstack) cod
      end
    else State.declare_thf_logic_formula $2 "axiom" $4 }
  | THEOREM ID COLON preterm DOT EXACT ignorepfterm DOT QED DOT {
    if (!State.coqglobalfile) then
      begin
	let co1 = !State.coqoutfn1 in
	let cod : Syntax.prectx -> (out_channel -> unit) -> out_channel -> unit =
	  (fun cx g -> fun c -> g c; Printf.fprintf c "Axiom %s:" $2; Syntax.print_pretrm_coq2 c (Syntax.prectx_all cx $4) (9999) (9999); Printf.fprintf c ".\n")
	in
	State.coqoutfn1 := cod [] co1;
	State.coqglobalsectionstack := State.updatecoqglobalsectionstack (!State.coqctx) (!State.coqglobalsectionstack) cod
      end
    else State.declare_thf_logic_formula $2 "lemma" $4 }
  | CONJECTURE ID COLON preterm DOT {
    if (!State.coqglobalfile) then
      begin
	let co1 = !State.coqoutfn1 in
	(*** Call a new satallax image on the current conjecture -- passing any slave arguments ***)
	let tmpcoqfile = "/tmp/scoqin671" in
	let tmpcoqfile2 = "/tmp/scoqin672" in
	let tmpcoq = open_out tmpcoqfile in
	co1 tmpcoq;
	Printf.fprintf tmpcoq "Conjecture %s:" $2;
	Syntax.print_pretrm_coq2 tmpcoq $4 (9999) (9999);
	Printf.fprintf tmpcoq ".\n";
	close_out tmpcoq;
	let sargs = List.fold_right (fun x a -> match a with b::r when b = "-c" -> r | r -> x::r) !State.slaveargs [] in
	let sargs = (List.fold_right (fun m a -> (m::"-m"::a)) !State.mode sargs) in
	let sargs = match (!State.timeout) with Some tm -> (string_of_float tm)::"-t"::sargs | None -> sargs in
	let sargs = tmpcoqfile::"-C"::"coqspfterm"::"-p"::tmpcoqfile2::"-c"::sargs in
	begin
	  if (!State.verbosity > 20) then (Printf.printf "call: "; List.iter (fun x -> Printf.printf " %s" x) (List.rev sargs); Printf.printf "\n");
	  match (Unix.system (String.concat " " (List.rev sargs))) with
	  | (Unix.WEXITED pstatus) when pstatus = 20 ->
	      let tmpcoqfile2in = open_in tmpcoqfile2 in
	      let b = Buffer.create 2048 in
	      begin
		try
		  while true do
		    let ch = input_char tmpcoqfile2in in
		    Buffer.add_char b ch
		  done
		with
		| End_of_file -> ()
	      end;
	      let pfstr = Buffer.contents b in
	      let tmpf = fun c ->
		begin
		  Printf.fprintf c "Theorem %s:" $2;
		  Syntax.print_pretrm_coq2 c $4 (9999) (9999);
		  Printf.fprintf c ".\n";
		  Printf.fprintf c "%s" pfstr;
		end
	      in
	      begin
		State.coqinticks := (Some tmpf,$5 + 1)::(None,$1)::!State.coqinticks;
	      end
	  | _ -> ()
	end;
	let cod : Syntax.prectx -> (out_channel -> unit) -> out_channel -> unit =
	  (fun cx g -> fun c -> g c; Printf.fprintf c "Axiom %s:" $2; Syntax.print_pretrm_coq2 c (Syntax.prectx_all cx $4) (9999) (9999); Printf.fprintf c ".\n")
	in
	State.coqoutfn1 := cod [] co1;
	State.coqglobalsectionstack := State.updatecoqglobalsectionstack (!State.coqctx) (!State.coqglobalsectionstack) cod
      end
    else
      State.declare_thf_logic_formula $2 "conjecture" $4 }
  | VAR ID COLON stp DOT {
    if (!State.coqglobalfile) then
      begin
	let co1 = !State.coqoutfn1 in
	let cod : (out_channel -> unit) -> out_channel -> unit = (fun g -> fun c -> g c; Printf.fprintf c "Parameter %s:" $2; Syntax.print_pretrm_coq2 c $4 (9999) (9999); Printf.fprintf c ".\n") in
	State.coqoutfn1 := cod co1;
	State.coqctx := (Some $2,Some $4,None)::!State.coqctx
      end
    else raise (State.GenericError "Variables are only allowed in global Coq files.") }
  | PARAM ID COLON stp DOT {
    if (!State.coqglobalfile) then
      begin
	let co1 = !State.coqoutfn1 in
	let cod : Syntax.prectx -> (out_channel -> unit) -> out_channel -> unit =
	  (fun cx g -> fun c -> g c; Printf.fprintf c "Parameter %s:" $2; Syntax.print_pretrm_coq2 c (Syntax.prectx_ar cx $4) (-1) (-1); Printf.fprintf c ".\n")
	in
	State.coqoutfn1 := cod [] co1;
	State.coqglobalsectionstack := State.updatecoqglobalsectionstack (!State.coqctx) (!State.coqglobalsectionstack) cod
      end
    else State.declare_typed_constant $2 "type" (Syntax.POf(Syntax.PName($2),$4)) }
  | DEF ID COLON stp DEQ preterm DOT {
    if (!State.coqglobalfile) then
      begin
	let co1 = !State.coqoutfn1 in
	let cod : Syntax.prectx -> (out_channel -> unit) -> out_channel -> unit =
	  (fun cx g -> fun c -> g c; Printf.fprintf c "Definition %s:" $2; Syntax.print_pretrm_coq2 c (Syntax.prectx_ar cx $4) (-1) (-1); Printf.fprintf c " := "; Syntax.print_pretrm_coq2 c (Syntax.prectx_lam cx $6) (9999) (9999); Printf.fprintf c ".\n")
	in
	State.coqoutfn1 := cod [] co1;
	State.coqglobalsectionstack := State.updatecoqglobalsectionstack (!State.coqctx) (!State.coqglobalsectionstack) cod
      end
    else State.declare_definition $2 "definition" (Syntax.PDef(Syntax.PName $2,Syntax.POf($6,$4))) }
  | DEF ID DEQ preterm DOT {
    if (!State.coqglobalfile) then
      begin
	let co1 = !State.coqoutfn1 in
	let cod : Syntax.prectx -> (out_channel -> unit) -> out_channel -> unit =
	  (fun cx g -> fun c -> g c; Printf.fprintf c "Definition %s:=" $2; Syntax.print_pretrm_coq2 c (Syntax.prectx_lam cx $4) (9999) (9999); Printf.fprintf c ".\n")
	in
	State.coqoutfn1 := cod [] co1;
	State.coqglobalsectionstack := State.updatecoqglobalsectionstack (!State.coqctx) (!State.coqglobalsectionstack) cod
      end
    else State.declare_definition $2 "definition" (Syntax.PDef(Syntax.PName $2,$4)) }
  | DEF ID tpids COLON stp DEQ preterm DOT {
    let pretp = List.fold_right (fun (_,a) b -> Syntax.PAr(a,b)) $3 $5 in
    let pretm = List.fold_right (fun (x,a) m -> Syntax.PLam([(x,a)],m)) $3 $7 in
    if (!State.coqglobalfile) then
      begin
	let co1 = !State.coqoutfn1 in
	let cod : Syntax.prectx -> (out_channel -> unit) -> out_channel -> unit =
	  (fun cx g -> fun c -> g c; Printf.fprintf c "Definition %s:" $2; Syntax.print_pretrm_coq2 c (Syntax.prectx_ar cx pretp) (-1) (-1); Printf.fprintf c " := "; Syntax.print_pretrm_coq2 c (Syntax.prectx_lam cx pretm) (9999) (9999); Printf.fprintf c ".\n")
	in
	State.coqoutfn1 := cod [] co1;
	State.coqglobalsectionstack := State.updatecoqglobalsectionstack (!State.coqctx) (!State.coqglobalsectionstack) cod
      end
    else State.declare_definition $2 "definition" (Syntax.PDef(Syntax.PName $2,Syntax.POf(pretm,pretp))) }
  | DEF ID tpids DEQ preterm DOT {
    let pretm = List.fold_right (fun (x,a) m -> Syntax.PLam([(x,a)],m)) $3 $5 in
    if (!State.coqglobalfile) then
      begin
	let co1 = !State.coqoutfn1 in
	let cod : Syntax.prectx -> (out_channel -> unit) -> out_channel -> unit =
	  (fun cx g -> fun c -> g c; Printf.fprintf c "Definition %s:=" $2; Syntax.print_pretrm_coq2 c (Syntax.prectx_lam cx pretm) (9999) (9999); Printf.fprintf c ".\n")
	in
	State.coqoutfn1 := cod [] co1;
	State.coqglobalsectionstack := State.updatecoqglobalsectionstack (!State.coqctx) (!State.coqglobalsectionstack) cod
      end
    else
      State.declare_definition $2 "definition" (Syntax.PDef(Syntax.PName $2,pretm)) }
  | BLET ID COLON stp DEQ preterm DOT {
    if (!State.coqglobalfile) then
      begin
	let co1 = !State.coqoutfn1 in
	let cod : (out_channel -> unit) -> out_channel -> unit = (fun g -> fun c -> g c; Printf.fprintf c "Definition %s:" $2; Syntax.print_pretrm_coq2 c $4 (-1) (-1); Printf.fprintf c " := "; Syntax.print_pretrm_coq2 c $6 (9999) (9999); Printf.fprintf c ".\n") in
	State.coqoutfn1 := cod co1;
	State.coqctx := (Some $2,Some $4,Some $6)::!State.coqctx
      end
    else raise (State.GenericError "Lets are only allowed in global Coq files.") }
  | BLET ID DEQ preterm DOT {
    if (!State.coqglobalfile) then
      begin
	let co1 = !State.coqoutfn1 in
	let cod : (out_channel -> unit) -> out_channel -> unit = (fun g -> fun c -> g c; Printf.fprintf c "Definition %s:=" $2; Syntax.print_pretrm_coq2 c $4 (9999) (9999); Printf.fprintf c ".\n") in
	State.coqoutfn1 := cod co1;
	State.coqctx := (Some $2,None,Some $4)::!State.coqctx
      end
    else raise (State.GenericError "Lets are only allowed in global Coq files.") }
  | BLET ID tpids COLON stp DEQ preterm DOT {
    let pretp = List.fold_right (fun (_,a) b -> Syntax.PAr(a,b)) $3 $5 in
    let pretm = List.fold_right (fun (x,a) m -> Syntax.PLam([(x,a)],m)) $3 $7 in
    if (!State.coqglobalfile) then
      begin
	let co1 = !State.coqoutfn1 in
	let cod : (out_channel -> unit) -> out_channel -> unit = (fun g -> fun c -> g c; Printf.fprintf c "Definition %s:" $2; Syntax.print_pretrm_coq2 c pretp (-1) (-1); Printf.fprintf c " := "; Syntax.print_pretrm_coq2 c pretm (9999) (9999); Printf.fprintf c ".\n") in
	State.coqoutfn1 := cod co1;
	State.coqctx := (Some $2,Some pretp,Some pretm)::!State.coqctx
      end
    else raise (State.GenericError "Lets are only allowed in global Coq files.") }
  | BLET ID tpids DEQ preterm DOT {
    let pretm = List.fold_right (fun (x,a) m -> Syntax.PLam([(x,a)],m)) $3 $5 in
    if (!State.coqglobalfile) then
      begin
	let co1 = !State.coqoutfn1 in
	let cod : (out_channel -> unit) -> out_channel -> unit = (fun g -> fun c -> g c; Printf.fprintf c "Definition %s:=" $2; Syntax.print_pretrm_coq2 c pretm (9999) (9999); Printf.fprintf c ".\n") in
	State.coqoutfn1 := cod co1;
	State.coqctx := (Some $2,None,Some pretm)::!State.coqctx
      end
    else
      raise (State.GenericError "Lets are only allowed in global Coq files.") }
      ;
stp : stp1 { $1 }
  | stp1 SAR stp { Syntax.PAr($1,$3) }
stp1 :
  | INDTYPE { Syntax.PName "set" }
  | PROPTYPE { Syntax.PPropTp }
  | LPAREN stp RPAREN { $2 }
bid: ID { $1 } | BLANK { "" }
ids: bid { [$1] }
  | bid ids { ($1::$2) }
;
tpids: LPAREN ids COLON stp RPAREN { (List.map (fun x -> (x,$4)) $2) }
  | LPAREN ids COLON stp RPAREN tpids { (List.append (List.map (fun x -> (x,$4)) $2) $6) }
;
preterm: preterm1 { $1 }
  | preterm preterm1 { Syntax.PAp($1,$2) }
  | preterm EQ preterm { Syntax.PAp(Syntax.PAp(Syntax.PEq,$1),$3) }
  | preterm NEQ preterm { Syntax.PAp(Syntax.PAp(Syntax.PNEq,$1),$3) }
  | preterm MEM preterm { Syntax.PAp(Syntax.PAp(Syntax.PName "In",$1),$3) }
  | preterm NMEM preterm { Syntax.PAp(Syntax.PNeg,Syntax.PAp(Syntax.PAp(Syntax.PName "In",$1),$3)) }
  | preterm SUBQ preterm { Syntax.PAp(Syntax.PAp(Syntax.PName "Subq",$1),$3) }
  | preterm NSUBQ preterm { Syntax.PAp(Syntax.PNeg,Syntax.PAp(Syntax.PAp(Syntax.PName "Subq",$1),$3)) }
  | preterm IMP preterm { Syntax.PAp(Syntax.PAp(Syntax.PImplies,$1),$3) }
  | preterm CONJ preterm { Syntax.PAp(Syntax.PAp(Syntax.PAnd,$1),$3) }
  | preterm DISJ preterm { Syntax.PAp(Syntax.PAp(Syntax.POr,$1),$3) }
  | preterm IFF preterm { Syntax.PAp(Syntax.PAp(Syntax.PIff,$1),$3) }
  | NEG preterm { Syntax.PAp(Syntax.PNeg,$2) }
  | ALL ids COMMA preterm { Syntax.PAll(List.map (fun x -> (x,Syntax.PName("set"))) $2,$4) }
  | ALL ids COLON stp COMMA preterm { Syntax.PAll(List.map (fun x -> (x,$4)) $2,$6) }
  | ALL tpids COMMA preterm { Syntax.PAll($2,$4) }
  | EX ID COMMA preterm { Syntax.PEx([($2,Syntax.PName("set"))],$4) }
  | EX ID COLON stp COMMA preterm { Syntax.PEx([($2,$4)],$6) }
  | EXU ID COLON stp COMMA preterm { Syntax.PExU($2,$4,$6) }
  | LAM ids DARR preterm { Syntax.PULam($2,$4) }
  | LAM ids COLON stp DARR preterm { Syntax.PLam(List.map (fun x -> (x,$4)) $2,$6) }
  | LAM tpids DARR preterm { List.fold_right (fun (x,a) m -> Syntax.PLam([(x,a)],m)) $2 $4 }
  | LLET bid DEQ preterm IN preterm { Syntax.PLet($2,$4,$6) }
  | LLET bid COLON stp DEQ preterm IN preterm { Syntax.PTLet($2,$4,$6,$8) }
;
preterm1: LPAREN preterm RPAREN { $2 }
  | LPAREN preterm COLON preterm RPAREN { $2 }
  | ID { Syntax.PName($1) }
  | FALSE     { Syntax.PFalse }
  | TRUE     { Syntax.PTrue }
  | POLY1 stp1 { Syntax.PAp(Syntax.PName $1,$2) }
  | POLY2 stp1 stp1 { Syntax.PAp(Syntax.PAp(Syntax.PName $1,$2),$3) }
  | NARY1 INT  { Syntax.PAp(Syntax.PName $1,Syntax.PInt $2) }
  | NARY2 INT INT { Syntax.PAp(Syntax.PAp(Syntax.PName $1,Syntax.PInt $2),Syntax.PInt $3) }
;
ignorepfterm: ignorepfterm1 { () }
  | ignorepfterm ignorepfterm1 { () }
  | ignorepfterm EQ ignorepfterm { () }
  | ignorepfterm NEQ ignorepfterm { () }
  | ignorepfterm MEM ignorepfterm { () }
  | ignorepfterm NMEM ignorepfterm { () }
  | ignorepfterm SUBQ ignorepfterm { () }
  | ignorepfterm NSUBQ ignorepfterm { () }
  | ignorepfterm IMP ignorepfterm { () }
  | ignorepfterm CONJ ignorepfterm { () }
  | ignorepfterm DISJ ignorepfterm { () }
  | ignorepfterm IFF ignorepfterm { () }
  | NEG ignorepfterm { () }
  | ALL ids COLON ignorepfterm COMMA ignorepfterm { () }
  | ALL tpids COMMA ignorepfterm { () }
  | EX ID COLON ignorepfterm COMMA ignorepfterm { () }
  | EXU ID COLON ignorepfterm COMMA ignorepfterm { () }
  | LAM ids DARR ignorepfterm { () }
  | LAM ids COLON ignorepfterm DARR ignorepfterm { () }
  | LAM tpids DARR ignorepfterm { () }
  | LLET bid DEQ ignorepfterm IN ignorepfterm { () }
  | LLET bid COLON ignorepfterm DEQ ignorepfterm IN ignorepfterm { () }
;
ignorepfterm1: LPAREN ignorepfterm RPAREN { () }
  | LPAREN ignorepfterm COLON ignorepfterm RPAREN { () }
  | ID { () }
  | FALSE     { () }
  | POLY1 ignorepfterm1 { () }
  | POLY2 ignorepfterm1 ignorepfterm1 { () }
  | NARY1 INT  { () }
  | NARY2 INT INT { () }
;
