(* File: satallaxmain.ml *)
(* Author: Chad E Brown *)
(* Created: September 2010 - moved most of this from satallax.ml to satallaxmain.ml in September 2011 *)

open Flags
open Syntax
open State
open Search
open Proofterm

exception InputHelpError of string
exception InputError of string
exception UnclassifiedError

let coqfile = ref "";; 

(*** Schedule for determining nontheorems ***)
let counterstrategy_schedule_1 = [
("satmode2a",10.0);
("satmode3b",10.0);
("satmode2",10.0);
("satmode3",10.0);
("mode0d",10.0);
("satmode1",10.0);
];;

(*** Satallax 2.7 schedule. ***)
(*** 68 modes, 299.1 total time, 4865 problems ***)
let strategy_schedule_2_7 = [
("mode438",0.2);
("mode439",0.2);
("mode495",0.2);
("mode371",2.7);
("mode446",2.0);
("mode447",2.8);
("mode445",1.0);
("mode456",0.3);
("mode375",0.2);
("mode405",0.6);
("mode412",0.8);
("mode455",1.9);
("mode450",0.2);
("mode496",2.6);
("mode379",3.4);
("mode448",0.2);
("mode389",0.6);
("mode388",3.7);
("mode457",0.5);
("mode453",0.2);
("mode497",0.2);
("mode454",1.7);
("mode451",0.4);
("mode400",0.3);
("mode498",3.0);
("mode459",0.4);
("mode411",0.4);
("mode461",0.2);
("mode460",0.2);
("mode393",0.2);
("mode499",3.5);
("mode458",1.2);
("mode464",1.5);
("mode485",2.3);
("mode466",0.3);
("mode467",0.3);
("mode500",4.6);
("mode398",3.1);
("mode469",0.8);
("mode471",0.9);
("mode484",2.0);
("mode473",0.5);
("mode479",7.6);
("mode501",7.0);
("mode474",0.7);
("mode502",2.2);
("mode406",3.7);
("mode213",2.4);
("mode481",3.5);
("mode493",13.6);
("mode503",7.0);
("mode504",1.4);
("mode480",1.4);
("mode483",5.8);
("mode478",2.9);
("mode482",1.8);
("mode505",2.5);
("mode490",11.8);
("mode401",54.9);
("mode487",6.2);
("mode506",7.0);
("mode507",3.5);
("mode492",10.1);
("mode368",25.8);
("mode491",10.0);
("mode508",11.8);
("mode433",14.2);
("mode494",28.0);
];;

(*** Satallax 2.5 schedule. Use this if a proof is requested. ***)
(*** 56 modes, 226.1 total time ***)
let strategy_schedule_2_5 = [
("mode175",0.1);
("mode288",0.1);
("mode238",0.1);
("mode188",0.2);
("mode19c",0.1);
("mode289",0.1);
("mode252",0.5);
("mode245",0.1);
("mode249m2",0.1);
("mode253",0.1);
("mode293",0.5);
("mode163",0.1);
("mode236",0.2);
("mode295",0.2);
("mode272",0.1);
("mode244m5",0.4);
("mode4a",0.1);
("mode299",0.5);
("mode233",0.8);
("mode261",0.6);
("mode290",0.5);
("mode213",1.1);
("mode185",0.1);
("mode257",0.3);
("mode93",0.1);
("mode223m2",2.4);
("mode204",6.6);
("mode205",1.1);
("mode86",0.7);
("mode8a",0.4);
("mode294",0.3);
("mode276",2.3);
("mode267",0.9);
("mode264",2.4);
("mode279",4.6);
("mode251",3.2);
("mode122c",21.1);
("mode273",3.4);
("mode172",3.0);
("mode14",5.4);
("mode250",19.2);
("mode108",2.0);
("mode282",2.1);
("mode6",2.2);
("mode223",17.4);
("mode283",11.4);
("mode208",3.1);
("mode173",10.2);
("mode280",3.9);
("mode274",9.9);
("mode269",14.0);
("mode252c",9.0);
("mode177",27.3);
("mode165",18.5);
("mode301",1.0);
("mode300",10.0)
];;

let print_help () =
  (print_string "Usage: satallax [-[VvN]] [-verb <int>] [-P <PicoMus>] [-M <modedir>] [-m <modefile>] [-t <timeout in seconds>] [-p <pfformat>] <problemfile>";
   print_newline();
   print_string "-M <dir> : Set the directory in which the mode file is stored.";
   print_newline();
   print_string "       The default mode directory is the 'modes' subdirectory of the Satallax directory.";
   print_newline();
   print_string "-m : Mode";
   print_newline();
   print_string "-P <file> : PicoMus executable file";
   print_newline();
   print_string "-E <file> : E prover executable file";
   print_newline();
   print_string "-V : Print version number and quit";
   print_newline();
   print_string "-v : Verbose";
   print_newline();
   print_string "-N : Try to determine if the problem is a non-theorem (Satisfiable or CounterSatisfiable)";
   print_newline();
   print_string "-verb <int> : Verbosity of given level, -verb 0 means silent";
   print_newline();
   print_string "-c [<file>|-] : Create a Coq version of problem, with a proof script if -p is included and proof search succeeds";
   print_newline();
   print_string "-C : The problem is given as a Coq file instead of as a THF file.";
   print_newline();
   print_string "-G : A Coq file containing multiple conjectures is given. Try to prove each of them independently.";
   print_newline();
   print_string "-p [tstp|coqscript|coqspfterm|hocore|modeltrue|model|isar]: Output a kind of proof object";
   print_newline());;

(*** Load the mode (error if cannot find it) ***)
let comment_line_p l =
  if (String.length l = 0) then
    true
  else
    (l.[0] = ';');;

let rec read_mode_file mf =
  let l = input_line mf in
  if (comment_line_p l) then
    read_mode_file mf
  else
    read_mode_file_value mf l
and read_mode_file_value mf flagname =
  let l = input_line mf in
  if (comment_line_p l) then
    read_mode_file_value mf flagname
  else if (l = "true") then
    begin
      set_bool_flag flagname true;
      read_mode_file mf
    end
  else if (l = "false") then
    begin
      set_bool_flag flagname false;
      read_mode_file mf
    end
  else
    begin
      set_int_flag flagname (int_of_string l);
      read_mode_file mf
    end

let modedir = ref (Config.satallaxdir ^ "/modes")
  
let load_mode m =
  let modefile = (!modedir ^ "/" ^ m) in
  if (Sys.file_exists modefile) then
    begin
      try
	read_mode_file (open_in modefile)
      with
      | End_of_file -> ()
    end
  else
    raise (InputError ("Could not find mode " ^ modefile));;

let read_coq_file (f:string) =
  if (!verbosity > 20) then Printf.printf "Starting to read Coq file %s\n" f;
  coqinchannel := if (f = "") then stdin else (open_in f);
  let ch = Lexing.from_channel !coqinchannel in
  try
    while true do
      Coqparser.documentitem Coqlexer.token ch
    done
  with
    Coqlexer.Eof ->
      begin
	if (!verbosity > 20) then Printf.printf "End of Coq file\n";
	if ((!coqglobalfile) && (not ((!coqinchannel) = stdin))) then
	  let p = pos_in !coqinchannel in
	  let j = ref 0 in
	  begin
	    seek_in !coqinchannel 0;
	    List.iter
	      (fun (x,i) ->
		if (!verbosity > 20) then Printf.printf "End of Coq file %d %d\n" i (!j);
		match x with
		| Some g -> if (!verbosity > 20) then g stdout; g !coqoutchannel; seek_in !coqinchannel i; j := i
		| None -> while (!j < i) do (incr j; let z = input_char !coqinchannel in output_char !coqoutchannel z) done
		      )
	      (List.rev (!State.coqinticks));
	    while (!j < p) do (incr j; let z = input_char !coqinchannel in output_char !coqoutchannel z) done;
	  end;
	  close_in !coqinchannel;
	  close_out !coqoutchannel
      end

let read_thf_file (f:string) (include_fun : string -> unit) =
  let ch = Lexing.from_channel (if (f = "") then stdin else (open_in f)) in
  let old_include_fun = !st_include_fun in
  st_include_fun := include_fun;
(***  List.iter Tptp_config.process_thf (Tptp_parser.tptp_file Tptp_lexer.token ch); ***)
  ignore (Tptp_parser.tptp_file Tptp_lexer.token ch);
  if (!verbosity > 4) then Printf.printf "Finished reading thf file %s\n" f;
  st_include_fun := old_include_fun

let rec find_read_thf_file_r odir dir f =
  let ff = (dir ^ "/" ^ f) in
  if (Sys.file_exists ff) then
    read_thf_file ff (find_read_thf_file odir)
  else if (String.length dir > 1) then
    find_read_thf_file_r odir (Filename.dirname dir) f
  else
    raise (FileNotFound f)
and find_read_thf_file dir f =
  let ff = (dir ^ "/" ^ f) in
  if (Sys.file_exists ff) then
    read_thf_file ff (find_read_thf_file dir)
  else
    begin
      try
	let tptpdir = Sys.getenv "TPTP" in
	let tff = (tptpdir ^ "/" ^ f) in
	if (Sys.file_exists tff) then
	  read_thf_file tff (find_read_thf_file dir)
	else
	  find_read_thf_file_r dir dir f
      with
      | Not_found -> find_read_thf_file_r dir dir f
    end;;

st_find_read_thf_fun := find_read_thf_file;;

(*** If the slave got a final result, then use it. ***)
let handle_slave_return pstatus =
  begin
    if (!verbosity > 4) then
      Printf.printf "slave returned with status %d\n" pstatus
    else ();
    if (pstatus >= 10) then exit pstatus else ()
  end;;

let printnumaxiomsflag : bool ref = ref false;;
let selectaxiomsflag : bool ref = ref false;;

let process_command_line_args () =
  let argc = Array.length Sys.argv in
  begin
    if (argc = 1) then (Version.print_version(); print_newline(); print_help(); exit 1) else
    let i = ref 1 in
    while (!i < argc) do
      (match Sys.argv.(!i) with
      | "-numaxioms" -> incr i; printnumaxiomsflag := true
      | "-selectaxioms" -> (*** This is only to experiment with different selections and (order) of the axioms/conjecture. ***)
	  begin (*** giving nothing for a problem with n axioms/conjecture is equivalent to giving -selectaxioms n (n-1) ... 0 ***)
	    selectaxiomsflag := true;
	    incr i; let num = (int_of_string Sys.argv.(!i)) in
	    for j = 0 to num - 1 do
	      incr i; let i2 = (int_of_string Sys.argv.(!i)) in
	      select_axioms_list := i2 :: !select_axioms_list
	    done
	  end
      | "-P" -> (incr i; slaveargs := (Sys.argv.(!i)::"-P"::!slaveargs); Config.picomus := Sys.argv.(!i))
      | "-E" -> (incr i; slaveargs := (Sys.argv.(!i)::"-E"::!slaveargs); Config.eprover := Sys.argv.(!i))
      | "-m" -> (incr i; mode := ((Sys.argv.(!i)) :: (!mode)))
      | "-M" ->
	  begin
	    incr i;
	    let mdir = Sys.argv.(!i) in
	    slaveargs := (mdir::"-M"::!slaveargs);
	    modedir := mdir
	  end
      | "-t" -> (incr i; timeout := (Some (float_of_string Sys.argv.(!i))))
      | "-slave" -> (incr i; slave := true)
      |	"-C" -> (incr i; slaveargs := ("-C"::!slaveargs); coqlocalfile := true)
      |	"-G" -> (incr i; coqglobalfile := true)
      | "-c" ->
	  begin
	    incr i;
	    let cf = Sys.argv.(!i) in
	    slaveargs := (cf::"-c"::!slaveargs);
	    coq := true;
	    if (cf = "-") then
	      coqoutchannel := stdout
	    else
	      begin
		coqfile := cf;
		coqoutchannel := (open_out cf);
	      end
	  end
      | "-p" ->
	  begin
	    incr i;
	    let pfkind = Sys.argv.(!i) in
	    slaveargs := (pfkind::"-p"::!slaveargs);
	    if ((String.lowercase pfkind) = "tstp") then
	      mkproofterm := Some TSTP
	    else if ((String.lowercase pfkind) = "coqscript") then
	      mkproofterm := Some CoqScript
	    else if ((String.lowercase pfkind) = "coqspfterm") then
	      mkproofterm := Some CoqSPfTerm
	    else if ((String.lowercase pfkind) = "hocore") then
	      mkproofterm := Some HOCore
	    else if ((String.lowercase pfkind) = "model") then
	      mkproofterm := Some Model
	    else if ((String.lowercase pfkind) = "modeltrue") then
	      mkproofterm := Some ModelTrue
	    else if ((String.lowercase pfkind) = "isar") then
        begin
	        mkproofterm := Some IsarScript;
          Flag.result_coq := false;
          Flag.result_isabellehol := true
        end
	    else
	      raise (InputHelpError ("Unknown kind of proof " ^ pfkind ^ " for -p"))
	  end
      | "-verb" ->
	  begin
	    incr i;
	    let cf = Sys.argv.(!i) in
	    slaveargs := (cf::"-verb"::!slaveargs);
	    verbosity := (int_of_string cf)
	  end
      |	"-N" ->
	  begin
	    incr i;
	    slaveargs := ("-N"::!slaveargs);
	    nontheorem := true;
	  end
      |	"-foffiles" -> (*** This is only for testing and debugging interaction with FO provers like E. ***)
	  begin
	    incr i;
	    slaveargs := ("-foffiles"::!slaveargs);
	    foffiles := true;
	  end
      | "" -> raise (InputHelpError "Problem processing command line arguments")
      |	"-" -> incr i; problemfile := ""
      | option ->
	  (if (option.[0] = '-') then
            for j = 1 to String.length option - 1 do
	      match option.[j] with
	      | 'v' -> slaveargs := ("-v"::!slaveargs); verbosity := 5
	      | 'V' -> Version.print_version() ; print_newline(); exit 0
	      | _ -> raise (InputHelpError (String.concat " " ["Unknown command line argument";String.make 1 (option.[j])]))
            done
	  else
	    begin
	      problemfile := option
	    end);
	  incr i)
    done
  end

let check_search_pfterm_ok () =
  if (get_bool_flag "USE_E") then
    begin
      raise (GenericError("Proofs cannot currently be reported when E is used (either set flag USE_E to false or do not use -p)"))
    end;;

let search_main () =
  match (!mode) with
  | (_::_) ->
      begin
	try
	  init_flags();
	  ignore (List.map load_mode (!mode));
	  begin
	    basetypestobool := get_bool_flag "BASETYPESTOPROP";
	    match (!mkproofterm) with
	    | Some TSTP ->
		begin
		  if (not (!coq)) then
		    begin (*** -p tstp implies -c - if -c was not given. Output TSTP proof via Coq out channel. - Chad, July 2012 ***)
		      coq := true;
		      coqoutchannel := stdout;
		    end;
		end
	    | Some CoqScript ->
		begin
		  if (not (!coq)) then
		    begin (*** -p coqscript implies -c - if -c was not given. - Chad, June 2011 ***)
		      coq := true;
		      coqoutchannel := stdout;
		    end;
		end
	    | Some CoqSPfTerm ->
		begin
		  coq2 := true;
		  if (not (!coq)) then
		    begin (*** -p coqscript implies -c - if -c was not given. - Chad, June 2011 ***)
		      coq := true;
		      coqoutchannel := stdout;
		    end;
		end
	    | Some IsarScript -> (*FIXME code in this section, and in related sections, need refactoring. names are a bit misleading.*)
		begin
		  if (not (!coq)) then
		    begin
		      coq := true;
		      coqoutchannel := stdout;
		    end;
		end
	    | _ -> ()
	  end;
	  if (!verbosity > 8) then print_flags () else ();
          (match (!mkproofterm) with Some _ -> check_search_pfterm_ok () | None -> ());
	  let s = (get_timeout_default 0.0) in
	  if (s > 0.0) then
	    begin
	      if ((!nontheorem) && (get_bool_flag "SPLIT_GLOBAL_DISJUNCTIONS") && (s >= 0.2)) then (set_timer (s *. 0.5); mult_timeout 0.5) else (set_timer s; timeout := Some 0.0);
	      if (!coq) then coq_init();
	      if (!coqlocalfile) then read_coq_file (!problemfile) else read_thf_file (!problemfile) (find_read_thf_file (Filename.dirname (!problemfile)));
	      if ((!coq) && (not (!coq2))) then print_coqsig !coqoutchannel;
	      if (!printnumaxiomsflag) then print_num_axioms ();
	      if (!selectaxiomsflag) then select_axioms ();
	      search ()
	    end
	  else
	    begin
	      if (!coq) then coq_init();
	      if (!coqlocalfile) then read_coq_file (!problemfile) else read_thf_file (!problemfile) (find_read_thf_file (Filename.dirname (!problemfile)));
	      if ((!coq) && (not (!coq2)) && (not (!slave))) then print_coqsig !coqoutchannel;
	      if (!printnumaxiomsflag) then print_num_axioms ();
	      if (!selectaxiomsflag) then select_axioms ();
	      search ()
	    end
	with
	| Unsatisfiable(r) ->
	    if (not (!nontheorem)) then (*** Some subgoals may have timedout and the last one reported Unsatisfiable ***)
	    begin
	      begin
		match (!mkproofterm,r) with
		| (Some TSTP,Some r) ->
		    if (!coqoutchannel = stdout) then
		      begin
			print_string "% SZS output start Proof"; print_newline();
		      end;
		    let c = !coqoutchannel in
		    begin
		      try print_tstp c r
		      with CoqProofTooBig coqproofsize ->
			begin
			  if (!verbosity > 0) then Printf.printf "%% SZS status Success\nCoq Proof Too Big: %d steps\n" coqproofsize;
			  exit 26;
			end
		    end;
		    if (c = stdout) then
		      begin
			print_string "% SZS output end Proof"; print_newline();
		      end
		    else
		      close_out c;
		| (Some CoqScript,Some r) ->
		    if (!coqoutchannel = stdout) then
		      begin
			print_string "% SZS output start Proof"; print_newline();
			print_string "% Coq Proof Script"; print_newline()
		      end;
		    let c = !coqoutchannel in
		    begin
		      try print_coq_proofscript c r
		      with CoqProofTooBig coqproofsize ->
			begin
			  if (!verbosity > 0) then Printf.printf "%% SZS status Success\nCoq Proof Too Big: %d steps\n" coqproofsize;
			  exit 26;
			end
		    end;
		    if (c = stdout) then
		      begin
			print_string "% SZS output end Proof"; print_newline();
		      end
		    else
		      close_out c;
		| (Some CoqSPfTerm,Some r) ->
		    if (!coqoutchannel = stdout) then
		      begin
			print_string "% SZS output start Proof"; print_newline();
			print_string "% Coq Proof Script"; print_newline()
		      end;
		    let c = !coqoutchannel in
		    begin
		      try print_coq_sproofterm c r
		      with CoqProofTooBig coqproofsize ->
			begin
			  if (!verbosity > 0) then Printf.printf "%% SZS status Success\nCoq Proof Too Big: %d steps\n" coqproofsize;
			  exit 26;
			end
		    end;
		    if (c = stdout) then
		      begin
			print_string "% SZS output end Proof"; print_newline();
		      end
		    else
		      close_out c;
		| (Some HOCore,Some r) ->
		    print_string "% Higher-Order Unsat Core BEGIN"; print_newline();
		    print_hocore stdout r;
		    print_string "% Higher-Order Unsat Core END"; print_newline();
		| (Some IsarScript, Some r) ->
		    if (!coqoutchannel = stdout) then
		      begin
			      print_string "(*% SZS output start Proof*)"; print_newline();
			      print_string "(*% Isar Proof Script*)"; print_newline()
		      end;
		    let c = !coqoutchannel in
		      begin
		        try print_coq_proofscript c r
		        with CoqProofTooBig coqproofsize -> (*FIXME naming is misleading*)
			        begin
			          if (!verbosity > 0) then Printf.printf "%% SZS status Success\nIsar Proof Too Big: %d steps\n" coqproofsize;
			          exit 26;
			        end
		      end;
		      if (c = stdout) then
		        begin
			        print_string "(*% SZS output end Proof*)"; print_newline();
		        end
		      else
		        close_out c;
		| _ -> ()
	      end;
	      match !conjecture with
	      | Some _ -> (if (!verbosity > 0) then (Printf.printf "(*%% SZS status Theorem*)\n"; Printf.printf "(*%% %s *)\n" (String.concat " " (!mode))); exit 20)
	      | None -> (if (!verbosity > 0) then (Printf.printf "(*%% SZS status Unsatisfiable*)\n"; Printf.printf "(*%% %s *)\n" (String.concat " " (!mode))); exit 25)
	    end
	    else
	      raise Timeout (*** if nontheorem was set, then assume we timedout here. ***)
	| Satisfiable ->
	    begin
	      match !conjecture with
	      | Some _ -> (if (!verbosity > 0) then Printf.printf "%% SZS status CounterSatisfiable\n"; exit 10)
	      | None -> (if (!verbosity > 0) then Printf.printf "%% SZS status Satisfiable\n"; exit 15)
	    end
      end
  | [] -> (*** Use a strategy schedule ***)
      let strategy_schedule =
	if (!nontheorem) then
	  begin
	    counterstrategy_schedule_1
	  end
	else if (mkprooftermp ()) then
	  begin
	    strategy_schedule_2_5
	  end
        else
	  begin
	    strategy_schedule_2_7
	  end
      in
      let scheduletime = List.fold_left (fun s1 (x,s2) -> (s1 +. s2)) 0.0 strategy_schedule in (*** total time of schedule ***)
      let timeoutfac = max 1. ((get_timeout_default scheduletime) /. scheduletime) in (*** timeout factor ***)
      let schedulenum = ref (List.length strategy_schedule) in
      List.iter
	(fun (m,s) ->
	  decr schedulenum;
	  if ((!schedulenum) > 0) then
	    let s1 = s *. timeoutfac in
	    begin
	      match (!timeout) with
	      | Some s2 ->
		  begin
		    if (s2 > s1) then
		      begin
			begin
			  if (!verbosity > 4) then
			    (Printf.printf "Starting slave::%s\n" (String.concat " " (List.rev ((!problemfile)::(string_of_float s1)::"-t"::m::"-m"::"-slave"::(!slaveargs)))); flush stdout);
			  match (Unix.system (String.concat " " (List.rev ((!problemfile)::(string_of_float s1)::"-t"::m::"-m"::"-slave"::(!slaveargs))))) with
			  | (Unix.WEXITED pstatus) ->
			      handle_slave_return pstatus
			  | _ ->
			      if (!verbosity > 0) then
				Printf.printf "slave returned with unknown status\n"
			      else ()
			end;
			timeout := (Some (s2 -. s1))
		      end
		    else
		      begin
			begin
			    (*** Final call - don't tell it it's a slave. ***)
			  if (!verbosity > 4) then
			    (Printf.printf "Starting final slave::%s\n" (String.concat " " (List.rev ((!problemfile)::(string_of_float s2)::"-t"::m::"-m"::(!slaveargs)))); flush stdout);
			  match (Unix.system (String.concat " " (List.rev ((!problemfile)::(string_of_float s2)::"-t"::m::"-m"::(!slaveargs))))) with
			  | (Unix.WEXITED pstatus) ->
			      handle_slave_return pstatus ; exit pstatus
			  | _ ->
			      if (!verbosity > 0) then
				(Printf.printf "slave returned with unknown status\n" ; exit 3)
			      else ()
			end;
			raise Timeout
		      end
		  end
	      | None ->
		  begin
		    if (!verbosity > 4) then
		      (Printf.printf "Starting slave::%s\n" (String.concat " " (List.rev ((!problemfile)::(string_of_float s1)::"-t"::m::"-m"::"-slave"::(!slaveargs)))); flush stdout);
		    match (Unix.system (String.concat " " (List.rev ((!problemfile)::(string_of_float s1)::"-t"::m::"-m"::"-slave"::(!slaveargs))))) with
		    | (Unix.WEXITED pstatus) ->
			handle_slave_return pstatus
		    | _ ->
			if (!verbosity > 0) then
			  Printf.printf "slave returned with unknown status\n"
			else ()
		  end
	    end
	  else
	    begin
	      match (!timeout) with
	      | Some s2 ->
		  begin
		(*** Final call - don't tell it it's a slave. ***)
		    if (!verbosity > 4) then
		      (Printf.printf "Starting final slave::%s\n" (String.concat " " (List.rev ((!problemfile)::(string_of_float s2)::"-t"::m::"-m"::(!slaveargs)))); flush stdout);
		    match (Unix.system (String.concat " " (List.rev ((!problemfile)::(string_of_float s2)::"-t"::m::"-m"::(!slaveargs))))) with
		    | (Unix.WEXITED pstatus) ->
			handle_slave_return pstatus ; exit pstatus
		    | _ ->
			if (!verbosity > 0) then
			  (Printf.printf "slave returned with unknown status\n" ; exit 3)
			else ()
		  end	      
	      | None ->
		  begin
		(*** Final call with no timeout - don't tell it it's a slave. ***)
		    if (!verbosity > 4) then
		      (Printf.printf "Starting final slave::%s\n" (String.concat " " (List.rev ((!problemfile)::m::"-m"::(!slaveargs)))); flush stdout);
		    match (Unix.system (String.concat " " (List.rev ((!problemfile)::m::"-m"::(!slaveargs))))) with
		    | (Unix.WEXITED pstatus) ->
			handle_slave_return pstatus ; exit pstatus
		    | _ ->
			if (!verbosity > 0) then
			  (Printf.printf "slave returned with unknown status\n" ; exit 3)
			else ()
		  end
	    end
	      )
	strategy_schedule;
      raise Timeout
